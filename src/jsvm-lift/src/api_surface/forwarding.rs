//! Source-local callable indexing and bounded wrapper-chain specialization.
//! Preserve original and specializing invocation provenance, not execution proof.
mod factories;
mod frame;
mod values;

use super::{
    callables::{member_parts, DispatchOperands},
    expression_symbol, unparenthesized, xhr_binding_is_not_reassigned, ApiBindingWitness, BTreeSet,
    CallExpression, Callable, Collector, Expression, GetSpan, Result, Scoping, Span, SymbolId,
    WorkBudget,
};
pub(super) use factories::collect_returned_values;
use factories::resolve_returned_callable;
use frame::{append_local_witnesses, instantiate, FrameProof, Wrapper};
use oxc_ast::{
    ast::{Argument, Function},
    AstKind,
};
use oxc_semantic::Semantic;
use oxc_syntax::scope::ScopeId;
use std::{cell::RefCell, collections::BTreeMap, rc::Rc};
use values::{ArgumentList, ValueBuilder};

pub(super) struct FrameContext<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    constants: &'c ProvenConstantEnvironment,
    callables: &'c CallableIndex,
}

impl<'s, 'c> From<&Collector<'s, 'c>> for FrameContext<'s, 'c> {
    fn from(collector: &Collector<'s, 'c>) -> Self {
        Self {
            source: collector.source,
            scoping: collector.scoping,
            constants: collector.constants,
            callables: collector.callables,
        }
    }
}

enum LocalBinding<'a> {
    Function(&'a Function<'a>),
    Initializer {
        value: &'a Expression<'a>,
        declaration: Span,
    },
}

/// Anchor a deferred root-scope lookup to an actual specializing
/// invocation. Initializer expressions still use their own evaluation
/// positions, never the later position of a caller that reads their result.
#[derive(Clone, Copy)]
struct DeferredLookup<'s, 'a> {
    semantic: &'s Semantic<'a>,
    invocation: Span,
}

impl DeferredLookup<'_, '_> {
    fn initialized(self, symbol: SymbolId, declaration: Span, budget: &WorkBudget) -> Result<bool> {
        let scoping = self.semantic.scoping();
        if scoping.symbol_scope_id(symbol) != scoping.root_scope_id()
            || declaration.end > self.invocation.start
        {
            return Ok(false);
        }
        Ok(
            crate::cfg_order::prove_event_completion_before_nested_event(
                self.semantic,
                declaration,
                self.invocation,
                budget,
            )?,
        )
    }
}

enum BindingOrigin<'a> {
    Declaration(SymbolId, &'a Function<'a>),
    Expression(&'a Expression<'a>),
}

/// Reuse the already validated semantic AST, rather than reparsing the source
/// or textually resolving names. Mutable lexical definitions and direct eval
/// in a visible scope preclude an exact local target.
type ProofKey = (u32, u32, u32, u32);
type CachedProofs = BTreeMap<ProofKey, Option<Rc<FrameProof>>>;

pub(super) struct WrapperIndex<'a> {
    bindings: BTreeMap<SymbolId, LocalBinding<'a>>,
    script_root_functions: BTreeMap<SymbolId, String>,
    eval_scopes: BTreeSet<ScopeId>,
    positional_limit: usize,
    frame_proofs: RefCell<CachedProofs>,
}

impl<'a> WrapperIndex<'a> {
    pub(super) fn collect(semantic: &Semantic<'a>, budget: &WorkBudget) -> Result<Self> {
        let scoping = semantic.scoping();
        let mut bindings = BTreeMap::new();
        let mut script_root_functions = BTreeMap::new();
        let mut eval_scopes = BTreeSet::new();
        // An acyclic wrapper chain can consume at most the sum of all
        // fixed formal counts before its final two API positions plus dispatch receiver and target. Keep a
        // bounded prefix large enough for every such chain; any truncation
        // carries an unknown-tail witness rather than inventing missing args.
        let mut positional_limit = 4usize;
        for node in semantic.nodes().iter() {
            budget.consume(1)?;
            let params = match node.kind() {
                AstKind::Function(fun) => fun.params.items.len(),
                AstKind::ArrowFunctionExpression(fun) => fun.params.items.len(),
                _ => 0,
            };
            positional_limit = positional_limit.saturating_add(params);
            if let AstKind::CallExpression(call) = node.kind() {
                if matches!(unparenthesized(&call.callee), Expression::Identifier(id) if id.name == "eval")
                {
                    eval_scopes.insert(node.scope_id());
                }
            }
        }
        for node in semantic.nodes().iter() {
            budget.consume(1)?;
            let (symbol, binding) = match node.kind() {
                AstKind::Function(fun) if fun.is_declaration() => {
                    if !Wrapper::function(fun, scoping).is_some_and(|wrapper| {
                        wrapper.invocation().is_some()
                            || (wrapper.returns_value
                                && matches!(
                                    unparenthesized(wrapper.body),
                                    Expression::Identifier(_)
                                        | Expression::StaticMemberExpression(_)
                                        | Expression::ComputedMemberExpression(_)
                                ))
                    }) {
                        continue;
                    }
                    let Some(symbol) = fun.id.as_ref().and_then(|id| id.symbol_id.get()) else {
                        continue;
                    };
                    (symbol, LocalBinding::Function(fun))
                }
                AstKind::VariableDeclarator(decl) => {
                    let Some(symbol) = decl
                        .id
                        .get_binding_identifier()
                        .and_then(|id| id.symbol_id.get())
                    else {
                        continue;
                    };
                    if !scoping.symbol_flags(symbol).is_const_variable() {
                        continue;
                    }
                    let Some(value) = decl.init.as_ref() else {
                        continue;
                    };
                    if !matches!(
                        unparenthesized(value),
                        Expression::Identifier(_)
                            | Expression::FunctionExpression(_)
                            | Expression::ArrowFunctionExpression(_)
                            | Expression::CallExpression(_)
                    ) {
                        continue;
                    }
                    (
                        symbol,
                        LocalBinding::Initializer {
                            value,
                            declaration: decl.span,
                        },
                    )
                }
                _ => continue,
            };
            if !scoping.symbol_redeclarations(symbol).is_empty()
                || !xhr_binding_is_not_reassigned(scoping, symbol)
            {
                continue;
            }
            if matches!(binding, LocalBinding::Function(_)) {
                let name = scoping.symbol_name(symbol);
                let mut dynamic = false;
                for scope in &eval_scopes {
                    budget.consume(1)?;
                    if scoping.find_binding(*scope, name.into()) == Some(symbol) {
                        dynamic = true;
                        break;
                    }
                }
                if dynamic {
                    continue;
                }
                if !semantic.source_type().is_module()
                    && scoping.symbol_scope_id(symbol) == scoping.root_scope_id()
                {
                    script_root_functions.insert(symbol, name.to_owned());
                }
            }
            bindings.insert(symbol, binding);
        }
        Ok(Self {
            bindings,
            script_root_functions,
            eval_scopes,
            positional_limit,
            frame_proofs: RefCell::new(BTreeMap::new()),
        })
    }

    pub(super) fn root_mutation_targets(&self) -> impl Iterator<Item = (&str, String)> {
        self.script_root_functions
            .iter()
            .map(|(symbol, name)| (name.as_str(), format!("wrapper_global:{symbol:?}")))
    }

    fn frame_has_dynamic_scope(
        &self,
        wrapper: &Wrapper<'_>,
        scoping: &Scoping,
        budget: &WorkBudget,
    ) -> Result<bool> {
        for symbol in wrapper.symbols() {
            for scope in &self.eval_scopes {
                budget.consume(1)?;
                if scoping.find_binding(*scope, scoping.symbol_name(symbol).into()) == Some(symbol)
                {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    fn frame_proof(
        &self,
        wrapper: &Wrapper<'_>,
        sink: Span,
        semantic: &Semantic<'_>,
        collector: &FrameContext<'_, '_>,
        budget: &WorkBudget,
    ) -> Result<Option<Rc<FrameProof>>> {
        let key = (wrapper.span.start, wrapper.span.end, sink.start, sink.end);
        if let Some(proof) = self.frame_proofs.borrow().get(&key) {
            return Ok(proof.clone());
        }
        let proof = if self.frame_has_dynamic_scope(wrapper, collector.scoping, budget)?
            || wrapper.uses_arguments_object()
        {
            None
        } else {
            Some(Rc::new(FrameProof::collect(
                wrapper,
                sink,
                semantic,
                collector.constants,
                budget,
            )?))
        };
        self.frame_proofs.borrow_mut().insert(key, proof.clone());
        Ok(proof)
    }

    fn may_resolve(&self, expr: &Expression<'_>, scoping: &Scoping) -> bool {
        expression_symbol(scoping, expr).is_some_and(|symbol| self.bindings.contains_key(&symbol))
            || matches!(
                unparenthesized(expr),
                Expression::FunctionExpression(_)
                    | Expression::ArrowFunctionExpression(_)
                    | Expression::CallExpression(_)
            )
    }

    fn binding_origin(
        &self,
        mut expr: &'a Expression<'a>,
        scoping: &Scoping,
        budget: &WorkBudget,
        witnesses: &mut Vec<ApiBindingWitness>,
        alias_kind: &str,
        mut deferred: Option<DeferredLookup<'_, 'a>>,
    ) -> Result<Option<BindingOrigin<'a>>> {
        let mut visited = BTreeSet::new();
        loop {
            budget.consume(1)?;
            let Some(symbol) = expression_symbol(scoping, expr) else {
                return Ok(Some(BindingOrigin::Expression(expr)));
            };
            let Some(binding) = self.bindings.get(&symbol) else {
                return Ok(Some(BindingOrigin::Expression(expr)));
            };
            if !visited.insert(symbol) {
                return Ok(None);
            }
            match binding {
                LocalBinding::Function(fun) => {
                    return Ok(Some(BindingOrigin::Declaration(symbol, fun)))
                }
                LocalBinding::Initializer { value, declaration } => {
                    if expr.span().start < declaration.end {
                        let Some(lookup) = deferred else {
                            return Ok(None);
                        };
                        if !lookup.initialized(symbol, *declaration, budget)? {
                            return Ok(None);
                        }
                    }
                    // Following an alias reads its initializer at creation
                    // time; do not transfer a later invocation anchor.
                    deferred = None;
                    witnesses.push(ApiBindingWitness {
                        kind: alias_kind.into(),
                        start: value.span().start,
                        end: value.span().end,
                    });
                    expr = value;
                }
            }
        }
    }

    fn factory_call(
        &self,
        expr: &'a Expression<'a>,
        scoping: &Scoping,
        budget: &WorkBudget,
        witnesses: &mut Vec<ApiBindingWitness>,
    ) -> Result<Option<&'a CallExpression<'a>>> {
        let Some(BindingOrigin::Expression(expr)) = self.binding_origin(
            expr,
            scoping,
            budget,
            witnesses,
            "wrapper_return_alias",
            None,
        )?
        else {
            return Ok(None);
        };
        Ok(match unparenthesized(expr) {
            Expression::CallExpression(call) if !call.optional => Some(call),
            _ => None,
        })
    }

    fn resolve(
        &self,
        expr: &'a Expression<'a>,
        scoping: &Scoping,
        budget: &WorkBudget,
        dependencies: &mut BTreeSet<String>,
        witnesses: &mut Vec<ApiBindingWitness>,
        deferred: Option<DeferredLookup<'_, 'a>>,
    ) -> Result<Option<Wrapper<'a>>> {
        Ok(
            match self.binding_origin(
                expr,
                scoping,
                budget,
                witnesses,
                "wrapper_alias",
                deferred,
            )? {
                Some(BindingOrigin::Declaration(symbol, fun)) => {
                    if self.script_root_functions.contains_key(&symbol) {
                        dependencies.insert(format!("wrapper_global:{symbol:?}"));
                    }
                    Wrapper::function(fun, scoping)
                }
                Some(BindingOrigin::Expression(value)) => Wrapper::expression(value, scoping),
                None => None,
            },
        )
    }
}

/// Resolve the same native dispatch head used by direct calls, but from the
/// argument values in the specializing caller frame. A captured function
/// value does not inherit its former member receiver.
fn forwarded_dispatch<'a>(
    callee: &'a Expression<'a>,
    original_args: &'a [Argument<'a>],
    args: &ArgumentList<'a>,
    span: Span,
    builder: &mut ValueBuilder<'_, 'a>,
    collector: &FrameContext<'_, '_>,
) -> Result<Option<Callable>> {
    let scoping = collector.scoping;
    let constants = collector.constants;
    let Some((original_object, key)) = member_parts(callee, scoping, constants) else {
        return Ok(None);
    };
    let Some(object) = builder.expression(original_object)?.expression() else {
        return Ok(None);
    };
    Ok(collector
        .callables
        .resolve_dispatch_values(
            DispatchOperands {
                original_object,
                object,
                key: &key,
                original_args,
                args,
                span,
            },
            collector.source,
            scoping,
            constants,
        )
        .map(|dispatch| dispatch.callable))
}

/// Follow a chain with concrete source argument origins. Each step has a
/// unique function span and charges the analysis budget; cycles cannot grow
/// the trace. Original syntactic API sites are emitted by the normal walker.
#[derive(Clone, Copy)]
pub(super) struct InvocationSite<'a> {
    pub(super) callee: &'a Expression<'a>,
    pub(super) arguments: &'a [Argument<'a>],
    pub(super) span: Span,
    pub(super) constructor: bool,
}

pub(super) fn specialize<'a>(
    site: InvocationSite<'a>,
    semantic: &Semantic<'a>,
    wrappers: &WrapperIndex<'a>,
    collector: &mut Collector<'_, '_>,
    budget: &WorkBudget,
) -> Result<()> {
    let scoping = collector.scoping;
    let indexed =
        collector
            .callables
            .resolve(site.callee, collector.source, scoping, collector.constants);
    if indexed
        .as_ref()
        .is_some_and(|callable| !callable.is_returned())
        || (indexed.is_none() && !wrappers.may_resolve(site.callee, scoping))
    {
        return Ok(());
    }
    let context = FrameContext::from(&*collector);
    let mut callee = site.callee;
    let mut builder = ValueBuilder::new(
        None,
        scoping,
        collector.constants,
        wrappers.positional_limit,
        budget,
    );
    let mut args = builder.call(site.arguments)?;
    let mut witnesses = Vec::new();
    let mut dependencies = BTreeSet::new();
    if builder.used_iterator {
        dependencies.insert("rest_iterator".into());
    }
    let mut visited = BTreeSet::new();
    let mut constructor = site.constructor;
    let mut captured_target = false;
    let mut sink = site.span;
    let mut indexed = indexed;
    loop {
        budget.consume(1)?;
        let callable = if let Some(callable) = indexed.take() {
            Some(callable)
        } else if !visited.is_empty() {
            context
                .callables
                .resolve(callee, context.source, scoping, context.constants)
                .map(|mut callable| {
                    if captured_target {
                        callable.capture_as_argument();
                    }
                    callable
                })
        } else {
            None
        };
        let callable = if callable.is_some() {
            callable
        } else if let Some(returned) =
            resolve_returned_callable(callee, semantic, wrappers, &context, budget)?
        {
            witnesses.extend(returned.witnesses);
            dependencies.extend(returned.dependencies);
            Some(returned.callable)
        } else {
            None
        };
        if let Some(mut callable) = callable {
            if callable.callable_as(constructor) {
                callable.prefix.append_forwarded(
                    args.values,
                    args.unknown_tail,
                    collector.source,
                    scoping,
                    collector.constants,
                );
                callable.mark_forwarding(&witnesses, sink);
                collector.emit_forwarded(site.callee, &callable, site.span, &dependencies);
            }
            return Ok(());
        }
        if constructor {
            return Ok(());
        }
        let Some(wrapper) = wrappers.resolve(
            callee,
            scoping,
            budget,
            &mut dependencies,
            &mut witnesses,
            (!visited.is_empty() && !captured_target).then_some(DeferredLookup {
                semantic,
                invocation: site.span,
            }),
        )?
        else {
            return Ok(());
        };
        if !visited.insert((wrapper.span.start, wrapper.span.end)) {
            return Ok(());
        }
        let Some((target, forwarded, sink_span, is_new)) = wrapper.invocation() else {
            return Ok(());
        };
        witnesses.push(ApiBindingWitness {
            kind: "wrapper_definition".into(),
            start: wrapper.span.start,
            end: wrapper.span.end,
        });
        witnesses.push(ApiBindingWitness {
            kind: "forwarded_invocation".into(),
            start: sink_span.start,
            end: sink_span.end,
        });
        sink = sink_span;
        let Some(proof) = wrappers.frame_proof(&wrapper, sink, semantic, &context, budget)? else {
            return Ok(());
        };
        let Some(mut builder) = instantiate(
            &wrapper,
            &args,
            &proof,
            &context,
            wrappers.positional_limit,
            budget,
        )?
        else {
            return Ok(());
        };
        append_local_witnesses(&wrapper, &mut witnesses);
        let next_args = builder.call(forwarded)?;
        if !is_new {
            if let Some(mut callable) =
                forwarded_dispatch(target, forwarded, &next_args, sink, &mut builder, &context)?
            {
                if builder.used_iterator {
                    dependencies.insert("rest_iterator".into());
                }
                callable.mark_forwarding(&witnesses, sink);
                collector.emit_forwarded(site.callee, &callable, site.span, &dependencies);
                return Ok(());
            }
        }
        let Some(target_expr) = builder.expression(target)?.expression() else {
            return Ok(());
        };
        if builder.used_iterator {
            dependencies.insert("rest_iterator".into());
        }
        captured_target = !std::ptr::eq(target, target_expr);
        args = next_args;
        callee = target_expr;
        constructor = is_new;
    }
}
