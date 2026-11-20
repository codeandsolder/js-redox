//! Specialize single-expression local forwarding chains using existing lexical
//! parameter proof and native callable evidence. Separate original body sink
//! sites from their call-specific specializations. No AST rewriting/evaluation.
use super::{
    callables::{member_parts, DispatchOperands, ForwardedValue, PositionalArguments},
    *,
};
use crate::source_tree_callflow::stable_parameter_index;
use oxc_ast::{
    ast::{
        Argument, ArrayExpression, ArrayExpressionElement, FormalParameters, Function,
        FunctionBody, Statement,
    },
    AstKind,
};
use oxc_semantic::Semantic;
use oxc_syntax::scope::ScopeId;
use std::{collections::BTreeMap, rc::Rc};

type ArgumentList<'a> = PositionalArguments<'a, 'a>;

/// Carry value origins rather than copying syntax into a different scope.
/// Materialized arrays share their positional contents; spreading a known
/// array or rest value consumes those positions, while apply uses indexed
/// contents without depending on Array.prototype[Symbol.iterator].
struct ValueBuilder<'s, 'a> {
    parameters: Option<(&'s Parameters, &'s ArgumentList<'a>)>,
    scoping: &'s Scoping,
    limit: usize,
    budget: &'s WorkBudget,
    used_iterator: bool,
}

impl<'s, 'a> ValueBuilder<'s, 'a> {
    fn new(
        parameters: Option<(&'s Parameters, &'s ArgumentList<'a>)>,
        scoping: &'s Scoping,
        limit: usize,
        budget: &'s WorkBudget,
    ) -> Self {
        Self {
            parameters,
            scoping,
            limit,
            budget,
            used_iterator: false,
        }
    }

    fn expression(&mut self, expr: &'a Expression<'a>) -> Result<ForwardedValue<'a, 'a>> {
        self.budget.consume(1)?;
        if let Some((params, origin)) = self.parameters {
            if let Some(symbol) = expression_symbol(self.scoping, expr) {
                if params.forwardable.contains(&symbol) {
                    if params.rest == Some(symbol) {
                        let mut positions = ArgumentList::default();
                        self.extend(&mut positions, origin, params.fixed.len(), expr.span())?;
                        return Ok(ForwardedValue::Array {
                            span: expr.span(),
                            positions: Rc::new(positions),
                        });
                    }
                    if let Some(index) = stable_parameter_index(
                        self.scoping,
                        symbol,
                        params.fixed.iter().copied().map(Some),
                    ) {
                        return Ok(origin.value(index));
                    }
                }
            }
            if let Expression::ArrayExpression(array) = unparenthesized(expr) {
                let positions = self.array(array)?;
                return Ok(ForwardedValue::Array {
                    span: expr.span(),
                    positions: Rc::new(positions),
                });
            }
        }
        Ok(ForwardedValue::Expression(expr))
    }

    fn extend(
        &self,
        result: &mut ArgumentList<'a>,
        origin: &ArgumentList<'a>,
        start: usize,
        span: Span,
    ) -> Result<()> {
        let available = origin.values.len().saturating_sub(start);
        let count = self
            .limit
            .saturating_sub(result.values.len())
            .min(available);
        self.budget.consume(count as u64)?;
        result
            .values
            .extend(origin.values.iter().skip(start).take(count).cloned());
        result.unknown_tail = if count < available {
            Some(span)
        } else {
            origin.unknown_tail
        };
        Ok(())
    }

    fn spread(
        &mut self,
        result: &mut ArgumentList<'a>,
        expression: &'a Expression<'a>,
        span: Span,
    ) -> Result<()> {
        let value = self.expression(expression)?;
        match value {
            ForwardedValue::Array { positions, .. } => {
                self.used_iterator = true;
                self.extend(result, &positions, 0, span)?;
            }
            ForwardedValue::Expression(expr) => {
                if let Expression::ArrayExpression(array) = unparenthesized(expr) {
                    // An expression captured in a preceding caller is not
                    // evaluated in the current wrapper's lexical frame.
                    let mut captured = Self::new(None, self.scoping, self.limit, self.budget);
                    let positions = captured.array(array)?;
                    self.used_iterator = true;
                    self.extend(result, &positions, 0, span)?;
                } else {
                    result.unknown_tail = Some(span);
                }
            }
            _ => result.unknown_tail = Some(span),
        }
        Ok(())
    }

    fn full(&self, result: &mut ArgumentList<'a>, span: Span) -> bool {
        if result.values.len() >= self.limit {
            result.unknown_tail = Some(span);
        }
        result.unknown_tail.is_some()
    }

    fn call(&mut self, args: &'a [Argument<'a>]) -> Result<ArgumentList<'a>> {
        let mut result = ArgumentList::default();
        self.budget.consume(args.len() as u64)?;
        for arg in args {
            if self.full(&mut result, arg.span()) {
                break;
            }
            if let Argument::SpreadElement(spread) = arg {
                self.spread(&mut result, &spread.argument, arg.span())?;
            } else if let Some(expr) = arg.as_expression() {
                result.values.push(self.expression(expr)?);
            }
            if result.unknown_tail.is_some() {
                break;
            }
        }
        Ok(result)
    }

    fn array(&mut self, array: &'a ArrayExpression<'a>) -> Result<ArgumentList<'a>> {
        let mut result = ArgumentList::default();
        self.budget.consume(array.elements.len() as u64)?;
        for element in &array.elements {
            if self.full(&mut result, element.span()) {
                break;
            }
            match element {
                ArrayExpressionElement::Elision(_) => {
                    result.values.push(ForwardedValue::Unknown(None))
                }
                ArrayExpressionElement::SpreadElement(spread) => {
                    self.spread(&mut result, &spread.argument, spread.span)?;
                }
                _ => {
                    if let Some(expr) = element.as_expression() {
                        result.values.push(self.expression(expr)?);
                    }
                }
            }
            if result.unknown_tail.is_some() {
                break;
            }
        }
        Ok(result)
    }
}

struct Parameters {
    fixed: Vec<SymbolId>,
    rest: Option<SymbolId>,
    forwardable: BTreeSet<SymbolId>,
}

impl Parameters {
    fn from_formals(params: &FormalParameters<'_>, scoping: &Scoping) -> Option<Self> {
        let fixed = params
            .items
            .iter()
            .map(|param| {
                if param.initializer.is_some() {
                    return None;
                }
                param.pattern.get_binding_identifier()?.symbol_id.get()
            })
            .collect::<Option<Vec<_>>>()?;
        let rest = if let Some(rest) = &params.rest {
            let symbol = rest
                .rest
                .argument
                .get_binding_identifier()?
                .symbol_id
                .get()?;
            if !xhr_binding_is_not_reassigned(scoping, symbol) {
                return None;
            }
            // A rest array can be mutated via a member/escape even if its
            // binding is never reassigned. Only direct spread uses are trusted.
            Some(symbol)
        } else {
            None
        };
        let all = fixed.iter().copied().chain(rest);
        let mut unique = BTreeSet::new();
        if !all.into_iter().all(|symbol| unique.insert(symbol)) {
            return None;
        }
        Some(Self {
            fixed,
            rest,
            forwardable: BTreeSet::new(),
        })
    }
}

struct Wrapper<'a> {
    span: Span,
    params: Parameters,
    body: &'a Expression<'a>,
}

fn single_expression<'a>(body: &'a FunctionBody<'a>) -> Option<&'a Expression<'a>> {
    match body.statements.as_slice() {
        [Statement::ReturnStatement(statement)] => statement.argument.as_ref(),
        [Statement::ExpressionStatement(statement)] => Some(&statement.expression),
        _ => None,
    }
}

#[derive(Default)]
struct ArgumentsObjectProbe(bool);

impl<'a> Visit<'a> for ArgumentsObjectProbe {
    fn visit_identifier_reference(&mut self, id: &oxc_ast::ast::IdentifierReference<'a>) {
        self.0 |= id.name == "arguments";
    }
}

fn uses_arguments_object(expression: &Expression<'_>) -> bool {
    let mut probe = ArgumentsObjectProbe::default();
    probe.visit_expression(expression);
    probe.0
}

impl<'a> Wrapper<'a> {
    fn function(fun: &'a Function<'a>, scoping: &Scoping) -> Option<Self> {
        if fun.generator {
            return None;
        }
        Some(Self {
            span: fun.span,
            params: Parameters::from_formals(&fun.params, scoping)?,
            body: single_expression(fun.body.as_ref()?)?,
        })
    }

    fn expression(expr: &'a Expression<'a>, scoping: &Scoping) -> Option<Self> {
        match unparenthesized(expr) {
            Expression::FunctionExpression(fun) => Self::function(fun, scoping),
            Expression::ArrowFunctionExpression(fun) => {
                let body = match &fun.body {
                    oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) => single_expression(body)?,
                    body => body.as_expression()?,
                };
                Some(Self {
                    span: fun.span,
                    params: Parameters::from_formals(&fun.params, scoping)?,
                    body,
                })
            }
            _ => None,
        }
    }

    fn invocation(&self) -> Option<(&'a Expression<'a>, &'a [Argument<'a>], Span, bool)> {
        let expr = unparenthesized(self.body);
        let expr = if let Expression::AwaitExpression(awaited) = expr {
            unparenthesized(&awaited.argument)
        } else {
            expr
        };
        match expr {
            Expression::CallExpression(call) if !call.optional => {
                Some((&call.callee, &call.arguments, call.span, false))
            }
            Expression::NewExpression(new) => Some((&new.callee, &new.arguments, new.span, true)),
            _ => None,
        }
    }
}

enum LocalBinding<'a> {
    Function(&'a Function<'a>),
    Initializer {
        value: &'a Expression<'a>,
        after: u32,
    },
}

/// Reuse the already validated semantic AST, rather than reparsing the source
/// or textually resolving names. Mutable lexical definitions and direct eval
/// in a visible scope preclude an exact local target.
pub(super) struct WrapperIndex<'a> {
    bindings: BTreeMap<SymbolId, LocalBinding<'a>>,
    script_root_functions: BTreeMap<SymbolId, String>,
    eval_scopes: BTreeSet<ScopeId>,
    positional_limit: usize,
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
                    if !Wrapper::function(fun, scoping)
                        .is_some_and(|wrapper| wrapper.invocation().is_some())
                    {
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
                    ) {
                        continue;
                    }
                    (
                        symbol,
                        LocalBinding::Initializer {
                            value,
                            after: decl.span.end,
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
        })
    }

    pub(super) fn root_mutation_targets(&self) -> impl Iterator<Item = (&str, String)> {
        self.script_root_functions
            .iter()
            .map(|(symbol, name)| (name.as_str(), format!("wrapper_global:{symbol:?}")))
    }

    fn parameters_have_dynamic_scope(
        &self,
        parameters: &Parameters,
        scoping: &Scoping,
        budget: &WorkBudget,
    ) -> Result<bool> {
        for symbol in parameters.fixed.iter().copied().chain(parameters.rest) {
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

    fn may_resolve(&self, expr: &Expression<'_>, scoping: &Scoping) -> bool {
        expression_symbol(scoping, expr).is_some_and(|symbol| self.bindings.contains_key(&symbol))
            || matches!(
                unparenthesized(expr),
                Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_)
            )
    }

    fn resolve(
        &self,
        mut expr: &'a Expression<'a>,
        scoping: &Scoping,
        budget: &WorkBudget,
        dependencies: &mut BTreeSet<String>,
        witnesses: &mut Vec<ApiBindingWitness>,
    ) -> Result<Option<Wrapper<'a>>> {
        let mut visited = BTreeSet::new();
        loop {
            budget.consume(1)?;
            if let Some(wrapper) = Wrapper::expression(expr, scoping) {
                return Ok(Some(wrapper));
            }
            let Some(symbol) = expression_symbol(scoping, expr) else {
                return Ok(None);
            };
            if !visited.insert(symbol) {
                return Ok(None);
            }
            let Some(binding) = self.bindings.get(&symbol) else {
                return Ok(None);
            };
            match binding {
                LocalBinding::Function(fun) => {
                    if self.script_root_functions.contains_key(&symbol) {
                        dependencies.insert(format!("wrapper_global:{symbol:?}"));
                    }
                    return Ok(Wrapper::function(fun, scoping));
                }
                LocalBinding::Initializer { value, after } => {
                    if expr.span().start < *after {
                        return Ok(None);
                    }
                    witnesses.push(ApiBindingWitness {
                        kind: "wrapper_alias".into(),
                        start: value.span().start,
                        end: value.span().end,
                    });
                    expr = value;
                }
            }
        }
    }
}

/// A caller's object literal must not become exact property evidence after
/// the wrapper exposes or changes it. Only direct callee/argument uses in the
/// one forwarding invocation are accepted, including parenthesized references.
fn parameter_is_direct(
    symbol: SymbolId,
    sink: Span,
    semantic: &Semantic<'_>,
    constants: &ProvenConstantEnvironment,
    spread_safe: bool,
    budget: &WorkBudget,
) -> Result<bool> {
    let scoping = semantic.scoping();
    for reference_id in scoping.get_resolved_reference_ids(symbol) {
        budget.consume(1)?;
        let reference = scoping.get_reference(*reference_id);
        if reference.is_write() || reference.flags().is_member_write_target() {
            return Ok(false);
        }
        let mut current = semantic.nodes().get_node(reference.node_id()).span();
        let mut dispatch_member = false;
        let mut inside_array = false;
        let mut accepted = false;
        for id in semantic.nodes().ancestor_ids(reference.node_id()) {
            budget.consume(1)?;
            let kind = semantic.nodes().kind(id);
            match kind {
                AstKind::ParenthesizedExpression(_) => {}
                AstKind::ArrayExpression(_) if !dispatch_member => {
                    inside_array = true;
                }
                AstKind::SpreadElement(_) if !dispatch_member && (inside_array || spread_safe) => {}
                AstKind::StaticMemberExpression(member)
                    if !dispatch_member
                        && !member.optional
                        && member.object.span() == current
                        && matches!(member.property.name.as_str(), "call" | "apply") =>
                {
                    dispatch_member = true;
                }
                AstKind::ComputedMemberExpression(member)
                    if !dispatch_member
                        && !member.optional
                        && member.object.span() == current
                        && static_string(&member.expression, scoping, constants)
                            .as_deref()
                            .is_some_and(|name| matches!(name, "call" | "apply")) =>
                {
                    dispatch_member = true;
                }
                AstKind::CallExpression(call) => {
                    accepted =
                        call.span == sink && (!dispatch_member || call.callee.span() == current);
                    break;
                }
                AstKind::NewExpression(new) => {
                    accepted = !dispatch_member && new.span == sink;
                    break;
                }
                _ => break,
            }
            current = kind.span();
        }
        if !accepted {
            return Ok(false);
        }
    }
    Ok(true)
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
    collector: &Collector<'_, '_>,
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
pub(super) fn specialize<'a>(
    call: &'a CallExpression<'a>,
    semantic: &Semantic<'a>,
    wrappers: &WrapperIndex<'a>,
    collector: &mut Collector<'_, '_>,
    budget: &WorkBudget,
) -> Result<()> {
    let scoping = collector.scoping;
    if call.optional || !wrappers.may_resolve(&call.callee, scoping) {
        return Ok(());
    }
    let mut callee = &call.callee;
    let mut builder = ValueBuilder::new(None, scoping, wrappers.positional_limit, budget);
    let mut args = builder.call(&call.arguments)?;
    let mut witnesses = Vec::new();
    let mut dependencies = BTreeSet::new();
    if builder.used_iterator {
        dependencies.insert("rest_iterator".into());
    }
    let mut visited = BTreeSet::new();
    let mut constructor = false;
    let mut captured_target = false;
    let mut sink = call.span;
    loop {
        budget.consume(1)?;
        if !visited.is_empty() {
            if let Some(mut callable) =
                collector
                    .callables
                    .resolve(callee, collector.source, scoping, collector.constants)
            {
                if captured_target {
                    callable.capture_as_argument();
                }
                if callable.callable_as(constructor) {
                    callable.prefix.append_forwarded(
                        args.values,
                        args.unknown_tail,
                        collector.source,
                        scoping,
                        collector.constants,
                    );
                    callable.mark_forwarding(&witnesses, sink);
                    collector.emit_forwarded(&call.callee, callable, call.span, &dependencies);
                }
                return Ok(());
            }
        }
        if constructor {
            return Ok(());
        }
        let Some(mut wrapper) =
            wrappers.resolve(callee, scoping, budget, &mut dependencies, &mut witnesses)?
        else {
            return Ok(());
        };
        if !visited.insert((wrapper.span.start, wrapper.span.end))
            || wrappers.parameters_have_dynamic_scope(&wrapper.params, scoping, budget)?
            || uses_arguments_object(wrapper.body)
        {
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
        for (index, symbol) in wrapper
            .params
            .fixed
            .iter()
            .copied()
            .chain(wrapper.params.rest)
            .enumerate()
        {
            let spread_safe = wrapper.params.rest == Some(symbol)
                || match args.value(index) {
                    ForwardedValue::Array { .. } => true,
                    ForwardedValue::Expression(expr) => {
                        matches!(unparenthesized(expr), Expression::ArrayExpression(_))
                    }
                    _ => false,
                };
            if parameter_is_direct(
                symbol,
                sink,
                semantic,
                collector.constants,
                spread_safe,
                budget,
            )? {
                wrapper.params.forwardable.insert(symbol);
            } else if wrapper.params.rest == Some(symbol) {
                return Ok(());
            }
        }
        let environment = Some((&wrapper.params, &args));
        let mut builder =
            ValueBuilder::new(environment, scoping, wrappers.positional_limit, budget);
        let next_args = builder.call(forwarded)?;
        if !is_new {
            if let Some(mut callable) =
                forwarded_dispatch(target, forwarded, &next_args, sink, &mut builder, collector)?
            {
                if builder.used_iterator {
                    dependencies.insert("rest_iterator".into());
                }
                callable.mark_forwarding(&witnesses, sink);
                collector.emit_forwarded(&call.callee, callable, call.span, &dependencies);
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
