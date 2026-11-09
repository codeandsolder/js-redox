//! Static *callsite* specializations of original lexical helper functions.
//!
//! The actual helper source remains intact. Each derivative substitutes
//! constant arguments only at references to the same parameter SymbolId,
//! and is then passed through the existing JS deobfuscator. This is useful
//! program recovery, not an independently runnable replacement module.
use crate::source_tree_callflow::{CallerView, ResolvedCallEdge};
use anyhow::{ensure, Result};
use jsvm_safe_core::{eval_static_primitive_with_resolver, StaticPrimitiveValue};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, BindingPattern, CallExpression, Expression, FormalParameters, Function,
    IdentifierReference, NewExpression, Statement, VariableDeclaration, VariableDeclarationKind,
    WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{operator::UnaryOperator, scope::ScopeFlags, symbol::SymbolId};
use rolldown_redox::ecmascript::parse_program;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct LiteralCall {
    pub helper: String,
    pub constants: Vec<(usize, String)>,
    pub span: Span,
}

fn unparen<'a>(mut expr: &'a Expression<'a>) -> &'a Expression<'a> {
    while let Expression::ParenthesizedExpression(inner) = expr {
        expr = &inner.expression;
    }
    expr
}

fn literal_argument<'a>(arg: &'a Argument<'a>, source: &'a str) -> Option<String> {
    let expr = unparen(arg.as_expression()?);
    let literal = match expr {
        Expression::NumericLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::StringLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::BigIntLiteral(_) => true,
        Expression::UnaryExpression(unary) => {
            matches!(
                unary.operator,
                UnaryOperator::UnaryPlus | UnaryOperator::UnaryNegation
            ) && matches!(unparen(&unary.argument), Expression::NumericLiteral(_))
        }
        _ => false,
    };
    if !literal {
        return None;
    }
    source
        .get(expr.span().start as usize..expr.span().end as usize)
        .map(str::to_owned)
}

struct Calls<'s> {
    source: &'s str,
    scoping: &'s Scoping,
    calls: Vec<LiteralCall>,
}

impl<'a> Visit<'a> for Calls<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Expression::Identifier(callee) = unparen(&call.callee) {
                let unresolved = callee.reference_id.get().is_some_and(|reference| {
                    self.scoping.get_reference(reference).symbol_id().is_none()
                });
                if unresolved {
                    let constants = call
                        .arguments
                        .iter()
                        .enumerate()
                        .filter_map(|(index, argument)| {
                            literal_argument(argument, self.source).map(|literal| (index, literal))
                        })
                        .collect::<Vec<_>>();
                    if !constants.is_empty() {
                        self.calls.push(LiteralCall {
                            helper: callee.name.to_string(),
                            constants,
                            span: call.span,
                        });
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

pub fn literal_calls(source: &str) -> Result<Vec<LiteralCall>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    ensure!(parsed.is_clean(), "invalid JavaScript in handler");
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let mut visitor = Calls {
        source,
        scoping: semantic.semantic.scoping(),
        calls: Vec::new(),
    };
    visitor.visit_program(&parsed.program);
    Ok(visitor.calls)
}

/// Infer exact primitive values for stable lexical bindings. This accepts
/// arbitrary expressions handled by the shared side-effect-free ECMAScript
/// evaluator, not only literal initializers or aliases with the same spelling.
/// Fixed-point iteration handles const declarations and aliases that occur
/// before their source binding in the AST without inventing unknown values.
struct StablePrimitiveBindings<'s> {
    scoping: &'s Scoping,
    values: BTreeMap<SymbolId, StaticPrimitiveValue>,
    changed: bool,
}

impl<'a> Visit<'a> for StablePrimitiveBindings<'_> {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        if matches!(
            declaration.kind,
            VariableDeclarationKind::Const | VariableDeclarationKind::Let
        ) {
            for declarator in &declaration.declarations {
                let (BindingPattern::BindingIdentifier(id), Some(init)) =
                    (&declarator.id, &declarator.init)
                else {
                    continue;
                };
                let Some(symbol) = id.symbol_id.get() else {
                    continue;
                };
                if self.values.contains_key(&symbol)
                    || !self.scoping.symbol_redeclarations(symbol).is_empty()
                    || self
                        .scoping
                        .get_resolved_reference_ids(symbol)
                        .iter()
                        .any(|reference| self.scoping.get_reference(*reference).is_write())
                {
                    continue;
                }
                let value = eval_static_primitive_with_resolver(init, &|id| {
                    id.reference_id
                        .get()
                        .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
                        .and_then(|source| self.values.get(&source).cloned())
                });
                if let Some(value) = value.filter(|value| value.render().is_some()) {
                    self.values.insert(symbol, value);
                    self.changed = true;
                }
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

/// Primitive arguments at exact source-resolved original callsites. Resolve
/// literal expressions and immutable lexical constant chains by SymbolId.
/// Calls with a spread stop collecting at its position: later indexes cannot
/// be reliably mapped to formal parameters.
#[derive(Clone, Debug)]
enum ExpressionInput {
    Parameter(usize),
    Literal(String),
}

#[derive(Clone, Debug)]
struct ExpressionEdit {
    start: usize,
    end: usize,
    input: ExpressionInput,
}

/// A copy of one original argument expression, with all allowable identifier
/// substitutions proven against the original lexical semantic SymbolIds.
#[derive(Clone, Debug)]
struct OriginalComputedArgument {
    source: String,
    edits: Vec<ExpressionEdit>,
}

impl OriginalComputedArgument {
    fn evaluate(&self, parameters: &BTreeMap<usize, String>) -> Option<String> {
        // No parameter-dependent inputs means the ordinary original-source
        // literal collector already evaluated this expression once.
        if !self
            .edits
            .iter()
            .any(|edit| matches!(edit.input, ExpressionInput::Parameter(_)))
        {
            return None;
        }
        let mut source = self.source.clone();
        for edit in self.edits.iter().rev() {
            let value = match &edit.input {
                ExpressionInput::Parameter(index) => parameters.get(index),
                ExpressionInput::Literal(value) => Some(value),
            };
            // Leave unknown parameters unresolved rather than requiring
            // every reference to be known: JavaScript short-circuit and
            // conditional evaluation may never read an unknown branch.
            if let Some(value) = value {
                source.replace_range(edit.start..edit.end, &format!("({value})"));
            }
        }
        // Parse the substituted expression as ordinary JavaScript and reuse
        // the shared side-effect-free evaluator. Unresolved identifiers,
        // effectful calls, assignments, and unsupported coercions remain
        // unknown rather than inferred.
        let wrapped = format!("const __redox_value=({source});");
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &wrapped, SourceType::unambiguous());
        if !parsed.is_clean() {
            return None;
        }
        let Statement::VariableDeclaration(decl) = parsed.program.body.first()? else {
            return None;
        };
        let expr = decl.declarations.first()?.init.as_ref()?;
        jsvm_safe_core::eval_static_primitive(expr)?.render()
    }
}

struct ExpressionInputs<'s> {
    scoping: &'s Scoping,
    expression_start: u32,
    parameters: &'s BTreeMap<SymbolId, usize>,
    values: &'s BTreeMap<SymbolId, StaticPrimitiveValue>,
    edits: Vec<ExpressionEdit>,
}

impl<'a> Visit<'a> for ExpressionInputs<'_> {
    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        let Some(symbol) = id
            .reference_id
            .get()
            .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
        else {
            return;
        };
        let input = self
            .parameters
            .get(&symbol)
            .copied()
            .map(ExpressionInput::Parameter)
            .or_else(|| {
                self.values
                    .get(&symbol)
                    .and_then(|value| value.render())
                    .map(ExpressionInput::Literal)
            });
        if let Some(input) = input {
            self.edits.push(ExpressionEdit {
                start: (id.span.start - self.expression_start) as usize,
                end: (id.span.end - self.expression_start) as usize,
                input,
            });
        }
    }
}

fn stable_formal_parameters(
    params: &FormalParameters<'_>,
    scoping: &Scoping,
) -> BTreeMap<SymbolId, usize> {
    params
        .items
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| {
            if parameter.initializer.is_some() {
                return None;
            }
            let BindingPattern::BindingIdentifier(id) = &parameter.pattern else {
                return None;
            };
            let symbol = id.symbol_id.get()?;
            if !scoping.symbol_redeclarations(symbol).is_empty()
                || scoping
                    .get_resolved_reference_ids(symbol)
                    .iter()
                    .any(|reference| scoping.get_reference(*reference).is_write())
            {
                return None;
            }
            Some((symbol, index))
        })
        .collect()
}

struct OriginalCallLiterals<'s> {
    source: &'s str,
    scoping: &'s Scoping,
    values: BTreeMap<SymbolId, StaticPrimitiveValue>,
    sites: BTreeMap<[u32; 2], Vec<(usize, String)>>,
    computed: BTreeMap<[u32; 2], Vec<Option<OriginalComputedArgument>>>,
    functions: Vec<BTreeMap<SymbolId, usize>>,
}

impl OriginalCallLiterals<'_> {
    fn argument_value(&self, arg: &Argument<'_>) -> Option<String> {
        if let Some(literal) = literal_argument(arg, self.source) {
            return Some(literal);
        }
        eval_static_primitive_with_resolver(arg.as_expression()?, &|id| {
            id.reference_id
                .get()
                .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
                .and_then(|symbol| self.values.get(&symbol).cloned())
        })?
        .render()
    }

    fn remember(&mut self, span: Span, arguments: &[Argument<'_>]) {
        let mut constants = Vec::new();
        let mut expressions = Vec::new();
        for (index, argument) in arguments.iter().enumerate() {
            if matches!(argument, Argument::SpreadElement(_)) {
                break;
            }
            if let Some(literal) = self.argument_value(argument) {
                constants.push((index, literal));
                expressions.push(None);
                continue;
            }
            let computed = argument.as_expression().and_then(|expr| {
                let start = expr.span().start;
                let source = self.source.get(start as usize..expr.span().end as usize)?;
                let parameters = self.functions.last()?;
                let mut refs = ExpressionInputs {
                    scoping: self.scoping,
                    expression_start: start,
                    parameters,
                    values: &self.values,
                    edits: Vec::new(),
                };
                refs.visit_expression(expr);
                if !refs
                    .edits
                    .iter()
                    .any(|edit| matches!(edit.input, ExpressionInput::Parameter(_)))
                {
                    return None;
                }
                refs.edits.sort_by_key(|edit| edit.start);
                Some(OriginalComputedArgument {
                    source: source.to_owned(),
                    edits: refs.edits,
                })
            });
            expressions.push(computed);
        }
        if !constants.is_empty() {
            self.sites.insert([span.start, span.end], constants);
        }
        if expressions.iter().any(Option::is_some) {
            self.computed.insert([span.start, span.end], expressions);
        }
    }
}

impl<'a> Visit<'a> for OriginalCallLiterals<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.functions
            .push(stable_formal_parameters(&function.params, self.scoping));
        walk::walk_function(self, function, flags);
        self.functions.pop();
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        self.functions
            .push(stable_formal_parameters(&function.params, self.scoping));
        walk::walk_arrow_function_expression(self, function);
        self.functions.pop();
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            let offset = if matches!(
                unparen(&call.callee),
                Expression::StaticMemberExpression(member)
                    if !member.optional && member.property.name == "call"
            ) {
                1
            } else {
                0
            };
            self.remember(call.span, call.arguments.get(offset..).unwrap_or_default());
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expr: &NewExpression<'a>) {
        self.remember(expr.span, &expr.arguments);
        walk::walk_new_expression(self, expr);
    }
}

/// An analysis-only variant of a real function, specialized at exact
/// statically resolved lexical callsites in the original JavaScript.
#[derive(Debug, Clone)]
pub struct ResolvedSpecialization {
    pub helper: String,
    pub function_span: [u32; 2],
    pub constants: Vec<(usize, String)>,
    pub call_sites: BTreeSet<[u32; 2]>,
    /// One shortest original-callsite chain from the selected entrypoint
    /// to this variant. Other routes can lead to the same merged variant.
    pub example_call_chain: Vec<[u32; 2]>,
    pub original: String,
    pub specialized: String,
}

/// Track original functions containing syntax that can indirectly mutate
/// their formal parameters. In particular, mapped arguments in sloppy-mode
/// functions and direct eval can bypass ordinary symbol write tracking.
/// Suppress *forwarded* constants through these callers, while retaining
/// directly written literal arguments at their own resolved callsites.
#[derive(Default)]
struct UnsafeParameterForwarding {
    stack: Vec<[u32; 2]>,
    functions: BTreeSet<[u32; 2]>,
    dynamic_scope: bool,
}

impl UnsafeParameterForwarding {
    fn mark_enclosing(&mut self) {
        self.functions.extend(self.stack.iter().copied());
    }
}

impl<'a> Visit<'a> for UnsafeParameterForwarding {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.stack.push([function.span.start, function.span.end]);
        walk::walk_function(self, function, flags);
        self.stack.pop();
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        self.stack.push([function.span.start, function.span.end]);
        walk::walk_arrow_function_expression(self, function);
        self.stack.pop();
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if matches!(unparen(&call.callee), Expression::Identifier(id) if id.name == "eval") {
            self.mark_enclosing();
            self.dynamic_scope = true;
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        if id.name == "arguments" {
            self.mark_enclosing();
        }
    }

    fn visit_with_statement(&mut self, stmt: &WithStatement<'a>) {
        self.mark_enclosing();
        self.dynamic_scope = true;
        walk::walk_with_statement(self, stmt);
    }
}

/// Original graph state. Two paths with different constant tuples remain
/// distinct; a union of independently inferred parameter values would create
/// impossible combinations. A cycle is handled by one visit per (function,
/// entire known tuple), which is finite for the source's finite literal set.
#[derive(Clone, Debug)]
struct CallHistoryEntry {
    function: [u32; 2],
    constants: Vec<(usize, String)>,
    computed_on_incoming_edge: bool,
}

#[derive(Clone, Debug)]
struct CallContext {
    function: [u32; 2],
    constants: Vec<(usize, String)>,
    chain: Vec<[u32; 2]>,
    /// Original-callsite provenance plus exact caller constants and whether
    /// the incoming edge evaluated an argument using a known parameter.
    history: Vec<CallHistoryEntry>,
    /// Delay widening once per recursive target to expose a representative
    /// recursive iteration, then retain only truly invariant input values.
    widened_cycles: BTreeSet<[u32; 2]>,
}

/// Recover function-level variants by tracing *exact* primitive arguments and
/// immutable forwarded formal parameters through arbitrarily deep lexical
/// call chains. Every root entry starts with unknown parameters. Each emitted
/// variant is attached to at least one real resolved incoming callsite.
///
/// This is a path-specific source-reading view, not an executable replacement.
pub fn specialize_resolved_call_graph(
    original: &str,
    views: &[CallerView],
) -> Result<Vec<ResolvedSpecialization>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, original, SourceType::unambiguous());
    ensure!(parsed.is_clean(), "invalid original lexical JavaScript");
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let scoping = semantic.semantic.scoping();
    let mut unsafe_forwarding = UnsafeParameterForwarding::default();
    unsafe_forwarding.visit_program(&parsed.program);

    // Dynamic with/eval can shadow or mutate a normally resolved identifier
    // at runtime, so never substitute a value through a lexical reference in
    // those programs. Pure self-contained argument expressions still work.
    let mut bindings = StablePrimitiveBindings {
        scoping,
        values: BTreeMap::new(),
        changed: false,
    };
    if !unsafe_forwarding.dynamic_scope {
        loop {
            bindings.changed = false;
            bindings.visit_program(&parsed.program);
            if !bindings.changed {
                break;
            }
        }
    }
    let mut collector = OriginalCallLiterals {
        source: original,
        scoping,
        values: bindings.values,
        sites: BTreeMap::new(),
        computed: BTreeMap::new(),
        functions: Vec::new(),
    };
    collector.visit_program(&parsed.program);

    let mut outgoing = BTreeMap::<[u32; 2], Vec<&ResolvedCallEdge>>::new();
    for edge in views.iter().flat_map(|view| &view.reachable_edges) {
        let at = outgoing.entry(edge.from_span).or_default();
        if !at
            .iter()
            .any(|prior| prior.call.span == edge.call.span && prior.to_span == edge.to_span)
        {
            at.push(edge);
        }
    }

    type RequestKey = ([u32; 2], Vec<(usize, String)>);
    type RequestValue = (String, BTreeSet<[u32; 2]>, Vec<[u32; 2]>);
    let mut requested = BTreeMap::<RequestKey, RequestValue>::new();
    let mut pending = views
        .iter()
        .map(|view| CallContext {
            function: view.entry_span,
            constants: Vec::new(),
            chain: Vec::new(),
            history: vec![CallHistoryEntry {
                function: view.entry_span,
                constants: Vec::new(),
                computed_on_incoming_edge: false,
            }],
            widened_cycles: BTreeSet::new(),
        })
        .collect::<VecDeque<_>>();
    let mut visited = BTreeSet::<RequestKey>::new();
    while let Some(context) = pending.pop_front() {
        if !visited.insert((context.function, context.constants.clone())) {
            continue;
        }
        let Some(edges) = outgoing.get(&context.function) else {
            continue;
        };
        let incoming = context
            .constants
            .iter()
            .cloned()
            .collect::<BTreeMap<_, _>>();
        for edge in edges {
            // Computed selectors may generate infinitely many distinct
            // values along a recursive call chain. Loop invariants are
            // propagated using exact-value intersection below.
            let direct = collector.sites.get(&edge.call.span);
            let forwarded_is_safe = !unsafe_forwarding.functions.contains(&context.function);
            let mut next = Vec::new();
            let mut computed_here = false;
            for (index, arg) in edge.call.arguments.iter().enumerate() {
                if !arg.positional {
                    break;
                }
                let literal = direct
                    .and_then(|values| values.iter().find(|(at, _)| *at == index))
                    .map(|(_, literal)| literal.clone())
                    .or_else(|| {
                        forwarded_is_safe
                            .then_some(arg.caller_param_index)
                            .flatten()
                            .and_then(|from| incoming.get(&from).cloned())
                    })
                    .or_else(|| {
                        let inferred = forwarded_is_safe
                            .then(|| collector.computed.get(&edge.call.span))
                            .flatten()
                            .and_then(|args| args.get(index))
                            .and_then(Option::as_ref)
                            .and_then(|computed| computed.evaluate(&incoming));
                        computed_here |= inferred.is_some();
                        inferred
                    });
                if let Some(literal) = literal {
                    next.push((index, literal));
                }
            }
            let mut chain = context.chain.clone();
            chain.push(edge.call.span);
            if !next.is_empty() {
                let entry = requested
                    .entry((edge.to_span, next.clone()))
                    .or_insert_with(|| (edge.call.callee.clone(), BTreeSet::new(), chain.clone()));
                entry.1.insert(edge.call.span);
            }
            let mut propagated = next;
            let mut widened_cycles = context.widened_cycles.clone();
            if let Some(previous) = context
                .history
                .iter()
                .rposition(|entry| entry.function == edge.to_span)
            {
                // Literal/identity forwarding alone draws from a finite set
                // of source constants and requires no widening. A recursive
                // computed edge may create new values on each iteration.
                let computed_in_cycle = computed_here
                    || context.history[previous + 1..]
                        .iter()
                        .any(|entry| entry.computed_on_incoming_edge);
                if computed_in_cycle && !widened_cycles.insert(edge.to_span) {
                    let before = context.history[previous]
                        .constants
                        .iter()
                        .cloned()
                        .collect::<BTreeMap<_, _>>();
                    propagated.retain(|(index, value)| {
                        before.get(index).is_some_and(|prior| prior == value)
                    });
                }
            }
            let mut history = context.history.clone();
            history.push(CallHistoryEntry {
                function: edge.to_span,
                constants: propagated.clone(),
                computed_on_incoming_edge: computed_here,
            });
            pending.push_back(CallContext {
                function: edge.to_span,
                constants: propagated,
                chain,
                history,
                widened_cycles,
            });
        }
    }

    let mut specializations = Vec::new();
    for ((function_span, constants), (helper, call_sites, example_call_chain)) in requested {
        let Some(raw) = original.get(function_span[0] as usize..function_span[1] as usize) else {
            continue;
        };
        // Source function expressions, named declarations, and arrows all
        // become root function-valued initializer expressions. This preserves
        // their own parameter symbols, nested scopes, and function bodies.
        let wrapped = format!("const __redox_lexical_helper = ({raw});\n");
        // A valid expression in its original lexical context can reference
        // contextual syntax such as super. Skip only this unwrappable body,
        // not the entire set of recoverable callsites.
        let wrapper_allocator = Allocator::default();
        if !parse_program(&wrapper_allocator, &wrapped, SourceType::unambiguous()).is_clean() {
            continue;
        }
        // Select precisely the literals that can actually replace a read
        // of their formal parameter. This simultaneously drops reassigned,
        // rest/default, and unused parameters. It avoids duplicate variants
        // differing only by literals irrelevant to the recovered body.
        let mut selected = Vec::new();
        for constant in &constants {
            if specialize_function(&wrapped, std::slice::from_ref(constant))?.is_some() {
                selected.push(constant.clone());
            }
        }
        if selected.is_empty() {
            continue;
        }
        let Some(specialized) = specialize_function(&wrapped, &selected)? else {
            continue;
        };
        specializations.push(ResolvedSpecialization {
            helper,
            function_span,
            constants: selected,
            call_sites,
            example_call_chain,
            original: wrapped,
            specialized,
        });
    }
    // Different callsite literal tuples may reduce to the same viable subset.
    // Merge these instead of emitting identical helper bodies repeatedly.
    let mut deduplicated =
        BTreeMap::<([u32; 2], Vec<(usize, String)>), ResolvedSpecialization>::new();
    for candidate in specializations {
        let key = (candidate.function_span, candidate.constants.clone());
        if let Some(existing) = deduplicated.get_mut(&key) {
            existing.call_sites.extend(candidate.call_sites);
            if candidate.example_call_chain.len() < existing.example_call_chain.len() {
                existing.example_call_chain = candidate.example_call_chain;
            }
        } else {
            deduplicated.insert(key, candidate);
        }
    }
    Ok(deduplicated.into_values().collect())
}

struct FunctionCandidate {
    params: BTreeMap<usize, SymbolId>,
}

/// Never select an arbitrary nested function from an object-valued helper.
/// The helper's root source must itself declare/initialize a function.
fn root_function_params<'a>(program: &'a oxc_ast::ast::Program<'a>) -> Option<FunctionCandidate> {
    let statement = program.body.first()?;
    let formal = match statement {
        Statement::FunctionDeclaration(function) => &function.params,
        Statement::VariableDeclaration(declaration) if declaration.declarations.len() == 1 => {
            let init = declaration.declarations[0].init.as_ref()?;
            match unparen(init) {
                Expression::FunctionExpression(function) => &function.params,
                Expression::ArrowFunctionExpression(function) => &function.params,
                _ => return None,
            }
        }
        _ => return None,
    };
    let mut params = BTreeMap::new();
    for (index, item) in formal.items.iter().enumerate() {
        if item.initializer.is_some() {
            continue;
        }
        if let BindingPattern::BindingIdentifier(id) = &item.pattern {
            if let Some(symbol) = id.symbol_id.get() {
                params.insert(index, symbol);
            }
        }
    }
    Some(FunctionCandidate { params })
}

struct ParameterReferences<'s> {
    scoping: &'s Scoping,
    target: BTreeMap<SymbolId, String>,
    edits: Vec<(Span, String)>,
    unsafe_dynamic_scope: bool,
    // Nested ordinary functions own a distinct arguments object. Arrows
    // inherit the nearest enclosing non-arrow function's binding.
    // The initial helper function is at depth one.
    ordinary_function_depth: usize,
}

impl<'a> Visit<'a> for ParameterReferences<'_> {
    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        if id.name == "eval" || (id.name == "arguments" && self.ordinary_function_depth <= 1) {
            self.unsafe_dynamic_scope = true;
        }
        if let Some(symbol) = id
            .reference_id
            .get()
            .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
        {
            if let Some(literal) = self.target.get(&symbol) {
                self.edits.push((id.span, format!("({literal})")));
            }
        }
    }

    fn visit_with_statement(&mut self, _statement: &WithStatement<'a>) {
        self.unsafe_dynamic_scope = true;
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.ordinary_function_depth += 1;
        walk::walk_function(self, function, flags);
        self.ordinary_function_depth -= 1;
    }
}

/// Replace references to stable simple parameters with exact primitive literal
/// arguments. Leaves the parameter list, function name, and external closures
/// unchanged. Rejects dynamic scope and any write or arguments alias to
/// the substituted parameters.
pub fn specialize_function(source: &str, constants: &[(usize, String)]) -> Result<Option<String>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    ensure!(parsed.is_clean(), "invalid helper source");
    // Oxc's parser accepts some context-dependent syntax such as super in a
    // detached arrow. Semantic early-error validation is required for source
    // extraction: such a function may be legal only in its original class.
    let semantic = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(&parsed.program);
    if !semantic.diagnostics.is_empty() {
        return Ok(None);
    }
    let scoping = semantic.semantic.scoping();
    let Some(root) = root_function_params(&parsed.program) else {
        return Ok(None);
    };
    let mut replacements = BTreeMap::new();
    for &(index, ref literal) in constants {
        let Some(&symbol) = root.params.get(&index) else {
            return Ok(None);
        };
        if scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .any(|reference| scoping.get_reference(*reference).is_write())
        {
            return Ok(None);
        }
        replacements.insert(symbol, literal.clone());
    }
    let mut visitor = ParameterReferences {
        scoping,
        target: replacements,
        edits: Vec::new(),
        unsafe_dynamic_scope: false,
        ordinary_function_depth: 0,
    };
    visitor.visit_program(&parsed.program);
    if visitor.unsafe_dynamic_scope || visitor.edits.is_empty() {
        return Ok(None);
    }
    let mut output = source.to_owned();
    visitor
        .edits
        .sort_by_key(|(span, _)| std::cmp::Reverse(span.start));
    for (span, literal) in visitor.edits {
        output.replace_range(span.start as usize..span.end as usize, &literal);
    }
    let verification = Allocator::default();
    if !parse_program(&verification, &output, SourceType::unambiguous()).is_clean() {
        return Ok(None);
    }
    Ok(Some(output))
}

#[derive(Debug, Clone)]
pub struct Specialization {
    pub helper: String,
    pub arguments: Vec<(usize, String)>,
    pub call_sites: BTreeSet<String>,
    pub original: String,
    pub source: String,
}

/// Group same-constant callsites into one specialized helper body each.
/// Their exact arguments are included in the ID; no arbitrary case cap.
pub fn specialize_calls(
    handlers: &[(String, String)],
    helpers: &BTreeMap<String, String>,
) -> Result<Vec<Specialization>> {
    let mut requested = BTreeMap::<(String, Vec<(usize, String)>), BTreeSet<String>>::new();
    for (path, source) in handlers {
        for call in literal_calls(source)? {
            if helpers.contains_key(&call.helper) {
                requested
                    .entry((call.helper, call.constants))
                    .or_default()
                    .insert(format!("{path}:{}", call.span.start));
            }
        }
    }
    let mut output = Vec::new();
    for ((helper, args), call_sites) in requested {
        let original = &helpers[&helper];
        if let Some(source) = specialize_function(original, &args)? {
            output.push(Specialization {
                helper,
                arguments: args,
                call_sites,
                original: original.clone(),
                source,
            });
        }
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::{literal_calls, specialize_function, specialize_resolved_call_graph};
    use crate::source_tree_callflow::reconstruct_caller_views;
    use anyhow::{anyhow, Result};

    #[test]
    fn function_call_wrapper_propagates_literal_selectors_to_true_leaf() -> Result<()> {
        let source = r#"const leaf=(opcode,selector,flag)=>opcode===88&&selector===4&&flag?7:0;
            const wrapper=(selector,flag)=>leaf.call(this,88,selector,!!flag);
            const outer=(selector,flag)=>wrapper(selector,flag);
            const api={};api.run=()=>outer(4,1);"#;
        let views = reconstruct_caller_views(source, Some("run"))?;
        let variants = specialize_resolved_call_graph(source, &views)?;
        let leaf = variants
            .iter()
            .find(|row| row.helper == "leaf")
            .ok_or_else(|| anyhow!("Function.call leaf not specialized: {variants:?}"))?;
        assert_eq!(
            leaf.constants,
            [(0, "88".into()), (1, "4".into()), (2, "true".into())]
        );
        assert_eq!(leaf.example_call_chain.len(), 3);
        assert!(leaf.specialized.contains("88") || leaf.specialized.contains("true"));
        Ok(())
    }

    #[test]
    fn function_call_wrapper_skips_this_argument_even_when_literal() -> Result<()> {
        let source = r#"const leaf=(a,b)=>a+b;
            const wrapper=x=>leaf.call(100,7,x);
            const api={};api.run=()=>wrapper(2);"#;
        let views = reconstruct_caller_views(source, Some("run"))?;
        let variants = specialize_resolved_call_graph(source, &views)?;
        let leaf = variants
            .iter()
            .find(|row| row.helper == "leaf")
            .ok_or_else(|| anyhow!("missing leaf"))?;
        assert_eq!(leaf.constants, [(0, "7".into()), (1, "2".into())]);
        Ok(())
    }

    #[test]
    fn carries_computed_bitwise_and_conditional_values_through_multiple_helpers() -> Result<()> {
        let src = r#"const leaf=(selector,flag)=>selector ? flag : 0;
            const outer=(left,right)=>leaf((left|0)+(right|0),right>4);
            const middle=(p,q)=>outer(p,q);
            const api={};api.run=()=>middle(4,7);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        let leaf = variants
            .iter()
            .find(|v| v.helper == "leaf")
            .ok_or_else(|| anyhow!("computed leaf was not specialized: {variants:?}"))?;
        assert_eq!(leaf.constants, [(0, "11".into()), (1, "true".into())]);
        assert_eq!(leaf.example_call_chain.len(), 3);
        Ok(())
    }

    #[test]
    fn computed_caller_values_do_not_cross_combine_different_paths() -> Result<()> {
        let src = r#"const leaf=(selector,which)=>selector+which;
            const middle=(a,b)=>leaf((a<<2)|b,a-b);
            const api={};api.run=()=>middle(1,2)+middle(3,1);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        let mut pairs = variants
            .iter()
            .filter(|v| v.helper == "leaf")
            .map(|v| v.constants.clone())
            .collect::<Vec<_>>();
        pairs.sort();
        assert_eq!(
            pairs,
            [
                [(0, "13".into()), (1, "2".into())],
                [(0, "6".into()), (1, "-1".into())]
            ]
        );
        Ok(())
    }

    #[test]
    fn computed_constructor_arguments_respect_original_symbol_identity() -> Result<()> {
        let src = r#"function Leaf(selector){this.value=selector;}
            const middle=(x)=>{
                const nested=(x)=>x+100;
                return new Leaf((x|0)+4);
            };
            const api={};api.run=()=>middle(5);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        let leaf = variants
            .iter()
            .find(|v| v.helper == "Leaf")
            .ok_or_else(|| anyhow!("computed constructor missing: {variants:?}"))?;
        assert_eq!(leaf.constants, [(0, "9".into())]);
        Ok(())
    }

    #[test]
    fn computed_arguments_do_not_use_written_params_or_effectful_unknowns() -> Result<()> {
        for middle in [
            "const middle=(x)=>{x=10;return leaf(x+2);};",
            "const middle=function(x){arguments[0]=10;return leaf(x+2);};",
            "const middle=(x)=>leaf(sideEffect()+x);",
            "const middle=(x)=>{eval('x=10');return leaf(x+2);};",
        ] {
            let src = format!(
                "const leaf=(selector)=>selector*2;{middle} const api={{}};api.run=()=>middle(5);"
            );
            let views = reconstruct_caller_views(&src, Some("run"))?;
            let variants = specialize_resolved_call_graph(&src, &views)?;
            assert!(
                variants.iter().all(|v| v.helper != "leaf"),
                "{middle}: {variants:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn computed_argument_with_undefined_parameter_is_not_assumed_known() -> Result<()> {
        let src = r#"const leaf=(selector)=>selector;
            const middle=(x,y)=>leaf(x+(y|0));
            const api={};api.run=(unknown)=>middle(3,unknown);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert!(variants.iter().all(|v| v.helper != "leaf"), "{variants:?}");
        Ok(())
    }

    #[test]
    fn computed_expression_short_circuits_an_unknown_parameter() -> Result<()> {
        let src = r#"const leaf=(selector)=>selector;
            const middle=(flag,unknown)=>leaf(flag ? 42 : unknown);
            const api={};api.run=(unknown)=>middle(true,unknown);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert!(
            variants
                .iter()
                .any(|v| { v.helper == "leaf" && v.constants == [(0, "42".into())] }),
            "{variants:?}"
        );
        Ok(())
    }

    #[test]
    fn recursive_computed_selectors_terminate_without_a_depth_constant() -> Result<()> {
        let src = r#"const leaf=(selector)=>selector;
            const recurse=(n)=>{leaf(n);return n < 100 ? recurse(n+1) : n;};
            const api={};api.run=()=>recurse(1);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert!(
            variants
                .iter()
                .any(|v| { v.helper == "leaf" && v.constants == [(0, "2".into())] }),
            "{variants:?}"
        );
        assert!(variants.len() < 12, "{variants:?}");
        Ok(())
    }

    #[test]
    fn computed_argument_value_preserves_negative_zero() -> Result<()> {
        let src = r#"const leaf=(value)=>1/value;
            const middle=(n)=>leaf(n*-1);
            const api={};api.run=()=>middle(0);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        let leaf = variants
            .iter()
            .find(|v| v.helper == "leaf")
            .ok_or_else(|| anyhow!("negative zero lost: {variants:?}"))?;
        assert_eq!(leaf.constants, [(0, "-0".into())]);
        Ok(())
    }

    #[test]
    fn evaluates_pure_argument_expressions_and_immutable_lexical_aliases() -> Result<()> {
        let src = r#"const base=2+3;
          const doubled=base*2;
          const through=(v,flag)=>v?flag:0;
          const leaf=(x,y,z)=>[x,y,z];
          const api={};api.run=()=>{
              const other=doubled+1;
              return leaf(other, !false, through(0,7))
                  +leaf(2**3, -0, null);
          };"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        let left = variants
            .iter()
            .find(|v| v.helper == "leaf" && v.constants.iter().any(|x| x == &(0, "11".into())))
            .ok_or_else(|| anyhow!("constant alias expression not recovered: {variants:?}"))?;
        assert!(left.constants.contains(&(1, "true".into())), "{left:?}");
        let right = variants
            .iter()
            .find(|v| v.helper == "leaf" && v.constants.iter().any(|x| x == &(0, "8".into())))
            .ok_or_else(|| anyhow!("pure exponent not recovered: {variants:?}"))?;
        assert!(
            right
                .constants
                .iter()
                .any(|x| x.0 == 1 && (x.1 == "-0" || x.1 == "(-0)")),
            "{right:?}"
        );
        Ok(())
    }

    #[test]
    fn lexical_symbols_not_name_strings_and_var_hoisting_not_guessed() -> Result<()> {
        let src = r#"const x=2;const leaf=(a,b)=>a+b;
          const api={};api.run=()=>{
            const x=9;
            if(false) var conditional=7;
            return leaf(x,conditional);
          };"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        let leaf = variants
            .iter()
            .find(|v| v.helper == "leaf")
            .ok_or_else(|| anyhow!("missing leaf"))?;
        assert_eq!(leaf.constants, [(0, "9".into())], "{leaf:?}");
        Ok(())
    }

    #[test]
    fn dynamic_scope_and_mutated_bindings_are_not_inferred_as_constants() -> Result<()> {
        for src in [
            "const leaf=x=>x;const api={};api.run=()=>{let x=3;x=4;return leaf(x);};",
            "const leaf=x=>x;const api={};api.run=()=>{const x=3;eval('1');return leaf(x);};",
            "const leaf=x=>x;const api={};api.run=()=>{const x=3;with({x:5})return leaf(x);};",
        ] {
            let views = reconstruct_caller_views(src, Some("run"))?;
            let variants = specialize_resolved_call_graph(src, &views)?;
            assert!(
                variants.iter().all(|v| v.helper != "leaf"),
                "{src}: {variants:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn propagates_literal_selectors_through_six_real_lexical_calls() -> Result<()> {
        let src = "const leaf=(selector,value)=>selector===7?value+1:value-1;          const p5=(s,x)=>leaf(s,x);const p4=(s,x)=>p5(s,x);          const p3=(s,x)=>p4(s,x);const p2=(s,x)=>p3(s,x);          const p1=(s,x)=>p2(s,x);const api={};          api.run=(input)=>p1(7,input);";
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        let leaf = variants
            .iter()
            .find(|variant| variant.helper == "leaf")
            .ok_or_else(|| anyhow!("deep helper was not specialized"))?;
        assert_eq!(leaf.constants, [(0, "7".into())]);
        assert_eq!(leaf.example_call_chain.len(), 6);
        assert!(leaf.specialized.contains("(7)===7"), "{leaf:?}");
        assert!(views[0].paths.iter().all(|path| path.functions.len() < 6));
        Ok(())
    }

    #[test]
    fn preserves_correlated_tuples_instead_of_cross_multiplying() -> Result<()> {
        let src = "const leaf=(a,b)=>[a,b];          const middle=(x,y)=>leaf(x,y);          const api={};api.run=()=>middle(1,2)+middle(3,4);";
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        let pairs = variants
            .iter()
            .filter(|variant| variant.helper == "leaf")
            .map(|variant| variant.constants.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            pairs,
            [
                [(0, "1".into()), (1, "2".into())],
                [(0, "3".into()), (1, "4".into())],
            ],
        );
        assert!(pairs
            .iter()
            .all(|pair| pair[0].1 != "1" || pair[1].1 == "2"));
        Ok(())
    }

    #[test]
    fn does_not_forward_reassigned_or_mapped_arguments_parameters() -> Result<()> {
        for middle in [
            "const middle=(x)=>{x=9;return leaf(x);};",
            "const middle=function(x){arguments[0]=9;return leaf(x);};",
            "const middle=function(x){eval('x=9');return leaf(x);};",
        ] {
            let src = format!("const leaf=(v)=>v*3;{middle}const api={{}};api.run=()=>middle(7);");
            let views = reconstruct_caller_views(&src, Some("run"))?;
            let variants = specialize_resolved_call_graph(&src, &views)?;
            assert!(
                variants.iter().all(|variant| variant.helper != "leaf"),
                "{middle}: {variants:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn propagates_only_stable_parameter_through_permuted_constructor_calls() -> Result<()> {
        let src = "function Leaf(a,b){this.result=a+b;}          const middle=(x,y)=>new Leaf(y,x);          const api={};api.run=(value)=>middle(value,13);";
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        let leaf = variants
            .iter()
            .find(|variant| variant.helper == "Leaf")
            .ok_or_else(|| anyhow!("constructor was not specialized"))?;
        assert_eq!(leaf.constants, [(0, "13".into())]);
        assert_eq!(leaf.example_call_chain.len(), 2);
        Ok(())
    }

    #[test]
    fn finite_cycle_propagates_constant_variants_without_unbounded_walk() -> Result<()> {
        let src = "const leaf=(value)=>value;          const left=(x)=>{leaf(x);return right(x);};          const right=(x)=>left(x);          const api={};api.run=()=>left(7);";
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert!(variants
            .iter()
            .any(|variant| { variant.helper == "leaf" && variant.constants == [(0, "7".into())] }));
        assert!(variants.len() < 10, "{variants:?}");
        Ok(())
    }

    #[test]
    fn recovers_distinct_literal_variants_from_original_lexical_graph() -> Result<()> {
        let src = r#"const helper=function(selector,value){
            if(selector===3)return value+1;
            return value*2;
        };
        const api={};
        api.run=function(x) {return helper(3,x)+helper(4,x);};"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert_eq!(variants.len(), 2, "{variants:?}");
        assert!(variants.iter().all(|v| v.helper == "helper"));
        assert!(variants.iter().all(|v| v.call_sites.len() == 1));
        assert!(variants.iter().any(|v| {
            v.constants == [(0, "3".into())] && v.specialized.contains("if((3)===3)")
        }));
        assert!(variants.iter().any(|v| {
            v.constants == [(0, "4".into())] && v.specialized.contains("if((4)===3)")
        }));
        Ok(())
    }

    #[test]
    fn uses_unchanged_subset_when_other_literal_parameter_is_written() -> Result<()> {
        let src = r#"const helper=function(a,b){a=9;return b+a;};
          const api={};api.run=()=>helper(3,4);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].constants, [(1, "4".into())]);
        assert!(variants[0].specialized.contains("return (4)+a"));
        assert!(variants[0].specialized.contains("a=9"));
        Ok(())
    }

    #[test]
    fn spread_argument_positions_are_never_misidentified() -> Result<()> {
        let src = r#"const helper=(a,b)=>a+b;
          const api={};api.run=(xs)=>helper(...xs,42)+helper(3,...xs);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].constants, [(0, "3".into())]);
        Ok(())
    }

    #[test]
    fn same_spelling_in_another_scope_is_not_the_target_function() -> Result<()> {
        let src = r#"const helper=(a)=>a*3;
          const api={};api.run=()=>{
              const helper=(a)=>a*4;
              return helper(7);
          };"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert!(variants[0].original.contains("a*4"));
        assert!(!variants[0].original.contains("a*3"));
        Ok(())
    }

    #[test]
    fn contextual_super_expression_does_not_abort_other_valid_helpers() -> Result<()> {
        let src = r#"class Base { method(x){return x;} }
          class Child extends Base {
            method(){
              const contextual=(x)=>super.method(x);
              const regular=(x)=>x*2;
              const api={};api.run=()=>contextual(3)+regular(4);
              return api;
            }
          }"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].helper, "regular");
        assert_eq!(variants[0].constants, [(0, "4".into())]);
        Ok(())
    }

    #[test]
    fn unused_literal_arguments_do_not_produce_redundant_variants() -> Result<()> {
        let src = r#"const helper=(selector,unused)=>selector*2;
            const api={};api.run=()=>helper(3,7)+helper(3,8);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].constants, [(0, "3".into())]);
        assert_eq!(variants[0].call_sites.len(), 2);
        Ok(())
    }

    #[test]
    fn constructor_call_and_same_literal_tuple_deduplicate() -> Result<()> {
        let src = r#"function Helper(flag){this.result=flag?1:0;}
          const api={};api.run=()=>[new Helper(true),new Helper(true)];"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].call_sites.len(), 2);
        assert_eq!(variants[0].constants, [(0, "true".into())]);
        assert!(variants[0].specialized.contains("(true)?1:0"));
        Ok(())
    }

    #[test]
    fn finds_only_unresolved_lexical_calls_with_primitive_literals() -> Result<()> {
        let src = "const h=function(){const local=(x,y)=>x; O(u,16); M(68,127,P); local(1,2); O(P, true); O(P, 'abc'); O(P,-12); };";
        let calls = literal_calls(src)?;
        assert_eq!(calls.len(), 5);
        assert_eq!(calls[0].constants, vec![(1, "16".to_owned())]);
        assert_eq!(
            calls[1].constants,
            vec![(0, "68".into()), (1, "127".into())]
        );
        assert_eq!(calls[2].constants, vec![(1, "true".into())]);
        assert_eq!(calls[3].constants, vec![(1, "'abc'".into())]);
        assert_eq!(calls[4].constants, vec![(1, "-12".into())]);
        Ok(())
    }

    #[test]
    fn substitutes_original_lexical_parameter_only() -> Result<()> {
        let src =
            "const O=function(J,Q){if(Q===16){const f=(Q)=>Q+1;return J + f(2);}return Q*2;};";
        let output = specialize_function(src, &[(1, "16".to_owned())])?
            .ok_or_else(|| anyhow!("expected specialized helper"))?;
        assert!(output.contains("if((16)===16)"));
        assert!(output.contains("const f=(Q)=>Q+1"));
        assert!(!output.contains("return Q*2"));
        assert!(output.contains("return (16)*2"));
        Ok(())
    }

    #[test]
    fn ignores_arguments_of_nested_ordinary_function_but_not_arrow() -> Result<()> {
        let own_arguments =
            "const M=function(selector,value){const nested=function(){return arguments[0];};return selector+nested(value);};";
        let fixed = specialize_function(own_arguments, &[(0, "68".into())])?
            .ok_or_else(|| anyhow!("nested arguments should not alias outer parameters"))?;
        assert!(fixed.contains("return (68)+nested(value)"), "{fixed}");
        assert!(fixed.contains("return arguments[0]"), "{fixed}");

        let inherited_arguments =
            "const M=function(selector){const nested=()=>arguments[0];return selector+nested();};";
        assert!(specialize_function(inherited_arguments, &[(0, "68".into())])?.is_none());

        // A nested direct eval can still resolve or modify an enclosing
        // function parameter. Preserve the previous dynamic-scope veto.
        let nested_eval =
            "const M=function(selector){const nested=function(){eval('selector=9')};return selector+nested();};";
        assert!(specialize_function(nested_eval, &[(0, "68".into())])?.is_none());
        Ok(())
    }

    #[test]
    fn rejects_aliasing_write_dynamic_scope_and_unsupported_parameters() -> Result<()> {
        for src in [
            "const f=function(x){x=2;return x;};",
            "const f=function(x){return arguments[0];};",
            "const f=function(x){return eval('x');};",
            "const f=function(x){with({x:7})return x;};",
            "const f=function(x=1){return x;};",
            "const f={invoke(x){return x+1;}};",
        ] {
            assert!(
                specialize_function(src, &[(0, "2".to_owned())])?.is_none(),
                "{src}"
            );
        }
        Ok(())
    }
}
