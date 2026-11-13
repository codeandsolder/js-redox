//! Exact source-resolved, caller-oriented JavaScript argument forwarding.
//!
//! This is an inspectable *source view*, never an in-place replacement. Direct
//! calls and constructions of uniquely resolved functions can be connected by
//! original lexical symbol identity. Forwarded parameters are traced only
//! when the referring binding is not written; other expressions are retained
//! as unknown/dynamic, not guessed as constant values.
use anyhow::{ensure, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, AssignmentExpression, AssignmentTarget, BindingPattern, CallExpression, Expression,
    FormalParameters, Function, NewExpression, VariableDeclaration, VariableDeclarationKind,
    VariableDeclarator, WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

type FunctionKey = (u32, u32);

fn key(span: Span) -> FunctionKey {
    (span.start, span.end)
}
fn unparen<'e, 'a>(mut expr: &'e Expression<'a>) -> &'e Expression<'a> {
    while let Expression::ParenthesizedExpression(paren) = expr {
        expr = &paren.expression;
    }
    expr
}
fn fragment(src: &str, span: Span) -> &str {
    src.get(span.start as usize..span.end as usize)
        .unwrap_or("")
}

#[derive(Clone, Debug)]
struct Definition {
    label: String,
    params: Vec<(String, Option<SymbolId>)>,
    symbol: Option<SymbolId>,
    member: bool,
    initialized_by_assignment: bool,
}

fn definition(
    params: &FormalParameters<'_>,
    label: String,
    symbol: Option<SymbolId>,
    member: bool,
) -> Definition {
    let params = params
        .items
        .iter()
        .map(|parameter| match &parameter.pattern {
            BindingPattern::BindingIdentifier(id) if parameter.initializer.is_none() => {
                (id.name.to_string(), id.symbol_id.get())
            }
            _ => ("<pattern/default>".to_owned(), None),
        })
        .collect();
    Definition {
        label,
        params,
        symbol,
        member,
        initialized_by_assignment: false,
    }
}

fn defined_callable(
    expression: &Expression<'_>,
    label: String,
    symbol: Option<SymbolId>,
    member: bool,
) -> Option<(FunctionKey, Definition)> {
    match unparen(expression) {
        Expression::FunctionExpression(function) => Some((
            key(function.span),
            definition(&function.params, label, symbol, member),
        )),
        Expression::ArrowFunctionExpression(function) => Some((
            key(function.span),
            definition(&function.params, label, symbol, member),
        )),
        _ => None,
    }
}

struct Definitions<'s> {
    functions: BTreeMap<FunctionKey, Definition>,
    scoping: &'s Scoping,
}
impl<'a> Visit<'a> for Definitions<'_> {
    fn visit_variable_declarator(&mut self, it: &VariableDeclarator<'a>) {
        if let (BindingPattern::BindingIdentifier(id), Some(init)) = (&it.id, &it.init) {
            if let Some((key, def)) =
                defined_callable(init, id.name.to_string(), id.symbol_id.get(), false)
            {
                self.functions.insert(key, def);
            }
        }
        walk::walk_variable_declarator(self, it);
    }
    fn visit_assignment_expression(&mut self, it: &AssignmentExpression<'a>) {
        if it.operator.as_str() == "=" {
            let target = match &it.left {
                AssignmentTarget::AssignmentTargetIdentifier(id) => {
                    let symbol = id
                        .reference_id
                        .get()
                        .and_then(|reference| self.scoping.get_reference(reference).symbol_id());
                    Some((id.name.to_string(), symbol, false))
                }
                AssignmentTarget::StaticMemberExpression(member) if !member.optional => {
                    Some((format!(".{}", member.property.name), None, true))
                }
                _ => None,
            };
            if let Some((label, symbol, member)) = target {
                if let Some((key, mut def)) = defined_callable(&it.right, label, symbol, member) {
                    // `let fn; fn = expression` has one expected resolved
                    // write: the assignment establishing the function itself.
                    def.initialized_by_assignment = !member;
                    self.functions.insert(key, def);
                }
            }
        }
        walk::walk_assignment_expression(self, it);
    }
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if function.is_declaration() {
            if let Some(id) = &function.id {
                self.functions.insert(
                    key(function.span),
                    definition(
                        &function.params,
                        id.name.to_string(),
                        id.symbol_id.get(),
                        false,
                    ),
                );
            }
        }
        walk::walk_function(self, function, flags);
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ArgumentLink {
    pub expression: String,
    /// True only when this argument occupies its stated position without an
    /// earlier spread that might supply zero or multiple parameters.
    pub positional: bool,
    pub caller_param_index: Option<usize>,
    pub caller_param: Option<String>,
    /// Syntactically direct this, not an aliased or spread expression.
    pub is_direct_this: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct CallLink {
    pub caller: String,
    pub callee: String,
    /// call / new / function.call. The latter receiver is recorded separately.
    pub kind: &'static str,
    pub span: [u32; 2],
    pub this_argument: Option<String>,
    pub arguments: Vec<ArgumentLink>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ConstructedReceiver {
    pub constructor: String,
    pub new_call_span: [u32; 2],
}

#[derive(Clone, Debug, Serialize)]
pub struct ForwardedParameter {
    pub param: String,
    pub index: usize,
    /// Root API function parameter index, if *every* edge forwards the same
    /// unchanged parameter without an intervening computed expression.
    pub from_entry_index: Option<usize>,
    pub from_entry: Option<String>,
    pub input_expression: String,
    /// Only proven along this exact statically resolved path.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub constructed_receiver: Option<ConstructedReceiver>,
}

#[derive(Clone, Debug, Serialize)]
pub struct CallerPath {
    pub functions: Vec<String>,
    pub function_spans: Vec<[u32; 2]>,
    pub links: Vec<CallLink>,
    pub leaf_parameters: Vec<ForwardedParameter>,
}

/// Each reachable edge is stored once per original callsite. This graph is
/// complete across statically resolved targets even when the browsable path
/// index is depth-limited to avoid combinatorial explosion.
#[derive(Clone, Debug, Serialize)]
pub struct ResolvedCallEdge {
    pub from_span: [u32; 2],
    pub to_span: [u32; 2],
    pub call: CallLink,
}

/// A function parameter may have several entry-origin possibilities when
/// multiple statically possible callsites converge. An unknown/literal input
/// is represented separately; it never becomes a guessed entry parameter.
#[derive(Clone, Debug, Serialize)]
pub struct ReachableParameter {
    pub name: String,
    pub index: usize,
    pub possible_entry_indices: Vec<usize>,
    pub unknown_or_nonentry_input: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReachableFunction {
    pub name: String,
    pub span: [u32; 2],
    pub shortest_call_depth: usize,
    pub parameters: Vec<ReachableParameter>,
}

#[derive(Clone, Debug, Serialize)]
pub struct CallerView {
    pub entry: String,
    pub entry_span: [u32; 2],
    pub paths: Vec<CallerPath>,
    pub reachable_edges: Vec<ResolvedCallEdge>,
    pub reachable_functions: Vec<ReachableFunction>,
    pub source: String,
}

/// Dynamic eval/with affects mutable alias proof across the program, but
/// call-method receivers can be evaluated independently in lexical functions
/// with no such syntax. Track exactly the enclosing functions containing
/// direct eval/with rather than disabling all graph edges for one unrelated
/// script helper (a common pattern in large bundled JavaScript).
#[derive(Default)]
struct DynamicScope {
    found: bool,
    stack: Vec<FunctionKey>,
    unsafe_callers: BTreeSet<FunctionKey>,
}

impl DynamicScope {
    fn mark_enclosing(&mut self) {
        self.found = true;
        self.unsafe_callers.extend(self.stack.iter().copied());
    }
}

impl<'a> Visit<'a> for DynamicScope {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.stack.push(key(function.span));
        walk::walk_function(self, function, flags);
        self.stack.pop();
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        self.stack.push(key(function.span));
        walk::walk_arrow_function_expression(self, function);
        self.stack.pop();
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if matches!(unparen(&call.callee), Expression::Identifier(id) if id.name == "eval") {
            self.mark_enclosing();
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_with_statement(&mut self, statement: &WithStatement<'a>) {
        self.mark_enclosing();
        walk::walk_with_statement(self, statement);
    }
}

/// Immutable, direct lexical aliases (const alias = original) are safe
/// call graph edges as long as the originating function binding is stable.
/// Keep this separate from Definitions: aliases are not distinct functions.
struct AliasCollector<'s> {
    scoping: &'s Scoping,
    dynamic_scope: bool,
    aliases: BTreeMap<SymbolId, SymbolId>,
}

impl<'a> Visit<'a> for AliasCollector<'_> {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        if declaration.kind == VariableDeclarationKind::Const
            || (!self.dynamic_scope
                && matches!(
                    declaration.kind,
                    VariableDeclarationKind::Let | VariableDeclarationKind::Var
                ))
        {
            for declarator in &declaration.declarations {
                let (BindingPattern::BindingIdentifier(id), Some(init)) =
                    (&declarator.id, &declarator.init)
                else {
                    continue;
                };
                let Expression::Identifier(source) = unparen(init) else {
                    continue;
                };
                let target = source
                    .reference_id
                    .get()
                    .and_then(|reference| self.scoping.get_reference(reference).symbol_id());
                if let (Some(alias), Some(target)) = (id.symbol_id.get(), target) {
                    if alias != target
                        && self.scoping.symbol_redeclarations(alias).is_empty()
                        && !self
                            .scoping
                            .get_resolved_reference_ids(alias)
                            .iter()
                            .any(|reference| self.scoping.get_reference(*reference).is_write())
                    {
                        self.aliases.insert(alias, target);
                    }
                }
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

/// A function value's own call property can override Function.prototype.call.
/// Exclude directly mutated bindings and aliases from exact call-method edges.
struct CallPropertyWrites<'s> {
    scoping: &'s Scoping,
    assigned: BTreeSet<SymbolId>,
}

impl CallPropertyWrites<'_> {
    fn mark_member(&mut self, member: &oxc_ast::ast::StaticMemberExpression<'_>) {
        if !member.optional && member.property.name == "call" {
            if let Expression::Identifier(id) = unparen(&member.object) {
                if let Some(symbol) = id
                    .reference_id
                    .get()
                    .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
                {
                    self.assigned.insert(symbol);
                }
            }
        }
    }
}

impl<'a> Visit<'a> for CallPropertyWrites<'_> {
    fn visit_assignment_expression(&mut self, expression: &AssignmentExpression<'a>) {
        if let AssignmentTarget::StaticMemberExpression(member) = &expression.left {
            self.mark_member(member);
        }
        walk::walk_assignment_expression(self, expression);
    }

    fn visit_unary_expression(&mut self, expression: &oxc_ast::ast::UnaryExpression<'a>) {
        if expression.operator.as_str() == "delete" {
            if let Expression::StaticMemberExpression(member) = unparen(&expression.argument) {
                self.mark_member(member);
            }
        }
        walk::walk_unary_expression(self, expression);
    }
}

struct Calls<'s> {
    source: &'s str,
    scoping: &'s Scoping,
    defs: &'s BTreeMap<FunctionKey, Definition>,
    symbols: &'s BTreeMap<SymbolId, FunctionKey>,
    aliases: &'s BTreeMap<SymbolId, SymbolId>,
    blocked_call_targets: &'s BTreeSet<FunctionKey>,
    unsafe_callers: &'s BTreeSet<FunctionKey>,
    stack: Vec<FunctionKey>,
    edges: BTreeMap<FunctionKey, Vec<(FunctionKey, CallLink)>>,
}
impl Calls<'_> {
    /// Follow a lexical const-to-identifier chain, bounded by the number of
    /// aliases. A cyclic or unresolved source never becomes a call edge.
    fn original_symbol(&self, mut symbol: SymbolId) -> Option<SymbolId> {
        let mut visited = BTreeSet::new();
        while let Some(&next) = self.aliases.get(&symbol) {
            if !visited.insert(symbol) {
                return None;
            }
            symbol = next;
        }
        Some(symbol)
    }

    fn emit(
        &mut self,
        callee: &Expression<'_>,
        args: &[Argument<'_>],
        span: Span,
        kind: &'static str,
    ) {
        let Some(&caller_key) = self.stack.last() else {
            return;
        };
        let (id, skip_receiver, kind) = match unparen(callee) {
            Expression::Identifier(id) => (id, false, kind),
            Expression::StaticMemberExpression(member)
                if kind == "call" && !member.optional && member.property.name == "call" =>
            {
                let Expression::Identifier(id) = unparen(&member.object) else {
                    return;
                };
                (id, true, "function.call")
            }
            _ => return,
        };
        let Some(target_symbol) = id
            .reference_id
            .get()
            .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
        else {
            return;
        };
        let Some(&callee_key) = self.symbols.get(&target_symbol) else {
            return;
        };
        // A spread in receiver position may supply zero or several values;
        // no subsequent fixed formal parameter position can be inferred.
        if skip_receiver
            && (self.unsafe_callers.contains(&caller_key)
                || self.blocked_call_targets.contains(&callee_key)
                || matches!(args.first(), Some(Argument::SpreadElement(_))))
        {
            return;
        }
        let Some(caller) = self.defs.get(&caller_key) else {
            return;
        };
        let Some(target) = self.defs.get(&callee_key) else {
            return;
        };
        let mut prior_spread = false;
        let arguments = args
            .iter()
            .skip(usize::from(skip_receiver))
            .map(|arg| {
                let spread = matches!(arg, Argument::SpreadElement(_));
                let positional = !prior_spread && !spread;
                prior_spread |= spread;
                let arg_span = arg.span();
                let mut forward = None;
                if let Some(Expression::Identifier(value)) = positional
                    .then(|| arg.as_expression())
                    .flatten()
                    .map(unparen)
                {
                    if let Some(symbol) = value
                        .reference_id
                        .get()
                        .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
                    {
                        if let Some(original) = self.original_symbol(symbol) {
                            if !self
                                .scoping
                                .get_resolved_reference_ids(original)
                                .iter()
                                .any(|reference| self.scoping.get_reference(*reference).is_write())
                            {
                                forward = caller.params.iter().enumerate().find_map(
                                    |(index, (_, target))| {
                                        (*target == Some(original)).then_some(index)
                                    },
                                );
                            }
                        }
                    }
                }
                ArgumentLink {
                    expression: fragment(self.source, arg_span).to_owned(),
                    positional,
                    caller_param: forward.map(|idx| caller.params[idx].0.clone()),
                    caller_param_index: forward,
                    is_direct_this: positional
                        && matches!(
                            arg.as_expression().map(unparen),
                            Some(Expression::ThisExpression(_))
                        ),
                }
            })
            .collect();
        let call = CallLink {
            caller: caller.label.clone(),
            callee: target.label.clone(),
            kind,
            span: [span.start, span.end],
            this_argument: if skip_receiver {
                args.first()
                    .map(|arg| fragment(self.source, arg.span()).to_owned())
            } else {
                None
            },
            arguments,
        };
        self.edges
            .entry(caller_key)
            .or_default()
            .push((callee_key, call));
    }
}
impl<'a> Visit<'a> for Calls<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.stack.push(key(function.span));
        walk::walk_function(self, function, flags);
        self.stack.pop();
    }
    fn visit_arrow_function_expression(&mut self, it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
        self.stack.push(key(it.span));
        walk::walk_arrow_function_expression(self, it);
        self.stack.pop();
    }
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            self.emit(&call.callee, &call.arguments, call.span, "call");
        }
        walk::walk_call_expression(self, call);
    }
    fn visit_new_expression(&mut self, expr: &NewExpression<'a>) {
        self.emit(&expr.callee, &expr.arguments, expr.span, "new");
        walk::walk_new_expression(self, expr);
    }
}

struct PathOrigins {
    entry: Vec<Option<usize>>,
    constructed: Vec<Option<ConstructedReceiver>>,
}

struct PathWalker<'s> {
    defs: &'s BTreeMap<FunctionKey, Definition>,
    edges: &'s BTreeMap<FunctionKey, Vec<(FunctionKey, CallLink)>>,
    root: FunctionKey,
    output: Vec<CallerPath>,
}

impl PathWalker<'_> {
    fn walk(
        &mut self,
        current: FunctionKey,
        origins: &PathOrigins,
        names: &mut Vec<String>,
        spans: &mut Vec<[u32; 2]>,
        links: &mut Vec<CallLink>,
        visited: &mut BTreeSet<FunctionKey>,
    ) {
        if links.len() >= 4 {
            return;
        }
        let Some(call_sites) = self.edges.get(&current) else {
            return;
        };
        for (next, edge) in call_sites {
            if !visited.insert(*next) {
                continue;
            }
            let Some(target) = self.defs.get(next) else {
                continue;
            };
            let root_params = &self.defs[&self.root].params;
            let next_origins = target
                .params
                .iter()
                .enumerate()
                .map(|(index, (_, binding))| {
                    binding.and_then(|_| {
                        edge.arguments.get(index).and_then(|argument| {
                            argument
                                .caller_param_index
                                .and_then(|i| origins.entry.get(i).copied().flatten())
                        })
                    })
                })
                .collect::<Vec<_>>();
            // The preceding edge must construct precisely this resolved
            // function. Its own direct this argument is then a fresh receiver.
            let constructor_here = links.last().and_then(|incoming| {
                (incoming.kind == "new" && incoming.callee == edge.caller).then(|| {
                    ConstructedReceiver {
                        constructor: incoming.callee.clone(),
                        new_call_span: incoming.span,
                    }
                })
            });
            let next_constructed = target
                .params
                .iter()
                .enumerate()
                .map(|(index, (_, binding))| {
                    binding.and_then(|_| {
                        edge.arguments.get(index).and_then(|argument| {
                            argument
                                .caller_param_index
                                .and_then(|i| origins.constructed.get(i).cloned().flatten())
                                .or_else(|| {
                                    (argument.is_direct_this && argument.positional)
                                        .then(|| constructor_here.clone())
                                        .flatten()
                                })
                        })
                    })
                })
                .collect::<Vec<_>>();
            names.push(target.label.clone());
            spans.push([next.0, next.1]);
            links.push(edge.clone());
            if links.len() >= 2 {
                let leaf_parameters = target
                    .params
                    .iter()
                    .enumerate()
                    .map(|(index, (name, _))| {
                        let from_entry_index = next_origins[index];
                        ForwardedParameter {
                            param: name.clone(),
                            index,
                            from_entry_index,
                            from_entry: from_entry_index.map(|i| root_params[i].0.clone()),
                            input_expression: edge
                                .arguments
                                .get(index)
                                .map_or_else(|| "<omitted>".into(), |a| a.expression.clone()),
                            constructed_receiver: next_constructed[index].clone(),
                        }
                    })
                    .collect();
                self.output.push(CallerPath {
                    functions: names.clone(),
                    function_spans: spans.clone(),
                    links: links.clone(),
                    leaf_parameters,
                });
            }
            let next_sources = PathOrigins {
                entry: next_origins,
                constructed: next_constructed,
            };
            self.walk(*next, &next_sources, names, spans, links, visited);
            names.pop();
            spans.pop();
            links.pop();
            visited.remove(next);
        }
    }
}

/// Propagate entry-parameter origins across all statically reachable call
/// edges until the finite union of possible origins reaches a fixed point.
/// This is a *may-flow* result: multiple inputs/unknowns remain explicit,
/// and no path enumeration or arbitrary depth limit is involved.
fn propagate_reachable_parameter_origins(
    root: FunctionKey,
    definitions: &BTreeMap<FunctionKey, Definition>,
    edges: &BTreeMap<FunctionKey, Vec<(FunctionKey, CallLink)>>,
) -> Vec<ReachableFunction> {
    let Some(entry) = definitions.get(&root) else {
        return Vec::new();
    };
    let mut shortest_depth = BTreeMap::from([(root, 0_usize)]);
    let mut distance_queue = VecDeque::from([root]);
    while let Some(from) = distance_queue.pop_front() {
        let depth = shortest_depth[&from];
        if let Some(calls) = edges.get(&from) {
            for (to, _) in calls {
                if let std::collections::btree_map::Entry::Vacant(slot) = shortest_depth.entry(*to)
                {
                    slot.insert(depth + 1);
                    distance_queue.push_back(*to);
                }
            }
        }
    }

    type Sources = BTreeSet<Option<usize>>;
    let mut states = BTreeMap::<FunctionKey, Vec<Sources>>::new();
    states.insert(
        root,
        entry
            .params
            .iter()
            .enumerate()
            .map(|(index, (_, binding))| BTreeSet::from([binding.map(|_| index)]))
            .collect(),
    );
    let mut pending = VecDeque::from([root]);
    while let Some(from) = pending.pop_front() {
        let Some(from_params) = states.get(&from).cloned() else {
            continue;
        };
        let Some(calls) = edges.get(&from) else {
            continue;
        };
        for (to, call) in calls {
            let Some(definition) = definitions.get(to) else {
                continue;
            };
            let (target_states, mut changed) = match states.entry(*to) {
                std::collections::btree_map::Entry::Vacant(slot) => (
                    slot.insert(vec![Sources::new(); definition.params.len()]),
                    true,
                ),
                std::collections::btree_map::Entry::Occupied(slot) => (slot.into_mut(), false),
            };
            for (index, (.., binding)) in definition.params.iter().enumerate() {
                let supplied = if binding.is_some() {
                    call.arguments
                        .get(index)
                        .filter(|argument| argument.positional)
                        .and_then(|argument| argument.caller_param_index)
                        .and_then(|source_index| from_params.get(source_index).cloned())
                } else {
                    None
                };
                // Defaults/destructuring, omitted arguments, spread arguments,
                // and computed input expressions have no direct entry origin.
                let input = supplied.unwrap_or_else(|| Sources::from([None]));
                let before = target_states[index].len();
                target_states[index].extend(input);
                changed |= target_states[index].len() != before;
            }
            if changed {
                pending.push_back(*to);
            }
        }
    }

    let mut functions = states
        .into_iter()
        .filter_map(|(key, params)| {
            let definition = definitions.get(&key)?;
            let depth = shortest_depth.get(&key).copied()?;
            Some(ReachableFunction {
                name: definition.label.clone(),
                span: [key.0, key.1],
                shortest_call_depth: depth,
                parameters: params
                    .into_iter()
                    .enumerate()
                    .map(|(index, sources)| ReachableParameter {
                        name: definition.params[index].0.clone(),
                        index,
                        possible_entry_indices: sources.iter().flatten().copied().collect(),
                        unknown_or_nonentry_input: sources.contains(&None),
                    })
                    .collect(),
            })
        })
        .collect::<Vec<_>>();
    functions.sort_by_key(|function| (function.shortest_call_depth, function.span));
    functions
}

impl CallerView {
    /// Render a focused subset of the full source-resolved graph. The JSON
    /// manifest can still retain all reachable paths for deeper inspection.
    #[must_use]
    pub fn render_paths(&self, original: &str, selected: &BTreeSet<usize>) -> String {
        let mut view = self.clone();
        view.paths = self
            .paths
            .iter()
            .enumerate()
            .filter(|(index, _)| selected.contains(index))
            .map(|(_, path)| path.clone())
            .collect();
        format_view(&view, original)
    }
}

fn format_view(view: &CallerView, original: &str) -> String {
    let mut output = format!("# Caller-oriented lexical forwarding: `{}`\n\n", view.entry);
    output.push_str("This is a **source-derived reading view**, not a rewritten executable. ");
    output.push_str("Edges resolve original lexical symbols, direct calls, constructors and eligible Function.call invocations. ");
    output.push_str("Parameter arrows trace unchanged, directly forwarded bindings only. ");
    output.push_str("Potential indirect `eval`, mapped `arguments`, or dynamic mutations require runtime analysis before claiming values are invariant.\n\n");
    for path in &view.paths {
        output.push_str(&format!("## `{}`\n\n", path.functions.join(" → ")));
        for edge in &path.links {
            output.push_str(&format!(
                "- `{}` → `{}` (**{}** at source bytes {}..{})\n",
                edge.caller, edge.callee, edge.kind, edge.span[0], edge.span[1]
            ));
            if let Some(receiver) = &edge.this_argument {
                output.push_str(&format!(
                    "  - this receiver: {receiver} (not a formal parameter)\n"
                ));
            }
            for (idx, arg) in edge.arguments.iter().enumerate() {
                let prefix = arg.caller_param.as_ref().map_or_else(
                    || "dynamic expression".to_owned(),
                    |param| format!("caller parameter `{param}`"),
                );
                output.push_str(&format!(
                    "  - argument {idx}: `{}` ← {prefix}\n",
                    arg.expression
                ));
            }
        }
        output.push_str("\n**Leaf parameter provenance:**\n\n");
        for param in &path.leaf_parameters {
            if let Some(receiver) = &param.constructed_receiver {
                output.push_str(&format!(
                    "- {} (parameter {}) comes from fresh receiver of new {} at source bytes {}..{}; inherited property behavior remains dynamic\n",
                    param.param, param.index, receiver.constructor,
                    receiver.new_call_span[0], receiver.new_call_span[1]
                ));
                continue;
            }
            match (&param.from_entry, &param.from_entry_index) {
                (Some(name), Some(index)) => output.push_str(&format!(
                    "- `{}` (parameter {}) ← entry `{}` (parameter {})\n",
                    param.param, param.index, name, index
                )),
                _ => output.push_str(&format!(
                    "- `{}` (parameter {}) ← dynamic/unknown (`{}`)\n",
                    param.param, param.index, param.input_expression
                )),
            }
        }
        output.push('\n');
    }
    output.push_str("## Complete reachable lexical call graph\n\n");
    output.push_str("Each original callsite occurs once, independent of path depth. ");
    output.push_str(
        "Function byte spans identify both endpoints; cycles do not truncate the graph.\n\n",
    );
    for edge in &view.reachable_edges {
        output.push_str(&format!(
            "- {} ({}..{}) to {} ({}..{}) via {} at {}..{}\n",
            edge.call.caller,
            edge.from_span[0],
            edge.from_span[1],
            edge.call.callee,
            edge.to_span[0],
            edge.to_span[1],
            edge.call.kind,
            edge.call.span[0],
            edge.call.span[1],
        ));
    }
    output.push_str("\n## Parameters reachable at arbitrary call depth\n\n");
    output.push_str("Each function is listed once. Origins are unions across all statically possible caller paths; unknown or non-entry inputs are explicit.\n\n");
    for function in &view.reachable_functions {
        output.push_str(&format!(
            "- **{}** ({}..{}, shortest call depth {})",
            function.name, function.span[0], function.span[1], function.shortest_call_depth
        ));
        if function.parameters.is_empty() {
            output.push_str(" — no parameters\n");
            continue;
        }
        output.push('\n');
        for parameter in &function.parameters {
            let mut names = parameter
                .possible_entry_indices
                .iter()
                .map(|index| format!("entry parameter {index}"))
                .collect::<Vec<_>>();
            if parameter.unknown_or_nonentry_input {
                names.push("unknown/non-entry input".to_owned());
            }
            output.push_str(&format!(
                "  - {} (parameter {}) ← {}\n",
                parameter.name,
                parameter.index,
                names.join(" or ")
            ));
        }
    }
    output.push_str("\n## Original source excerpts\n\n");
    output.push_str(
        "These are **verbatim original function expressions**, not runnable copies; \
        the complete original program and separately reconstructed lexical helpers \
        remain in the source-tree output. Excerpts are truncated when large.\n\n",
    );
    let mut seen = BTreeSet::new();
    for path in &view.paths {
        for (label, span) in path.functions.iter().zip(&path.function_spans) {
            if !seen.insert(*span) {
                continue;
            }
            let raw = original
                .get(span[0] as usize..span[1] as usize)
                .unwrap_or("");
            let excerpt = raw.chars().take(1600).collect::<String>();
            let clipped = raw.chars().count() > 1600;
            // Embedded source may contain Markdown fences inside JS strings
            // or comments. Always choose a fence longer than any original
            // backtick run, keeping the browsing view structurally intact.
            let max_run = excerpt
                .split(|ch| ch != '`')
                .map(str::len)
                .max()
                .unwrap_or(0);
            let fence = "`".repeat(3.max(max_run + 1));
            output.push_str(&format!(
                "### `{label}` — bytes {}..{}\n\n{fence}js\n{excerpt}\n{fence}\n\n",
                span[0], span[1]
            ));
            if clipped {
                output.push_str("*Excerpt truncated; follow the original source / helper implementation link for the complete function.*\n\n");
            }
        }
    }
    output
}

/// Discover exported member-assigned entry functions and their exact direct
/// lexical call chains. `entry_member` optionally narrows to one member name;
/// matching applies to AST property declarations, not arbitrary text.
pub fn reconstruct_caller_views(
    source: &str,
    entry_member: Option<&str>,
) -> Result<Vec<CallerView>> {
    let arena = Allocator::default();
    let parsed = parse_program(&arena, source, SourceType::unambiguous());
    ensure!(
        parsed.is_clean(),
        "caller view original JavaScript is invalid"
    );
    let semantics = SemanticBuilder::new().build(&parsed.program);
    let scoping = semantics.semantic.scoping();
    let mut finder = Definitions {
        functions: BTreeMap::new(),
        scoping,
    };
    finder.visit_program(&parsed.program);
    let mut symbols = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    for (key, def) in &finder.functions {
        if let Some(symbol) = def.symbol {
            if symbols.insert(symbol, *key).is_some() {
                ambiguous.insert(symbol);
            }
        }
    }
    for symbol in ambiguous {
        symbols.remove(&symbol);
    }
    for symbol in symbols.keys().copied().collect::<Vec<_>>() {
        let writes = scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .filter(|reference| scoping.get_reference(**reference).is_write())
            .count();
        let declaration_assignment = finder
            .functions
            .get(&symbols[&symbol])
            .is_some_and(|definition| definition.initialized_by_assignment);
        // A single assignment can establish a previously declared function;
        // any additional write means the call target can vary at runtime.
        if writes > usize::from(declaration_assignment) {
            symbols.remove(&symbol);
        }
    }
    // First validate the original function definitions, then extend the map
    // through const aliases. A renamed direct call is still a call to the
    // original function, not a new function definition.
    let mut dynamic_scope = DynamicScope::default();
    dynamic_scope.visit_program(&parsed.program);
    let mut aliases = AliasCollector {
        scoping,
        dynamic_scope: dynamic_scope.found,
        aliases: BTreeMap::new(),
    };
    aliases.visit_program(&parsed.program);
    let mut expanded = symbols.clone();
    // Alias-to-alias chains may be declared in any source order.
    for _ in 0..aliases.aliases.len() {
        let mut grew = false;
        for (alias, target) in &aliases.aliases {
            if let Some(&key) = expanded.get(target) {
                if expanded.insert(*alias, key).is_none() {
                    grew = true;
                }
            }
        }
        if !grew {
            break;
        }
    }

    let mut call_writes = CallPropertyWrites {
        scoping,
        assigned: BTreeSet::new(),
    };
    call_writes.visit_program(&parsed.program);
    let blocked_call_targets = call_writes
        .assigned
        .iter()
        .filter_map(|symbol| expanded.get(symbol).copied())
        .collect::<BTreeSet<_>>();
    let mut collector = Calls {
        source,
        scoping,
        defs: &finder.functions,
        symbols: &expanded,
        aliases: &aliases.aliases,
        blocked_call_targets: &blocked_call_targets,
        unsafe_callers: &dynamic_scope.unsafe_callers,
        stack: Vec::new(),
        edges: BTreeMap::new(),
    };
    collector.visit_program(&parsed.program);
    let mut views = Vec::new();
    for (root, def) in &finder.functions {
        if !def.member || entry_member.is_some_and(|name| def.label.trim_start_matches('.') != name)
        {
            continue;
        }
        let origins = PathOrigins {
            entry: (0..def.params.len()).map(Some).collect(),
            constructed: vec![None; def.params.len()],
        };
        let mut walker = PathWalker {
            defs: &finder.functions,
            edges: &collector.edges,
            root: *root,
            output: Vec::new(),
        };
        walker.walk(
            *root,
            &origins,
            &mut vec![def.label.clone()],
            &mut vec![[root.0, root.1]],
            &mut Vec::new(),
            &mut BTreeSet::from([*root]),
        );
        // Explore the *finite graph* separately from the path-focused index.
        // Each reachable function is expanded once; cycles and arbitrary
        // call depths are represented without enumerating every simple path.
        let mut queue = VecDeque::from([*root]);
        let mut visited = BTreeSet::new();
        let mut reachable_edges = Vec::new();
        while let Some(from) = queue.pop_front() {
            if !visited.insert(from) {
                continue;
            }
            if let Some(edges) = collector.edges.get(&from) {
                for (to, call) in edges {
                    reachable_edges.push(ResolvedCallEdge {
                        from_span: [from.0, from.1],
                        to_span: [to.0, to.1],
                        call: call.clone(),
                    });
                    queue.push_back(*to);
                }
            }
        }
        reachable_edges.sort_by_key(|edge| (edge.from_span, edge.to_span, edge.call.span));
        let reachable_functions =
            propagate_reachable_parameter_origins(*root, &finder.functions, &collector.edges);
        let mut paths = walker.output;
        if reachable_edges.is_empty() {
            continue;
        }
        // Stable display ordering and bounded, meaningful entries.
        paths.sort_by(|a, b| a.functions.cmp(&b.functions));
        let mut view = CallerView {
            entry: def.label.clone(),
            entry_span: [root.0, root.1],
            paths,
            reachable_edges,
            reachable_functions,
            source: String::new(),
        };
        view.source = format_view(&view, source);
        views.push(view);
    }
    Ok(views)
}

#[cfg(test)]
mod tests {
    use super::reconstruct_caller_views;

    #[test]
    fn unrelated_dynamic_eval_does_not_suppress_other_lexical_call_wrappers() -> anyhow::Result<()>
    {
        let source = r#"const unrelated=x=>eval(x);
            const leaf=x=>x===88?true:false;
            const wrapper=()=>leaf.call(this,88);
            const api={};api.run=()=>wrapper();"#;
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        assert!(
            view.reachable_edges
                .iter()
                .any(|edge| { edge.call.callee == "leaf" && edge.call.kind == "function.call" }),
            "{view:?}"
        );
        Ok(())
    }

    #[test]
    fn source_resolved_function_call_preserves_receiver_and_formal_offsets() -> anyhow::Result<()> {
        let source = r#"const leaf=(a,b)=>a*10+b;
            const alias=leaf;
            const wrapper=(x)=>alias.call({kind:"receiver"},8,x);
            const api={};api.run=()=>wrapper(3);"#;
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        let edge = view
            .reachable_edges
            .iter()
            .find(|edge| edge.call.callee == "leaf" && edge.call.kind == "function.call")
            .ok_or_else(|| anyhow::anyhow!("missing lexical Function.call edge"))?;
        assert_eq!(edge.call.arguments.len(), 2);
        assert_eq!(edge.call.arguments[0].expression, "8");
        assert_eq!(edge.call.arguments[1].caller_param_index, Some(0));
        assert_eq!(
            edge.call.this_argument.as_deref(),
            Some("{kind:\"receiver\"}")
        );
        assert_eq!(view.reachable_edges.len(), 2);
        Ok(())
    }

    #[test]
    fn function_call_property_mutation_rejects_false_edges() -> anyhow::Result<()> {
        for mutation in [
            "leaf.call=function(){return 0;};",
            "const alias=leaf;alias.call=function(){return 0;};",
            "delete leaf.call;",
        ] {
            let source=format!(
                "const leaf=x=>x;{mutation}const middle=x=>leaf.call(null,7);const api={{}};api.run=()=>middle(1);"
            );
            let view = reconstruct_caller_views(&source, Some("run"))?.remove(0);
            assert!(
                view.reachable_edges
                    .iter()
                    .all(|edge| edge.call.callee != "leaf"),
                "{mutation}: {view:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn shadowed_or_dynamic_function_call_target_is_not_original_lexical_function(
    ) -> anyhow::Result<()> {
        let source = r#"const leaf=x=>x;
            const wrapper=(leaf,value)=>leaf.call(null,value);
            const api={};api.run=()=>wrapper(x=>x*2,7);"#;
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        assert!(
            view.reachable_edges
                .iter()
                .all(|edge| edge.call.callee != "leaf"),
            "{view:?}"
        );
        Ok(())
    }

    #[test]
    fn spreading_receiver_or_dynamic_eval_disables_exact_function_call_edges() -> anyhow::Result<()>
    {
        let cases=[
            "const leaf=x=>x;const wrapper=a=>leaf.call(...a,9);",
            "const leaf=x=>x;const wrapper=()=>{eval('leaf.call=function(){}');return leaf.call(null,9);};",
        ];
        for body in cases {
            let src = format!("{body}const api={{}};api.run=()=>wrapper([]);");
            let view = reconstruct_caller_views(&src, Some("run"))?.remove(0);
            assert!(
                view.reachable_edges
                    .iter()
                    .all(|edge| edge.call.callee != "leaf"),
                "{view:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn spread_after_function_call_receiver_does_not_shift_original_parameter_indexes(
    ) -> anyhow::Result<()> {
        let source = r#"const leaf=(a,b,c)=>c;
            const wrapper=(x,y,z)=>leaf.call(null,x,...y,z);
            const api={};api.run=()=>wrapper(1,[],3);"#;
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        let edge = view
            .reachable_edges
            .iter()
            .find(|edge| edge.call.callee == "leaf")
            .ok_or_else(|| anyhow::anyhow!("missing Function.call edge"))?;
        assert_eq!(edge.call.arguments.len(), 3);
        assert!(edge.call.arguments[0].positional);
        assert!(!edge.call.arguments[1].positional);
        assert!(!edge.call.arguments[2].positional);
        Ok(())
    }

    #[test]
    fn complete_graph_reaches_beyond_display_depth_and_preserves_cycles() -> anyhow::Result<()> {
        let source = r#"const f5=(x)=>x ? f1(x-1) : x;
          const f4=(x)=>f5(x);
          const f3=(x)=>f4(x);
          const f2=(x)=>f3(x);
          const f1=(x)=>f2(x);
          const api={}; api.run=(x)=>f1(x);"#;
        let views = reconstruct_caller_views(source, Some("run"))?;
        assert_eq!(views.len(), 1);
        let view = &views[0];
        assert!(view
            .paths
            .iter()
            .all(|path| !path.functions.contains(&"f5".to_owned())));
        assert!(view
            .reachable_edges
            .iter()
            .any(|edge| edge.call.callee == "f5"));
        assert_eq!(view.reachable_edges.len(), 6);
        assert!(view
            .source
            .contains("Complete reachable lexical call graph"));
        Ok(())
    }

    #[test]
    fn propagates_parameter_origins_beyond_display_cap_and_through_cycles() -> anyhow::Result<()> {
        let source = r#"const leaf=(p)=>p;
          const f4=(p)=>leaf(p);
          const f3=(p)=>f4(p);
          const f2=(p)=>f3(p);
          const f1=(p)=>f2(p);
          const api={};api.run=(input)=>f1(input);"#;
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        assert!(view
            .paths
            .iter()
            .all(|path| !path.functions.contains(&"leaf".into())));
        let leaf = view
            .reachable_functions
            .iter()
            .find(|item| item.name == "leaf")
            .ok_or_else(|| anyhow::anyhow!("leaf missing"))?;
        assert_eq!(leaf.shortest_call_depth, 5);
        assert_eq!(leaf.parameters[0].possible_entry_indices, [0]);
        assert!(!leaf.parameters[0].unknown_or_nonentry_input);
        Ok(())
    }

    #[test]
    fn multiple_callers_preserve_ambiguous_and_nonentry_sources() -> anyhow::Result<()> {
        let source = r#"const leaf=(p)=>p;
          const fromA=(x)=>leaf(x);
          const fromB=(y)=>leaf(y);
          const api={};api.run=(first,second)=>{
              fromA(first);
              fromB(second);
              leaf(5);
          };"#;
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        let leaf = view
            .reachable_functions
            .iter()
            .find(|item| item.name == "leaf")
            .ok_or_else(|| anyhow::anyhow!("leaf missing"))?;
        assert_eq!(leaf.parameters[0].possible_entry_indices, [0, 1]);
        assert!(leaf.parameters[0].unknown_or_nonentry_input);
        Ok(())
    }

    #[test]
    fn recursive_parameter_swaps_converge_to_all_possible_sources() -> anyhow::Result<()> {
        let source = r#"const one=(a,b)=>two(a,b);
          const two=(a,b)=>one(b,a);
          const api={};api.run=(first,second)=>one(first,second);"#;
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        let one = view
            .reachable_functions
            .iter()
            .find(|item| item.name == "one")
            .ok_or_else(|| anyhow::anyhow!("recursive function missing"))?;
        for param in &one.parameters {
            assert_eq!(param.possible_entry_indices, [0, 1]);
            assert!(!param.unknown_or_nonentry_input);
        }
        assert_eq!(view.reachable_edges.len(), 3);
        Ok(())
    }

    #[test]
    fn entry_defaults_are_not_identical_to_external_argument_values() -> anyhow::Result<()> {
        let source = "const helper=(value)=>value;                      const api={};api.run=(input=42)=>helper(input);";
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        let entry = view
            .reachable_functions
            .iter()
            .find(|function| function.name == ".run")
            .ok_or_else(|| anyhow::anyhow!("entry missing"))?;
        assert!(entry.parameters[0].possible_entry_indices.is_empty());
        assert!(entry.parameters[0].unknown_or_nonentry_input);
        let helper = view
            .reachable_functions
            .iter()
            .find(|function| function.name == "helper")
            .ok_or_else(|| anyhow::anyhow!("helper missing"))?;
        assert!(helper.parameters[0].possible_entry_indices.is_empty());
        assert!(helper.parameters[0].unknown_or_nonentry_input);
        Ok(())
    }

    #[test]
    fn zero_parameter_functions_still_propagate_reachability() -> anyhow::Result<()> {
        let source = "const leaf=(p)=>p;const noArgs=()=>leaf(5);                      const entry={};entry.run=()=>noArgs();";
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        let leaf = view
            .reachable_functions
            .iter()
            .find(|function| function.name == "leaf")
            .ok_or_else(|| anyhow::anyhow!("zero-parameter intermediary blocked leaf"))?;
        assert_eq!(leaf.shortest_call_depth, 2);
        assert!(leaf.parameters[0].possible_entry_indices.is_empty());
        assert!(leaf.parameters[0].unknown_or_nonentry_input);
        Ok(())
    }

    #[test]
    fn spread_and_default_arguments_do_not_claim_direct_forwarding() -> anyhow::Result<()> {
        let source = r#"const leaf=(a,b)=>[a,b];
          const withDefault=(a=10)=>leaf(a,a);
          const middle=(x,y,arr)=>{
              leaf(...arr,x);
              leaf(x,...arr);
              withDefault(y);
          };
          const api={};api.run=(one,two,arr)=>middle(one,two,arr);"#;
        let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
        let leaf = view
            .reachable_functions
            .iter()
            .find(|item| item.name == "leaf")
            .ok_or_else(|| anyhow::anyhow!("leaf missing"))?;
        assert!(leaf.parameters[0].possible_entry_indices.contains(&0));
        assert!(leaf.parameters[0].unknown_or_nonentry_input);
        assert!(leaf.parameters[1].unknown_or_nonentry_input);
        assert!(!leaf.parameters[1].possible_entry_indices.contains(&0));
        Ok(())
    }

    #[test]
    fn one_hop_entry_has_graph_even_without_long_path() -> anyhow::Result<()> {
        let source = "const helper=(x)=>x;const api={};api.run=(x)=>helper(x);";
        let views = reconstruct_caller_views(source, Some("run"))?;
        assert_eq!(views.len(), 1);
        assert!(views[0].paths.is_empty());
        assert_eq!(views[0].reachable_edges.len(), 1);
        Ok(())
    }

    #[test]
    fn forwards_an_entry_parameter_through_new_and_call_by_resolved_symbols() -> anyhow::Result<()>
    {
        let source = r#"function app(){
            const deep=function(a,b){return b;};
            const Wd=function(x,y){return deep(y,x);};
            const AV={}; AV.aoF_=function(J,Q){return new Wd(Q,J);};
        }"#;
        let views = reconstruct_caller_views(source, Some("aoF_"))?;
        assert_eq!(views.len(), 1, "{views:?}");
        let path = views[0]
            .paths
            .iter()
            .find(|path| path.functions.last().is_some_and(|name| name == "deep"))
            .ok_or_else(|| anyhow::anyhow!("missing 3-function path"))?;
        assert_eq!(path.functions, vec![".aoF_", "Wd", "deep"]);
        assert_eq!(path.leaf_parameters[0].from_entry_index, Some(0));
        assert_eq!(path.leaf_parameters[1].from_entry_index, Some(1));
        assert!(views[0]
            .source
            .contains("`a` (parameter 0) ← entry `J` (parameter 0)"));
        Ok(())
    }

    #[test]
    fn construction_receiver_propagates_through_exact_forwarding() -> anyhow::Result<()> {
        let source = r#"function outer() {
          const leaf = state => state;
          const middle = value => leaf(value);
          const Wd = function(input) { middle((this)); };
          const AV = {}; AV.aoF_ = function(arg) { return new Wd(arg); };
        }"#;
        let view = reconstruct_caller_views(source, Some("aoF_"))?.remove(0);
        let path = view
            .paths
            .iter()
            .find(|p| p.functions == [".aoF_", "Wd", "middle", "leaf"])
            .ok_or_else(|| anyhow::anyhow!("missing resolved path"))?;
        let receiver = path.leaf_parameters[0]
            .constructed_receiver
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("fresh this origin missing"))?;
        assert_eq!(receiver.constructor, "Wd");
        assert!(path.leaf_parameters[0].from_entry_index.is_none());
        assert!(view.source.contains("fresh receiver of new Wd"));
        Ok(())
    }

    #[test]
    fn direct_calls_and_forwarded_objects_do_not_prove_fresh_receivers() -> anyhow::Result<()> {
        for source in [
          "const leaf=x=>x;const Wd=function(){leaf(this)};const api={};api.run=()=>Wd();",
          "const leaf=x=>x;const Wd=function(x){leaf(x)};const api={};api.run=(obj)=>new Wd(obj);",
        ] {
            let view = reconstruct_caller_views(source, Some("run"))?.remove(0);
            let path = view.paths.iter()
                .find(|p| p.functions.last().is_some_and(|name| name == "leaf"))
                .ok_or_else(|| anyhow::anyhow!("missing leaf"))?;
            assert!(path.leaf_parameters[0].constructed_receiver.is_none(),
                "unsound construction proof: {path:?}");
        }
        Ok(())
    }

    #[test]
    fn arrow_functions_and_initialized_lexical_assignments_work() -> anyhow::Result<()> {
        let source = r#"let middle;middle=(x)=>last(x);
          const last=(y)=>y; const service={};service.run=(arg)=>middle(arg);"#;
        let views = reconstruct_caller_views(source, Some("run"))?;
        assert_eq!(views.len(), 1);
        let path = views[0]
            .paths
            .iter()
            .find(|p| p.functions.last().is_some_and(|x| x == "last"))
            .ok_or_else(|| anyhow::anyhow!("arrow call chain absent"))?;
        assert_eq!(path.leaf_parameters[0].from_entry_index, Some(0));
        Ok(())
    }

    #[test]
    fn follows_immutable_function_and_parameter_alias_chains() -> anyhow::Result<()> {
        let source = r#"function app(){
            const deep=(leaf)=>leaf;
            var deepAlias=deep;
            const deepAlias2=deepAlias;
            const middle=(input)=>{
                const copied=input;
                const forwarded=copied;
                return deepAlias2(forwarded);
            };
            let middleAlias=middle;
            const entry={}; entry.run=(request)=>middleAlias(request);
        }"#;
        let views = reconstruct_caller_views(source, Some("run"))?;
        assert_eq!(views.len(), 1, "{views:?}");
        let path = views[0]
            .paths
            .iter()
            .find(|path| path.functions.last().is_some_and(|name| name == "deep"))
            .ok_or_else(|| anyhow::anyhow!("missing aliased deep path"))?;
        assert_eq!(path.functions, vec![".run", "middle", "deep"]);
        assert_eq!(path.leaf_parameters[0].from_entry_index, Some(0));
        Ok(())
    }

    #[test]
    fn mutated_let_alias_or_eval_blocks_false_function_edges() -> anyhow::Result<()> {
        for mutation in [
            "const deep=(v)=>v; let alias=deep; alias=()=>0;",
            "const deep=(v)=>v; let alias=deep; eval('alias = ()=>0');",
        ] {
            let source = format!(
                "function app(){{{mutation} const middle=(arg)=>alias(arg);                 const entry={{}};entry.run=(request)=>middle(request);}}"
            );
            let views = reconstruct_caller_views(&source, Some("run"))?;
            assert!(
                views.iter().all(|view| view
                    .paths
                    .iter()
                    .all(|path| { !path.functions.iter().any(|name| name == "deep") })),
                "{views:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn shadowed_function_name_is_not_resolved_via_alias() -> anyhow::Result<()> {
        let source = "const deep=(v)=>v;const middle=(deep, arg)=>{const alias=deep;return alias(arg);};                      const entry={};entry.run=(request)=>middle(()=>0,request);";
        let views = reconstruct_caller_views(source, Some("run"))?;
        assert!(views.iter().all(|view| view
            .paths
            .iter()
            .all(|path| { !path.functions.iter().any(|name| name == "deep") })));
        Ok(())
    }

    #[test]
    fn alias_of_mutated_function_does_not_create_certain_call_edge() -> anyhow::Result<()> {
        let source = r#"function app(){
            let deep=(value)=>value;
            const alias=deep;
            deep=(value)=>value+1;
            const middle=(arg)=>alias(arg);
            const entry={};entry.run=(request)=>middle(request);
        }"#;
        let views = reconstruct_caller_views(source, Some("run"))?;
        assert!(views.iter().all(|view| view
            .paths
            .iter()
            .all(|path| { !path.functions.iter().any(|name| name == "deep") })));
        Ok(())
    }

    #[test]
    fn aliased_parameter_with_direct_write_is_not_invariant() -> anyhow::Result<()> {
        let source = r#"const deep=(p)=>p;
            const middle=(arg)=>{const copy=arg; arg=0;return deep(copy);};
            const entry={};entry.run=(request)=>middle(request);"#;
        let views = reconstruct_caller_views(source, Some("run"))?;
        assert_eq!(views.len(), 1);
        let path = views[0]
            .paths
            .iter()
            .find(|p| p.functions.last().is_some_and(|name| name == "deep"))
            .ok_or_else(|| anyhow::anyhow!("missing path"))?;
        assert_eq!(path.leaf_parameters[0].from_entry_index, None);
        Ok(())
    }

    #[test]
    fn rejects_mutated_parameter_as_certain_forwarding() -> anyhow::Result<()> {
        let source = r#"const deep=function(p){return p;};const Wd=function(x){x=3;return deep(x);};const api={};api.m=function(arg){return new Wd(arg);};"#;
        let views = reconstruct_caller_views(source, Some("m"))?;
        assert_eq!(views.len(), 1);
        let path = &views[0].paths[0];
        assert_eq!(path.leaf_parameters[0].from_entry_index, None);
        Ok(())
    }
}
