//! Recover structured control flow from numeric-state ternary dispatchers.
//!
//! The parser handles arbitrary state labels and source expressions, not any
//! particular obfuscator vocabulary. Only single-entry reducible loops are
//! rendered: irreducible graphs and unmodelled state transitions are left
//! unchanged rather than emitted with altered execution order.
use crate::{
    control_flow::direct_assignment_name,
    direct_identifier_name, fragment,
    numeric::exact_u64,
    value_eval::{eval, inert_literal_value, known_bool},
};
use oxc_ast::ast::{
    ArrayExpressionElement, AssignmentExpression, AssignmentTarget, BindingPattern, CallExpression,
    Expression, ForStatement, ForStatementInit, IdentifierReference, Statement, UpdateExpression,
    VariableDeclarationKind, WhileStatement, WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_ecmascript::{
    side_effects::{MayHaveSideEffects, MayHaveSideEffectsContext, PropertyReadSideEffects},
    GlobalContext,
};
use oxc_semantic::Scoping;
use oxc_span::GetSpan;
use oxc_syntax::symbol::SymbolId;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Debug, Clone)]
enum Next {
    State(u64),
    Choose {
        condition: String,
        yes: Box<Route>,
        no: Box<Route>,
    },
}

#[derive(Debug, Clone)]
struct Route {
    effects: Vec<String>,
    next: Next,
}

impl Route {
    fn jump(state: &str, target: u64) -> Self {
        Self {
            effects: vec![format!("{state} = {target};")],
            next: Next::State(target),
        }
    }
    fn targets(&self, out: &mut Vec<u64>) {
        match &self.next {
            Next::State(target) => out.push(*target),
            Next::Choose { yes, no, .. } => {
                yes.targets(out);
                no.targets(out);
            }
        }
    }
    fn plain_target(&self) -> Option<u64> {
        match self.next {
            Next::State(state) => Some(state),
            Next::Choose { .. } => None,
        }
    }
}

fn number(expr: &Expression<'_>) -> Option<u64> {
    eval(expr)?.number().and_then(exact_u64)
}

fn unparen<'a>(expr: &'a Expression<'a>) -> &'a Expression<'a> {
    match expr {
        Expression::ParenthesizedExpression(paren) => unparen(&paren.expression),
        _ => expr,
    }
}

fn state_test(expr: &Expression<'_>, state: &str) -> Option<u64> {
    let Expression::BinaryExpression(test) = unparen(expr) else {
        return None;
    };
    if !matches!(test.operator.as_str(), "==" | "===") {
        return None;
    }
    match (
        direct_identifier_name(unparen(&test.left)),
        direct_identifier_name(unparen(&test.right)),
    ) {
        (Some(id), _) if id == state => number(&test.right),
        (_, Some(id)) if id == state => number(&test.left),
        _ => None,
    }
}

fn parse_target(expr: &Expression<'_>, state: &str, source: &str) -> Option<Route> {
    match unparen(expr) {
        Expression::ConditionalExpression(branch) => Some(Route {
            effects: vec![],
            next: Next::Choose {
                condition: fragment(source, branch.test.span()).to_owned(),
                yes: Box::new(parse_target(&branch.consequent, state, source)?),
                no: Box::new(parse_target(&branch.alternate, state, source)?),
            },
        }),
        Expression::SequenceExpression(sequence) => {
            let (last, rest) = sequence.expressions.split_last()?;
            let mut result = parse_target(last, state, source)?;
            let mut effects = rest
                .iter()
                .map(|effect| format!("({});", fragment(source, effect.span())))
                .collect::<Vec<_>>();
            effects.append(&mut result.effects);
            result.effects = effects;
            Some(result)
        }
        expr => Some(Route::jump(state, number(expr)?)),
    }
}

fn parse_route(expr: &Expression<'_>, state: &str, source: &str) -> Option<Route> {
    let expr = unparen(expr);
    match expr {
        Expression::AssignmentExpression(assignment)
            if assignment.operator.as_str() == "="
                && direct_assignment_name(&assignment.left) == Some(state) =>
        {
            parse_target(&assignment.right, state, source)
        }
        Expression::SequenceExpression(sequence) => {
            let (last, rest) = sequence.expressions.split_last()?;
            let mut result = parse_route(last, state, source)?;
            result.effects.splice(
                0..0,
                rest.iter()
                    .map(|expression| format!("({});", fragment(source, expression.span())))
                    .collect::<Vec<_>>(),
            );
            Some(result)
        }
        Expression::ConditionalExpression(conditional) => Some(Route {
            effects: Vec::new(),
            next: Next::Choose {
                condition: fragment(source, conditional.test.span()).to_owned(),
                yes: Box::new(parse_route(&conditional.consequent, state, source)?),
                no: Box::new(parse_route(&conditional.alternate, state, source)?),
            },
        }),
        _ => None,
    }
}

fn collect_dispatch(
    expr: &Expression<'_>,
    state: &str,
    source: &str,
    cases: &mut BTreeMap<u64, Option<Route>>,
) -> Option<()> {
    match unparen(expr) {
        Expression::ConditionalExpression(branch) => {
            let value = state_test(&branch.test, state)?;
            // Keep an unsupported case in the index, but only require its
            // transition to be modelled if that numeric state is reachable
            // from the proved initializer. Unknown unreachable transitions
            // must not prevent recovery of the actually executed states.
            let route = parse_route(&branch.consequent, state, source);
            if cases.insert(value, route).is_some() {
                return None;
            }
            collect_dispatch(&branch.alternate, state, source, cases)
        }
        Expression::LogicalExpression(logical) if logical.operator.as_str() == "&&" => {
            let value = state_test(&logical.left, state)?;
            let route = parse_route(&logical.right, state, source);
            if cases.insert(value, route).is_some() {
                return None;
            }
            Some(())
        }
        _ => None,
    }
}

/// Inspect the value of a declaration initializer for a statically assigned
/// state. The full declaration remains in the generated source (including
/// evaluation of the array elements), so this only establishes the next edge.
/// Expressions after the assignment must not be able to write the state.
fn inert_after_state_write(expr: &Expression<'_>) -> bool {
    match unparen(expr) {
        Expression::Identifier(_)
        | Expression::StringLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::ThisExpression(_) => true,
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "void" => {
            inert_after_state_write(&unary.argument)
        }
        Expression::ArrayExpression(array) => array.elements.iter().all(|item| match item {
            ArrayExpressionElement::Elision(_) => true,
            ArrayExpressionElement::Identifier(_)
            | ArrayExpressionElement::StringLiteral(_)
            | ArrayExpressionElement::NumericLiteral(_)
            | ArrayExpressionElement::NullLiteral(_)
            | ArrayExpressionElement::BooleanLiteral(_) => true,
            ArrayExpressionElement::UnaryExpression(unary) if unary.operator.as_str() == "void" => {
                inert_after_state_write(&unary.argument)
            }
            _ => false,
        }),
        _ => false,
    }
}

fn assigned_state_in_initializer(expr: &Expression<'_>, state: &str) -> Option<u64> {
    let Expression::SequenceExpression(sequence) = unparen(expr) else {
        return None;
    };
    let (last, prefix) = sequence.expressions.split_last()?;
    if !inert_after_state_write(last) {
        return None;
    }
    let mut result = None;
    for item in prefix {
        match unparen(item) {
            Expression::AssignmentExpression(assign)
                if assign.operator.as_str() == "="
                    && direct_assignment_name(&assign.left) == Some(state) =>
            {
                result = Some(number(&assign.right)?);
            }
            expr if inert_after_state_write(expr) => {}
            _ => return None,
        }
    }
    result
}

/// Statement-form state dispatchers are the same graph as ternary
/// dispatchers, with effects spread across statement blocks instead of
/// comma expressions. Keep the original effect order and lexical scope.
fn parse_statement_route(
    stmt: &Statement<'_>,
    state: &str,
    exit: u64,
    source: &str,
) -> Option<Route> {
    match stmt {
        Statement::ExpressionStatement(expression) => {
            parse_route(&expression.expression, state, source)
        }
        Statement::ReturnStatement(_) | Statement::ThrowStatement(_) => Some(Route {
            // Both return and throw leave the dispatcher's function
            // immediately. Keep the original expression evaluation and
            // abrupt completion in the effect, and treat the transition as
            // the synthetic graph exit for reachability and branch joins.
            effects: vec![fragment(source, stmt.span()).to_owned()],
            next: Next::State(exit),
        }),
        Statement::VariableDeclaration(declaration)
            if declaration.kind == VariableDeclarationKind::Var
                && declaration.declarations.len() == 1 =>
        {
            let initializer = declaration.declarations[0].init.as_ref()?;
            let target = assigned_state_in_initializer(initializer, state)?;
            Some(Route {
                effects: vec![fragment(source, stmt.span()).to_owned()],
                next: Next::State(target),
            })
        }
        Statement::BlockStatement(block) => {
            let (last, prefix) = block.body.split_last()?;
            // Moving a block-local declaration outside its original block
            // changes temporal-dead-zone/closure semantics. Retain those
            // structures until the graph emitter can render lexical regions.
            if prefix.iter().any(|statement| {
                matches!(
                    statement,
                    Statement::VariableDeclaration(declaration)
                        if declaration.kind != oxc_ast::ast::VariableDeclarationKind::Var
                ) || matches!(
                    statement,
                    Statement::FunctionDeclaration(_) | Statement::ClassDeclaration(_)
                )
            }) {
                return None;
            }
            let mut route = parse_statement_route(last, state, exit, source)?;
            let mut effects = prefix
                .iter()
                .map(|statement| fragment(source, statement.span()).to_owned())
                .collect::<Vec<_>>();
            effects.append(&mut route.effects);
            route.effects = effects;
            Some(route)
        }
        Statement::IfStatement(branch) => Some(Route {
            effects: Vec::new(),
            next: Next::Choose {
                condition: fragment(source, branch.test.span()).to_owned(),
                yes: Box::new(parse_statement_route(
                    &branch.consequent,
                    state,
                    exit,
                    source,
                )?),
                no: Box::new(parse_statement_route(
                    branch.alternate.as_ref()?,
                    state,
                    exit,
                    source,
                )?),
            },
        }),
        _ => None,
    }
}

/// Early-case statements are only interchangeable with a graph exit when
/// they *unconditionally* complete the current function (return or throw).
/// Preserve all preceding expressions in a block; their lexical-scope
/// restrictions are independently validated by parse_statement_route.
fn has_terminal_completion(stmt: &Statement<'_>) -> bool {
    match stmt {
        Statement::ReturnStatement(_) | Statement::ThrowStatement(_) => true,
        Statement::BlockStatement(block) => block.body.last().is_some_and(has_terminal_completion),
        _ => false,
    }
}

fn collect_dispatch_statement(
    stmt: &Statement<'_>,
    state: &str,
    exit: u64,
    source: &str,
    cases: &mut BTreeMap<u64, Option<Route>>,
) -> Option<()> {
    match stmt {
        Statement::IfStatement(branch) => {
            let value = state_test(&branch.test, state)?;
            let route = parse_statement_route(&branch.consequent, state, exit, source);
            if cases.insert(value, route).is_some() {
                return None;
            }
            if let Some(alternate) = &branch.alternate {
                collect_dispatch_statement(alternate, state, exit, source, cases)?;
            }
            Some(())
        }
        Statement::ExpressionStatement(expression) => {
            collect_dispatch(&expression.expression, state, source, cases)
        }
        Statement::BlockStatement(block) => {
            let (last, preceding) = block.body.split_last()?;
            // Independent early-return / early-throw state cases can
            // precede the final if/else ladder. A matching branch must
            // complete the function unconditionally, and all branch effects
            // must be represented exactly once in the structured output.
            for statement in preceding {
                let Statement::IfStatement(branch) = statement else {
                    return None;
                };
                if branch.alternate.is_some() || !has_terminal_completion(&branch.consequent) {
                    return None;
                }
                let label = state_test(&branch.test, state)?;
                let route = parse_statement_route(&branch.consequent, state, exit, source)?;
                if cases.insert(label, Some(route)).is_some() {
                    return None;
                }
            }
            collect_dispatch_statement(last, state, exit, source, cases)
        }
        _ => None,
    }
}

fn exit_state(expr: &Expression<'_>, state: &str) -> Option<u64> {
    let Expression::BinaryExpression(binary) = unparen(expr) else {
        return None;
    };
    if !matches!(binary.operator.as_str(), "!=" | "!==") {
        return None;
    }
    if direct_identifier_name(unparen(&binary.left)) == Some(state) {
        number(&binary.right)
    } else if direct_identifier_name(unparen(&binary.right)) == Some(state) {
        number(&binary.left)
    } else {
        None
    }
}

#[derive(Debug, Clone)]
enum LoopBody {
    Natural {
        condition: String,
        enters_on_true: bool,
        entering: Route,
        exiting: Route,
        header_effects: Vec<String>,
        body_start: u64,
    },
    /// Single-entry cycle with common exit and early breaks from its body.
    MultiExit { body: String },
}

#[derive(Debug, Clone)]
struct Loop {
    members: BTreeSet<u64>,
    exit: u64,
    body: LoopBody,
}

fn reachable(start: u64, exit: u64, graph: &BTreeMap<u64, Route>) -> Option<BTreeSet<u64>> {
    let mut done = BTreeSet::new();
    let mut queue = VecDeque::from([start]);
    while let Some(current) = queue.pop_front() {
        if current == exit || !done.insert(current) {
            continue;
        }
        let route = graph.get(&current)?;
        let mut targets = Vec::new();
        route.targets(&mut targets);
        for target in targets {
            queue.push_back(target);
        }
        if done.len() > 2048 {
            return None;
        }
    }
    Some(done)
}

/// Collapse already-structured inner loops before discovering outer ones.
fn collapsed_edges(
    state: u64,
    graph: &BTreeMap<u64, Route>,
    loops: &BTreeMap<u64, Loop>,
) -> Vec<u64> {
    if let Some(plan) = loops.get(&state) {
        return vec![plan.exit];
    }
    let mut edges = Vec::new();
    if let Some(route) = graph.get(&state) {
        route.targets(&mut edges);
    }
    edges
}

fn loop_region(
    enter: u64,
    header: u64,
    graph: &BTreeMap<u64, Route>,
    loops: &BTreeMap<u64, Loop>,
) -> BTreeSet<u64> {
    let mut region = BTreeSet::from([header]);
    let mut queue = VecDeque::from([enter]);
    while let Some(node) = queue.pop_front() {
        if !region.insert(node) {
            continue;
        }
        for next in collapsed_edges(node, graph, loops) {
            queue.push_back(next);
        }
    }
    region
}

fn build_loops(
    graph: &BTreeMap<u64, Route>,
    nodes: &BTreeSet<u64>,
    exit: u64,
) -> Option<BTreeMap<u64, Loop>> {
    let mut loops = BTreeMap::new();
    // Choose innermost single-entry natural loops first. Collapsing each
    // discovered loop exposes the surrounding reducible loop, even when its
    // body contains conditional paths and further loops.
    loop {
        let mut choices = Vec::new();
        for &header in nodes {
            if loops.contains_key(&header)
                || loops
                    .values()
                    .any(|plan: &Loop| plan.members.contains(&header))
            {
                continue;
            }
            let route = graph.get(&header)?;
            let Next::Choose { condition, yes, no } = &route.next else {
                continue;
            };
            let (Some(a), Some(b)) = (yes.plain_target(), no.plain_target()) else {
                continue;
            };
            let a_returns = all_paths_reach(a, header, exit, graph, &loops, &mut BTreeSet::new());
            let b_returns = all_paths_reach(b, header, exit, graph, &loops, &mut BTreeSet::new());
            if a_returns == b_returns {
                continue;
            }
            let (entering, exiting, enters_on_true, enter, out) = if a_returns {
                (yes, no, true, a, b)
            } else {
                (no, yes, false, b, a)
            };
            let region = loop_region(enter, header, graph, &loops);
            if !region.is_subset(nodes) {
                continue;
            }
            // The only way into a loop must be through its header.
            let mut valid = true;
            for &outside in nodes {
                if region.contains(&outside)
                    || loops.values().any(|plan: &Loop| {
                        plan.members.contains(&outside) && !loops.contains_key(&outside)
                    })
                {
                    continue;
                }
                if collapsed_edges(outside, graph, &loops)
                    .iter()
                    .any(|target| region.contains(target) && *target != header)
                {
                    valid = false;
                    break;
                }
            }
            if !valid {
                continue;
            }
            let mut members = region;
            for (nested_header, nested) in &loops {
                if members.contains(nested_header) {
                    members.extend(nested.members.iter().copied());
                }
            }
            choices.push((
                members.len(),
                header,
                Loop {
                    members,
                    exit: out,
                    body: LoopBody::Natural {
                        condition: condition.clone(),
                        enters_on_true,
                        entering: entering.as_ref().clone(),
                        exiting: exiting.as_ref().clone(),
                        header_effects: route.effects.clone(),
                        body_start: enter,
                    },
                },
            ));
        }
        if choices.is_empty() {
            break;
        }
        choices.sort_by_key(|(size, header, _)| (*size, *header));
        let (_, header, selected) = choices.remove(0);
        loops.insert(header, selected);
    }
    Some(loops)
}

/// Expand a cycle from one header until every path either returns to it
/// or reaches the *same* exit. A repeated non-header node on a path is an
/// unstructured inner cycle and cannot be represented by this loop.
struct MultiExitEmitter<'a> {
    graph: &'a BTreeMap<u64, Route>,
    header: u64,
    exit: u64,
    members: BTreeSet<u64>,
    visited: BTreeSet<u64>,
    saw_continue: bool,
    saw_break: bool,
    fuel: usize,
}

impl MultiExitEmitter<'_> {
    fn state(&mut self, state: u64, initial: bool) -> Option<String> {
        self.fuel = self.fuel.checked_sub(1)?;
        if !initial && state == self.header {
            self.saw_continue = true;
            return Some("continue;".into());
        }
        if state == self.exit {
            self.saw_break = true;
            return Some("break;".into());
        }
        if !self.visited.insert(state) {
            return None;
        }
        self.members.insert(state);
        let route = self.graph.get(&state)?;
        let text = self.route(route);
        self.visited.remove(&state);
        text
    }

    fn route(&mut self, route: &Route) -> Option<String> {
        self.fuel = self.fuel.checked_sub(1)?;
        let mut text = route.effects.join("\n");
        match &route.next {
            Next::State(target) => text.push_str(&self.state(*target, false)?),
            Next::Choose { condition, yes, no } => {
                let then_body = self.route(yes)?;
                let else_body = self.route(no)?;
                text.push_str(&format!(
                    "\nif ({condition}) {{\n{then_body}\n}} else {{\n{else_body}\n}}"
                ));
            }
        }
        Some(text)
    }
}

/// Natural single-entry cycles can have early exits from internal branches:
/// neither header arm necessarily returns to the header on every path.
/// Render each edge as structured break/continue, then collapse the whole
/// loop to its common exit for the outer branch-join calculation.
/// Tarjan SCCs identify actual cyclic regions rather than trying every
/// pair of graph states as possible loop boundaries. The graph is already
/// restricted to the statically proven reachable states.
fn strongly_connected_regions(
    graph: &BTreeMap<u64, Route>,
    nodes: &BTreeSet<u64>,
) -> Vec<BTreeSet<u64>> {
    struct Search<'a> {
        graph: &'a BTreeMap<u64, Route>,
        nodes: &'a BTreeSet<u64>,
        next: usize,
        index: BTreeMap<u64, usize>,
        low: BTreeMap<u64, usize>,
        stack: Vec<u64>,
        on_stack: BTreeSet<u64>,
        regions: Vec<BTreeSet<u64>>,
    }
    impl Search<'_> {
        fn visit(&mut self, node: u64) {
            let index = self.next;
            self.next += 1;
            self.index.insert(node, index);
            self.low.insert(node, index);
            self.stack.push(node);
            self.on_stack.insert(node);
            let mut successors = Vec::new();
            if let Some(route) = self.graph.get(&node) {
                route.targets(&mut successors);
            }
            for next in successors
                .into_iter()
                .filter(|state| self.nodes.contains(state))
            {
                if !self.index.contains_key(&next) {
                    self.visit(next);
                    if let Some(&child_low) = self.low.get(&next) {
                        if let Some(current) = self.low.get_mut(&node) {
                            *current = (*current).min(child_low);
                        }
                    }
                } else if self.on_stack.contains(&next) {
                    if let Some(&target_index) = self.index.get(&next) {
                        if let Some(current) = self.low.get_mut(&node) {
                            *current = (*current).min(target_index);
                        }
                    }
                }
            }
            if self.low.get(&node) == self.index.get(&node) {
                let mut region = BTreeSet::new();
                while let Some(member) = self.stack.pop() {
                    self.on_stack.remove(&member);
                    region.insert(member);
                    if member == node {
                        break;
                    }
                }
                self.regions.push(region);
            }
        }
    }
    let mut search = Search {
        graph,
        nodes,
        next: 0,
        index: BTreeMap::new(),
        low: BTreeMap::new(),
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        regions: Vec::new(),
    };
    for &node in nodes {
        if !search.index.contains_key(&node) {
            search.visit(node);
        }
    }
    search.regions
}

fn extend_multi_exit_loops(
    graph: &BTreeMap<u64, Route>,
    nodes: &BTreeSet<u64>,
    initial: u64,
    exit: u64,
    loops: &mut BTreeMap<u64, Loop>,
) {
    let regions = strongly_connected_regions(graph, nodes);
    for region in regions {
        let is_cycle = region.len() > 1
            || region.iter().any(|&state| {
                let mut targets = Vec::new();
                if let Some(route) = graph.get(&state) {
                    route.targets(&mut targets);
                }
                targets.contains(&state)
            });
        if !is_cycle
            || loops
                .values()
                .any(|plan| !plan.members.is_disjoint(&region))
        {
            continue;
        }
        let mut entries = BTreeSet::new();
        if region.contains(&initial) {
            entries.insert(initial);
        }
        let mut exits = BTreeSet::new();
        for &state in nodes {
            let mut targets = Vec::new();
            if let Some(route) = graph.get(&state) {
                route.targets(&mut targets);
            }
            for target in targets {
                if region.contains(&state) && !region.contains(&target) {
                    exits.insert(target);
                } else if !region.contains(&state) && region.contains(&target) {
                    entries.insert(target);
                }
            }
        }
        let Some(&header) = entries.first() else {
            continue;
        };
        if entries.len() != 1 || exits.is_empty() {
            continue;
        }
        // A shared exit must be reachable from every outgoing edge of the
        // cycle; then the exact path emitter verifies that no alternative
        // transition can bypass the exit or hide an unstructured inner cycle.
        let mut exit_maps = exits
            .iter()
            .map(|&state| reachable_collapsed(state, exit, graph, loops));
        let Some(first) = exit_maps.next() else {
            continue;
        };
        let candidates = exit_maps.fold(
            first.keys().copied().collect::<BTreeSet<_>>(),
            |acc, map| {
                acc.intersection(&map.keys().copied().collect())
                    .copied()
                    .collect()
            },
        );
        let mut candidate_plans = Vec::new();
        for stop in candidates.difference(&region) {
            let mut emitter = MultiExitEmitter {
                graph,
                header,
                exit: *stop,
                members: BTreeSet::new(),
                visited: BTreeSet::new(),
                saw_continue: false,
                saw_break: false,
                fuel: 4096,
            };
            let Some(body) = emitter.state(header, true) else {
                continue;
            };
            if !emitter.saw_continue || !emitter.saw_break {
                continue;
            }
            let occupied = loops
                .values()
                .flat_map(|plan| plan.members.iter().copied())
                .collect::<BTreeSet<_>>();
            if !emitter.members.is_disjoint(&occupied) {
                continue;
            }
            let unique_entry = nodes.difference(&emitter.members).all(|&outside| {
                collapsed_edges(outside, graph, loops)
                    .iter()
                    .all(|target| *target == header || !emitter.members.contains(target))
            });
            if unique_entry {
                candidate_plans.push(Loop {
                    members: emitter.members,
                    exit: *stop,
                    body: LoopBody::MultiExit { body },
                });
            }
        }
        candidate_plans.sort_by_key(|plan| (plan.members.len(), plan.exit));
        if let Some(plan) = candidate_plans.into_iter().next() {
            loops.insert(header, plan);
        }
    }
}

fn reachable_collapsed(
    start: u64,
    exit: u64,
    graph: &BTreeMap<u64, Route>,
    loops: &BTreeMap<u64, Loop>,
) -> BTreeMap<u64, usize> {
    let mut done = BTreeMap::new();
    let mut queue = VecDeque::from([(start, 0)]);
    while let Some((current, distance)) = queue.pop_front() {
        if done.contains_key(&current) {
            continue;
        }
        done.insert(current, distance);
        if current == exit {
            continue;
        }
        if let Some(loop_plan) = loops.get(&current) {
            queue.push_back((loop_plan.exit, distance + 1));
        } else if let Some(route) = graph.get(&current) {
            let mut targets = Vec::new();
            route.targets(&mut targets);
            for next in targets {
                queue.push_back((next, distance + 1));
            }
        }
    }
    done
}

/// The merge must postdominate BOTH arms; sharing a merely reachable node
/// would silently drop code on a bypassing path.
fn all_paths_reach(
    current: u64,
    join: u64,
    exit: u64,
    graph: &BTreeMap<u64, Route>,
    loops: &BTreeMap<u64, Loop>,
    visited: &mut BTreeSet<u64>,
) -> bool {
    if current == join {
        return true;
    }
    if current == exit || !visited.insert(current) {
        return false;
    }
    let result = if let Some(loop_plan) = loops.get(&current) {
        all_paths_reach(loop_plan.exit, join, exit, graph, loops, visited)
    } else if let Some(route) = graph.get(&current) {
        let mut targets = Vec::new();
        route.targets(&mut targets);
        !targets.is_empty()
            && targets
                .into_iter()
                .all(|target| all_paths_reach(target, join, exit, graph, loops, visited))
    } else {
        false
    };
    visited.remove(&current);
    result
}

fn branch_join(
    yes: u64,
    no: u64,
    exit: u64,
    graph: &BTreeMap<u64, Route>,
    loops: &BTreeMap<u64, Loop>,
) -> Option<u64> {
    let a = reachable_collapsed(yes, exit, graph, loops);
    let b = reachable_collapsed(no, exit, graph, loops);
    a.iter()
        .filter_map(|(&state, &distance)| {
            let other = *b.get(&state)?;
            if !all_paths_reach(yes, state, exit, graph, loops, &mut BTreeSet::new())
                || !all_paths_reach(no, state, exit, graph, loops, &mut BTreeSet::new())
            {
                return None;
            }
            Some((distance.max(other), distance + other, state))
        })
        .min()
        .map(|(_, _, state)| state)
}

struct Emitter<'a> {
    graph: &'a BTreeMap<u64, Route>,
    loops: &'a BTreeMap<u64, Loop>,
    exit: u64,
    visited: BTreeSet<u64>,
    fuel: usize,
}

impl Emitter<'_> {
    fn spend(&mut self) -> Option<()> {
        self.fuel = self.fuel.checked_sub(1)?;
        Some(())
    }

    fn lines(&mut self, route: &Route, stop: u64) -> Option<String> {
        self.spend()?;
        let mut text = route.effects.join("\n");
        match &route.next {
            Next::State(next) => {
                text.push_str(&self.walk(*next, stop)?);
            }
            Next::Choose { condition, yes, no } => {
                let left = yes.plain_target()?;
                let right = no.plain_target()?;
                let join = branch_join(left, right, self.exit, self.graph, self.loops)?;
                let yes_text = self.lines(yes, join)?;
                let no_text = self.lines(no, join)?;
                text.push_str(&format!(
                    "\nif ({condition}) {{\n{yes_text}\n}} else {{\n{no_text}\n}}"
                ));
                text.push_str(&self.walk(join, stop)?);
            }
        }
        Some(text)
    }

    fn walk(&mut self, start: u64, stop: u64) -> Option<String> {
        self.spend()?;
        let mut cursor = start;
        let mut out = String::new();
        while cursor != stop && cursor != self.exit {
            self.spend()?;
            if !self.visited.insert(cursor) {
                return None;
            }
            if let Some(loop_plan) = self.loops.get(&cursor) {
                // Render the loop body as its own region. Natural loops
                // may contain internal conditionals and previously collapsed
                // nested loops; both return to the header on every path.
                match &loop_plan.body {
                    LoopBody::MultiExit { body } => {
                        out.push_str(&format!("\nfor (;;) {{\n{body}\n}}\n"));
                    }
                    LoopBody::Natural {
                        condition,
                        enters_on_true,
                        entering,
                        exiting,
                        header_effects,
                        body_start,
                    } => {
                        let mut body = entering.effects.join("\n");
                        let mut region = Emitter {
                            graph: self.graph,
                            loops: self.loops,
                            exit: self.exit,
                            visited: BTreeSet::new(),
                            fuel: self.fuel,
                        };
                        body.push_str(&region.walk(*body_start, cursor)?);
                        self.fuel = region.fuel;
                        let cond = if *enters_on_true {
                            condition.clone()
                        } else {
                            format!("!({condition})")
                        };
                        if header_effects.is_empty() {
                            out.push_str(&format!("\nwhile ({cond}) {{\n{body}\n}}\n"));
                            out.push_str(&exiting.effects.join("\n"));
                        } else {
                            out.push_str("\nfor (;;) {\n");
                            out.push_str(&header_effects.join("\n"));
                            out.push_str(&format!(
                                "\nif (!({cond})) {{\n{}\nbreak;\n}}\n{body}\n}}\n",
                                exiting.effects.join("\n")
                            ));
                        }
                    }
                }
                cursor = loop_plan.exit;
            } else {
                let route = self.graph.get(&cursor)?;
                let mut targets = Vec::new();
                route.targets(&mut targets);
                out.push('\n');
                out.push_str(&route.effects.join("\n"));
                match &route.next {
                    Next::State(next) => cursor = *next,
                    Next::Choose { condition, yes, no } => {
                        let left = yes.plain_target()?;
                        let right = no.plain_target()?;
                        let join = branch_join(left, right, self.exit, self.graph, self.loops)?;
                        let yes_text = self.lines(yes, join)?;
                        let no_text = self.lines(no, join)?;
                        out.push_str(&format!(
                            "\nif ({condition}) {{\n{yes_text}\n}} else {{\n{no_text}\n}}"
                        ));
                        cursor = join;
                    }
                }
            }
        }
        Some(out)
    }
}

/// Turn a reducible numeric-state for/ternary dispatcher into ordinary JavaScript
/// statement sequencing and while/if control flow, retaining assignment effects.
pub(crate) fn reconstruct_for(it: &ForStatement<'_>, source: &str) -> Option<String> {
    if it.update.is_some() {
        return None;
    }
    let init = it.init.as_ref()?;
    let (state, initial) = match init {
        ForStatementInit::AssignmentExpression(assign) if assign.operator.as_str() == "=" => (
            direct_assignment_name(&assign.left)?,
            number(&assign.right)?,
        ),
        ForStatementInit::VariableDeclaration(decl)
            if decl.kind == VariableDeclarationKind::Var && decl.declarations.len() == 1 =>
        {
            let item = &decl.declarations[0];
            let BindingPattern::BindingIdentifier(id) = &item.id else {
                return None;
            };
            (id.name.as_str(), number(item.init.as_ref()?)?)
        }
        _ => return None,
    };
    let init_text = format!("{};", fragment(source, init.span()));
    reconstruct_state_loop(
        state,
        initial,
        it.test.as_ref()?,
        &it.body,
        &init_text,
        source,
    )
}

/// Resolve a simple numeric initializer to its exact lexical binding.
pub(crate) fn state_initializer<'a>(
    stmt: &'a Statement<'a>,
    scoping: &Scoping,
) -> Option<(SymbolId, &'a str, u64)> {
    match stmt {
        Statement::ExpressionStatement(expression) => {
            let Expression::AssignmentExpression(assignment) = &expression.expression else {
                return None;
            };
            if assignment.operator.as_str() != "=" {
                return None;
            }
            let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(id) = &assignment.left
            else {
                return None;
            };
            let ref_id = id.reference_id.get()?;
            let symbol = crate::statically_resolved_symbol(scoping, ref_id)?;
            Some((symbol, id.name.as_str(), number(&assignment.right)?))
        }
        Statement::VariableDeclaration(declaration) if declaration.declarations.len() == 1 => {
            let item = &declaration.declarations[0];
            let BindingPattern::BindingIdentifier(binding) = &item.id else {
                return None;
            };
            Some((
                binding.symbol_id.get()?,
                binding.name.as_str(),
                number(item.init.as_ref()?)?,
            ))
        }
        _ => None,
    }
}

/// Match the loop's tested state to the same semantic symbol as its initializer.
pub(crate) fn while_state_binding<'a>(
    it: &'a WhileStatement<'a>,
    scoping: &Scoping,
) -> Option<(SymbolId, &'a str)> {
    let Expression::BinaryExpression(binary) = unparen(&it.test) else {
        return None;
    };
    if !matches!(binary.operator.as_str(), "!=" | "!==") {
        return None;
    }
    let id = match (unparen(&binary.left), unparen(&binary.right)) {
        (Expression::Identifier(id), other) if number(other).is_some() => id,
        (other, Expression::Identifier(id)) if number(other).is_some() => id,
        _ => return None,
    };
    Some((
        crate::statically_resolved_symbol(scoping, id.reference_id.get()?)?,
        id.name.as_str(),
    ))
}

/// The original initializer stays where it was. The intervening statements
/// also stay in execution order, and only the while statement is rewritten.
pub(crate) fn reconstruct_while_with_known_state(
    it: &WhileStatement<'_>,
    state: &str,
    initial: u64,
    source: &str,
) -> Option<String> {
    reconstruct_state_loop(state, initial, &it.test, &it.body, "", source)
}

/// Track every write to the dispatcher's original lexical state symbol,
/// including nested expressions and catch handlers. A nonnumeric assignment,
/// update, dynamic evaluation, or nested shadowing invalidates a closed
/// reachable-state proof; none of those may introduce unknown dispatch cases.
struct ExceptionStateWrites<'s> {
    symbol: SymbolId,
    state_name: &'s str,
    scoping: &'s Scoping,
    source: &'s str,
    targets: BTreeSet<u64>,
    unsafe_write: bool,
}

impl<'a> Visit<'a> for ExceptionStateWrites<'_> {
    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        if id.name == self.state_name
            && id
                .reference_id
                .get()
                .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
                != Some(self.symbol)
        {
            self.unsafe_write = true;
        }
    }

    fn visit_assignment_expression(&mut self, assignment: &AssignmentExpression<'a>) {
        if let AssignmentTarget::AssignmentTargetIdentifier(id) = &assignment.left {
            if id.name == self.state_name {
                if assignment.operator.as_str() != "=" {
                    self.unsafe_write = true;
                } else if let Some(route) =
                    parse_target(&assignment.right, self.state_name, self.source)
                {
                    let mut targets = Vec::new();
                    route.targets(&mut targets);
                    self.targets.extend(targets);
                } else {
                    self.unsafe_write = true;
                }
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_update_expression(&mut self, update: &UpdateExpression<'a>) {
        if update.argument.get_identifier_name() == Some(self.state_name) {
            self.unsafe_write = true;
        }
        walk::walk_update_expression(self, update);
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if matches!(unparen(&call.callee), Expression::Identifier(id) if id.name=="eval") {
            self.unsafe_write = true;
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_with_statement(&mut self, stmt: &WithStatement<'a>) {
        self.unsafe_write = true;
        walk::walk_with_statement(self, stmt);
    }
}

/// The surrounding loop condition is evaluated *before every dispatch*.
/// Proving state transitions inside the try is insufficient if that condition
/// can itself write the state or invoke a getter/function which does so.
struct ExceptionLoopEffectContext<'s> {
    scoping: &'s Scoping,
}

impl<'a> GlobalContext<'a> for ExceptionLoopEffectContext<'_> {
    fn is_global_reference(&self, id: &IdentifierReference<'a>) -> bool {
        id.reference_id
            .get()
            .is_none_or(|reference| self.scoping.get_reference(reference).symbol_id().is_none())
    }
}

impl<'a> MayHaveSideEffectsContext<'a> for ExceptionLoopEffectContext<'_> {
    fn annotations(&self) -> bool {
        false
    }
    fn manual_pure_functions(&self, _callee: &Expression<'_>) -> bool {
        false
    }
    fn property_read_side_effects(&self) -> PropertyReadSideEffects {
        PropertyReadSideEffects::All
    }
    fn unknown_global_side_effects(&self) -> bool {
        true
    }
}

/// A numeric-state dispatch branch that only assigns a proven inert primitive
/// result to the lexical state binding. A single-statement block has the same
/// effects, but sequences, calls and destructuring are not silent transitions.
fn inert_exception_transition(statement: &Statement<'_>, state: &str) -> Option<u64> {
    let statement = match statement {
        Statement::BlockStatement(block) if block.body.len() == 1 => &block.body[0],
        other => other,
    };
    let Statement::ExpressionStatement(expr) = statement else {
        return None;
    };
    let Expression::AssignmentExpression(assign) = &expr.expression else {
        return None;
    };
    if assign.operator.as_str() != "=" || direct_assignment_name(&assign.left) != Some(state) {
        return None;
    }
    if !inert_literal_value(&assign.right) {
        return None;
    }
    // Strictly numeric state targets: coercing Boolean or null to numbers
    // would invent a different value under strict-equality dispatch tests.
    let crate::value_eval::Value::Number(value) = eval(&assign.right)? else {
        return None;
    };
    exact_u64(value)
}

/// Follow only finite silent transitions: an all-silent cycle must remain a
/// loop, not be turned into a direct assignment to one of its nodes.
fn resolve_inert_exception_chain(start: u64, silent: &BTreeMap<u64, u64>) -> Option<u64> {
    let mut seen = BTreeSet::new();
    let mut current = start;
    while let Some(&next) = silent.get(&current) {
        if !seen.insert(current) {
            return None;
        }
        current = next;
    }
    Some(current)
}

/// One AST terminal assignment that can be retargeted from a silent state.
/// The emitted source and graph edge must change together.
#[derive(Clone)]
struct TerminalStateEdit {
    span: oxc_span::Span,
    from: u64,
    to: u64,
}

fn terminal_rhs_edits(
    expr: &Expression<'_>,
    silent: &BTreeMap<u64, u64>,
    edits: &mut Vec<TerminalStateEdit>,
) {
    match unparen(expr) {
        Expression::ConditionalExpression(branch) => {
            terminal_rhs_edits(&branch.consequent, silent, edits);
            terminal_rhs_edits(&branch.alternate, silent, edits);
        }
        Expression::SequenceExpression(sequence) => {
            if let Some(last) = sequence.expressions.last() {
                terminal_rhs_edits(last, silent, edits);
            }
        }
        value if inert_literal_value(value) => {
            if let Some(crate::value_eval::Value::Number(number)) = eval(value) {
                if let Some(from) = exact_u64(number) {
                    if let Some(to) = resolve_inert_exception_chain(from, silent) {
                        if from != to {
                            edits.push(TerminalStateEdit {
                                span: value.span(),
                                from,
                                to,
                            });
                        }
                    }
                }
            }
        }
        _ => {}
    }
}

fn terminal_assignment_edits(
    expr: &Expression<'_>,
    state: &str,
    silent: &BTreeMap<u64, u64>,
    edits: &mut Vec<TerminalStateEdit>,
) {
    match unparen(expr) {
        Expression::AssignmentExpression(assign)
            if assign.operator.as_str() == "="
                && direct_assignment_name(&assign.left) == Some(state) =>
        {
            terminal_rhs_edits(&assign.right, silent, edits);
        }
        Expression::SequenceExpression(sequence) => {
            if let Some(last) = sequence.expressions.last() {
                terminal_assignment_edits(last, state, silent, edits);
            }
        }
        Expression::ConditionalExpression(branch) => {
            terminal_assignment_edits(&branch.consequent, state, silent, edits);
            terminal_assignment_edits(&branch.alternate, state, silent, edits);
        }
        _ => {}
    }
}

/// Follow only terminal statement shapes supported by the route parser.
/// Prefix statements retain all their existing effects and state writes.
fn terminal_statement_edits(
    statement: &Statement<'_>,
    state: &str,
    silent: &BTreeMap<u64, u64>,
    edits: &mut Vec<TerminalStateEdit>,
) {
    match statement {
        Statement::ExpressionStatement(expr) => {
            terminal_assignment_edits(&expr.expression, state, silent, edits);
        }
        Statement::BlockStatement(block) => {
            if let Some(last) = block.body.last() {
                terminal_statement_edits(last, state, silent, edits);
            }
        }
        Statement::IfStatement(branch) => {
            terminal_statement_edits(&branch.consequent, state, silent, edits);
            if let Some(alternate) = &branch.alternate {
                terminal_statement_edits(alternate, state, silent, edits);
            }
        }
        _ => {}
    }
}

fn rewrite_route_targets(route: &mut Route, redirect: &BTreeMap<u64, u64>) {
    fn rewrite(next: &mut Next, redirect: &BTreeMap<u64, u64>) {
        match next {
            Next::State(target) => {
                if let Some(destination) = redirect.get(target) {
                    *target = *destination;
                }
            }
            Next::Choose { yes, no, .. } => {
                rewrite(&mut yes.next, redirect);
                rewrite(&mut no.next, redirect);
            }
        }
    }
    rewrite(&mut route.next, redirect);
}

/// Each rewritten source terminal must correspond to exactly one modelled
/// CFG edge. Unmodelled or differently parsed forms stay unchanged.
fn verified_terminal_edits(
    statement: &Statement<'_>,
    state: &str,
    silent: &BTreeMap<u64, u64>,
    route: &mut Route,
) -> Vec<TerminalStateEdit> {
    let mut edits = Vec::new();
    terminal_statement_edits(statement, state, silent, &mut edits);
    let mut edge_targets = Vec::new();
    route.targets(&mut edge_targets);
    let mut edge_counts = BTreeMap::new();
    for target in edge_targets {
        *edge_counts.entry(target).or_insert(0_usize) += 1;
    }
    let mut edit_counts = BTreeMap::new();
    for edit in &edits {
        *edit_counts.entry(edit.from).or_insert(0_usize) += 1;
    }
    let redirect = edits
        .iter()
        .filter(|edit| edit_counts.get(&edit.from) == edge_counts.get(&edit.from))
        .map(|edit| (edit.from, edit.to))
        .collect::<BTreeMap<_, _>>();
    edits.retain(|edit| redirect.contains_key(&edit.from));
    if !redirect.is_empty() {
        rewrite_route_targets(route, &redirect);
    }
    edits
}

fn print_terminal_edits(
    statement: &Statement<'_>,
    source: &str,
    edits: &[TerminalStateEdit],
) -> Option<String> {
    let span = statement.span();
    let mut text = fragment(source, span).to_owned();
    let mut ordered = edits.to_vec();
    ordered.sort_by_key(|edit| std::cmp::Reverse(edit.span.start));
    for edit in ordered {
        let start = usize::try_from(edit.span.start.checked_sub(span.start)?).ok()?;
        let end = usize::try_from(edit.span.end.checked_sub(span.start)?).ok()?;
        if start > end || !text.is_char_boundary(start) || !text.is_char_boundary(end) {
            return None;
        }
        text.replace_range(start..end, &edit.to.to_string());
    }
    Some(text)
}

/// Count all concrete finite successor targets of a modeled route. A
/// convergent predecessor may contain effects and conditional arms, as long
/// as every successful path reaches the same numeric state.
fn single_numeric_destination(route: &Route) -> Option<u64> {
    let mut targets = Vec::new();
    route.targets(&mut targets);
    let target = *targets.first()?;
    targets
        .iter()
        .all(|candidate| *candidate == target)
        .then_some(target)
}

/// Splice the successor route into every matching conditional arm while
/// retaining the original prefix effects and branch conditions. This keeps
/// the modeled graph faithful to the emitted straight-line source region.
fn splice_unique_successor(route: &mut Route, target: u64, successor: &Route) -> bool {
    match &mut route.next {
        Next::State(state) if *state == target => {
            route.effects.extend(successor.effects.iter().cloned());
            route.next = successor.next.clone();
            true
        }
        Next::Choose { yes, no, .. } => {
            let yes_changed = splice_unique_successor(yes, target, successor);
            let no_changed = splice_unique_successor(no, target, successor);
            yes_changed && no_changed
        }
        Next::State(_) => false,
    }
}

/// Merge a state with its sole entering predecessor, without cloning its body.
///
/// All successful predecessor CFG arms must reach the same state, which
/// must have exactly one distinct incoming source case and no
/// independent initializer/catch entry. The original target statement runs
/// inside the same try block after the assignment, so a thrown exception
/// observes the same state as in the original next iteration.
///
/// A new wrapper block contains two *sibling* source statements. Neither the
/// predecessor nor the wrapper creates lexical bindings, and the target's
/// existing block (if any) retains its own lexical scope.
struct ExceptionEntryProof<'a> {
    roots: &'a BTreeSet<u64>,
    reachable: &'a BTreeSet<u64>,
    excluded: &'a BTreeSet<u64>,
}

fn single_entry_exception_regions(
    dispatcher: &Statement<'_>,
    state: &str,
    entry: ExceptionEntryProof<'_>,
    cases: &mut BTreeMap<u64, Option<Route>>,
    edits: &BTreeMap<u64, Vec<TerminalStateEdit>>,
    effects: &ExceptionLoopEffectContext<'_>,
    source: &str,
) -> Option<(BTreeMap<u64, String>, BTreeSet<u64>)> {
    let mut statements = BTreeMap::new();
    let mut cursor = dispatcher;
    loop {
        let Statement::IfStatement(branch) = cursor else {
            return None;
        };
        if branch.test.may_have_side_effects(effects) {
            return None;
        }
        let label = state_test(&branch.test, state)?;
        statements.insert(label, &branch.consequent);
        match branch.alternate.as_ref() {
            Some(other @ Statement::IfStatement(_)) => cursor = other,
            None => break,
            Some(_) => return None,
        }
    }

    // Count distinct source cases, not duplicate conditional arms from
    // the same case. Multiple arms may safely converge to one successor.
    let mut incoming = BTreeMap::<u64, BTreeSet<u64>>::new();
    for &label in entry.reachable {
        let mut targets = Vec::new();
        cases.get(&label)?.as_ref()?.targets(&mut targets);
        for target in targets {
            incoming.entry(target).or_default().insert(label);
        }
    }

    let mut combined = BTreeMap::new();
    let mut absorbed = BTreeSet::new();
    let mut occupied = BTreeSet::new();
    for &predecessor in entry.reachable {
        if occupied.contains(&predecessor) || entry.excluded.contains(&predecessor) {
            continue;
        }
        let Some(&body) = statements.get(&predecessor) else {
            continue;
        };
        let Some(target) = cases
            .get(&predecessor)?
            .as_ref()
            .and_then(single_numeric_destination)
        else {
            continue;
        };
        if target == predecessor
            || !entry.reachable.contains(&target)
            || entry.roots.contains(&target)
            || occupied.contains(&target)
            || entry.excluded.contains(&target)
            || edits.contains_key(&predecessor)
        {
            continue;
        }
        if incoming
            .get(&target)
            .is_none_or(|sources| sources.len() != 1 || !sources.contains(&predecessor))
        {
            continue;
        }
        let Some(&successor) = statements.get(&target) else {
            continue;
        };
        // Both cases must have modeled routes. The original source bodies
        // are preserved in their existing lexical blocks without cloning.
        let Some(successor_route) = cases.get(&target)?.as_ref().cloned() else {
            continue;
        };
        let first = fragment(source, body.span());
        let second = match edits.get(&target) {
            Some(replacements) => print_terminal_edits(successor, source, replacements)?,
            None => fragment(source, successor.span()).to_owned(),
        };
        if !splice_unique_successor(
            cases.get_mut(&predecessor)?.as_mut()?,
            target,
            &successor_route,
        ) {
            return None;
        }
        combined.insert(predecessor, format!("{{ {first};\n{second} }}"));
        absorbed.insert(target);
        occupied.insert(predecessor);
        occupied.insert(target);
    }
    Some((combined, absorbed))
}

/// Recover a single-entry, single-join conditional region without cloning
/// either branch or its shared continuation. This handles both full diamonds
/// (entry -> left/right -> join) and triangles (entry -> side/join -> join).
///
/// The proof is over *source-case* predecessors, not raw conditional edges.
/// Independent catch/initializer entries and competing incoming edges are
/// rejected. A join may loop back to the entry in a later iteration, but no
/// side or join may be entered from outside the proven region. All original
/// source statements remain inside the same try block and keep their numeric
/// state writes, so throwing effects retain their catch-visible state.
fn exception_diamond_regions(
    dispatcher: &Statement<'_>,
    state: &str,
    entry: ExceptionEntryProof<'_>,
    cases: &mut BTreeMap<u64, Option<Route>>,
    edits: &BTreeMap<u64, Vec<TerminalStateEdit>>,
    effects: &ExceptionLoopEffectContext<'_>,
    source: &str,
) -> Option<(BTreeMap<u64, String>, BTreeSet<u64>)> {
    let mut statements = BTreeMap::new();
    let mut tests = BTreeMap::new();
    let mut cursor = dispatcher;
    loop {
        let Statement::IfStatement(branch) = cursor else {
            return None;
        };
        if branch.test.may_have_side_effects(effects) {
            return None;
        }
        let label = state_test(&branch.test, state)?;
        statements.insert(label, &branch.consequent);
        tests.insert(label, fragment(source, branch.test.span()));
        match branch.alternate.as_ref() {
            Some(other @ Statement::IfStatement(_)) => cursor = other,
            None => break,
            Some(_) => return None,
        }
    }

    let mut incoming = BTreeMap::<u64, BTreeSet<u64>>::new();
    for &label in entry.reachable {
        let Some(Some(route)) = cases.get(&label) else {
            return None;
        };
        let mut targets = Vec::new();
        route.targets(&mut targets);
        for target in targets {
            incoming.entry(target).or_default().insert(label);
        }
    }

    let text_of = |label: u64| -> Option<String> {
        let statement = *statements.get(&label)?;
        match edits.get(&label) {
            Some(changes) => print_terminal_edits(statement, source, changes),
            None => Some(fragment(source, statement.span()).to_owned()),
        }
    };

    for &predecessor in entry.reachable {
        let Some(Some(route)) = cases.get(&predecessor) else {
            continue;
        };
        let Next::Choose { yes, no, .. } = &route.next else {
            continue;
        };
        let (Some(left), Some(right)) = (yes.plain_target(), no.plain_target()) else {
            continue;
        };
        if left == right {
            continue;
        }

        let mut left_targets = BTreeSet::from([left]);
        let mut right_targets = BTreeSet::from([right]);
        if let Some(target) = cases
            .get(&left)
            .and_then(Option::as_ref)
            .and_then(single_numeric_destination)
        {
            left_targets.insert(target);
        }
        if let Some(target) = cases
            .get(&right)
            .and_then(Option::as_ref)
            .and_then(single_numeric_destination)
        {
            right_targets.insert(target);
        }

        for &join in left_targets.intersection(&right_targets) {
            if join == predecessor
                || !entry.reachable.contains(&join)
                || entry.roots.contains(&join)
            {
                continue;
            }
            let mut indirect = Vec::new();
            let mut expected_join_inputs = BTreeSet::new();
            let mut valid = true;
            for branch in [left, right] {
                if branch == join {
                    expected_join_inputs.insert(predecessor);
                    continue;
                }
                let valid_branch = branch != predecessor
                    && entry.reachable.contains(&branch)
                    && !entry.roots.contains(&branch)
                    && incoming.get(&branch).is_some_and(|sources| {
                        sources.len() == 1 && sources.contains(&predecessor)
                    })
                    && cases
                        .get(&branch)
                        .and_then(Option::as_ref)
                        .and_then(single_numeric_destination)
                        == Some(join);
                if !valid_branch {
                    valid = false;
                    break;
                }
                indirect.push(branch);
                expected_join_inputs.insert(branch);
            }
            if !valid
                || incoming.get(&join) != Some(&expected_join_inputs)
                || cases.get(&join).and_then(Option::as_ref).is_none()
            {
                continue;
            }

            let mut composed = route.clone();
            let Some(Some(join_route)) = cases.get(&join).cloned() else {
                continue;
            };
            let Next::Choose { yes, no, .. } = &mut composed.next else {
                continue;
            };
            for (side, target) in [(yes, left), (no, right)] {
                if target != join {
                    let Some(Some(branch_route)) = cases.get(&target).cloned() else {
                        valid = false;
                        break;
                    };
                    valid &= splice_unique_successor(side, target, &branch_route);
                }
            }
            if !valid || !splice_unique_successor(&mut composed, join, &join_route) {
                continue;
            }

            // Keep exact source statements, including all conditional effects,
            // lexical blocks, return/throw statements and original assignments.
            let first = text_of(predecessor)?;
            let last = text_of(join)?;
            let branching = if indirect.len() == 2 {
                let a = indirect[0];
                let b = indirect[1];
                format!(
                    "if ({}) {{ {}; }} else {{ {}; }}",
                    tests.get(&a)?,
                    text_of(a)?,
                    text_of(b)?,
                )
            } else {
                let target = *indirect.first()?;
                format!("if ({}) {{ {}; }}", tests.get(&target)?, text_of(target)?)
            };
            let region = format!("{{ {first};\n{branching}\n{last}; }}");
            *cases.get_mut(&predecessor)?.as_mut()? = composed;
            indirect.push(join);
            return Some((
                BTreeMap::from([(predecessor, region)]),
                indirect.into_iter().collect(),
            ));
        }
    }

    Some((BTreeMap::new(), BTreeSet::new()))
}

/// Return values that cannot throw or execute user code. Reading a resolved
/// function-scoped binding is safe even before assignment (it yields
/// undefined), unlike a block-scoped binding with a temporal dead zone.
fn nonthrowing_return(
    statement: &Statement<'_>,
    scoping: &Scoping,
    source: &str,
) -> Option<(String, Option<SymbolId>)> {
    let statement = match statement {
        Statement::BlockStatement(block) if block.body.len() == 1 => &block.body[0],
        other => other,
    };
    let Statement::ReturnStatement(ret) = statement else {
        return None;
    };
    let binding = match ret.argument.as_ref().map(unparen) {
        Some(Expression::Identifier(id)) => {
            let symbol = id
                .reference_id
                .get()
                .and_then(|r| scoping.get_reference(r).symbol_id())?;
            if !scoping
                .symbol_flags(symbol)
                .is_function_scoped_declaration()
                || scoping.symbol_scope_id(symbol) == scoping.root_scope_id()
            {
                return None;
            }
            Some(symbol)
        }
        Some(expr)
            if inert_literal_value(expr) || matches!(expr, Expression::ThisExpression(_)) =>
        {
            None
        }
        None => None,
        _ => return None,
    };
    Some((fragment(source, statement.span()).to_owned(), binding))
}

/// Preserve exception-handling scope and the original one-state-per-iteration
/// execution order. Only remove state comparisons proven unreachable from
/// both the lexical initializer and every statically possible catch recovery.
///
/// This deliberately leaves the try/catch in place: combining states into a
/// single iteration could alter catch-visible intermediate state or a loop
/// condition's evaluation count.
pub(crate) fn prune_exception_dispatcher(
    loop_stmt: &WhileStatement<'_>,
    state: &str,
    initial: u64,
    symbol: SymbolId,
    scoping: &Scoping,
    source: &str,
) -> Option<String> {
    let effects = ExceptionLoopEffectContext { scoping };
    if loop_stmt.test.may_have_side_effects(&effects) {
        return None;
    }
    let Statement::TryStatement(protected) = &loop_stmt.body else {
        return None;
    };
    if protected.finalizer.is_some() || protected.block.body.len() != 1 {
        return None;
    }
    let handler = protected.handler.as_ref()?;
    let dispatcher = &protected.block.body[0];

    let mut writes = ExceptionStateWrites {
        symbol,
        state_name: state,
        scoping,
        source,
        targets: BTreeSet::new(),
        unsafe_write: false,
    };
    writes.visit_statement(dispatcher);
    if writes.unsafe_write {
        return None;
    }
    // Do not seed the reachability graph with states written *inside* the
    // normal dispatcher: those are transitions, not independent entries.
    // Only the catch handler can resume a failed iteration from a new state.
    writes.targets.clear();
    writes.visit_block_statement(&handler.body);
    if writes.unsafe_write {
        return None;
    }

    let exit = u64::MAX;
    if writes.targets.contains(&exit) {
        return None;
    }
    let mut cases = BTreeMap::new();
    collect_dispatch_statement(dispatcher, state, exit, source, &mut cases)?;
    if cases.contains_key(&exit) {
        return None;
    }

    // Skipping an iteration is only valid if its loop predicate is pure and
    // invariably true. Keep all catch-root entries, and never collapse a
    // self-loop or cyclic chain of effect-free state assignments.
    let mut retargeted = BTreeMap::new();
    let mut terminal_returns = BTreeMap::new();
    if known_bool(&loop_stmt.test) == Some(true) {
        let mut silent = BTreeMap::new();
        let mut cursor = dispatcher;
        loop {
            let Statement::IfStatement(branch) = cursor else {
                return None;
            };
            let label = state_test(&branch.test, state)?;
            if let Some(target) = inert_exception_transition(&branch.consequent, state) {
                silent.insert(label, target);
            }
            if let Some(completion) = nonthrowing_return(&branch.consequent, scoping, source) {
                terminal_returns.insert(label, completion);
            }
            match branch.alternate.as_ref() {
                Some(other @ Statement::IfStatement(_)) => cursor = other,
                None => break,
                Some(_) => return None,
            }
        }
        // Retarget terminal numeric assignments in any supported branch, not
        // only in already-silent branches. Prefix effects and conditions
        // remain in their original positions; the CFG and text edits agree.
        let mut cursor = dispatcher;
        loop {
            let Statement::IfStatement(branch) = cursor else {
                return None;
            };
            let label = state_test(&branch.test, state)?;
            if let Some(Some(route)) = cases.get_mut(&label) {
                let edits = verified_terminal_edits(&branch.consequent, state, &silent, route);
                if !edits.is_empty() {
                    retargeted.insert(label, edits);
                }
            }
            match branch.alternate.as_ref() {
                Some(other @ Statement::IfStatement(_)) => cursor = other,
                None => break,
                Some(_) => return None,
            }
        }
    }

    // The outer catch can retry at the state it intercepted, *or* resume
    // from any numeric state it assigns. Treat each catch target as a root;
    // rejecting unknown reachable transitions prevents false dead cases.
    let mut roots = writes.targets;
    roots.insert(initial);
    let mut reachable = BTreeSet::new();
    let mut work = VecDeque::from_iter(roots.iter().copied());
    while let Some(current) = work.pop_front() {
        if current == exit || !reachable.insert(current) {
            continue;
        }
        let route = cases.get(&current)?.as_ref()?;
        let mut next = Vec::new();
        route.targets(&mut next);
        work.extend(next);
    }

    // Recover one conditional diamond, then recover independent linear
    // regions against the UPDATED CFG. Protect the diamond's entry and
    // absorbed states so a second rewrite cannot discard its source body.
    // This preserves disjoint straight-line improvements in the same pass.
    let (combined_regions, absorbed_regions) = if known_bool(&loop_stmt.test) == Some(true) {
        let empty = BTreeSet::new();
        let (mut combined, mut absorbed) = exception_diamond_regions(
            dispatcher,
            state,
            ExceptionEntryProof {
                roots: &roots,
                reachable: &reachable,
                excluded: &empty,
            },
            &mut cases,
            &retargeted,
            &effects,
            source,
        )?;
        let mut after_diamond = reachable.clone();
        if !absorbed.is_empty() {
            after_diamond.clear();
            let mut work = VecDeque::from_iter(roots.iter().copied());
            while let Some(current) = work.pop_front() {
                if current == exit || !after_diamond.insert(current) {
                    continue;
                }
                let route = cases.get(&current)?.as_ref()?;
                let mut next = Vec::new();
                route.targets(&mut next);
                work.extend(next);
            }
        }
        let mut excluded = absorbed.clone();
        excluded.extend(combined.keys().copied());
        let (linear, linear_absorbed) = single_entry_exception_regions(
            dispatcher,
            state,
            ExceptionEntryProof {
                roots: &roots,
                reachable: &after_diamond,
                excluded: &excluded,
            },
            &mut cases,
            &retargeted,
            &effects,
            source,
        )?;
        combined.extend(linear);
        absorbed.extend(linear_absorbed);
        (combined, absorbed)
    } else {
        (BTreeMap::new(), BTreeSet::new())
    };
    if !absorbed_regions.is_empty() {
        reachable.clear();
        let mut work = VecDeque::from_iter(roots.iter().copied());
        while let Some(current) = work.pop_front() {
            if current == exit || !reachable.insert(current) {
                continue;
            }
            let route = cases.get(&current)?.as_ref()?;
            let mut next = Vec::new();
            route.targets(&mut next);
            work.extend(next);
        }
    }

    // Extract a single common return sink rather than duplicating it in
    // predecessor states. Each incoming state assignment remains observable
    // in its original source position. Only the proven inert loop predicate
    // and pure numeric dispatch comparisons are advanced across the return.
    let mut completion_tail = Vec::new();
    if known_bool(&loop_stmt.test) == Some(true) {
        let mut cursor = dispatcher;
        loop {
            let Statement::IfStatement(branch) = cursor else {
                return None;
            };
            let label = state_test(&branch.test, state)?;
            if branch.test.may_have_side_effects(&effects) {
                return None;
            }
            if reachable.contains(&label) {
                if let Some((completion, binding)) = terminal_returns.get(&label) {
                    // This tail is emitted in the original try block, beside
                    // the dispatch statement. A return identifier must bind
                    // to precisely the same symbol in that enclosing scope.
                    let Expression::BinaryExpression(test) = unparen(&branch.test) else {
                        return None;
                    };
                    let state_id = [unparen(&test.left), unparen(&test.right)]
                        .into_iter()
                        .find_map(|side| match side {
                            Expression::Identifier(id) if id.name == state => Some(id),
                            _ => None,
                        })?;
                    let scope = scoping
                        .get_reference(state_id.reference_id.get()?)
                        .scope_id();
                    if binding.is_none_or(|symbol| {
                        scoping.find_binding(scope, scoping.symbol_name(symbol).into())
                            == Some(symbol)
                    }) {
                        completion_tail.push((
                            label,
                            fragment(source, branch.test.span()).to_owned(),
                            completion.clone(),
                        ));
                    }
                }
            }
            match branch.alternate.as_ref() {
                Some(other @ Statement::IfStatement(_)) => cursor = other,
                None => break,
                Some(_) => return None,
            }
        }
    }

    let mut alternatives = Vec::new();
    let mut hoisted = HoistedVars::default();
    let mut cursor = dispatcher;
    loop {
        let Statement::IfStatement(branch) = cursor else {
            return None;
        };
        let label = state_test(&branch.test, state)?;
        if completion_tail
            .iter()
            .any(|(terminal, _, _)| *terminal == label)
        {
            // One common terminal return is emitted after the dispatcher.
        } else if absorbed_regions.contains(&label) {
            // Its original body now occurs inside the sole entering region,
            // so no declaration or observable effect is discarded.
        } else if reachable.contains(&label) {
            let consequent = if let Some(region) = combined_regions.get(&label) {
                region.clone()
            } else {
                match retargeted.get(&label) {
                    Some(edits) => print_terminal_edits(&branch.consequent, source, edits)?,
                    None => fragment(source, branch.consequent.span()).to_owned(),
                }
            };
            alternatives.push(format!(
                "if ({}) {consequent}",
                fragment(source, branch.test.span()),
            ));
        } else {
            hoisted.visit_statement(&branch.consequent);
        }
        match branch.alternate.as_ref() {
            Some(other @ Statement::IfStatement(_)) => cursor = other,
            None => break,
            Some(_) => return None,
        }
    }
    // Unreachable var declarations still create function-scoped bindings.
    // Annex B function declarations have separate binding rules, so keep
    // such a dispatcher unchanged rather than silently discarding them.
    if hoisted.unsupported || hoisted.function_declaration {
        return None;
    }
    if (alternatives.len() == cases.len() && retargeted.is_empty() && completion_tail.is_empty())
        || (alternatives.is_empty() && completion_tail.is_empty())
    {
        return None;
    }
    let mut text = if alternatives.is_empty() {
        String::new()
    } else {
        let mut text = alternatives.remove(0);
        for branch in alternatives {
            text.push_str(" else ");
            text.push_str(&branch);
        }
        text
    };
    for (_, test, completion) in completion_tail {
        text.push_str(&format!("\nif ({test}) {completion}"));
    }
    if !hoisted.names.is_empty() {
        text = format!(
            "var {};\n{text}",
            hoisted.names.into_iter().collect::<Vec<_>>().join(", ")
        );
    }
    Some(text)
}

/// Recover a while loop preceded by a numeric state initializer in the same
/// lexical block. Both syntaxes share the same control-flow reconstruction.
pub(crate) fn reconstruct_while_adjacent(
    init: &Statement<'_>,
    loop_stmt: &WhileStatement<'_>,
    source: &str,
) -> Option<String> {
    let (state, initial) = match init {
        Statement::ExpressionStatement(stmt) => {
            let Expression::AssignmentExpression(assign) = &stmt.expression else {
                return None;
            };
            if assign.operator.as_str() != "=" {
                return None;
            }
            (
                direct_assignment_name(&assign.left)?,
                number(&assign.right)?,
            )
        }
        Statement::VariableDeclaration(decl) if decl.declarations.len() == 1 => {
            let declaration = &decl.declarations[0];
            let BindingPattern::BindingIdentifier(binding) = &declaration.id else {
                return None;
            };
            (binding.name.as_str(), number(declaration.init.as_ref()?)?)
        }
        _ => return None,
    };
    let initial_text = fragment(source, init.span());
    reconstruct_state_loop(
        state,
        initial,
        &loop_stmt.test,
        &loop_stmt.body,
        initial_text,
        source,
    )
}

/// A `var` declaration is function-scoped even inside a branch that the
/// reconstructed graph proves dead. Re-declaring the same name (without an
/// initializer) preserves the original hoisted binding; source declarations
/// that actually execute remain in their exact original statement positions.
#[derive(Default)]
struct HoistedVars {
    names: BTreeSet<String>,
    unsupported: bool,
    function_declaration: bool,
}

/// Destructuring is only syntax for introducing several bindings: retain
/// all those names even when the initializer itself cannot execute.
#[derive(Default)]
struct DeclaredBindingNames {
    names: BTreeSet<String>,
}

impl<'a> Visit<'a> for DeclaredBindingNames {
    fn visit_binding_identifier(&mut self, binding: &oxc_ast::ast::BindingIdentifier<'a>) {
        self.names.insert(binding.name.to_string());
    }
    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: oxc_syntax::scope::ScopeFlags) {
    }
    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}
    fn visit_class(&mut self, _: &oxc_ast::ast::Class<'a>) {}
}

impl<'a> Visit<'a> for HoistedVars {
    fn visit_variable_declaration(&mut self, decl: &oxc_ast::ast::VariableDeclaration<'a>) {
        if decl.kind == VariableDeclarationKind::Var {
            let mut bindings = DeclaredBindingNames::default();
            for item in &decl.declarations {
                bindings.visit_binding_pattern(&item.id);
            }
            self.names.extend(bindings.names);
        }
        walk::walk_variable_declaration(self, decl);
    }

    fn visit_statement(&mut self, stmt: &Statement<'a>) {
        if matches!(stmt, Statement::FunctionDeclaration(_)) {
            self.function_declaration = true;
            return;
        }
        walk::walk_statement(self, stmt);
    }

    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: oxc_syntax::scope::ScopeFlags) {
    }
    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}
    fn visit_class(&mut self, _: &oxc_ast::ast::Class<'a>) {}
}

fn reconstruct_state_loop(
    state: &str,
    initial: u64,
    test: &Expression<'_>,
    body: &Statement<'_>,
    initial_text: &str,
    source: &str,
) -> Option<String> {
    let exit = exit_state(test, state)?;
    let mut candidate_cases = BTreeMap::new();
    collect_dispatch_statement(body, state, exit, source, &mut candidate_cases)?;
    // A route is proof-bearing only when its complete effects and successor
    // are known. Drop unmodelled cases *from the graph*, not from the original
    // source: reachable() will reject a missing route if execution can enter
    // that state, while genuinely unreachable branches are irrelevant.
    let graph = candidate_cases
        .into_iter()
        .filter_map(|(number, route)| route.map(|route| (number, route)))
        .collect::<BTreeMap<_, _>>();
    let nodes = reachable(initial, exit, &graph)?;
    let mut loops = build_loops(&graph, &nodes, exit)?;
    extend_multi_exit_loops(&graph, &nodes, initial, exit, &mut loops);
    // Do not generate an infinite/repeated CFG expansion. Every loop must
    // have a single entry; all reachable code must be fully accounted for.
    for (&header, loop_plan) in &loops {
        if !loop_plan.members.contains(&header) {
            return None;
        }
        for (&node, route) in &graph {
            if loop_plan.members.contains(&node) {
                continue;
            }
            let mut targets = Vec::new();
            route.targets(&mut targets);
            if targets
                .iter()
                .any(|target| loop_plan.members.contains(target) && *target != header)
            {
                return None;
            }
        }
    }
    let mut emitter = Emitter {
        graph: &graph,
        loops: &loops,
        exit,
        visited: BTreeSet::new(),
        fuel: 4096,
    };
    let code = emitter.walk(initial, exit)?;
    let mut hoisted = HoistedVars::default();
    hoisted.visit_statement(body);
    if hoisted.unsupported {
        return None;
    }
    let declarations = if hoisted.names.is_empty() {
        String::new()
    } else {
        format!(
            "var {};\n",
            hoisted.names.into_iter().collect::<Vec<_>>().join(", ")
        )
    };
    Some(format!(
        "{{\n{init_text}\n{declarations}{code}\n}}",
        init_text = initial_text
    ))
}

#[cfg(test)]
mod tests {
    use super::reconstruct_for;
    use crate::deobfuscate;
    use oxc_allocator::Allocator;
    use oxc_ast::ast::Statement;
    use oxc_ast_visit::{walk, Visit};
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;
    use work_budget::WorkBudget;

    #[derive(Default)]
    struct FindFor<'s> {
        source: &'s str,
        outputs: Vec<String>,
    }

    impl<'a> Visit<'a> for FindFor<'_> {
        fn visit_for_statement(&mut self, it: &oxc_ast::ast::ForStatement<'a>) {
            if let Some(recovered) = reconstruct_for(it, self.source) {
                self.outputs.push(recovered);
            }
            walk::walk_for_statement(self, it);
        }
    }

    fn recover(source: &str) -> String {
        let allocator = Allocator::default();
        let result = parse_program(&allocator, source, SourceType::cjs());
        assert!(!result.fatal_error, "fixture must parse");
        let mut visitor = FindFor {
            source,
            ..Default::default()
        };
        visitor.visit_program(&result.program);
        assert_eq!(visitor.outputs.len(), 1, "expected one structured CFG");
        visitor.outputs.remove(0)
    }

    #[test]
    fn restructures_numeric_state_cycle_into_while_without_identifier_assumptions() {
        let original = r#"
            function f(n, log) {
                let state;
                for (state = 41; state != 76;)
                    state == 91 ? (log.push("call"), state = 76)
                    : state == 41 && (state = n > 3 ? 76 : 91);
                return log;
            }
        "#;
        let restored = recover(original);
        assert!(restored.contains("if (n > 3)"), "{restored}");
        assert!(restored.contains("log.push(\"call\")"), "{restored}");
        assert!(!restored.contains("state == 91"), "{restored}");
    }

    #[test]
    fn finds_simple_reducible_loops_and_preserves_effectful_test() {
        let original = r#"
            function f(n, log) {
                var s, left = n;
                for (s = 87; s != 14;)
                    s === 87 ? (log.push("start"), s = 2)
                    : s === 2 ? (s = 45)
                    : s === 45 ? (s = left > 0 ? 71 : 50)
                    : s === 71 ? (log.push(left), left--, s = 65)
                    : s === 65 ? (s = 45)
                    : s === 50 ? (s = 73)
                    : s === 73 ? (s = left-- ? 88 : 61)
                    : s === 88 ? (log.push("again"), s = 96)
                    : s === 96 ? (s = 73)
                    : s === 61 && (s = 14);
                return log;
            }
        "#;
        let restored = recover(original);
        assert!(restored.contains("while (left > 0)"), "{restored}");
        assert!(restored.contains("while (left--)"), "{restored}");
        assert!(restored.contains("log.push(\"start\")"), "{restored}");
        assert!(restored.contains("log.push(\"again\")"), "{restored}");
        let allocator = Allocator::default();
        assert!(!parse_program(&allocator, &restored, SourceType::cjs()).fatal_error);
        let result = deobfuscate(original, 4, &WorkBudget::unlimited("if-ladder-test"));
        assert!(result.is_ok(), "unlimited budget should complete");
        let recovered = result.ok().flatten();
        assert!(recovered.is_some(), "valid source should rewrite");
        if let Some(fully) = recovered {
            assert_eq!(fully.transforms.get("if_ladder_structured"), Some(&1));
        }
    }

    #[test]
    fn structures_nested_reducible_loops_with_branch_reconvergence() {
        let source = r#"
            function process(flags, limit) {
                var s, out=[], i=0, x=0, arr=[];
                for(s=86;s!=50;)
                    s==86?(i=0,arr=[],s=44)
                    :s==44?s=48
                    :s==48?s=i<limit?94:41
                    :s==94?(x=i,s=2)
                    :s==2?s=flags[i]?83:92
                    :s==92?s=97
                    :s==97?s=x>=arr.length?81:33
                    :s==81?(arr.push(i),s=17)
                    :s==17?s=97
                    :s==33?(x=arr[x],s=83)
                    :s==83?(out.push(x),s=96)
                    :s==96?(i++,s=48)
                    :s==41&&(s=50);
                return out;
            }
        "#;
        let output = recover(source);
        assert!(output.contains("while (i<limit)"), "{output}");
        assert!(output.contains("while (x>=arr.length)"), "{output}");
        assert!(!output.contains("s==97"), "{output}");
        let allocator = Allocator::default();
        assert!(!parse_program(&allocator, &output, SourceType::cjs()).fatal_error);
    }

    #[test]
    fn structures_var_initializers_and_sequential_terminal_state_cases() {
        let source = r#"
            function dispatch(input, log) {
                let value;
                const run = function(mode) {
                    for (var state = 6; state != 2;)
                        if (state == 30) var captured = (state = 67, [input, log, arguments]);
                        else if (state == 81) state = mode == 1 ? 17 : 24;
                        else if (state == 6) state = input ? 85 : 2;
                        else if (state == 67) state = mode == 127 ? 14 : 81;
                        else if (state == 63) { log.push("end"); state = 2; }
                        else if (state == 14) { var result = log.push(captured.length); state = 73; }
                        else if (state == 24) { result = log.push(24); state = 73; }
                        else {
                            if (state == 73) return result;
                            if (state == 17) {var local = !input; state = (log.push(local), 73);}
                            else state == 85 && (state = input > 1 ? 30 : 63);
                        }
                };
                value = run(127);
                return [value, log];
            }
        "#;
        let restored = recover(source);
        assert!(!restored.contains("state == 30"), "{restored}");
        assert!(restored.contains("return result"), "{restored}");
        assert!(restored.contains("var captured"), "{restored}");
        let allocator = Allocator::default();
        assert!(!parse_program(&allocator, &restored, SourceType::cjs()).fatal_error);
    }

    #[test]
    fn does_not_restructure_ambiguous_declaration_side_effects() {
        for source in [
            "function f(){for(var state=1;state!=2;)if(state==1)var x=(state=2,call());}",
            "function f(){for(var state=1;state!=2;)if(state==1)var x=(state=2,[...effect()]);}",
            "function f(){for(var state=1;state!=2;)if(state==1)var x=(state=2,[state=1]);}",
        ] {
            let allocator = Allocator::default();
            let parsed = parse_program(&allocator, source, SourceType::cjs());
            assert!(!parsed.fatal_error);
            let mut visitor = FindFor {
                source,
                ..Default::default()
            };
            visitor.visit_program(&parsed.program);
            assert!(
                visitor.outputs.is_empty(),
                "must not infer dynamic edge: {source}"
            );
        }
    }

    #[test]
    fn restructures_statement_if_else_dispatch_with_early_exit_and_sequence() {
        let source = r#"
            function f(data, log) {
                var s, item;
                for (s=94; s!=54;)
                    if (s==94) {
                        for (item in data) if (item==="stop") return log;
                        s=10;
                    } else if (s==10) s=56;
                    else if (s==56) s=data.length?67:54;
                    else if (s==67) {
                        log.push("value");
                        s=(item=0,54);
                    }
                return log;
            }
        "#;
        let restored = recover(source);
        assert!(!restored.contains("s==94"), "{restored}");
        assert!(restored.contains("for (item in data)"), "{restored}");
        assert!(restored.contains("return log"), "{restored}");
        assert!(restored.contains("item=0"), "{restored}");
        assert!(restored.contains("log.push"), "{restored}");
        let allocator = Allocator::default();
        assert!(!parse_program(&allocator, &restored, SourceType::cjs()).fatal_error);
    }

    #[test]
    fn rejects_if_else_dispatch_that_writes_unknown_or_lexically_scoped_state() {
        for source in [
            "function f(){var s;for(s=3;s!=9;)if(s==3){s=external()}else if(s==9){s=9;}}",
            "function f(){var s;for(s=3;s!=9;)if(s==3){const v=9;s=9;}else if(s==9){s=9;}}",
        ] {
            let allocator = Allocator::default();
            let parsed = parse_program(&allocator, source, SourceType::cjs());
            assert!(!parsed.fatal_error);
            let mut visitor = FindFor {
                source,
                ..Default::default()
            };
            visitor.visit_program(&parsed.program);
            assert!(
                visitor.outputs.is_empty(),
                "unexpected reconstruction for {source}"
            );
        }
    }

    #[test]
    fn dead_numeric_state_writes_removed_only_when_unobserved() {
        let source = "function f(n){var s,sum=0;for(s=3;s!=9;)s==3?(s=n?4:9):s==4?(sum++,s=3):s==9&&(s=9);return sum;}";
        let result = deobfuscate(source, 12, &WorkBudget::unlimited("dead-state"));
        assert!(result.is_ok());
        if let Some(value) = result.ok().flatten() {
            assert!(value.source.contains("while (n)"), "{}", value.source);
            assert!(!value.source.contains("s = 4"), "{}", value.source);
            assert!(!value.source.contains("s = 9"), "{}", value.source);
            assert_eq!(value.transforms.get("if_ladder_structured"), Some(&1));
        }

        let live = "function f(n){var s=0;for(s=3;s!=9;)s==3?(s=n?9:3):s==9&&(s=9);return s;}";
        let result = deobfuscate(live, 12, &WorkBudget::unlimited("live-state"));
        assert!(result.is_ok());
        if let Some(value) = result.ok().flatten() {
            assert!(value.source.contains("s = 3"), "{}", value.source);
        }

        let aliased = "function f(s){for(s=3;s!=9;)s==3?(s=9):s==9&&(s=9);return arguments[0];}";
        let result = deobfuscate(aliased, 12, &WorkBudget::unlimited("aliased-state"));
        assert!(result.is_ok());
        if let Some(value) = result.ok().flatten() {
            assert!(value.source.contains("s = 9"), "{}", value.source);
        }

        let captured = "function f(){var s=0;const read=()=>s;for(s=3;s!=9;)s==3?(s=9):s==9&&(s=9);return read();}";
        let result = deobfuscate(captured, 12, &WorkBudget::unlimited("captured-state"));
        assert!(result.is_ok());
        if let Some(value) = result.ok().flatten() {
            assert!(value.source.contains("s = 9"), "{}", value.source);
        }
    }

    #[test]
    fn preserves_observable_const_assignment_exception() {
        let original = "function f(){const s=3;s=9;return 1;}";
        let result = deobfuscate(original, 12, &WorkBudget::unlimited("const-write"));
        assert!(result.is_ok());
        if let Some(value) = result.ok().flatten() {
            assert!(value.source.contains("s=9"), "{}", value.source);
        }
    }

    #[test]
    fn structures_reducible_cycle_with_mid_body_break_and_effects() {
        let source = r#"
            function f(limit, log) {
                let state=1;
                while(state!=99) {
                    if(state==1) state=2;
                    else if(state==2) state=limit>0?3:5;
                    else if(state==3) {
                        log.push(limit);
                        limit--;
                        state=limit>0?2:5;
                    } else if(state==5) {
                        log.push("end");
                        state=99;
                    }
                }
                return log;
            }
        "#;
        let result = deobfuscate(source, 12, &WorkBudget::unlimited("mid-body-break"));
        assert!(result.is_ok(), "{result:?}");
        let Ok(Some(value)) = result else {
            unreachable!()
        };
        assert_eq!(
            value.transforms.get("if_ladder_structured"),
            Some(&1),
            "{value:?}"
        );
        assert!(!value.source.contains("state==2"), "{}", value.source);
        assert!(value.source.contains("for (;;)"), "{}", value.source);
        assert!(value.source.contains("log.push"), "{}", value.source);
    }

    #[test]
    fn structures_alternate_exit_from_inside_single_entry_cycle() {
        let source = r#"
            function f(flag, log) {
                let state=20;
                while(state!=90)
                    if(state==20) state=flag?21:24;
                    else if(state==21) state=flag?22:23;
                    else if(state==22) {log.push(22);state=20;}
                    else if(state==23) {log.push(23);state=24;}
                    else if(state==24) {log.push(24);state=90;}
                return log;
            }
        "#;
        let result = deobfuscate(source, 12, &WorkBudget::unlimited("multiple-cycle-exits"));
        assert!(result.is_ok(), "{result:?}");
        let Ok(Some(value)) = result else {
            unreachable!()
        };
        assert_eq!(
            value.transforms.get("if_ladder_structured"),
            Some(&1),
            "{value:?}"
        );
        assert!(!value.source.contains("state==20"), "{}", value.source);
        assert!(value.source.contains("for (;;)"), "{}", value.source);
    }

    #[test]
    fn rejects_irreducible_cycle_with_multiple_entry_states() {
        let source = r#"
            function f(flag) {
                let state=1;
                while(state!=9) {
                    if(state==1) state=flag?2:3;
                    else if(state==2) state=3;
                    else if(state==3) state=flag?2:9;
                }
                return state;
            }
        "#;
        let result = deobfuscate(source, 12, &WorkBudget::unlimited("multiple-cycle-entries"));
        assert!(result.is_ok(), "{result:?}");
        let Ok(Some(value)) = result else {
            unreachable!()
        };
        assert!(
            !value.transforms.contains_key("if_ladder_structured"),
            "{value:?}"
        );
        assert!(value.source.contains("while"), "{}", value.source);
    }

    #[test]
    fn structures_dispatcher_with_early_throw_and_early_return_cases() {
        let source = r#"
            function route(flag, log) {
                for (s=1;s!=9;) if (s==1) s=flag?40:2;
                else {
                    if (s==40) { log.push("throw"); throw new Error("boom"); }
                    if (s==2) { log.push("ok"); s=3; }
                    else if (s==3) return log;
                }
            }
        "#;
        let restored = recover(source);
        assert!(!restored.contains("s==40"), "{restored}");
        assert!(!restored.contains("s==2"), "{restored}");
        assert!(restored.contains("throw new Error"), "{restored}");
        assert!(restored.contains("return log"), "{restored}");
        assert!(restored.contains("log.push"), "{restored}");
    }

    #[test]
    fn structures_dispatcher_with_unreachable_throwing_case() {
        let source = r#"
            function route(log) {
                for (s=1;s!=9;)
                    if (s==1) s=2;
                    else {
                        if (s==40) throw new Error("unreachable");
                        if (s==2) { log.push("ok"); s=9; }
                    }
                return log;
            }
        "#;
        let restored = recover(source);
        assert!(!restored.contains("unreachable"), "{restored}");
        assert!(restored.contains("log.push"), "{restored}");
    }

    #[test]
    fn refuses_nonterminal_early_case_in_dispatch_block() {
        let source = r#"
            function route(log) {
                for (s=1;s!=9;)
                    if (s==1) s=2;
                    else {
                        if (s==40) log.push("not terminal");
                        if (s==2) { log.push("ok"); s=9; }
                    }
                return log;
            }
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(!parsed.fatal_error);
        let mut visitor = FindFor {
            source,
            ..Default::default()
        };
        visitor.visit_program(&parsed.program);
        assert!(
            visitor.outputs.is_empty(),
            "nonterminal early if must not be moved"
        );
    }

    #[test]
    fn reconstructs_known_reachable_states_despite_unmodelled_dead_dispatch_cases() {
        let original = r#"
          function f(log) {
            let state=1;
            while(state!=9)
              if(state==1){log.push(1);state=2;}
              else if(state==2){log.push(2);state=9;}
              else if(state==7){log.push("dead");state=unmodelled();}
            return log;
          }
        "#;
        let result = deobfuscate(
            original,
            12,
            &WorkBudget::unlimited("dead-unmodelled-state"),
        );
        assert!(result.is_ok(), "deobfuscation should succeed");
        let Ok(Some(value)) = result else {
            unreachable!();
        };
        assert!(
            value.transforms.contains_key("if_ladder_structured"),
            "{value:?}"
        );
        assert!(!value.source.contains("unmodelled()"), "{}", value.source);
        assert!(!value.source.contains("dead"), "{}", value.source);
        assert!(value.source.contains("log.push(1)"), "{}", value.source);
        assert!(value.source.contains("log.push(2)"), "{}", value.source);
    }

    #[test]
    fn does_not_claim_a_reachable_unmodelled_state_is_recoverable() {
        let original = r#"
          function f(log) {
            let state=1;
            while(state!=9)
              if(state==1){log.push(1);state=7;}
              else if(state==2){log.push(2);state=9;}
              else if(state==7){state=unmodelled();}
            return log;
          }
        "#;
        let result = deobfuscate(
            original,
            12,
            &WorkBudget::unlimited("live-unmodelled-state"),
        );
        assert!(result.is_ok(), "deobfuscation should succeed");
        let Ok(Some(value)) = result else {
            unreachable!();
        };
        assert!(
            !value.transforms.contains_key("if_ladder_structured"),
            "{value:?}"
        );
        assert!(value.source.contains("unmodelled()"), "{}", value.source);
    }

    #[test]
    fn reconstructs_for_dispatcher_with_dead_unsupported_branch() {
        let source = r#"function f(x){
          for(var s=1;s!=9;)s==1?(x.push(1),s=2)
             :s==2?(x.push(2),s=9)
             :s==7&&(x.push(7),s=unmodelled());
          return x;
        }"#;
        let result = deobfuscate(source, 12, &WorkBudget::unlimited("for-dead-unknown"));
        assert!(result.is_ok(), "deobfuscation should succeed");
        let Ok(Some(value)) = result else {
            unreachable!();
        };
        assert!(
            value.transforms.contains_key("if_ladder_structured"),
            "{value:?}"
        );
        assert!(!value.source.contains("unmodelled()"), "{}", value.source);
    }

    #[test]
    fn reconstructs_while_with_adjacent_variable_or_assignment_initializer() {
        for source in [
            "function f(n,out){let s=41;while(s!=76)s==41?(s=n?91:76):s==91&&(out.push(1),s=76);return out;}",
            "function f(n,out){let s;s=41;while(s!=76)s==41?(s=n?91:76):s==91&&(out.push(1),s=76);return out;}",
        ] {
            let outcome = deobfuscate(source, 12, &WorkBudget::unlimited("while-recovery"));
            assert!(outcome.is_ok());
            if let Some(value) = outcome.ok().flatten() {
                assert!(value.source.contains("if (n)"), "{}", value.source);
                assert!(!value.source.contains("while(s!=76)"), "{}", value.source);
                assert_eq!(value.transforms.get("if_ladder_structured"), Some(&1));
            }
        }
        let separated = "function f(n){let s=41;sideEffect();while(s!=76)s==41?(s=n?91:76):s==91&&(s=76);return s;}";
        let outcome = deobfuscate(separated, 12, &WorkBudget::unlimited("while-separation"));
        assert!(outcome.is_ok());
        if let Some(value) = outcome.ok().flatten() {
            assert!(value.source.contains("if (n)"), "{}", value.source);
            assert!(!value.source.contains("while(s!=76)"), "{}", value.source);
        }
    }

    #[test]
    fn reconstructs_cross_block_and_nonadjacent_while_with_preserved_side_effects() {
        let source = r#"
            function f(n, log) {
                let state;
                state = 3;
                log.push("before");
                {
                    log.push("between");
                    while (state != 9)
                        state == 3 ? (log.push("start"), state = 4)
                        : state == 4 ? (state = n-- ? 3 : 9)
                        : state == 9 && (state = 9);
                }
                return log;
            }
        "#;
        let result = deobfuscate(source, 12, &WorkBudget::unlimited("cross-block-state"));
        assert!(result.is_ok());
        let recovered = result.ok().flatten().map(|value| value.source);
        assert!(recovered.is_some());
        if let Some(output) = recovered {
            assert!(output.contains("while (n--)"), "{output}");
            assert!(!output.contains("state == 3"), "{output}");
            let before = output.find("before");
            let between = output.find("between");
            let action = output.find("start");
            assert!(before < between && between < action, "{output}");
            let allocator = Allocator::default();
            assert!(!parse_program(&allocator, &output, SourceType::cjs()).fatal_error);
        }
    }

    #[test]
    fn rejects_nonadjacent_state_with_intervening_or_captured_clobber() {
        let fixtures = [
            // A different statement modifies the same semantic symbol.
            "function f(n){let s=3; s=n; sideEffect();while(s!=9)s==3?(s=9):s==9&&(s=9);}",
            // A local closure may mutate state while another helper runs.
            "function f(n){let s=3;const clobber=()=>s=9; clobber();while(s!=9)s==3?(s=9):s==9&&(s=9);}",
            // Direct eval can write function-local bindings without a reference.
            "function f(n){let s=3;eval(n); sideEffect();while(s!=9)s==3?(s=9):s==9&&(s=9);}",
            // An aliased sloppy-mode argument may be changed in the gap.
            "function f(s){s=3;arguments[0]=9;sideEffect();while(s!=9)s==3?(s=9):s==9&&(s=9);}",
            // A shadowed state identifier is not the initializer's symbol.
            "function f(){let s=3; { let s; sideEffect(); while(s!=9)s==3?(s=9):s==9&&(s=9); }}",
        ];
        for source in fixtures {
            let outcome = deobfuscate(source, 12, &WorkBudget::unlimited("state-clobber"));
            assert!(outcome.is_ok());
            if let Some(value) = outcome.ok().flatten() {
                assert!(
                    !value.source.contains("if_ladder_structured"),
                    "unexpected textual marker: {}",
                    value.source
                );
                assert!(
                    !value.transforms.contains_key("if_ladder_structured"),
                    "state reconstruction crossed a clobber in: {source}"
                );
            }
        }
    }

    #[test]
    fn refuses_unknown_state_successors() {
        let source = "for (s = 1; s != 9;) s == 1 ? (s = next()) : s == 2 && (s = 9)";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let statement = parsed.program.body.first().and_then(|item| {
            if let Statement::ForStatement(stmt) = item {
                Some(stmt.as_ref())
            } else {
                None
            }
        });
        assert!(
            statement.is_some(),
            "fixture should parse as a for statement"
        );
        if let Some(stmt) = statement {
            assert!(reconstruct_for(stmt, source).is_none());
        }
    }

    #[test]
    fn no_invented_restructure_for_irreducible_cycle() {
        // Two entries into the same cycle; a single-entry natural while
        // would omit a path. This stays as the original dispatcher.
        let source = "for (s = 1; s != 9;) s == 1 ? (s = pick() ? 2 : 3) : s == 2 ? (s = 3) : s == 3 ? (s = 2) : s == 4 && (s = 9)";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let statement = parsed.program.body.first().and_then(|item| {
            if let Statement::ForStatement(stmt) = item {
                Some(stmt.as_ref())
            } else {
                None
            }
        });
        assert!(
            statement.is_some(),
            "fixture should parse as a for statement"
        );
        if let Some(stmt) = statement {
            assert!(reconstruct_for(stmt, source).is_none());
        }
    }
}
