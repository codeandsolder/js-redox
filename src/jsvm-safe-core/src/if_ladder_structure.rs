//! Recover structured control flow from numeric-state ternary dispatchers.
//!
//! The parser handles arbitrary state labels and source expressions, not any
//! particular obfuscator vocabulary. Only single-entry reducible loops are
//! rendered: irreducible graphs and unmodelled state transitions are left
//! unchanged rather than emitted with altered execution order.
use crate::{
    control_flow::direct_assignment_name, direct_identifier_name, fragment, numeric::exact_u64,
    value_eval::eval,
};
use oxc_ast::ast::{
    ArrayExpressionElement, BindingPattern, Expression, ForStatement, ForStatementInit, Statement,
    VariableDeclarationKind, WhileStatement,
};
use oxc_ast_visit::{walk, Visit};
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
    cases: &mut BTreeMap<u64, Route>,
) -> Option<()> {
    match unparen(expr) {
        Expression::ConditionalExpression(branch) => {
            let value = state_test(&branch.test, state)?;
            let route = parse_route(&branch.consequent, state, source)?;
            if cases.insert(value, route).is_some() {
                return None;
            }
            collect_dispatch(&branch.alternate, state, source, cases)
        }
        Expression::LogicalExpression(logical) if logical.operator.as_str() == "&&" => {
            let value = state_test(&logical.left, state)?;
            let route = parse_route(&logical.right, state, source)?;
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
        Statement::ReturnStatement(_) => Some(Route {
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

fn collect_dispatch_statement(
    stmt: &Statement<'_>,
    state: &str,
    exit: u64,
    source: &str,
    cases: &mut BTreeMap<u64, Route>,
) -> Option<()> {
    match stmt {
        Statement::IfStatement(branch) => {
            let value = state_test(&branch.test, state)?;
            let route = parse_statement_route(&branch.consequent, state, exit, source)?;
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
            // Independent early-return state cases can precede the usual
            // if/else-if ladder. They do not flow into the later dispatch:
            // their entire matching branch exits the current function.
            for statement in preceding {
                let Statement::IfStatement(branch) = statement else {
                    return None;
                };
                if branch.alternate.is_some() {
                    return None;
                }
                let label = state_test(&branch.test, state)?;
                let return_stmt = match &branch.consequent {
                    Statement::ReturnStatement(return_stmt) => return_stmt,
                    Statement::BlockStatement(block) if block.body.len() == 1 => {
                        let Statement::ReturnStatement(return_stmt) = &block.body[0] else {
                            return None;
                        };
                        return_stmt
                    }
                    _ => return None,
                };
                let route = Route {
                    effects: vec![fragment(source, return_stmt.span()).to_owned()],
                    next: Next::State(exit),
                };
                if cases.insert(label, route).is_some() {
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
struct Loop {
    members: BTreeSet<u64>,
    condition: String,
    enters_on_true: bool,
    entering: Route,
    exiting: Route,
    header_effects: Vec<String>,
    body_start: u64,
    exit: u64,
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
                    condition: condition.clone(),
                    enters_on_true,
                    entering: entering.as_ref().clone(),
                    exiting: exiting.as_ref().clone(),
                    header_effects: route.effects.clone(),
                    body_start: enter,
                    exit: out,
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
                let mut body = loop_plan.entering.effects.join("\n");
                // The entry path can visit a loop-body node before reaching
                // the loop header (a do/while-shaped SCC). Re-emitting that
                // node inside the loop is required for subsequent iterations.
                // Use a fresh visited set for the body region while sharing
                // the same bounded work fuel, not a global visited set which
                // incorrectly rejects this reducible control flow.
                let mut region = Emitter {
                    graph: self.graph,
                    loops: self.loops,
                    exit: self.exit,
                    visited: BTreeSet::new(),
                    fuel: self.fuel,
                };
                body.push_str(&region.walk(loop_plan.body_start, cursor)?);
                self.fuel = region.fuel;
                let cond = if loop_plan.enters_on_true {
                    loop_plan.condition.clone()
                } else {
                    format!("!({})", loop_plan.condition)
                };
                if loop_plan.header_effects.is_empty() {
                    out.push_str(&format!("\nwhile ({cond}) {{\n{body}\n}}\n"));
                    out.push_str(&loop_plan.exiting.effects.join("\n"));
                } else {
                    out.push_str("\nfor (;;) {\n");
                    out.push_str(&loop_plan.header_effects.join("\n"));
                    out.push_str(&format!(
                        "\nif (!({cond})) {{\n{}\nbreak;\n}}\n{body}\n}}\n",
                        loop_plan.exiting.effects.join("\n")
                    ));
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
}

impl<'a> Visit<'a> for HoistedVars {
    fn visit_variable_declaration(&mut self, decl: &oxc_ast::ast::VariableDeclaration<'a>) {
        if decl.kind == VariableDeclarationKind::Var {
            for item in &decl.declarations {
                if let BindingPattern::BindingIdentifier(id) = &item.id {
                    self.names.insert(id.name.to_string());
                } else {
                    self.unsupported = true;
                }
            }
        }
        walk::walk_variable_declaration(self, decl);
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
    let mut graph = BTreeMap::new();
    collect_dispatch_statement(body, state, exit, source, &mut graph)?;
    let nodes = reachable(initial, exit, &graph)?;
    let loops = build_loops(&graph, &nodes, exit)?;
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
