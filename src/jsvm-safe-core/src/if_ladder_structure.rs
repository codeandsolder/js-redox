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
    BindingPattern, Expression, ForStatement, ForStatementInit, Statement, WhileStatement,
};
use oxc_span::GetSpan;
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
    let expr = unparen(expr);
    match expr {
        Expression::ConditionalExpression(branch) => Some(Route {
            effects: vec![],
            next: Next::Choose {
                condition: fragment(source, branch.test.span()).to_owned(),
                yes: Box::new(parse_target(&branch.consequent, state, source)?),
                no: Box::new(parse_target(&branch.alternate, state, source)?),
            },
        }),
        _ => Some(Route::jump(state, number(expr)?)),
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
                body.push_str(&self.walk(loop_plan.body_start, cursor)?);
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
    let ForStatementInit::AssignmentExpression(init) = it.init.as_ref()? else {
        return None;
    };
    if init.operator.as_str() != "=" {
        return None;
    }
    let state = direct_assignment_name(&init.left)?;
    let initial = number(&init.right)?;
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

fn reconstruct_state_loop(
    state: &str,
    initial: u64,
    test: &Expression<'_>,
    body: &Statement<'_>,
    initial_text: &str,
    source: &str,
) -> Option<String> {
    let exit = exit_state(test, state)?;
    let dispatch = match body {
        Statement::ExpressionStatement(stmt) => &stmt.expression,
        Statement::BlockStatement(block) if block.body.len() == 1 => {
            let Statement::ExpressionStatement(stmt) = &block.body[0] else {
                return None;
            };
            &stmt.expression
        }
        _ => return None,
    };
    let mut graph = BTreeMap::new();
    collect_dispatch(dispatch, state, source, &mut graph)?;
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
    Some(format!("{{\n{initial_text}\n{code}\n}}"))
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
            assert!(value.source.contains("while(s!=76)"), "{}", value.source);
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
