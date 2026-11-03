use oxc_ast::{
    ast::{Expression, FunctionType},
    AstKind,
};
use oxc_cfg::{
    graph::{visit::EdgeRef, Direction},
    BlockNodeId, EdgeType,
};
use oxc_semantic::Semantic;
use oxc_span::{GetSpan, Span};
use oxc_syntax::node::NodeId;
use std::collections::{HashMap, HashSet, VecDeque};
use work_budget::{BudgetExceeded, BudgetPoller, WorkBudget};

fn deepest_exact_span_node(semantic: &Semantic<'_>, span: Span) -> Option<NodeId> {
    let nodes = semantic.nodes();
    nodes
        .iter_enumerated()
        .filter(|(_, node)| node.kind().span() == span)
        .max_by_key(|(node_id, _)| nodes.ancestor_ids(*node_id).count())
        .map(|(node_id, _)| node_id)
}

fn enclosing_function(semantic: &Semantic<'_>, node_id: NodeId) -> Option<NodeId> {
    semantic
        .nodes()
        .ancestors_enumerated(node_id)
        .find_map(|(ancestor_id, node)| {
            matches!(
                node.kind(),
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            )
            .then_some(ancestor_id)
        })
}

fn enclosing_execution_context(semantic: &Semantic<'_>, node_id: NodeId) -> Option<NodeId> {
    semantic
        .nodes()
        .ancestors_enumerated(node_id)
        .find_map(|(ancestor_id, node)| {
            matches!(
                node.kind(),
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Program(_)
            )
            .then_some(ancestor_id)
        })
}

fn usable_edge(edge: &EdgeType) -> bool {
    !matches!(edge, EdgeType::NewFunction | EdgeType::Unreachable)
}

fn expression_is_direct_event(expression: &Expression<'_>, event: Span) -> bool {
    if expression.span() == event {
        return true;
    }
    match expression {
        Expression::ParenthesizedExpression(parenthesized) => {
            expression_is_direct_event(&parenthesized.expression, event)
        }
        _ => false,
    }
}

/// Prove a local JavaScript evaluation-order fact that remains valid across
/// loops and try/catch: if `event` is a complete earlier item of the same
/// sequence expression containing `barrier`, every execution of the later
/// item necessarily follows normal completion of the event item in that very
/// sequence evaluation.
fn sequence_event_completion_precedes_barrier(
    semantic: &Semantic<'_>,
    event_node: NodeId,
    event: Span,
    barrier: Span,
) -> bool {
    let nodes = semantic.nodes();
    nodes.ancestors_enumerated(event_node).any(|(_, ancestor)| {
        let AstKind::SequenceExpression(sequence) = ancestor.kind() else {
            return false;
        };
        let event_index = sequence
            .expressions
            .iter()
            .position(|expression| expression_is_direct_event(expression, event));
        let barrier_index = sequence.expressions.iter().position(|expression| {
            let span = expression.span();
            span.start <= barrier.start && barrier.end <= span.end
        });
        matches!((event_index, barrier_index), (Some(event_index), Some(barrier_index)) if event_index < barrier_index)
    })
}

fn event_reachable_from(semantic: &Semantic<'_>, from: BlockNodeId, event: BlockNodeId) -> bool {
    semantic
        .cfg()
        .is_some_and(|cfg| cfg.is_reachable(from, event))
}

/// Prove that, conditional on `event` executing during one invocation of its
/// enclosing function, none of `barriers` can have executed earlier in that
/// invocation.
///
/// The proof uses Oxc's CFG rather than source-order heuristics. `NewFunction`
/// and statically unreachable edges are excluded by the CFG reachability
/// contract. Barriers must belong to the same function as the event; otherwise
/// the query fails closed. Events and barriers sharing a basic block are
/// ordered by source position, matching JavaScript's left-to-right evaluation
/// inside a straight-line block.
pub fn prove_event_before_barriers(
    semantic: &Semantic<'_>,
    event: Span,
    barriers: &[Span],
) -> bool {
    let Some(cfg) = semantic.cfg() else {
        return false;
    };
    let nodes = semantic.nodes();
    let Some(event_node) = deepest_exact_span_node(semantic, event) else {
        return false;
    };
    let Some(function_node) = enclosing_function(semantic, event_node) else {
        return false;
    };
    let function_entry = nodes.cfg_id(function_node);
    let event_block = nodes.cfg_id(event_node);

    let mut barriers_by_block = HashMap::<BlockNodeId, Vec<Span>>::new();
    for barrier in barriers {
        if barrier == &event {
            continue;
        }
        let Some(barrier_node) = deepest_exact_span_node(semantic, *barrier) else {
            return false;
        };
        if enclosing_function(semantic, barrier_node) != Some(function_node) {
            return false;
        }
        if sequence_event_completion_precedes_barrier(semantic, event_node, event, *barrier) {
            continue;
        }
        barriers_by_block
            .entry(nodes.cfg_id(barrier_node))
            .or_default()
            .push(*barrier);
    }

    if !event_reachable_from(semantic, function_entry, event_block) {
        return false;
    }
    if barriers_by_block.is_empty() {
        return true;
    }

    let mut queue = VecDeque::from([(function_entry, false)]);
    let mut seen = HashSet::new();
    let mut reached_event = false;
    while let Some((block, crossed_barrier)) = queue.pop_front() {
        if !seen.insert((block, crossed_barrier)) {
            continue;
        }
        if !event_reachable_from(semantic, block, event_block) {
            continue;
        }

        let barriers_here = barriers_by_block.get(&block);
        if block == event_block {
            reached_event = true;
            let earlier_here = barriers_here
                .is_some_and(|spans| spans.iter().any(|barrier| barrier.start < event.start));
            if crossed_barrier || earlier_here {
                return false;
            }
            continue;
        }

        let crossed_barrier =
            crossed_barrier || barriers_here.is_some_and(|spans| !spans.is_empty());
        for edge in cfg.graph().edges_directed(block, Direction::Outgoing) {
            if !usable_edge(edge.weight()) {
                continue;
            }
            if matches!(edge.weight(), EdgeType::Backedge)
                && event_reachable_from(semantic, edge.target(), event_block)
            {
                // Re-entering a loop can make a source-later barrier precede a
                // later execution of the event. This theorem deliberately
                // reasons about acyclic event prefixes and fails closed here.
                return false;
            }
            queue.push_back((edge.target(), crossed_barrier));
        }
    }

    reached_event
}

fn prove_required_before_node(
    semantic: &Semantic<'_>,
    execution_context: NodeId,
    event_node: NodeId,
    event: Span,
    required: Span,
) -> bool {
    let Some(cfg) = semantic.cfg() else {
        return false;
    };
    let nodes = semantic.nodes();
    let event_block = nodes.cfg_id(event_node);
    let Some(required_node) = deepest_exact_span_node(semantic, required) else {
        return false;
    };
    if enclosing_execution_context(semantic, required_node) != Some(execution_context) {
        return false;
    }
    let required_block = nodes.cfg_id(required_node);
    let function_entry = nodes.cfg_id(execution_context);
    let mut queue = VecDeque::from([(function_entry, false)]);
    let mut seen = HashSet::new();
    let mut reached_event = false;

    while let Some((block, crossed_required)) = queue.pop_front() {
        if !seen.insert((block, crossed_required)) {
            continue;
        }
        if !event_reachable_from(semantic, block, event_block) {
            continue;
        }

        if block == event_block {
            reached_event = true;
            let required_here_before =
                required_block == event_block && required.start < event.start;
            if !crossed_required && !required_here_before {
                return false;
            }
            continue;
        }

        let crossed_required = crossed_required || block == required_block;
        for edge in cfg.graph().edges_directed(block, Direction::Outgoing) {
            if !usable_edge(edge.weight()) {
                continue;
            }
            // Cycles are safe here: the visited state includes whether the
            // required event has already been crossed. A path that reaches the
            // target before the requirement remains distinguishable from later
            // loop iterations and therefore fails the proof naturally.
            queue.push_back((edge.target(), crossed_required));
        }
    }

    reached_event
}

/// Prove that every supplied `required` AST evaluation begins before `event`
/// on every path that reaches `event` in the same execution context.
///
/// This is a conditional dominance-style proof over Oxc's CFG. Cycles are
/// handled by carrying whether the requirement has been crossed as part of the
/// traversal state. Cross-function requirements and unresolved spans fail closed.
pub fn prove_events_before_event(semantic: &Semantic<'_>, required: &[Span], event: Span) -> bool {
    let Some(event_node) = deepest_exact_span_node(semantic, event) else {
        return false;
    };
    let Some(execution_context) = enclosing_execution_context(semantic, event_node) else {
        return false;
    };
    !required.is_empty()
        && required.iter().all(|required| {
            *required != event
                && prove_required_before_node(
                    semantic,
                    execution_context,
                    event_node,
                    event,
                    *required,
                )
        })
}

fn has_enclosing_try_before_execution_context(
    semantic: &Semantic<'_>,
    node_id: NodeId,
    execution_context: NodeId,
) -> bool {
    semantic
        .nodes()
        .ancestors_enumerated(node_id)
        .take_while(|(ancestor_id, _)| *ancestor_id != execution_context)
        .any(|(_, node)| matches!(node.kind(), AstKind::TryStatement(_)))
}

/// Prove that a required operation which takes effect on normal completion of
/// its AST node has completed before `event` in the same execution context.
///
/// Oxc associates expression nodes with the CFG block where their evaluation
/// begins. A throw before the operation's completion could therefore otherwise
/// make entry dominance look like effect dominance. We fail closed when the
/// required node is enclosed by `try`; without a local catcher, any abrupt
/// completion leaves the execution context and cannot reach the later event.
pub fn prove_event_completion_before_event(
    semantic: &Semantic<'_>,
    required: Span,
    event: Span,
) -> bool {
    let Some(required_node) = deepest_exact_span_node(semantic, required) else {
        return false;
    };
    let Some(event_node) = deepest_exact_span_node(semantic, event) else {
        return false;
    };
    let Some(execution_context) = enclosing_execution_context(semantic, event_node) else {
        return false;
    };
    if enclosing_execution_context(semantic, required_node) != Some(execution_context)
        || has_enclosing_try_before_execution_context(semantic, required_node, execution_context)
    {
        return false;
    }
    required != event
        && prove_required_before_node(semantic, execution_context, event_node, event, required)
}

fn function_value_is_runtime_expression(kind: AstKind<'_>) -> bool {
    matches!(kind, AstKind::Function(function) if function.r#type == FunctionType::FunctionExpression)
        || matches!(kind, AstKind::ArrowFunctionExpression(_))
}

/// Find the deepest exact-span AST node while charging the caller's work budget.
fn deepest_exact_span_node_budgeted(
    semantic: &Semantic<'_>,
    span: Span,
    budget: &WorkBudget,
) -> Result<Option<NodeId>, BudgetExceeded> {
    let nodes = semantic.nodes();
    let mut deepest = None::<(NodeId, usize)>;
    let mut poller = BudgetPoller::new(budget, 128);
    for (node_id, node) in nodes.iter_enumerated() {
        if !poller.poll(1) {
            break;
        }
        if node.kind().span() != span {
            continue;
        }
        let mut depth = 0usize;
        for _ in nodes.ancestor_ids(node_id) {
            if !poller.poll(1) {
                break;
            }
            depth = depth.saturating_add(1);
        }
        if deepest.is_none_or(|(_, current_depth)| depth > current_depth) {
            deepest = Some((node_id, depth));
        }
    }
    poller.finish()?;
    Ok(deepest.map(|(node_id, _)| node_id))
}

fn enclosing_execution_context_budgeted(
    semantic: &Semantic<'_>,
    node_id: NodeId,
    budget: &WorkBudget,
) -> Result<Option<NodeId>, BudgetExceeded> {
    let mut poller = BudgetPoller::new(budget, 128);
    let mut found = None;
    for (ancestor_id, node) in semantic.nodes().ancestors_enumerated(node_id) {
        if !poller.poll(1) {
            break;
        }
        if matches!(
            node.kind(),
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::Program(_)
        ) {
            found = Some(ancestor_id);
            break;
        }
    }
    poller.finish()?;
    Ok(found)
}

fn has_enclosing_try_before_execution_context_budgeted(
    semantic: &Semantic<'_>,
    node_id: NodeId,
    execution_context: NodeId,
    budget: &WorkBudget,
) -> Result<bool, BudgetExceeded> {
    let mut poller = BudgetPoller::new(budget, 128);
    let mut found = false;
    for (ancestor_id, node) in semantic.nodes().ancestors_enumerated(node_id) {
        if !poller.poll(1) {
            break;
        }
        if ancestor_id == execution_context {
            break;
        }
        if matches!(node.kind(), AstKind::TryStatement(_)) {
            found = true;
            break;
        }
    }
    poller.finish()?;
    Ok(found)
}

fn prove_required_before_node_budgeted(
    semantic: &Semantic<'_>,
    execution_context: NodeId,
    event_node: NodeId,
    event: Span,
    required: Span,
    budget: &WorkBudget,
) -> Result<bool, BudgetExceeded> {
    let Some(cfg) = semantic.cfg() else {
        return Ok(false);
    };
    let nodes = semantic.nodes();
    let event_block = nodes.cfg_id(event_node);
    let Some(required_node) = deepest_exact_span_node_budgeted(semantic, required, budget)? else {
        return Ok(false);
    };
    if enclosing_execution_context_budgeted(semantic, required_node, budget)?
        != Some(execution_context)
    {
        return Ok(false);
    }
    let required_block = nodes.cfg_id(required_node);
    let function_entry = nodes.cfg_id(execution_context);

    // Precompute the blocks that can reach the event once, rather than
    // re-running a graph search from every path-state below.
    let mut reaches_event = HashSet::new();
    let mut reverse_queue = VecDeque::from([event_block]);
    let mut reverse_poller = BudgetPoller::new(budget, 128);
    while let Some(block) = reverse_queue.pop_front() {
        if !reverse_poller.poll(1) {
            break;
        }
        if !reaches_event.insert(block) {
            continue;
        }
        for edge in cfg.graph().edges_directed(block, Direction::Incoming) {
            if !reverse_poller.poll(1) {
                break;
            }
            if usable_edge(edge.weight()) {
                reverse_queue.push_back(edge.source());
            }
        }
    }
    reverse_poller.finish()?;
    if !reaches_event.contains(&function_entry) {
        return Ok(false);
    }

    let mut queue = VecDeque::from([(function_entry, false)]);
    let mut seen = HashSet::new();
    let mut reached_event = false;
    let mut poller = BudgetPoller::new(budget, 128);

    while let Some((block, crossed_required)) = queue.pop_front() {
        if !poller.poll(1) {
            break;
        }
        if !seen.insert((block, crossed_required)) {
            continue;
        }
        if !reaches_event.contains(&block) {
            continue;
        }
        if block == event_block {
            reached_event = true;
            let required_here_before =
                required_block == event_block && required.start < event.start;
            if !crossed_required && !required_here_before {
                poller.finish()?;
                return Ok(false);
            }
            continue;
        }

        let crossed_required = crossed_required || block == required_block;
        for edge in cfg.graph().edges_directed(block, Direction::Outgoing) {
            if !poller.poll(1) {
                break;
            }
            if usable_edge(edge.weight()) {
                queue.push_back((edge.target(), crossed_required));
            }
        }
    }
    poller.finish()?;
    Ok(reached_event)
}

/// Witness a possible path in the *syntactic CFG* from a completed source
/// assignment to a later call without crossing any write to that binding.
///
/// This is an existential graph fact, NOT input-feasibility, branch reachability,
/// dispatcher identity, or must-reach value provenance. Feasible JavaScript
/// execution is an independent obligation. The source and sink must resolve to
/// the same execution context. Oxc's NewFunction and Unreachable edges are
/// ignored; graph cycles are handled with a visited set.
///
/// Every span lookup and graph traversal is charged to the caller's budget.
pub fn cfg_has_write_free_path(
    semantic: &Semantic<'_>,
    source: Span,
    sink: Span,
    barriers: &[Span],
    budget: &WorkBudget,
) -> Result<bool, BudgetExceeded> {
    budget.checkpoint()?;
    if source.end > sink.start {
        return Ok(false);
    }
    let Some(cfg) = semantic.cfg() else {
        return Ok(false);
    };
    let Some(source_node) = deepest_exact_span_node_budgeted(semantic, source, budget)? else {
        return Ok(false);
    };
    let Some(sink_node) = deepest_exact_span_node_budgeted(semantic, sink, budget)? else {
        return Ok(false);
    };
    let Some(context) = enclosing_execution_context_budgeted(semantic, source_node, budget)? else {
        return Ok(false);
    };
    if enclosing_execution_context_budgeted(semantic, sink_node, budget)? != Some(context) {
        return Ok(false);
    }
    let nodes = semantic.nodes();
    let source_block = nodes.cfg_id(source_node);
    let sink_block = nodes.cfg_id(sink_node);
    let mut barriers_by_block = HashMap::<BlockNodeId, Vec<Span>>::new();
    for &barrier in barriers {
        budget.consume(1)?;
        let Some(barrier_node) = deepest_exact_span_node_budgeted(semantic, barrier, budget)?
        else {
            return Ok(false);
        };
        if enclosing_execution_context_budgeted(semantic, barrier_node, budget)? != Some(context) {
            return Ok(false);
        }
        barriers_by_block
            .entry(nodes.cfg_id(barrier_node))
            .or_default()
            .push(barrier);
    }

    let mut queue = VecDeque::from([source_block]);
    let mut visited = HashSet::new();
    while let Some(block) = queue.pop_front() {
        budget.consume(1)?;
        if !visited.insert(block) {
            continue;
        }
        // The source assignment has completed before traversal begins.
        // An intervening write in the same block is ordered by byte span;
        // writes in other blocks conservatively block the entire block.
        let killed = barriers_by_block.get(&block).is_some_and(|writes| {
            writes.iter().any(|write| {
                (block != source_block || write.start >= source.end)
                    && (block != sink_block || write.start < sink.start)
            })
        });
        if killed {
            continue;
        }
        if block == sink_block {
            return Ok(true);
        }
        for edge in cfg.graph().edges_directed(block, Direction::Outgoing) {
            budget.consume(1)?;
            if usable_edge(edge.weight()) {
                queue.push_back(edge.target());
            }
        }
    }
    Ok(false)
}

/// Prove that a required operation has completed before execution of an event
/// inside a later-created nested function value.
///
/// The proof is deliberately narrower than general interprocedural ordering:
/// the directly nested bridge must be a function expression or arrow. Function
/// declarations fail closed because hoisting decouples body availability from
/// source evaluation order. For function values, the nearest outer parent
/// expression begins before the function object can be created, so proving the
/// required operation complete before that parent is a sufficient premise for
/// every later execution of the nested body.
///
/// All AST/ancestor/CFG traversal on this production-facing path is charged to
/// the caller's shared work budget.
pub fn prove_event_completion_before_nested_event(
    semantic: &Semantic<'_>,
    required: Span,
    nested_event: Span,
    budget: &WorkBudget,
) -> Result<bool, BudgetExceeded> {
    budget.checkpoint()?;
    let Some(required_node) = deepest_exact_span_node_budgeted(semantic, required, budget)? else {
        return Ok(false);
    };
    let Some(nested_event_node) = deepest_exact_span_node_budgeted(semantic, nested_event, budget)?
    else {
        return Ok(false);
    };
    let Some(required_context) =
        enclosing_execution_context_budgeted(semantic, required_node, budget)?
    else {
        return Ok(false);
    };
    let Some(nested_context) =
        enclosing_execution_context_budgeted(semantic, nested_event_node, budget)?
    else {
        return Ok(false);
    };
    if nested_context == required_context {
        if has_enclosing_try_before_execution_context_budgeted(
            semantic,
            required_node,
            required_context,
            budget,
        )? {
            return Ok(false);
        }
        return Ok(required != nested_event
            && prove_required_before_node_budgeted(
                semantic,
                required_context,
                nested_event_node,
                nested_event,
                required,
                budget,
            )?);
    }

    let mut bridge_function = nested_context;
    loop {
        budget.checkpoint()?;
        if !matches!(
            semantic.nodes().kind(bridge_function),
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
        ) {
            return Ok(false);
        }
        let Some(parent_context) =
            enclosing_execution_context_budgeted(semantic, bridge_function, budget)?
        else {
            return Ok(false);
        };
        if parent_context == required_context {
            break;
        }
        bridge_function = parent_context;
    }

    let nodes = semantic.nodes();
    if !function_value_is_runtime_expression(nodes.kind(bridge_function)) {
        return Ok(false);
    }
    let creation_anchor = nodes.parent_id(bridge_function);
    if enclosing_execution_context_budgeted(semantic, creation_anchor, budget)?
        != Some(required_context)
    {
        return Ok(false);
    }
    let anchor_span = nodes.kind(creation_anchor).span();
    if has_enclosing_try_before_execution_context_budgeted(
        semantic,
        required_node,
        required_context,
        budget,
    )? {
        return Ok(false);
    }
    Ok(required != anchor_span
        && prove_required_before_node_budgeted(
            semantic,
            required_context,
            creation_anchor,
            anchor_span,
            required,
            budget,
        )?)
}

#[cfg(test)]
mod tests {
    use super::{
        prove_event_before_barriers, prove_event_completion_before_event,
        prove_event_completion_before_nested_event, prove_events_before_event,
    };
    use crate::test_support::{source_slice, TestFailure, TestResult, TestValue};
    use oxc_allocator::Allocator;
    use oxc_ast::{ast::Program, AstKind};
    use oxc_semantic::{Semantic, SemanticBuilder};
    use oxc_span::{SourceType, Span};
    use rolldown_redox::ecmascript::parse_program;
    use work_budget::{BudgetExceededKind, BudgetLimits, WorkBudget};

    fn test_budget() -> WorkBudget {
        WorkBudget::unlimited("cfg-order-test")
    }

    fn semantic<'a>(program: &'a Program<'a>) -> Semantic<'a> {
        let ret = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .with_check_syntax_error(true)
            .build(program);
        assert!(ret.diagnostics.is_empty());
        ret.semantic
    }

    fn call_span(semantic: &Semantic<'_>, source: &str, needle: &str) -> Result<Span, TestFailure> {
        semantic
            .nodes()
            .iter()
            .filter_map(|node| match node.kind() {
                AstKind::CallExpression(call) => Some(call.span),
                _ => None,
            })
            .find(|span| {
                source_slice(source, span.start, span.end, "call span")
                    .is_ok_and(|text| text == needle)
            })
            .test_value("matching call span")
    }

    fn assignment_span(
        semantic: &Semantic<'_>,
        source: &str,
        needle: &str,
    ) -> Result<Span, TestFailure> {
        semantic
            .nodes()
            .iter()
            .filter_map(|node| match node.kind() {
                AstKind::AssignmentExpression(assignment) => Some(assignment.span),
                _ => None,
            })
            .find(|span| {
                source_slice(source, span.start, span.end, "assignment span")
                    .is_ok_and(|text| text == needle)
            })
            .test_value("matching assignment span")
    }

    fn prove(source: &str, event: &str, barriers: &[&str]) -> Result<bool, TestFailure> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = semantic(&parsed.program);
        let event = call_span(&semantic, source, event)?;
        let barriers = barriers
            .iter()
            .map(|barrier| call_span(&semantic, source, barrier))
            .collect::<Result<Vec<_>, TestFailure>>()?;
        Ok(prove_event_before_barriers(&semantic, event, &barriers))
    }

    #[test]
    fn sequence_completion_orders_later_barrier_across_loop_backedge() -> TestResult {
        let source = "function f() { for (;;) { event(), barrier(); if (stop) break; } }";
        assert!(prove(source, "event()", &["barrier()"])?);

        Ok(())
    }

    #[test]
    fn sequence_completion_rejects_earlier_barrier() -> TestResult {
        let source = "function f() { for (;;) { barrier(), event(); if (stop) break; } }";
        assert!(!prove(source, "event()", &["barrier()"])?);

        Ok(())
    }

    #[test]
    fn sequence_completion_rejects_conditionally_skipped_event_item() -> TestResult {
        let source = "function f() { for (;;) { (flag && event()), barrier(); if (stop) break; } }";
        assert!(!prove(source, "event()", &["barrier()"])?);

        Ok(())
    }

    #[test]
    fn proves_completed_assignment_before_later_event() -> TestResult {
        let source = "function f() { state.value = 1; target(); }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let assignment = assignment_span(&semantic, source, "state.value = 1")?;
        let target = call_span(&semantic, source, "target()")?;
        assert!(prove_event_completion_before_event(
            &semantic, assignment, target
        ));

        Ok(())
    }

    #[test]
    fn completed_event_rejects_enclosing_try() -> TestResult {
        let source = "function f() { try { state.value = explode(); } catch (_) {} target(); }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let assignment = assignment_span(&semantic, source, "state.value = explode()")?;
        let target = call_span(&semantic, source, "target()")?;
        assert!(!prove_event_completion_before_event(
            &semantic, assignment, target
        ));

        Ok(())
    }

    #[test]
    fn proves_completed_event_before_nested_function_expression_execution() -> TestResult {
        let source =
            "function outer() { proto.run = function() {}; holder.f = function() { target(); }; }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let install = assignment_span(&semantic, source, "proto.run = function() {}")?;
        let target = call_span(&semantic, source, "target()")?;
        assert!(prove_event_completion_before_nested_event(
            &semantic,
            install,
            target,
            &test_budget(),
        )
        .test_value("nested completion proof")?);

        Ok(())
    }

    #[test]
    fn nested_completion_rejects_function_declaration_bridge() -> TestResult {
        let source =
            "function outer() { proto.run = function() {}; function later() { target(); } }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let install = assignment_span(&semantic, source, "proto.run = function() {}")?;
        let target = call_span(&semantic, source, "target()")?;
        assert!(!prove_event_completion_before_nested_event(
            &semantic,
            install,
            target,
            &test_budget(),
        )
        .test_value("nested completion proof")?);

        Ok(())
    }

    #[test]
    fn nested_completion_rejects_function_value_created_before_required_event() -> TestResult {
        let source =
            "function outer() { holder.f = function() { target(); }; proto.run = function() {}; }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let install = assignment_span(&semantic, source, "proto.run = function() {}")?;
        let target = call_span(&semantic, source, "target()")?;
        assert!(!prove_event_completion_before_nested_event(
            &semantic,
            install,
            target,
            &test_budget(),
        )
        .test_value("nested completion proof")?);

        Ok(())
    }

    #[test]
    fn nested_completion_propagates_work_budget_exhaustion() -> TestResult {
        let source =
            "function outer() { proto.run = function() {}; holder.f = function() { target(); }; }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let install = assignment_span(&semantic, source, "proto.run = function() {}")?;
        let target = call_span(&semantic, source, "target()")?;
        let budget = WorkBudget::new("cfg-order-fuel", BudgetLimits::work(0));
        assert!(matches!(
            prove_event_completion_before_nested_event(&semantic, install, target, &budget),
            Err(ref error)
                if error.kind() == BudgetExceededKind::Work
                    && error.scope() == "cfg-order-fuel"
        ));

        Ok(())
    }

    #[test]
    fn proves_required_event_before_target() -> TestResult {
        let source = "function f() { init(); target(); }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let init = call_span(&semantic, source, "init()")?;
        let target = call_span(&semantic, source, "target()")?;
        assert!(prove_events_before_event(&semantic, &[init], target));

        Ok(())
    }

    #[test]
    fn proves_required_event_before_target_inside_loop() -> TestResult {
        let source = "function f(flag) { while (flag) { init(); target(); } }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let init = call_span(&semantic, source, "init()")?;
        let target = call_span(&semantic, source, "target()")?;
        assert!(prove_events_before_event(&semantic, &[init], target));

        Ok(())
    }

    #[test]
    fn rejects_target_before_required_event_inside_loop() -> TestResult {
        let source = "function f(flag) { while (flag) { target(); init(); } }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let init = call_span(&semantic, source, "init()")?;
        let target = call_span(&semantic, source, "target()")?;
        assert!(!prove_events_before_event(&semantic, &[init], target));

        Ok(())
    }

    #[test]
    fn rejects_optional_required_event_before_target() -> TestResult {
        let source = "function f(flag) { if (flag) init(); target(); }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let init = call_span(&semantic, source, "init()")?;
        let target = call_span(&semantic, source, "target()")?;
        assert!(!prove_events_before_event(&semantic, &[init], target));

        Ok(())
    }

    #[test]
    fn proves_straight_line_event_before_later_barrier() -> TestResult {
        assert!(prove(
            "function f() { target(); barrier(); }",
            "target()",
            &["barrier()"]
        )?);

        Ok(())
    }

    #[test]
    fn rejects_straight_line_barrier_before_event() -> TestResult {
        assert!(!prove(
            "function f() { barrier(); target(); }",
            "target()",
            &["barrier()"]
        )?);

        Ok(())
    }

    #[test]
    fn proves_mutually_exclusive_barrier_cannot_precede_event() -> TestResult {
        assert!(prove(
            "function f(flag) { if (flag) { barrier(); } else { target(); } }",
            "target()",
            &["barrier()"]
        )?);

        Ok(())
    }

    #[test]
    fn proves_mutually_exclusive_switch_case_barrier_cannot_precede_event() -> TestResult {
        assert!(prove(
            "function f(value) { switch (value) { case 1: barrier(); break; case 2: target(); break; default: break; } }",
            "target()",
            &["barrier()"]
        )?);

        Ok(())
    }

    #[test]
    fn rejects_relevant_loop_backedge() -> TestResult {
        assert!(!prove(
            "function f(flag) { while (flag) { barrier(); flag = false; } target(); }",
            "target()",
            &["barrier()"]
        )?);

        Ok(())
    }

    #[test]
    fn rejects_optional_barrier_that_can_precede_event() -> TestResult {
        assert!(!prove(
            "function f(flag) { if (flag) barrier(); target(); }",
            "target()",
            &["barrier()"]
        )?);

        Ok(())
    }

    #[test]
    fn rejects_barrier_from_nested_function() -> TestResult {
        assert!(!prove(
            "function f() { function nested() { barrier(); } target(); }",
            "target()",
            &["barrier()"]
        )?);

        Ok(())
    }
}
