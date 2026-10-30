use oxc_ast::{ast::FunctionType, AstKind};
use oxc_cfg::{
    graph::{visit::EdgeRef, Direction},
    BlockNodeId, EdgeType,
};
use oxc_semantic::Semantic;
use oxc_span::{GetSpan, Span};
use oxc_syntax::node::NodeId;
use std::collections::{HashMap, HashSet, VecDeque};

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
        barriers_by_block
            .entry(nodes.cfg_id(barrier_node))
            .or_default()
            .push(*barrier);
    }

    if !event_reachable_from(semantic, function_entry, event_block) {
        return false;
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
pub fn prove_event_completion_before_nested_event(
    semantic: &Semantic<'_>,
    required: Span,
    nested_event: Span,
) -> bool {
    let Some(required_node) = deepest_exact_span_node(semantic, required) else {
        return false;
    };
    let Some(nested_event_node) = deepest_exact_span_node(semantic, nested_event) else {
        return false;
    };
    let Some(required_context) = enclosing_execution_context(semantic, required_node) else {
        return false;
    };
    let Some(nested_context) = enclosing_execution_context(semantic, nested_event_node) else {
        return false;
    };
    if nested_context == required_context {
        return prove_event_completion_before_event(semantic, required, nested_event);
    }

    let mut bridge_function = nested_context;
    loop {
        if !matches!(
            semantic.nodes().kind(bridge_function),
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
        ) {
            return false;
        }
        let Some(parent_context) = enclosing_execution_context(semantic, bridge_function) else {
            return false;
        };
        if parent_context == required_context {
            break;
        }
        bridge_function = parent_context;
    }

    let nodes = semantic.nodes();
    if !function_value_is_runtime_expression(nodes.kind(bridge_function)) {
        return false;
    }
    let creation_anchor = nodes.parent_id(bridge_function);
    if enclosing_execution_context(semantic, creation_anchor) != Some(required_context) {
        return false;
    }
    let anchor_span = nodes.kind(creation_anchor).span();
    if has_enclosing_try_before_execution_context(semantic, required_node, required_context) {
        return false;
    }
    required != anchor_span
        && prove_required_before_node(
            semantic,
            required_context,
            creation_anchor,
            anchor_span,
            required,
        )
}

#[cfg(test)]
mod tests {
    use super::{
        prove_event_before_barriers, prove_event_completion_before_event,
        prove_event_completion_before_nested_event, prove_events_before_event,
    };
    use oxc_allocator::Allocator;
    use oxc_ast::{ast::Program, AstKind};
    use oxc_semantic::{Semantic, SemanticBuilder};
    use oxc_span::{SourceType, Span};
    use rolldown_redox::ecmascript::parse_program;

    fn semantic<'a>(program: &'a Program<'a>) -> Semantic<'a> {
        let ret = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .with_check_syntax_error(true)
            .build(program);
        assert!(ret.diagnostics.is_empty());
        ret.semantic
    }

    fn call_span(semantic: &Semantic<'_>, source: &str, needle: &str) -> Span {
        semantic
            .nodes()
            .iter()
            .filter_map(|node| match node.kind() {
                AstKind::CallExpression(call) => Some(call.span),
                _ => None,
            })
            .find(|span| &source[span.start as usize..span.end as usize] == needle)
            .unwrap_or_else(|| panic!("missing call {needle}"))
    }

    fn assignment_span(semantic: &Semantic<'_>, source: &str, needle: &str) -> Span {
        semantic
            .nodes()
            .iter()
            .filter_map(|node| match node.kind() {
                AstKind::AssignmentExpression(assignment) => Some(assignment.span),
                _ => None,
            })
            .find(|span| &source[span.start as usize..span.end as usize] == needle)
            .unwrap_or_else(|| panic!("missing assignment {needle}"))
    }

    fn prove(source: &str, event: &str, barriers: &[&str]) -> bool {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = semantic(&parsed.program);
        let event = call_span(&semantic, source, event);
        let barriers = barriers
            .iter()
            .map(|barrier| call_span(&semantic, source, barrier))
            .collect::<Vec<_>>();
        prove_event_before_barriers(&semantic, event, &barriers)
    }

    #[test]
    fn proves_completed_assignment_before_later_event() {
        let source = "function f() { state.value = 1; target(); }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let assignment = assignment_span(&semantic, source, "state.value = 1");
        let target = call_span(&semantic, source, "target()");
        assert!(prove_event_completion_before_event(
            &semantic, assignment, target
        ));
    }

    #[test]
    fn completed_event_rejects_enclosing_try() {
        let source = "function f() { try { state.value = explode(); } catch (_) {} target(); }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let assignment = assignment_span(&semantic, source, "state.value = explode()");
        let target = call_span(&semantic, source, "target()");
        assert!(!prove_event_completion_before_event(
            &semantic, assignment, target
        ));
    }

    #[test]
    fn proves_completed_event_before_nested_function_expression_execution() {
        let source =
            "function outer() { proto.run = function() {}; holder.f = function() { target(); }; }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let install = assignment_span(&semantic, source, "proto.run = function() {}");
        let target = call_span(&semantic, source, "target()");
        assert!(prove_event_completion_before_nested_event(
            &semantic, install, target
        ));
    }

    #[test]
    fn nested_completion_rejects_function_declaration_bridge() {
        let source =
            "function outer() { proto.run = function() {}; function later() { target(); } }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let install = assignment_span(&semantic, source, "proto.run = function() {}");
        let target = call_span(&semantic, source, "target()");
        assert!(!prove_event_completion_before_nested_event(
            &semantic, install, target
        ));
    }

    #[test]
    fn nested_completion_rejects_function_value_created_before_required_event() {
        let source =
            "function outer() { holder.f = function() { target(); }; proto.run = function() {}; }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let install = assignment_span(&semantic, source, "proto.run = function() {}");
        let target = call_span(&semantic, source, "target()");
        assert!(!prove_event_completion_before_nested_event(
            &semantic, install, target
        ));
    }

    #[test]
    fn proves_required_event_before_target() {
        let source = "function f() { init(); target(); }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let init = call_span(&semantic, source, "init()");
        let target = call_span(&semantic, source, "target()");
        assert!(prove_events_before_event(&semantic, &[init], target));
    }

    #[test]
    fn proves_required_event_before_target_inside_loop() {
        let source = "function f(flag) { while (flag) { init(); target(); } }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let init = call_span(&semantic, source, "init()");
        let target = call_span(&semantic, source, "target()");
        assert!(prove_events_before_event(&semantic, &[init], target));
    }

    #[test]
    fn rejects_target_before_required_event_inside_loop() {
        let source = "function f(flag) { while (flag) { target(); init(); } }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let init = call_span(&semantic, source, "init()");
        let target = call_span(&semantic, source, "target()");
        assert!(!prove_events_before_event(&semantic, &[init], target));
    }

    #[test]
    fn rejects_optional_required_event_before_target() {
        let source = "function f(flag) { if (flag) init(); target(); }";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = semantic(&parsed.program);
        let init = call_span(&semantic, source, "init()");
        let target = call_span(&semantic, source, "target()");
        assert!(!prove_events_before_event(&semantic, &[init], target));
    }

    #[test]
    fn proves_straight_line_event_before_later_barrier() {
        assert!(prove(
            "function f() { target(); barrier(); }",
            "target()",
            &["barrier()"]
        ));
    }

    #[test]
    fn rejects_straight_line_barrier_before_event() {
        assert!(!prove(
            "function f() { barrier(); target(); }",
            "target()",
            &["barrier()"]
        ));
    }

    #[test]
    fn proves_mutually_exclusive_barrier_cannot_precede_event() {
        assert!(prove(
            "function f(flag) { if (flag) { barrier(); } else { target(); } }",
            "target()",
            &["barrier()"]
        ));
    }

    #[test]
    fn proves_mutually_exclusive_switch_case_barrier_cannot_precede_event() {
        assert!(prove(
            "function f(value) { switch (value) { case 1: barrier(); break; case 2: target(); break; default: break; } }",
            "target()",
            &["barrier()"]
        ));
    }

    #[test]
    fn rejects_relevant_loop_backedge() {
        assert!(!prove(
            "function f(flag) { while (flag) { barrier(); flag = false; } target(); }",
            "target()",
            &["barrier()"]
        ));
    }

    #[test]
    fn rejects_optional_barrier_that_can_precede_event() {
        assert!(!prove(
            "function f(flag) { if (flag) barrier(); target(); }",
            "target()",
            &["barrier()"]
        ));
    }

    #[test]
    fn rejects_barrier_from_nested_function() {
        assert!(!prove(
            "function f() { function nested() { barrier(); } target(); }",
            "target()",
            &["barrier()"]
        ));
    }
}
