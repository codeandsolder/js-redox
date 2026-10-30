use oxc_ast::AstKind;
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

fn prove_required_before_event(
    semantic: &Semantic<'_>,
    function_node: NodeId,
    event_block: BlockNodeId,
    event: Span,
    required: Span,
) -> bool {
    let Some(cfg) = semantic.cfg() else {
        return false;
    };
    let nodes = semantic.nodes();
    let Some(required_node) = deepest_exact_span_node(semantic, required) else {
        return false;
    };
    if enclosing_function(semantic, required_node) != Some(function_node) {
        return false;
    }
    let required_block = nodes.cfg_id(required_node);
    let function_entry = nodes.cfg_id(function_node);
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

/// Prove that every supplied `required` event executes before `event` on every
/// acyclic path that reaches `event` in the same function invocation.
///
/// This is a conditional dominance-style proof over Oxc's CFG. It fails closed
/// on cross-function requirements, unresolved spans, or relevant loop
/// backedges.
pub fn prove_events_before_event(semantic: &Semantic<'_>, required: &[Span], event: Span) -> bool {
    let Some(event_node) = deepest_exact_span_node(semantic, event) else {
        return false;
    };
    let Some(function_node) = enclosing_function(semantic, event_node) else {
        return false;
    };
    let event_block = semantic.nodes().cfg_id(event_node);
    !required.is_empty()
        && required.iter().all(|required| {
            *required != event
                && prove_required_before_event(
                    semantic,
                    function_node,
                    event_block,
                    event,
                    *required,
                )
        })
}

#[cfg(test)]
mod tests {
    use super::{prove_event_before_barriers, prove_events_before_event};
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
