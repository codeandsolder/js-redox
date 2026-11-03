//! Proven registry-accessor call results flowing into local indirect invocations.
//! An accessor may project a lazy cell: its result is NOT necessarily a handler.
use crate::cfg_order::{prove_event_before_barriers, prove_event_completion_before_event};
use crate::forwarding_semantics::{ProvenLazyRegistryReadCall, ProvenRegistryReadCall};
use crate::registry_identity::ProvenOriginRegistryReadCall;
use oxc_ast::{
    ast::{AssignmentTarget, BindingPattern, Expression},
    AstKind,
};
use oxc_semantic::Semantic;
use oxc_span::{GetSpan, Span};
use oxc_syntax::{node::NodeId, symbol::SymbolId};
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RegistryAccessorResultUse {
    pub binding: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
    pub accessor_call_start: u32,
    pub accessor_call_end: u32,
    pub indirect_call_start: u32,
    pub indirect_call_end: u32,
    /// Only proves retention of the accessor's return value, not handler identity.
    pub definite_accessor_result: bool,
}
/// A proven lazy-registry *accessor shape* whose returned value might reach
/// an indirect call. The fast path calls the cell update method; the slow path
/// returns a property of that cell after an update. This is NOT a proof that
/// either result equals the registered handler.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct LazyRegistryAccessorResultUse {
    pub result: RegistryAccessorResultUse,
    pub registry_path: Vec<String>,
    pub fast_probe_property: String,
    pub update_method: String,
    pub slow_projection_property: String,
    pub slow_selector_start: u32,
    pub slow_selector_end: u32,
}

/// Join independent, span-exact proofs. No structural candidate is promoted
/// to a definite result merely because its accessor has a lazy-cell shape.
pub fn join_lazy_accessor_results(
    uses: &[RegistryAccessorResultUse],
    lazy_reads: &[ProvenLazyRegistryReadCall],
    budget: &WorkBudget,
) -> Result<Vec<LazyRegistryAccessorResultUse>, BudgetExceeded> {
    budget.checkpoint()?;
    let mut sites = HashMap::new();
    for read in lazy_reads {
        budget.consume(1)?;
        sites.insert((read.read.call_start, read.read.call_end), read);
    }
    let mut result = Vec::new();
    for use_site in uses {
        budget.consume(1)?;
        let Some(read) = sites.get(&(use_site.accessor_call_start, use_site.accessor_call_end))
        else {
            continue;
        };
        result.push(LazyRegistryAccessorResultUse {
            result: use_site.clone(),
            registry_path: read.read.registry_path.clone(),
            fast_probe_property: read.probe_property.clone(),
            update_method: read.update_property.clone(),
            slow_projection_property: read.projection_property.clone(),
            slow_selector_start: read.selector_start,
            slow_selector_end: read.selector_end,
        });
    }
    Ok(result)
}

/// A structural lazy accessor-to-call relation whose registry receiver also
/// has an exact allocation/constructor origin at the SAME accessor call.
/// The dynamic key may remain unknown. This does NOT prove a returned handler.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ExactOriginLazyAccessorResultUse {
    pub lazy: LazyRegistryAccessorResultUse,
    pub origin_allocation_start: u32,
    pub origin_allocation_end: u32,
    pub origin_constructor_start: u32,
    pub origin_constructor_end: u32,
    pub exact_key: Option<i64>,
}

/// Require unique, nonconflicting exact-origin facts for a specific call, and
/// preserve the registry path established by the independent lazy analysis.
pub fn join_exact_origin_lazy_accessor_results(
    lazy_uses: &[LazyRegistryAccessorResultUse],
    origin_reads: &[ProvenOriginRegistryReadCall],
    budget: &WorkBudget,
) -> Result<Vec<ExactOriginLazyAccessorResultUse>, BudgetExceeded> {
    budget.checkpoint()?;
    let mut by_call = HashMap::new();
    for origin in origin_reads {
        budget.consume(1)?;
        let site = (origin.read.call_start, origin.read.call_end);
        match by_call.entry(site) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(Some(origin));
            }
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                if entry.get().is_some_and(|previous| *previous != origin) {
                    entry.insert(None);
                }
            }
        }
    }
    let mut joined = Vec::new();
    for lazy in lazy_uses {
        budget.consume(1)?;
        let site = (
            lazy.result.accessor_call_start,
            lazy.result.accessor_call_end,
        );
        let Some(origin) = by_call.get(&site).and_then(|entry| *entry) else {
            continue;
        };
        if origin.read.registry_path != lazy.registry_path {
            continue;
        }
        joined.push(ExactOriginLazyAccessorResultUse {
            lazy: lazy.clone(),
            origin_allocation_start: origin.origin.allocation_start,
            origin_allocation_end: origin.origin.allocation_end,
            origin_constructor_start: origin.origin.constructor_start,
            origin_constructor_end: origin.origin.constructor_end,
            exact_key: origin.exact_key,
        });
    }
    Ok(joined)
}

struct Source {
    symbol: SymbolId,
    assignment: Span,
    accessor: Span,
    context: NodeId,
    target: Option<Span>,
}
fn reference_symbol(
    s: &Semantic<'_>,
    id: &oxc_ast::ast::IdentifierReference<'_>,
) -> Option<SymbolId> {
    s.scoping()
        .get_reference(id.reference_id.get()?)
        .symbol_id()
}
fn owner(s: &Semantic<'_>, id: NodeId) -> Option<NodeId> {
    s.nodes().ancestors_enumerated(id).find_map(|(id, n)| {
        matches!(
            n.kind(),
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
        )
        .then_some(id)
    })
}
fn source_call(e: &Expression<'_>, sites: &HashSet<(u32, u32)>) -> Option<Span> {
    match e {
        Expression::ParenthesizedExpression(p) => source_call(&p.expression, sites),
        Expression::CallExpression(c) if sites.contains(&(c.span.start, c.span.end)) => {
            Some(c.span)
        }
        _ => None,
    }
}
/// Bindings captured from outer functions are not local to this invocation.
/// Ask Oxc for the declaration node instead of approximating scope ownership
/// with a file-global set of declared symbols.
fn locally_owned_symbol(s: &Semantic<'_>, symbol: SymbolId, context: NodeId) -> bool {
    owner(s, s.scoping().symbol_declaration(symbol)) == Some(context)
}
fn is_direct_eval_callee(expression: &Expression<'_>) -> bool {
    match expression {
        Expression::Identifier(id) => id.name == "eval",
        Expression::ParenthesizedExpression(p) => is_direct_eval_callee(&p.expression),
        _ => false,
    }
}
fn has_dynamic_scope(
    s: &Semantic<'_>,
    context: NodeId,
    budget: &WorkBudget,
) -> Result<bool, BudgetExceeded> {
    for (id, n) in s.nodes().iter_enumerated() {
        budget.consume(1)?;
        // A nested function can run direct eval and mutate a captured
        // local without producing a resolved write reference. Scan the
        // entire lexical subtree, not only this function's immediate body.
        if !s
            .nodes()
            .ancestor_ids(id)
            .any(|ancestor| ancestor == context)
        {
            continue;
        }
        match n.kind() {
            AstKind::WithStatement(_) => return Ok(true),
            AstKind::CallExpression(c) if is_direct_eval_callee(&c.callee) => return Ok(true),
            _ => {}
        }
    }
    Ok(false)
}
fn is_definite(
    s: &Semantic<'_>,
    d: &Source,
    call: Span,
    budget: &WorkBudget,
) -> Result<bool, BudgetExceeded> {
    if !prove_event_completion_before_event(s, d.assignment, call)
        || has_dynamic_scope(s, d.context, budget)?
    {
        return Ok(false);
    }
    // Sloppy parameter/var redeclarations can alias mapped arguments
    // entries. A write to arguments[index] is not a symbol write.
    let parameter_binding = match s.nodes().kind(d.context) {
        AstKind::Function(f) => f.params.items.iter().any(|p| {
            matches!(&p.pattern, BindingPattern::BindingIdentifier(id) if id.symbol_id.get() == Some(d.symbol))
        }),
        AstKind::ArrowFunctionExpression(f) => f.params.items.iter().any(|p| {
            matches!(&p.pattern, BindingPattern::BindingIdentifier(id) if id.symbol_id.get() == Some(d.symbol))
        }),
        _ => false,
    };
    if parameter_binding {
        for (id, node) in s.nodes().iter_enumerated() {
            budget.consume(1)?;
            if s.nodes()
                .ancestor_ids(id)
                .any(|ancestor| ancestor == d.context)
                && matches!(node.kind(), AstKind::IdentifierReference(name) if name.name == "arguments")
            {
                return Ok(false);
            }
        }
    }
    for id in s.scoping().get_resolved_reference_ids(d.symbol) {
        budget.consume(1)?;
        let r = s.scoping().get_reference(*id);
        if !r.is_write() {
            continue;
        }
        if owner(s, r.node_id()) != Some(d.context) {
            // Captured writes are unsafe. Captured reads alone are fine.
            return Ok(false);
        }
        let barrier = s.nodes().get_node(r.node_id()).kind().span();
        if Some(barrier) == d.target {
            continue;
        }
        budget.consume(1)?;
        if !prove_event_completion_before_event(s, barrier, d.assignment)
            && !prove_event_before_barriers(s, call, &[barrier])
        {
            return Ok(false);
        }
    }
    Ok(true)
}
/// Non-definite edges are structural candidates, never confirmed dispatch.
/// Definite edges prove a local call-result reaching definition, but do not
/// assign any semantics to the registry accessor's returned object.
pub fn analyze(
    s: &Semantic<'_>,
    reads: &[ProvenRegistryReadCall],
    budget: &WorkBudget,
) -> Result<Vec<RegistryAccessorResultUse>, BudgetExceeded> {
    budget.checkpoint()?;
    let sites = reads
        .iter()
        .map(|r| (r.call_start, r.call_end))
        .collect::<HashSet<_>>();
    let mut defs = Vec::new();
    let mut calls = Vec::new();
    for (id, n) in s.nodes().iter_enumerated() {
        budget.consume(1)?;
        let Some(context) = owner(s, id) else {
            continue;
        };
        match n.kind() {
            AstKind::VariableDeclarator(d) => {
                let BindingPattern::BindingIdentifier(b) = &d.id else {
                    continue;
                };
                let Some(symbol) = b.symbol_id.get() else {
                    continue;
                };
                if let Some(accessor) = d.init.as_ref().and_then(|e| source_call(e, &sites)) {
                    defs.push(Source {
                        symbol,
                        assignment: d.span,
                        accessor,
                        context,
                        target: None,
                    });
                }
            }
            AstKind::AssignmentExpression(a)
                if a.operator == oxc_syntax::operator::AssignmentOperator::Assign =>
            {
                let AssignmentTarget::AssignmentTargetIdentifier(b) = &a.left else {
                    continue;
                };
                let Some(symbol) = reference_symbol(s, b) else {
                    continue;
                };
                if let Some(accessor) = source_call(&a.right, &sites) {
                    defs.push(Source {
                        symbol,
                        assignment: a.span,
                        accessor,
                        context,
                        target: Some(b.span),
                    });
                }
            }
            AstKind::CallExpression(c) => {
                let Expression::Identifier(b) = &c.callee else {
                    continue;
                };
                if let Some(symbol) = reference_symbol(s, b) {
                    calls.push((symbol, b.name.to_string(), c.span, context));
                }
            }
            _ => {}
        }
    }
    let mut edges = Vec::new();
    for (symbol, binding, call, context) in calls {
        for d in &defs {
            budget.consume(1)?;
            if d.symbol != symbol || d.context != context || d.assignment.end > call.start {
                continue;
            }
            edges.push(RegistryAccessorResultUse {
                binding: binding.clone(),
                assignment_start: d.assignment.start,
                assignment_end: d.assignment.end,
                accessor_call_start: d.accessor.start,
                accessor_call_end: d.accessor.end,
                indirect_call_start: call.start,
                indirect_call_end: call.end,
                definite_accessor_result: locally_owned_symbol(s, symbol, context)
                    && is_definite(s, d, call, budget)?,
            });
        }
    }
    edges.sort_by_key(|e| {
        (
            e.indirect_call_start,
            e.assignment_start,
            e.accessor_call_start,
        )
    });
    edges.dedup();
    Ok(edges)
}
#[cfg(test)]
mod tests {
    use super::analyze;
    use crate::forwarding_semantics::structurally_proven_registry_read_calls;
    use crate::test_support::{TestFailure, TestResult, TestValue};
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;
    use work_budget::{BudgetLimits, WorkBudget};

    const ACCESSOR: &str = "function read(s,k) { return s.T[k]; }\n";
    fn inspect(body: &str) -> Result<Vec<super::RegistryAccessorResultUse>, TestFailure> {
        let source = format!("{ACCESSOR}{body}");
        let alloc = Allocator::default();
        let parsed = parse_program(&alloc, &source, SourceType::cjs());
        assert!(parsed.is_clean());
        let ret = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(ret.diagnostics.is_empty());
        let b = WorkBudget::unlimited("call-value-tests");
        let reads =
            structurally_proven_registry_read_calls(&parsed.program, ret.semantic.scoping(), &b)
                .test_value("reads")?;
        assert!(!reads.is_empty());
        analyze(&ret.semantic, &reads, &b).test_value("edges")
    }
    #[test]
    fn stable_result_is_definite() -> TestResult {
        let e = inspect("function run(s,k) { let h=read(s,k); h(); }")?;
        assert_eq!(e.len(), 1);
        assert!(e[0].definite_accessor_result);
        Ok(())
    }
    #[test]
    fn branch_and_capture_are_not_definite() -> TestResult {
        let e = inspect("function run(s,k,c){ let h=read(s,k); if(c) h=other; h(); }")?;
        assert_eq!(e.len(), 1);
        assert!(!e[0].definite_accessor_result);
        let e = inspect("function run(s,k){ let h=read(s,k); function f(){h=other;} f(); h(); }")?;
        assert_eq!(e.len(), 1);
        assert!(!e[0].definite_accessor_result);
        Ok(())
    }
    #[test]
    fn shadowing_and_eval_do_not_prove_dispatch() -> TestResult {
        assert!(
            inspect("function run(s,k){ let h=read(s,k); { const h=other; h(); } }")?.is_empty()
        );
        let e = inspect("function run(s,k){ let h=read(s,k); eval('h=other'); h(); }")?;
        assert_eq!(e.len(), 1);
        assert!(!e[0].definite_accessor_result);
        Ok(())
    }
    #[test]
    fn nested_dynamic_scope_is_not_a_definite_source() -> TestResult {
        let e = inspect(
            "function run(s,k){ let h=read(s,k); function change(){eval('h=other')} change(); h(); }"
        )?;
        assert_eq!(e.len(), 1);
        assert!(!e[0].definite_accessor_result);
        let e = inspect(
            "function run(s,k){ let h=read(s,k); function change(){(eval)('h=other')} change(); h(); }"
        )?;
        assert_eq!(e.len(), 1);
        assert!(!e[0].definite_accessor_result);
        Ok(())
    }

    #[test]
    fn mapped_arguments_parameter_alias_is_not_definite() -> TestResult {
        let e = inspect("function run(h,s,k){ var h=read(s,k); arguments[0]=other; h(); }")?;
        assert_eq!(e.len(), 1);
        assert!(!e[0].definite_accessor_result);
        Ok(())
    }

    #[test]
    fn nested_read_only_capture_is_preserved() -> TestResult {
        let e = inspect(
            "function run(s,k){ let h=read(s,k); function peek(){return h;} peek(); h(); }",
        )?;
        assert_eq!(e.len(), 1);
        assert!(e[0].definite_accessor_result);
        Ok(())
    }

    #[test]
    fn definite_source_accepts_locally_owned_parameter() -> TestResult {
        let e = inspect("function run(h,s,k){ h=read(s,k); h(); }")?;
        assert_eq!(e.len(), 1);
        assert!(e[0].definite_accessor_result);
        Ok(())
    }

    #[test]
    fn outer_binding_is_not_local_to_nested_assignment() -> TestResult {
        let e = inspect(
            "function outer(){let h=other; function inner(s,k){h=read(s,k);h();} inner(x,y);}",
        )?;
        assert_eq!(e.len(), 1);
        assert!(!e[0].definite_accessor_result);
        Ok(())
    }

    #[test]
    fn joins_lazy_shape_without_inventing_handler_identity() -> TestResult {
        use super::join_lazy_accessor_results;
        use crate::forwarding_semantics::structurally_proven_lazy_registry_read_calls;
        let source = r#"
            function get(state, index, cell) {
                if (cell = state.T[index], cell === undefined) throw Error();
                if (cell.value) return cell.create();
                return (cell.create(index * index + 3), cell).prototype;
            }
            function run(s, n, flag) {
                let h = get(s, n);
                if (flag) h = fallback;
                h();
            }
        "#;
        let alloc = Allocator::default();
        let parsed = parse_program(&alloc, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let built = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(built.diagnostics.is_empty());
        let b = WorkBudget::unlimited("lazy-result-join");
        let reads =
            structurally_proven_registry_read_calls(&parsed.program, built.semantic.scoping(), &b)
                .test_value("structural reads")?;
        let lazy = structurally_proven_lazy_registry_read_calls(
            &parsed.program,
            built.semantic.scoping(),
            &b,
        )
        .test_value("lazy reads")?;
        assert_eq!(lazy.len(), 1);
        let uses = analyze(&built.semantic, &reads, &b).test_value("result uses")?;
        assert_eq!(uses.len(), 1);
        let joined = join_lazy_accessor_results(&uses, &lazy, &b).test_value("joined")?;
        assert_eq!(joined.len(), 1);
        assert_eq!(joined[0].registry_path, ["T"]);
        assert_eq!(joined[0].fast_probe_property, "value");
        assert_eq!(joined[0].update_method, "create");
        assert_eq!(joined[0].slow_projection_property, "prototype");
        assert!(!joined[0].result.definite_accessor_result);
        let b = WorkBudget::new("zero-lazy-join", BudgetLimits::work(0));
        assert!(join_lazy_accessor_results(&uses, &lazy, &b).is_err());
        Ok(())
    }

    #[test]
    fn unrelated_accessor_does_not_inherit_lazy_shape() -> TestResult {
        use super::join_lazy_accessor_results;
        use crate::forwarding_semantics::structurally_proven_lazy_registry_read_calls;
        let source = r#"
            function get(state, index, cell) {
                if (cell = state.T[index], cell === undefined) throw Error();
                if (cell.value) return cell.create();
                return (cell.create(index * index + 3), cell).prototype;
            }
            function plain(state, index) { return state.T[index]; }
            function run(s, n) { let a = get(s, n); let b = plain(s, n); a(); b(); }
        "#;
        let alloc = Allocator::default();
        let parsed = parse_program(&alloc, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let built = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(built.diagnostics.is_empty());
        let b = WorkBudget::unlimited("lazy-result-mismatch");
        let reads =
            structurally_proven_registry_read_calls(&parsed.program, built.semantic.scoping(), &b)
                .test_value("structural reads")?;
        let lazy = structurally_proven_lazy_registry_read_calls(
            &parsed.program,
            built.semantic.scoping(),
            &b,
        )
        .test_value("lazy reads")?;
        assert_eq!(lazy.len(), 1);
        let uses = analyze(&built.semantic, &reads, &b).test_value("result uses")?;
        assert_eq!(uses.len(), 2);
        let joined = join_lazy_accessor_results(&uses, &lazy, &b).test_value("joined")?;
        assert_eq!(joined.len(), 1);
        assert_eq!(joined[0].result.binding, "a");
        Ok(())
    }

    #[test]
    fn exact_origin_lazy_join_requires_same_call_and_registry_path() -> TestResult {
        use super::{
            join_exact_origin_lazy_accessor_results, LazyRegistryAccessorResultUse,
            RegistryAccessorResultUse,
        };
        use crate::forwarding_semantics::ProvenRegistryReadCall;
        use crate::registry_identity::{ProvenOriginRegistryReadCall, ProvenRegistryObjectOrigin};
        let lazy = LazyRegistryAccessorResultUse {
            result: RegistryAccessorResultUse {
                binding: "callable".into(),
                assignment_start: 1,
                assignment_end: 15,
                accessor_call_start: 5,
                accessor_call_end: 15,
                indirect_call_start: 30,
                indirect_call_end: 40,
                definite_accessor_result: false,
            },
            registry_path: vec!["handlers".into()],
            fast_probe_property: "loaded".into(),
            update_method: "refresh".into(),
            slow_projection_property: "current".into(),
            slow_selector_start: 100,
            slow_selector_end: 120,
        };
        let origin = ProvenOriginRegistryReadCall {
            read: ProvenRegistryReadCall {
                call_start: 5,
                call_end: 15,
                receiver_start: 7,
                receiver_end: 8,
                key_start: 9,
                key_end: 10,
                registry_path: vec!["handlers".into()],
            },
            origin: ProvenRegistryObjectOrigin {
                allocation_start: 500,
                allocation_end: 520,
                constructor_start: 400,
                constructor_end: 450,
            },
            exact_key: None,
        };
        let budget = WorkBudget::unlimited("origin lazy join");
        let joined = join_exact_origin_lazy_accessor_results(
            std::slice::from_ref(&lazy),
            std::slice::from_ref(&origin),
            &budget,
        )
        .test_value("origin joined")?;
        assert_eq!(joined.len(), 1);
        assert_eq!(joined[0].lazy, lazy);
        assert_eq!(joined[0].origin_allocation_start, 500);
        assert_eq!(joined[0].exact_key, None);
        let mut wrong_path = origin.clone();
        wrong_path.read.registry_path = vec!["unrelated".into()];
        assert!(join_exact_origin_lazy_accessor_results(
            std::slice::from_ref(&lazy),
            &[wrong_path],
            &budget,
        )
        .test_value("path reject")?
        .is_empty());
        let mut wrong_call = origin.clone();
        wrong_call.read.call_start = 6;
        assert!(join_exact_origin_lazy_accessor_results(
            std::slice::from_ref(&lazy),
            &[wrong_call],
            &budget,
        )
        .test_value("call reject")?
        .is_empty());
        let mut conflict = origin.clone();
        conflict.origin.allocation_start = 501;
        assert!(join_exact_origin_lazy_accessor_results(
            std::slice::from_ref(&lazy),
            &[origin.clone(), conflict],
            &budget,
        )
        .test_value("ambiguous origin reject")?
        .is_empty());
        let duplicate =
            join_exact_origin_lazy_accessor_results(&[lazy], &[origin.clone(), origin], &budget)
                .test_value("duplicate same proof")?;
        assert_eq!(duplicate.len(), 1);
        let empty_budget = WorkBudget::new("exhausted", BudgetLimits::work(0));
        assert!(join_exact_origin_lazy_accessor_results(&[], &[], &empty_budget,).is_err());
        Ok(())
    }

    #[test]
    fn budget_is_enforced() -> TestResult {
        let alloc = Allocator::default();
        let p = parse_program(&alloc, ACCESSOR, SourceType::cjs());
        let s = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&p.program);
        let b = WorkBudget::new("zero", BudgetLimits::work(0));
        assert!(analyze(&s.semantic, &[], &b).is_err());
        Ok(())
    }
}
