//! Proven registry-accessor call results flowing into local indirect invocations.
//! An accessor may project a lazy cell: its result is NOT necessarily a handler.
use crate::cfg_order::{prove_event_before_barriers, prove_event_completion_before_event};
use crate::forwarding_semantics::ProvenRegistryReadCall;
use oxc_ast::{
    ast::{AssignmentTarget, BindingPattern, Expression},
    AstKind,
};
use oxc_semantic::Semantic;
use oxc_span::{GetSpan, Span};
use oxc_syntax::{node::NodeId, symbol::SymbolId};
use serde::Serialize;
use std::collections::HashSet;
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
fn has_dynamic_scope(
    s: &Semantic<'_>,
    context: NodeId,
    budget: &WorkBudget,
) -> Result<bool, BudgetExceeded> {
    for (id, n) in s.nodes().iter_enumerated() {
        budget.consume(1)?;
        if owner(s, id) != Some(context) {
            continue;
        }
        match n.kind() {
            AstKind::WithStatement(_) => return Ok(true),
            AstKind::CallExpression(c) if matches!(&c.callee,Expression::Identifier(i) if i.name=="eval") => {
                return Ok(true)
            }
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
    for id in s.scoping().get_resolved_reference_ids(d.symbol) {
        budget.consume(1)?;
        let r = s.scoping().get_reference(*id);
        if owner(s, r.node_id()) != Some(d.context) {
            return Ok(false);
        }
        if !r.is_write() {
            continue;
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
    let mut locals = HashSet::new();
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
                locals.insert(symbol);
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
                definite_accessor_result: locals.contains(&symbol)
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
        Ok(analyze(&ret.semantic, &reads, &b).test_value("edges")?)
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
