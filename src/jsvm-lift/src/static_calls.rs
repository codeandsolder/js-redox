//! Conservative syntactic direct-call graph for a single ECMAScript source.
//!
//! Edges mean "this call expression names this source-defined function".
//! They do not prove that either the call expression or its target executes:
//! branches, lexical mutation, callbacks, dynamic scope, and cross-script
//! bindings remain independent obligations.
use oxc_ast::{
    ast::{Expression, FunctionType},
    AstKind,
};
use oxc_semantic::Semantic;
use oxc_span::{GetSpan, Span};
use oxc_syntax::symbol::SymbolId;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StaticCallEdge {
    /// Null is this script's top-level execution context.
    pub caller: Option<[u32; 2]>,
    pub callee: [u32; 2],
    pub call: [u32; 2],
    /// direct_inline_function or lexical_binding_candidate
    pub resolution: &'static str,
    pub constructor: bool,
    pub optional: bool,
    /// Some ancestor has conditional/loop/try semantics.
    pub path_dependent: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct StaticUnresolvedCall {
    pub caller: Option<[u32; 2]>,
    pub call: [u32; 2],
    pub callee_expression: [u32; 2],
    pub callee_kind: &'static str,
    pub optional: bool,
    pub constructor: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct StaticCallGraph {
    pub schema: &'static str,
    pub functions: Vec<[u32; 2]>,
    pub direct_edges: Vec<StaticCallEdge>,
    pub unresolved_calls: Vec<StaticUnresolvedCall>,
    /// A MAY-reachability over the explicit static edges from script top level.
    /// Not a proof of runtime execution or of stable lexical bindings.
    pub possibly_reachable_from_top_level: Vec<[u32; 2]>,
}

fn pair(span: Span) -> [u32; 2] {
    [span.start, span.end]
}

fn unwrap_parentheses<'a, 'b>(mut value: &'b Expression<'a>) -> &'b Expression<'a> {
    while let Expression::ParenthesizedExpression(parenthesized) = value {
        value = &parenthesized.expression;
    }
    value
}

fn function_literal(value: &Expression<'_>) -> Option<Span> {
    match unwrap_parentheses(value) {
        Expression::FunctionExpression(fun) if fun.body.is_some() => Some(fun.span),
        Expression::ArrowFunctionExpression(fun) => Some(fun.span),
        _ => None,
    }
}

fn callee_kind(value: &Expression<'_>) -> &'static str {
    match unwrap_parentheses(value) {
        Expression::Identifier(_) => "identifier",
        Expression::StaticMemberExpression(_) => "static_member",
        Expression::ComputedMemberExpression(_) => "computed_member",
        Expression::PrivateFieldExpression(_) => "private_member",
        Expression::SequenceExpression(_) => "sequence",
        Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_) => "inline",
        _ => "expression",
    }
}

fn ref_symbol(value: &Expression<'_>, semantic: &Semantic<'_>) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = unwrap_parentheses(value) else {
        return None;
    };
    let reference_id = identifier.reference_id.get()?;
    semantic.scoping().get_reference(reference_id).symbol_id()
}

fn enclosing_context_and_guard(
    semantic: &Semantic<'_>,
    node_id: oxc_syntax::node::NodeId,
) -> (Option<[u32; 2]>, bool) {
    let nodes = semantic.nodes();
    let mut guarded = false;
    for ancestor in nodes.ancestor_ids(node_id) {
        match nodes.kind(ancestor) {
            AstKind::Function(fun) => return (Some(pair(fun.span)), guarded),
            AstKind::ArrowFunctionExpression(fun) => return (Some(pair(fun.span)), guarded),
            AstKind::IfStatement(_)
            | AstKind::ConditionalExpression(_)
            | AstKind::LogicalExpression(_)
            | AstKind::ForStatement(_)
            | AstKind::ForInStatement(_)
            | AstKind::ForOfStatement(_)
            | AstKind::WhileStatement(_)
            | AstKind::DoWhileStatement(_)
            | AstKind::SwitchStatement(_)
            | AstKind::TryStatement(_)
            | AstKind::CatchClause(_) => guarded = true,
            _ => {}
        }
    }
    (None, guarded)
}

/// Build source-local direct-call candidates with exact semantic symbol
/// identity. The graph deliberately does not assert value immutability,
/// cross-script resolution, callback execution, or runtime reachability.
///
/// A symbol gets a candidate only when exactly one function definition is
/// visible in this source's declarations/variable initializers. Any distinct
/// definitions invalidate the direct edge rather than guessing a target.
pub fn analyze_static_calls(
    semantic: &Semantic<'_>,
    budget: &WorkBudget,
) -> Result<StaticCallGraph, BudgetExceeded> {
    let nodes = semantic.nodes();
    let mut definitions = HashMap::<SymbolId, BTreeSet<(u32, u32)>>::new();
    let mut functions = BTreeSet::<(u32, u32)>::new();
    for node in nodes.iter() {
        budget.consume(1)?;
        match node.kind() {
            AstKind::Function(fun) if fun.body.is_some() => {
                functions.insert((fun.span.start, fun.span.end));
                if fun.r#type == FunctionType::FunctionDeclaration {
                    if let Some(symbol) = fun.id.as_ref().and_then(|id| id.symbol_id.get()) {
                        definitions
                            .entry(symbol)
                            .or_default()
                            .insert((fun.span.start, fun.span.end));
                    }
                }
            }
            AstKind::ArrowFunctionExpression(fun) => {
                functions.insert((fun.span.start, fun.span.end));
            }
            AstKind::VariableDeclarator(decl) => {
                if let Some((symbol, function)) = decl
                    .id
                    .get_binding_identifier()
                    .and_then(|ident| ident.symbol_id.get())
                    .zip(decl.init.as_ref().and_then(function_literal))
                {
                    definitions
                        .entry(symbol)
                        .or_default()
                        .insert((function.start, function.end));
                }
            }
            _ => {}
        }
    }

    let mut direct_edges = Vec::new();
    let mut unresolved_calls = Vec::new();
    for (node_id, node) in nodes.iter_enumerated() {
        budget.consume(1)?;
        let (call, callee, optional, constructor) = match node.kind() {
            AstKind::CallExpression(expr) => (expr.span, &expr.callee, expr.optional, false),
            AstKind::NewExpression(expr) => (expr.span, &expr.callee, false, true),
            _ => continue,
        };
        let (caller, path_dependent) = enclosing_context_and_guard(semantic, node_id);
        let target = function_literal(callee)
            .map(|span| (span, "direct_inline_function"))
            .or_else(|| {
                let symbol = ref_symbol(callee, semantic)?;
                let matches = definitions.get(&symbol)?;
                if matches.len() != 1 {
                    return None;
                }
                let &(start, end) = matches.iter().next()?;
                Some((Span::new(start, end), "lexical_binding_candidate"))
            });
        if let Some((target, resolution)) = target {
            direct_edges.push(StaticCallEdge {
                caller,
                callee: pair(target),
                call: pair(call),
                resolution,
                constructor,
                optional,
                path_dependent: path_dependent || optional,
            });
        } else {
            unresolved_calls.push(StaticUnresolvedCall {
                caller,
                call: pair(call),
                callee_expression: pair(callee.span()),
                callee_kind: callee_kind(callee),
                optional,
                constructor,
            });
        }
    }
    direct_edges.sort_by_key(|edge| (edge.call, edge.callee));
    unresolved_calls.sort_by_key(|call| call.call);

    let mut adjacency = BTreeMap::<Option<[u32; 2]>, Vec<[u32; 2]>>::new();
    for edge in &direct_edges {
        adjacency.entry(edge.caller).or_default().push(edge.callee);
    }
    let mut reachable = BTreeSet::<[u32; 2]>::new();
    let mut pending = VecDeque::from([None]);
    while let Some(caller) = pending.pop_front() {
        budget.consume(1)?;
        for callee in adjacency.get(&caller).into_iter().flatten() {
            if reachable.insert(*callee) {
                pending.push_back(Some(*callee));
            }
        }
    }
    Ok(StaticCallGraph {
        schema: "jsvm-static-calls/v1",
        functions: functions.into_iter().map(|(a, b)| [a, b]).collect(),
        direct_edges,
        unresolved_calls,
        possibly_reachable_from_top_level: reachable.into_iter().collect(),
    })
}

#[cfg(test)]
mod tests {
    use super::analyze_static_calls;
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;
    use work_budget::WorkBudget;

    #[test]
    fn maps_direct_iifes_and_lexical_calls_but_not_callbacks_as_execution() -> anyhow::Result<()> {
        let code = r#"
            const handler = function() { return 1; };
            function init() {
              if (maybe) handler();
              const callback = () => 2;
              register(callback);
              (function inline() { return handler(); })();
            }
            init();
            function unused() { handler(); }
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, code, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .build(&parsed.program);
        let graph = analyze_static_calls(
            &semantic.semantic,
            &WorkBudget::unlimited("test-static-calls"),
        )?;
        assert_eq!(graph.functions.len(), 5);
        assert!(graph
            .direct_edges
            .iter()
            .any(|e| e.caller.is_none() && e.resolution == "lexical_binding_candidate"));
        assert!(graph
            .direct_edges
            .iter()
            .any(|e| e.resolution == "direct_inline_function"));
        assert!(graph
            .unresolved_calls
            .iter()
            .any(|e| e.callee_kind == "identifier"));
        assert_eq!(graph.possibly_reachable_from_top_level.len(), 3);
        assert!(graph.direct_edges.iter().any(|e| e.path_dependent));
        Ok(())
    }

    #[test]
    fn shadowed_identifiers_remain_separate() -> anyhow::Result<()> {
        let code = "function f(){}function g(f){f();} f();";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, code, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .build(&parsed.program);
        let graph = analyze_static_calls(
            &semantic.semantic,
            &WorkBudget::unlimited("test-static-shadow"),
        )?;
        assert_eq!(graph.direct_edges.len(), 1);
        assert_eq!(graph.unresolved_calls.len(), 1);
        Ok(())
    }
}
