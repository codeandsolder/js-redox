//! Source-bound, non-execution behavior inventory for a recovered JS function.
//!
//! Every event retains exact source offsets. Nested closures have a separate
//! lexical depth: their bodies are not treated as executed parent code.
use oxc_ast::{ast::Expression, AstKind};
use oxc_semantic::Semantic;
use oxc_span::{GetSpan, Span};
use serde::Serialize;
use std::collections::BTreeMap;
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Debug, Clone, Serialize)]
pub struct FunctionSurfaceEvent {
    pub kind: &'static str,
    pub span: [u32; 2],
    pub lexical_depth: usize,
    /// Preview only; exact source spans remain authoritative.
    pub expression: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FunctionExternalReference {
    pub name: String,
    pub declaration: Option<[u32; 2]>,
    pub reads: usize,
    pub writes: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct FunctionSourceSurface {
    pub function: [u32; 2],
    pub nested_functions: Vec<[u32; 2]>,
    pub external_references: Vec<FunctionExternalReference>,
    pub calls: Vec<FunctionSurfaceEvent>,
    pub effects: Vec<FunctionSurfaceEvent>,
    /// Source appearances do not prove a particular runtime path executed.
    pub executed_behavior_proven: bool,
}

fn range(span: Span) -> [u32; 2] {
    [span.start, span.end]
}

fn preview(source: &str, span: Span) -> Option<String> {
    let raw = source.get(span.start as usize..span.end as usize)?;
    let mut chars = raw.chars();
    let mut out = String::new();
    for _ in 0..160 {
        match chars.next() {
            Some(c) => out.push(c),
            None => return Some(out),
        }
    }
    if chars.next().is_some() {
        out.push('…');
    }
    Some(out)
}

fn strip_parens<'a, 'b>(mut expr: &'b Expression<'a>) -> &'b Expression<'a> {
    while let Expression::ParenthesizedExpression(parenthesized) = expr {
        expr = &parenthesized.expression;
    }
    expr
}

fn call_kind(expr: &Expression<'_>) -> &'static str {
    match strip_parens(expr) {
        Expression::Identifier(_) => "identifier_call",
        Expression::StaticMemberExpression(_) => "static_member_call",
        Expression::ComputedMemberExpression(_) => "computed_member_call",
        Expression::PrivateFieldExpression(_) => "private_member_call",
        Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_) => {
            "inline_function_call"
        }
        _ => "expression_call",
    }
}

fn is_ident(expr: &Expression<'_>, name: &str) -> bool {
    matches!(strip_parens(expr), Expression::Identifier(id) if id.name == name)
}

fn member_target_kind(target: &oxc_ast::ast::AssignmentTarget<'_>) -> Option<&'static str> {
    match target {
        oxc_ast::ast::AssignmentTarget::ComputedMemberExpression(_) => {
            Some("computed_member_write")
        }
        oxc_ast::ast::AssignmentTarget::StaticMemberExpression(_) => Some("static_member_write"),
        oxc_ast::ast::AssignmentTarget::PrivateFieldExpression(_) => Some("private_member_write"),
        _ => None,
    }
}

/// Resolve the exact function in an existing semantic AST and inventory source
/// behavior. This is a syntax and lexical-identity index, not execution or
/// side-effect proof. Returns None for an ambiguous or missing function span.
pub fn analyze_function_source_surface(
    source: &str,
    semantic: &Semantic<'_>,
    span: Span,
    budget: &WorkBudget,
) -> Result<Option<FunctionSourceSurface>, BudgetExceeded> {
    let nodes = semantic.nodes();
    let targets = nodes
        .iter_enumerated()
        .filter(|(_, node)| {
            node.kind().span() == span
                && matches!(
                    node.kind(),
                    AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
                )
        })
        .map(|(id, _)| id)
        .collect::<Vec<_>>();
    let [target] = targets.as_slice() else {
        return Ok(None);
    };
    let mut calls = Vec::new();
    let mut effects = Vec::new();
    let mut nested_functions = Vec::new();
    let mut references = BTreeMap::<(String, Option<(u32, u32)>), (usize, usize)>::new();

    for (id, node) in nodes.iter_enumerated() {
        budget.consume(1)?;
        let current = node.kind().span();
        if current.start < span.start || current.end > span.end || id == *target {
            continue;
        }
        let mut depth = 0_usize;
        let mut belongs = nodes.parent_id(id) == *target;
        for ancestor in nodes.ancestor_ids(id) {
            if ancestor == *target {
                belongs = true;
                break;
            }
            if matches!(
                nodes.kind(ancestor),
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            ) {
                depth += 1;
            }
        }
        if !belongs {
            continue;
        }

        let mut event = |kind, event_span: Span, expression: Option<String>, is_call: bool| {
            let item = FunctionSurfaceEvent {
                kind,
                span: range(event_span),
                lexical_depth: depth,
                expression,
            };
            if is_call {
                calls.push(item);
            } else {
                effects.push(item);
            }
        };
        match node.kind() {
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) => {
                nested_functions.push(range(current));
            }
            AstKind::IdentifierReference(identifier) => {
                let resolved = identifier
                    .reference_id
                    .get()
                    .map(|reference_id| semantic.scoping().get_reference(reference_id));
                let declaration = resolved
                    .and_then(|reference| reference.symbol_id())
                    .map(|symbol| semantic.scoping().symbol_span(symbol));
                if declaration.is_some_and(|decl| span.start <= decl.start && decl.end <= span.end)
                {
                    continue;
                }
                let key = (
                    identifier.name.to_string(),
                    declaration.map(|decl| (decl.start, decl.end)),
                );
                let entry = references.entry(key).or_default();
                if resolved.is_none_or(|reference| reference.is_read()) {
                    entry.0 += 1;
                }
                if resolved.is_some_and(|reference| reference.is_write()) {
                    entry.1 += 1;
                }
            }
            AstKind::CallExpression(call) => {
                event(
                    call_kind(&call.callee),
                    call.span,
                    preview(source, call.callee.span()),
                    true,
                );
                if !call.optional && is_ident(&call.callee, "eval") {
                    event("direct_eval_candidate", call.span, None, false);
                }
                if is_ident(&call.callee, "Function") {
                    event("function_constructor_candidate", call.span, None, false);
                }
            }
            AstKind::NewExpression(expr) => {
                event(
                    "constructor_call",
                    expr.span,
                    preview(source, expr.callee.span()),
                    true,
                );
                if is_ident(&expr.callee, "Function") {
                    event("function_constructor_candidate", expr.span, None, false);
                }
            }
            AstKind::ImportExpression(expr) => event("dynamic_import", expr.span, None, false),
            AstKind::WithStatement(expr) => event("dynamic_with", expr.span, None, false),
            AstKind::AssignmentExpression(expr) => {
                if let Some(kind) = member_target_kind(&expr.left) {
                    event(kind, expr.span, preview(source, expr.left.span()), false);
                }
            }
            AstKind::UpdateExpression(expr) => {
                if matches!(
                    &expr.argument,
                    oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(_)
                        | oxc_ast::ast::SimpleAssignmentTarget::StaticMemberExpression(_)
                        | oxc_ast::ast::SimpleAssignmentTarget::PrivateFieldExpression(_)
                ) {
                    event(
                        "member_update",
                        expr.span,
                        preview(source, expr.argument.span()),
                        false,
                    );
                }
            }
            AstKind::UnaryExpression(expr) if expr.operator.as_str() == "delete" => {
                event(
                    "delete",
                    expr.span,
                    preview(source, expr.argument.span()),
                    false,
                );
            }
            AstKind::ThrowStatement(expr) => event("throw", expr.span, None, false),
            _ => {}
        }
    }

    let external_references = references
        .into_iter()
        .map(
            |((name, declaration), (reads, writes))| FunctionExternalReference {
                name,
                declaration: declaration.map(|(start, end)| [start, end]),
                reads,
                writes,
            },
        )
        .collect();
    Ok(Some(FunctionSourceSurface {
        function: range(span),
        nested_functions,
        external_references,
        calls,
        effects,
        executed_behavior_proven: false,
    }))
}

#[cfg(test)]
mod tests {
    use super::analyze_function_source_surface;
    use oxc_allocator::Allocator;
    use oxc_ast::AstKind;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;
    use work_budget::WorkBudget;

    #[test]
    fn separates_nested_effects_and_external_binding_identity() {
        let source = r#"
            let external;
            const handler = function(arg) {
                const own = 1;
                fetch(external);
                arg.x = own;
                function nested(source) { return eval(source); }
                return nested;
            };
            function unrelated() { eval(external); }
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .build(&parsed.program);
        let target = semantic
            .semantic
            .nodes()
            .iter()
            .find_map(|node| {
                if let AstKind::Function(function) = node.kind() {
                    if source
                        .get(function.span.start as usize..function.span.end as usize)
                        .is_some_and(|text| text.starts_with("function(arg)"))
                    {
                        return Some(function.span);
                    }
                }
                None
            })
            .expect("handler");
        let result = analyze_function_source_surface(
            source,
            &semantic.semantic,
            target,
            &WorkBudget::unlimited("function-surface-test"),
        )
        .expect("budget")
        .expect("exact function");
        let evals = result
            .effects
            .iter()
            .filter(|e| e.kind == "direct_eval_candidate")
            .collect::<Vec<_>>();
        assert_eq!(evals.len(), 1);
        assert_eq!(evals[0].lexical_depth, 1);
        assert_eq!(
            result
                .calls
                .iter()
                .filter(|c| c.kind == "identifier_call")
                .count(),
            2
        );
        assert_eq!(
            result
                .effects
                .iter()
                .filter(|e| e.kind == "static_member_write")
                .count(),
            1
        );
        assert!(result
            .external_references
            .iter()
            .any(|r| r.name == "external" && r.reads == 1));
        assert!(result
            .external_references
            .iter()
            .any(|r| r.name == "fetch" && r.declaration.is_none()));
        assert!(!result.external_references.iter().any(|r| r.name == "own"));
        assert!(!result.external_references.iter().any(|r| r.name == "arg"));
        assert_eq!(result.nested_functions.len(), 1);
        assert!(!result.executed_behavior_proven);
    }
}
