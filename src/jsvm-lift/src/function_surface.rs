//! Source-bound, non-execution behavior inventory for a recovered JS function.
//!
//! Every event retains exact source offsets. Nested closures have a separate
//! lexical depth: their bodies are not treated as executed parent code.
use oxc_ast::{ast::Expression, AstKind};
use oxc_semantic::Semantic;
use oxc_span::{GetSpan, Span};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FunctionSurfaceEvent {
    pub kind: &'static str,
    pub span: [u32; 2],
    pub lexical_depth: usize,
    /// Preview only; exact source spans remain authoritative.
    pub expression: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FunctionExternalReference {
    pub name: String,
    pub declaration: Option<[u32; 2]>,
    pub reads: usize,
    pub writes: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
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

type ExternalRefKey = (String, Option<(u32, u32)>);
type ExternalRefCounts = (usize, usize);

#[derive(Debug)]
struct SurfaceAccumulator {
    span: Span,
    nested_functions: Vec<[u32; 2]>,
    references: BTreeMap<ExternalRefKey, ExternalRefCounts>,
    calls: Vec<FunctionSurfaceEvent>,
    effects: Vec<FunctionSurfaceEvent>,
}

impl SurfaceAccumulator {
    fn new(span: Span) -> Self {
        Self {
            span,
            nested_functions: Vec::new(),
            references: BTreeMap::new(),
            calls: Vec::new(),
            effects: Vec::new(),
        }
    }

    fn add_event(
        &mut self,
        kind: &'static str,
        event_span: Span,
        expression: Option<String>,
        lexical_depth: usize,
        is_call: bool,
    ) {
        let item = FunctionSurfaceEvent {
            kind,
            span: range(event_span),
            lexical_depth,
            expression,
        };
        if is_call {
            self.calls.push(item);
        } else {
            self.effects.push(item);
        }
    }

    fn observe(&mut self, source: &str, semantic: &Semantic<'_>, kind: AstKind<'_>, depth: usize) {
        match kind {
            AstKind::Function(function) => self.nested_functions.push(range(function.span)),
            AstKind::ArrowFunctionExpression(function) => {
                self.nested_functions.push(range(function.span));
            }
            AstKind::IdentifierReference(identifier) => {
                let resolved = identifier
                    .reference_id
                    .get()
                    .map(|reference_id| semantic.scoping().get_reference(reference_id));
                let declaration = resolved
                    .and_then(|reference| reference.symbol_id())
                    .map(|symbol| semantic.scoping().symbol_span(symbol));
                if declaration
                    .is_some_and(|decl| self.span.start <= decl.start && decl.end <= self.span.end)
                {
                    return;
                }
                let key = (
                    identifier.name.to_string(),
                    declaration.map(|decl| (decl.start, decl.end)),
                );
                let entry = self.references.entry(key).or_default();
                if resolved.is_none_or(|reference| reference.is_read()) {
                    entry.0 += 1;
                }
                if resolved.is_some_and(|reference| reference.is_write()) {
                    entry.1 += 1;
                }
            }
            AstKind::CallExpression(call) => {
                self.add_event(
                    call_kind(&call.callee),
                    call.span,
                    preview(source, call.callee.span()),
                    depth,
                    true,
                );
                if !call.optional && is_ident(&call.callee, "eval") {
                    self.add_event("direct_eval_candidate", call.span, None, depth, false);
                }
                if is_ident(&call.callee, "Function") {
                    self.add_event(
                        "function_constructor_candidate",
                        call.span,
                        None,
                        depth,
                        false,
                    );
                }
            }
            AstKind::NewExpression(expr) => {
                self.add_event(
                    "constructor_call",
                    expr.span,
                    preview(source, expr.callee.span()),
                    depth,
                    true,
                );
                if is_ident(&expr.callee, "Function") {
                    self.add_event(
                        "function_constructor_candidate",
                        expr.span,
                        None,
                        depth,
                        false,
                    );
                }
            }
            AstKind::ImportExpression(expr) => {
                self.add_event("dynamic_import", expr.span, None, depth, false);
            }
            AstKind::WithStatement(expr) => {
                self.add_event("dynamic_with", expr.span, None, depth, false);
            }
            AstKind::AssignmentExpression(expr) => {
                if let Some(kind) = member_target_kind(&expr.left) {
                    self.add_event(
                        kind,
                        expr.span,
                        preview(source, expr.left.span()),
                        depth,
                        false,
                    );
                }
            }
            AstKind::UpdateExpression(expr) => {
                if matches!(
                    &expr.argument,
                    oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(_)
                        | oxc_ast::ast::SimpleAssignmentTarget::StaticMemberExpression(_)
                        | oxc_ast::ast::SimpleAssignmentTarget::PrivateFieldExpression(_)
                ) {
                    self.add_event(
                        "member_update",
                        expr.span,
                        preview(source, expr.argument.span()),
                        depth,
                        false,
                    );
                }
            }
            AstKind::UnaryExpression(expr) if expr.operator.as_str() == "delete" => {
                self.add_event(
                    "delete",
                    expr.span,
                    preview(source, expr.argument.span()),
                    depth,
                    false,
                );
            }
            AstKind::ThrowStatement(expr) => {
                self.add_event("throw", expr.span, None, depth, false);
            }
            _ => {}
        }
    }

    fn finish(self) -> FunctionSourceSurface {
        let external_references = self
            .references
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
        FunctionSourceSurface {
            function: range(self.span),
            nested_functions: self.nested_functions,
            external_references,
            calls: self.calls,
            effects: self.effects,
            executed_behavior_proven: false,
        }
    }
}

/// Inventory many selected functions in one pass over the semantic AST.
///
/// This scales with total AST nodes and lexical nesting depth, rather than
/// rescanning the entire AST separately for each recovered handler. Source
/// spans are resolved to unique function nodes before collecting evidence;
/// missing/ambiguous spans produce None, not a speculative match. Results
/// preserve the requested order, including duplicates.
pub fn analyze_function_source_surfaces(
    source: &str,
    semantic: &Semantic<'_>,
    spans: &[Span],
    budget: &WorkBudget,
) -> Result<Vec<Option<FunctionSourceSurface>>, BudgetExceeded> {
    if spans.is_empty() {
        return Ok(Vec::new());
    }
    let nodes = semantic.nodes();
    let requested = spans
        .iter()
        .map(|span| (span.start, span.end))
        .collect::<BTreeSet<_>>();
    let mut matching_nodes = BTreeMap::<(u32, u32), Vec<_>>::new();

    for (id, node) in nodes.iter_enumerated() {
        budget.consume(1)?;
        let span = node.kind().span();
        if requested.contains(&(span.start, span.end))
            && matches!(
                node.kind(),
                AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
            )
        {
            matching_nodes
                .entry((span.start, span.end))
                .or_default()
                .push(id);
        }
    }

    let mut target_by_node = HashMap::new();
    let mut target_by_span = BTreeMap::new();
    let mut accumulators = Vec::new();
    for (span, candidate_nodes) in matching_nodes {
        let [node_id] = candidate_nodes.as_slice() else {
            continue;
        };
        let index = accumulators.len();
        target_by_node.insert(*node_id, index);
        target_by_span.insert(span, index);
        accumulators.push(SurfaceAccumulator::new(Span::new(span.0, span.1)));
    }

    if !accumulators.is_empty() {
        for (id, node) in nodes.iter_enumerated() {
            budget.consume(1)?;
            let mut depth = 0;
            for ancestor in nodes.ancestor_ids(id) {
                budget.consume(1)?;
                if let Some(&target_index) = target_by_node.get(&ancestor) {
                    accumulators[target_index].observe(source, semantic, node.kind(), depth);
                }
                if matches!(
                    nodes.kind(ancestor),
                    AstKind::Function(_) | AstKind::ArrowFunctionExpression(_)
                ) {
                    depth += 1;
                }
            }
        }
    }

    let completed = accumulators
        .into_iter()
        .map(SurfaceAccumulator::finish)
        .collect::<Vec<_>>();
    Ok(spans
        .iter()
        .map(|span| {
            target_by_span
                .get(&(span.start, span.end))
                .map(|&index| completed[index].clone())
        })
        .collect())
}

/// Inspect one exact function, using the same implementation as batch mode.
pub fn analyze_function_source_surface(
    source: &str,
    semantic: &Semantic<'_>,
    span: Span,
    budget: &WorkBudget,
) -> Result<Option<FunctionSourceSurface>, BudgetExceeded> {
    Ok(
        analyze_function_source_surfaces(source, semantic, &[span], budget)?
            .into_iter()
            .next()
            .flatten(),
    )
}

#[cfg(test)]
mod tests {
    use super::{analyze_function_source_surface, analyze_function_source_surfaces};
    use oxc_allocator::Allocator;
    use oxc_ast::AstKind;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;
    use work_budget::WorkBudget;

    #[test]
    fn batch_preserves_exact_function_order_and_nested_semantics() -> anyhow::Result<()> {
        let source = r#"
            const x = 1;
            function outer(a) {
                function inner(z) { return eval(z) + a + x; }
                return inner(a);
            }
            function unrelated() { return eval("0"); }
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .build(&parsed.program);
        let spans = semantic
            .semantic
            .nodes()
            .iter()
            .filter_map(|node| match node.kind() {
                AstKind::Function(function) => Some(function.span),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(spans.len(), 3);
        let named_span = |name: &str| {
            spans
                .iter()
                .find(|span| {
                    source
                        .get(span.start as usize..span.end as usize)
                        .is_some_and(|text| text.starts_with(name))
                })
                .copied()
                .ok_or_else(|| anyhow::anyhow!("named exact function"))
        };
        let inner_span = named_span("function inner")?;
        let outer_span = named_span("function outer")?;
        let unrelated_span = named_span("function unrelated")?;
        let missing = oxc_span::Span::new(1, 2);
        let requested = [inner_span, outer_span, missing, outer_span, unrelated_span];
        let budget = WorkBudget::unlimited("function-surface-batch-test");
        let batch =
            analyze_function_source_surfaces(source, &semantic.semantic, &requested, &budget)?;
        assert_eq!(batch.len(), requested.len());
        assert!(batch[2].is_none());
        assert_eq!(
            batch[1], batch[3],
            "duplicate span preserves identical evidence"
        );
        for (span, item) in requested.into_iter().zip(batch.iter()) {
            let single =
                analyze_function_source_surface(source, &semantic.semantic, span, &budget)?;
            assert_eq!(&single, item, "batch and singleton must agree");
        }
        let inner = batch[0].as_ref().ok_or_else(|| anyhow::anyhow!("inner"))?;
        assert_eq!(inner.function, [inner_span.start, inner_span.end]);
        assert_eq!(
            inner
                .effects
                .iter()
                .filter(|event| event.kind == "direct_eval_candidate" && event.lexical_depth == 0)
                .count(),
            1
        );
        let outer = batch[1].as_ref().ok_or_else(|| anyhow::anyhow!("outer"))?;
        assert_eq!(
            outer
                .effects
                .iter()
                .filter(|event| event.kind == "direct_eval_candidate" && event.lexical_depth == 1)
                .count(),
            1
        );
        assert!(outer.external_references.iter().any(|r| r.name == "x"));
        assert!(!outer.external_references.iter().any(|r| r.name == "a"));
        let unrelated = batch[4]
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("unrelated"))?;
        assert_eq!(
            unrelated
                .effects
                .iter()
                .filter(|e| e.kind == "direct_eval_candidate")
                .count(),
            1
        );
        assert!(unrelated.nested_functions.is_empty());
        assert!(
            analyze_function_source_surfaces(source, &semantic.semantic, &[], &budget)?.is_empty()
        );
        Ok(())
    }

    #[test]
    fn separates_nested_effects_and_external_binding_identity() -> anyhow::Result<()> {
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
            .ok_or_else(|| anyhow::anyhow!("handler"))?;
        let result = analyze_function_source_surface(
            source,
            &semantic.semantic,
            target,
            &WorkBudget::unlimited("function-surface-test"),
        )?
        .ok_or_else(|| anyhow::anyhow!("exact function"))?;
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
        Ok(())
    }
}
