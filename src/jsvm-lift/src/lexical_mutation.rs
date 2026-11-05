//! Generic scope-aware lexical binding mutation hazards.
//!
//! A resolved binding with one visible write may still be changed by direct
//! eval in its lexical environment. This audit never infers runtime execution.

use oxc_ast::{ast::Expression, AstKind};
use oxc_semantic::Semantic;
use oxc_span::{GetSpan, Span};
use oxc_syntax::symbol::SymbolId;
use work_budget::{BudgetExceeded, WorkBudget};

/// Dynamic source mutation site; enclosing function is provenance only.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LexicalDynamicSourceSite {
    pub span: Span,
    pub enclosing_function: Option<Span>,
}

/// Syntactic threats to any resolved lexical binding's value.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LexicalBindingMutationAudit {
    pub explicit_writes: Vec<Span>,
    pub unique_expected_write: bool,
    pub lexical_direct_eval_calls: Vec<LexicalDynamicSourceSite>,
    pub lexical_with_statements: Vec<LexicalDynamicSourceSite>,
    pub root_scope_binding: bool,
    /// No syntax-level hazards; never implies initialization or call ordering.
    pub source_mutation_isolated: bool,
}

/// Direct eval is sensitive to JavaScript grammar. Parentheses are fine, but
/// a comma sequence makes evaluation indirect and cannot write lexical locals.
fn syntactic_direct_eval(expression: &Expression<'_>) -> bool {
    match expression {
        Expression::Identifier(identifier) => identifier.name == "eval",
        Expression::ParenthesizedExpression(parenthesized) => {
            syntactic_direct_eval(&parenthesized.expression)
        }
        _ => false,
    }
}

fn enclosing_function(semantic: &Semantic<'_>, node: &oxc_semantic::AstNode<'_>) -> Option<Span> {
    semantic
        .nodes()
        .ancestors(node.id())
        .find_map(|parent| match parent.kind() {
            AstKind::Function(function) => Some(function.span),
            AstKind::ArrowFunctionExpression(function) => Some(function.span),
            _ => None,
        })
}

/// Audit mutation hazards for any resolved lexical binding.
///
/// Shadowing and unrelated scopes do not contaminate the result. Nested
/// functions are considered possible hazards without asserting their call.
/// Budget exhaustion never silently means no hazards.
pub fn audit_lexical_binding_mutation(
    semantic: &Semantic<'_>,
    symbol: SymbolId,
    expected_write: Span,
    budget: &WorkBudget,
) -> Result<LexicalBindingMutationAudit, BudgetExceeded> {
    let scoping = semantic.scoping();
    let name = scoping.symbol_name(symbol);
    let mut explicit_writes = Vec::new();
    for reference_id in scoping.get_resolved_reference_ids(symbol) {
        budget.consume(1)?;
        let reference = scoping.get_reference(*reference_id);
        if reference.is_write() {
            explicit_writes.push(semantic.nodes().get_node(reference.node_id()).kind().span());
        }
    }
    explicit_writes.sort_unstable_by_key(|span| (span.start, span.end));
    explicit_writes.dedup();
    let unique_expected_write = matches!(explicit_writes.as_slice(), [write]
        if expected_write.start <= write.start && write.end <= expected_write.end);

    let mut lexical_direct_eval_calls = Vec::new();
    let mut lexical_with_statements = Vec::new();
    for node in semantic.nodes().iter() {
        budget.consume(1)?;
        if scoping.find_binding(node.scope_id(), name.into()) != Some(symbol) {
            continue;
        }
        let site = LexicalDynamicSourceSite {
            span: node.span(),
            enclosing_function: enclosing_function(semantic, node),
        };
        match node.kind() {
            AstKind::CallExpression(call)
                if !call.optional && syntactic_direct_eval(&call.callee) =>
            {
                lexical_direct_eval_calls.push(site);
            }
            AstKind::WithStatement(_) => lexical_with_statements.push(site),
            _ => {}
        }
    }
    let key = |site: &LexicalDynamicSourceSite| (site.span.start, site.span.end);
    lexical_direct_eval_calls.sort_unstable_by_key(key);
    lexical_direct_eval_calls.dedup();
    lexical_with_statements.sort_unstable_by_key(key);
    lexical_with_statements.dedup();
    let root_scope_binding = scoping.symbol_scope_id(symbol) == scoping.root_scope_id();
    let source_mutation_isolated = unique_expected_write
        && lexical_direct_eval_calls.is_empty()
        && lexical_with_statements.is_empty()
        && !root_scope_binding;
    Ok(LexicalBindingMutationAudit {
        explicit_writes,
        unique_expected_write,
        lexical_direct_eval_calls,
        lexical_with_statements,
        root_scope_binding,
        source_mutation_isolated,
    })
}

#[cfg(test)]
mod tests {
    use super::{audit_lexical_binding_mutation, syntactic_direct_eval};
    use crate::test_support::{source_offset, TestResult, TestValue};
    use oxc_allocator::Allocator;
    use oxc_ast::ast::{Expression, Statement};
    use oxc_semantic::SemanticBuilder;
    use oxc_span::{SourceType, Span};
    use rolldown_redox::ecmascript::parse_program;
    use work_budget::WorkBudget;

    #[test]
    fn direct_eval_is_not_indirect_sequence_eval() -> TestResult {
        let samples = [
            ("eval('x')", true),
            ("(eval)('x')", true),
            ("((eval))('x')", true),
            ("(0,eval)('x')", false),
            ("(eval,eval)('x')", false),
        ];
        for (source, expected) in samples {
            let allocator = Allocator::default();
            let parsed = parse_program(&allocator, source, SourceType::cjs());
            assert!(parsed.is_clean(), "{source}");
            let statement = match parsed.program.body.first() {
                Some(Statement::ExpressionStatement(statement)) => Some(statement),
                _ => None,
            }
            .test_value("eval expression statement")?;
            let call = match &statement.expression {
                Expression::CallExpression(call) => Some(call),
                _ => None,
            }
            .test_value("eval call expression")?;
            assert_eq!(syntactic_direct_eval(&call.callee), expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn tracks_hazard_lexical_context_and_enclosing_function() -> TestResult {
        let source = r#"
            (function() {
                let target;
                target = function() { return 1; };
                function danger(s) { return eval(s); }
                function noDanger(s) { return (0,eval)(s); }
                function shadow(target, s) { return eval(s); }
            })();
            (function() {
                let target;
                function unrelated(s) { return eval(s); }
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let target = scoping
            .scope_descendants_from_root()
            .flat_map(|id| scoping.get_bindings(id).values().copied())
            .filter(|symbol| scoping.symbol_name(*symbol) == "target")
            .min_by_key(|symbol| scoping.symbol_span(*symbol).start)
            .test_value("first target binding")?;
        let start = source_offset(source, "target = function", "assignment")?;
        let audit = audit_lexical_binding_mutation(
            &semantic.semantic,
            target,
            Span::new(start, start + 28),
            &WorkBudget::unlimited("lexical-audit-test"),
        )
        .test_value("lexical mutation audit")?;
        assert!(audit.unique_expected_write);
        assert_eq!(audit.lexical_direct_eval_calls.len(), 1);
        assert!(audit.lexical_direct_eval_calls[0]
            .enclosing_function
            .is_some());
        assert!(!audit.source_mutation_isolated);
        Ok(())
    }
}
