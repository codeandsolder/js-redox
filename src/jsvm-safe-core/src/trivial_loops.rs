//! Simplify syntactically inert loops left by constant specialization.
//! This is not an arbitrary bounded-loop evaluator: it recognizes loops
//! whose precise number of iterations is established by their own AST.

use crate::fragment;
use oxc_ast::ast::{
    Expression, ForStatement, Statement, VariableDeclaration, VariableDeclarationKind,
    WhileStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::GetSpan;

#[derive(Default)]
struct HoistingHazards {
    present: bool,
}

impl<'a> Visit<'a> for HoistingHazards {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        if declaration.kind == VariableDeclarationKind::Var {
            self.present = true;
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_function(
        &mut self,
        _function: &oxc_ast::ast::Function<'a>,
        _flags: oxc_syntax::scope::ScopeFlags,
    ) {
        // A dead function declaration can be observable under Annex B.
        self.present = true;
    }
}

#[derive(Default)]
struct ControlTransfers {
    present: bool,
}

impl<'a> Visit<'a> for ControlTransfers {
    fn visit_break_statement(&mut self, statement: &oxc_ast::ast::BreakStatement<'a>) {
        // A named break continues to target its label after unwrapping a
        // single-iteration loop. Only an unnamed break could have targeted
        // this loop and would change meaning when lifted into a block.
        if statement.label.is_none() {
            self.present = true;
        }
    }

    fn visit_continue_statement(&mut self, _statement: &oxc_ast::ast::ContinueStatement<'a>) {
        self.present = true;
    }
}

/// Discard a primitive literal statement only if it cannot be a directive.
pub(crate) fn inert_literal_statement(expr: &Expression<'_>) -> bool {
    match expr {
        Expression::BooleanLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::BigIntLiteral(_) => true,
        Expression::ParenthesizedExpression(paren) => inert_literal_statement(&paren.expression),
        // String literals can be directive prologues; never remove them.
        _ => false,
    }
}

fn literal_bool(expr: &Expression<'_>, expected: bool) -> bool {
    match expr {
        Expression::BooleanLiteral(value) => value.value == expected,
        Expression::ParenthesizedExpression(paren) => literal_bool(&paren.expression, expected),
        _ => false,
    }
}

/// Only literal false; this preserves JS var-hoisting and Annex-B function
/// declarations by declining bodies where removing the syntax changes binding.
pub(crate) fn never_entered_while(it: &WhileStatement<'_>) -> Option<String> {
    if !literal_bool(&it.test, false) {
        return None;
    }
    let mut hazards = HoistingHazards::default();
    hazards.visit_statement(&it.body);
    (!hazards.present).then_some("{}".to_owned())
}

/// For (0; true; true) { ...; break; } executes its body exactly once unless
/// an earlier unlabeled break/continue targets the for statement. Require an
/// immediate final unlabeled break, with no earlier unlabeled break or continue.
/// Keep the original enclosing lexical block.
pub(crate) fn single_iteration_for(it: &ForStatement<'_>, source: &str) -> Option<String> {
    let init = it.init.as_ref()?.as_expression()?;
    if !matches!(init, Expression::NumericLiteral(_))
        || !literal_bool(it.test.as_ref()?, true)
        || !literal_bool(it.update.as_ref()?, true)
    {
        return None;
    }
    let Statement::BlockStatement(block) = &it.body else {
        return None;
    };
    let (last, prefix) = block.body.split_last()?;
    let Statement::BreakStatement(last_break) = last else {
        return None;
    };
    if last_break.label.is_some() {
        return None;
    }
    let mut flow = ControlTransfers::default();
    for stmt in prefix {
        flow.visit_statement(stmt);
    }
    if flow.present {
        return None;
    }
    let content = prefix
        .iter()
        .map(|stmt| fragment(source, stmt.span()))
        .collect::<Vec<_>>()
        .join("\n");
    Some(format!("{{\n{content}\n}}"))
}

#[cfg(test)]
mod tests {
    use crate::deobfuscate;
    use work_budget::{BudgetExceeded, WorkBudget};

    fn rewritten(input: &str) -> Result<String, BudgetExceeded> {
        Ok(
            deobfuscate(input, 12, &WorkBudget::unlimited("trivial-loops"))?
                .map_or_else(|| input.to_owned(), |result| result.source),
        )
    }

    #[test]
    fn drops_inert_primitive_statements_but_preserves_directives() -> Result<(), BudgetExceeded> {
        let source = "function f(){'use strict';false;123;null;return this;}";
        let result = rewritten(source)?;
        assert!(result.contains("'use strict'"), "{result}");
        assert!(!result.contains("false;"), "{result}");
        assert!(!result.contains("123;"), "{result}");
        assert!(!result.contains("null;"), "{result}");
        Ok(())
    }

    #[test]
    fn removes_unreachable_body_without_hoisted_binding() -> Result<(), BudgetExceeded> {
        let result = rewritten("function f(){let x=2;while(false){x=9;}return x;}")?;
        assert!(!result.contains("while"), "{result}");
        assert!(result.contains("return x"), "{result}");

        let hoisted = rewritten("function f(){while(false){var x=9;}return typeof x;}")?;
        assert!(hoisted.contains("while(false)"), "{hoisted}");
        Ok(())
    }

    #[test]
    fn unwraps_exactly_one_iteration_but_not_continue_or_inner_break() -> Result<(), BudgetExceeded>
    {
        let source = "function f(x){for(0;true;true){x++;break;}return x;}";
        let result = rewritten(source)?;
        assert!(!result.contains("for(0;"), "{result}");
        assert!(result.contains("x++"), "{result}");

        let labeled = rewritten(
            "function f(x){for(0;true;true){done:{if(x){break done;}x++;}break;}return x;}",
        )?;
        assert!(!labeled.contains("for("), "{labeled}");
        assert!(labeled.contains("break done"), "{labeled}");

        for input in [
            "function f(x){for(0;true;true){if(x)continue;x++;break;}return x;}",
            "function f(x){for(0;true;true){if(x)break;x++;break;}return x;}",
            "function f(x){for(x=0;true;true){x++;break;}return x;}",
        ] {
            let result = rewritten(input)?;
            assert!(result.contains("for("), "{result}");
        }
        Ok(())
    }
}
