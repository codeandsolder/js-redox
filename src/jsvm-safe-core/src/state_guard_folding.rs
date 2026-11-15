//! Fold a numeric-state guard into the branch that established its truth.
//!
//! Unlike replacing the original branch predicate with a copy, this moves
//! the guarded body into the selected arm. The original dynamic test is
//! evaluated exactly once, both numeric state assignments remain in place,
//! and the body stays in the same surrounding try/catch and function frame.
//! The two statements must be adjacent; no intervening user code may modify
//! the established numeric state.

use crate::{
    fragment,
    if_ladder_structure::exception_state_is_unaliased,
    statically_resolved_symbol,
    value_eval::{eval, inert_literal_value, Value},
};
use oxc_ast::ast::{
    AssignmentTarget, Expression, Statement, VariableDeclaration, VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::{GetSpan, Span};
use oxc_syntax::symbol::SymbolId;

fn unparen<'a>(expr: &'a Expression<'a>) -> &'a Expression<'a> {
    match expr {
        Expression::ParenthesizedExpression(paren) => unparen(&paren.expression),
        _ => expr,
    }
}

fn final_numeric_write(stmt: &Statement<'_>, scoping: &Scoping) -> Option<(SymbolId, f64)> {
    let last = match stmt {
        Statement::BlockStatement(block) => block.body.last()?,
        other => other,
    };
    let Statement::ExpressionStatement(expr) = last else {
        return None;
    };
    let Expression::AssignmentExpression(assign) = unparen(&expr.expression) else {
        return None;
    };
    if assign.operator.as_str() != "=" || !inert_literal_value(&assign.right) {
        return None;
    }
    let AssignmentTarget::AssignmentTargetIdentifier(id) = &assign.left else {
        return None;
    };
    let symbol = statically_resolved_symbol(scoping, id.reference_id.get()?)?;
    let Value::Number(number) = eval(&assign.right)? else {
        return None;
    };
    Some((symbol, number))
}

/// The state is proven to be a JavaScript Number by both branch assignments.
/// Compare against an inert primitive literal using actual JavaScript numeric
/// equality, respecting signed zero, NaN, strict/loose booleans and strings.
fn compared_number(expr: &Expression<'_>, strict: bool) -> Option<f64> {
    if !inert_literal_value(expr) {
        return None;
    }
    let value = eval(expr)?;
    match value {
        Value::Number(number) => Some(number),
        Value::String(_) | Value::Bool(_) if !strict => value.number(),
        _ => None,
    }
}

fn numeric_guard_label(test: &Expression<'_>, scoping: &Scoping) -> Option<(SymbolId, f64)> {
    let Expression::BinaryExpression(bin) = unparen(test) else {
        return None;
    };
    let strict = match bin.operator.as_str() {
        "===" => true,
        "==" => false,
        _ => return None,
    };
    for (candidate, other) in [(&bin.left, &bin.right), (&bin.right, &bin.left)] {
        if let Expression::Identifier(id) = unparen(candidate) {
            let Some(reference) = id.reference_id.get() else {
                continue;
            };
            let Some(symbol) = statically_resolved_symbol(scoping, reference) else {
                continue;
            };
            if let Some(number) = compared_number(other, strict) {
                return Some((symbol, number));
            }
        }
    }
    None
}

#[derive(Default)]
struct AnnexBFunctionDeclarations {
    found: bool,
}

impl<'a> Visit<'a> for AnnexBFunctionDeclarations {
    fn visit_variable_declaration(&mut self, decl: &VariableDeclaration<'a>) {
        // Explicit Resource Management executes Symbol.dispose at the end
        // of the arm block. That can throw or change the state *after* its
        // final textual assignment, so the following guard is not constant.
        if !matches!(
            decl.kind,
            VariableDeclarationKind::Var
                | VariableDeclarationKind::Let
                | VariableDeclarationKind::Const
        ) {
            self.found = true;
        }
        walk::walk_variable_declaration(self, decl);
    }

    fn visit_statement(&mut self, stmt: &Statement<'a>) {
        if matches!(stmt, Statement::FunctionDeclaration(_)) {
            self.found = true;
        } else {
            walk::walk_statement(self, stmt);
        }
    }
    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: oxc_syntax::scope::ScopeFlags) {
    }
    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}
    fn visit_class(&mut self, _: &oxc_ast::ast::Class<'a>) {}
}

/// Return a source interval and its replacement plus the exact state binding.
/// The caller separately checks function-local binding safety and edit overlap.
///
/// The original arm bodies are retained inside their own nested scopes. The
/// sole guard body is moved into its matching arm, without duplication.
/// There are no new calls or comparisons, including for effectful test values.
pub(crate) fn fold_adjacent_state_guard(
    before: &Statement<'_>,
    after: &Statement<'_>,
    source: &str,
    scoping: &Scoping,
) -> Option<(Span, String, SymbolId)> {
    let Statement::IfStatement(branch) = before else {
        return None;
    };
    let Statement::IfStatement(guard) = after else {
        return None;
    };
    if guard.alternate.is_some() {
        return None;
    }
    let alternate = branch.alternate.as_ref()?;
    let (yes_symbol, yes_value) = final_numeric_write(&branch.consequent, scoping)?;
    let (no_symbol, no_value) = final_numeric_write(alternate, scoping)?;
    let (test_symbol, tested_value) = numeric_guard_label(&guard.test, scoping)?;
    if yes_symbol != no_symbol
        || yes_symbol != test_symbol
        || !exception_state_is_unaliased(yes_symbol, scoping)
    {
        return None;
    }
    let match_yes = yes_value == tested_value;
    let match_no = no_value == tested_value;
    // Only move an effect executed on exactly one path. Do not duplicate the
    // body or silently erase its declarations in always/never guards.
    if match_yes == match_no {
        return None;
    }
    let mut unsafe_functions = AnnexBFunctionDeclarations::default();
    unsafe_functions.visit_statement(&branch.consequent);
    unsafe_functions.visit_statement(alternate);
    unsafe_functions.visit_statement(&guard.consequent);
    if unsafe_functions.found {
        return None;
    }
    let test = fragment(source, branch.test.span());
    let yes = fragment(source, branch.consequent.span());
    let no = fragment(source, alternate.span());
    let effect = fragment(source, guard.consequent.span());
    let text = if match_yes {
        format!("if ({test}) {{\n{yes}\n{effect}\n}} else {{\n{no}\n}}")
    } else {
        format!("if ({test}) {{\n{yes}\n}} else {{\n{no}\n{effect}\n}}")
    };
    Some((
        Span::new(before.span().start, after.span().end),
        text,
        yes_symbol,
    ))
}
