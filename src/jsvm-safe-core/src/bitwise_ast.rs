//! Shared exact AST interpretation used by both bitwise proofs.
//! Only syntactic parentheses and checked integer literals are interpreted;
//! this deliberately does not assume arbitrary JavaScript expression purity.
use crate::numeric::exact_i64;
use oxc_ast::ast::Expression;

pub fn unparen<'e, 'a>(mut expr: &'e Expression<'a>) -> &'e Expression<'a> {
    while let Expression::ParenthesizedExpression(parenthesized) = expr {
        expr = &parenthesized.expression;
    }
    expr
}

pub fn integer_literal(expr: &Expression<'_>) -> Option<i64> {
    match unparen(expr) {
        Expression::NumericLiteral(number) => exact_i64(number.value),
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "-" => {
            integer_literal(&unary.argument)?.checked_neg()
        }
        _ => None,
    }
}
