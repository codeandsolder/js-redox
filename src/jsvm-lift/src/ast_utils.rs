use crate::numeric::exact_u64;
use oxc_ast::ast::{AssignmentTarget, Expression};

#[must_use = "Use the returned identifier; absence means this is not an identifier expression"]
pub fn expr_ident<'a>(expr: &'a Expression<'a>) -> Option<&'a str> {
    match expr {
        Expression::Identifier(id) => Some(id.name.as_str()),
        Expression::ParenthesizedExpression(paren) => expr_ident(&paren.expression),
        _ => None,
    }
}

#[must_use = "Use the returned identifier; absence means this is not an identifier target"]
pub fn target_ident<'a>(target: &'a AssignmentTarget<'a>) -> Option<&'a str> {
    match target {
        AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.as_str()),
        _ => None,
    }
}

#[must_use = "Use the exact integer when present; absence means it cannot be proven"]
pub fn numeric_u64(expr: &Expression<'_>) -> Option<u64> {
    match expr {
        Expression::NumericLiteral(number) => exact_u64(number.value),
        Expression::ParenthesizedExpression(paren) => numeric_u64(&paren.expression),
        _ => None,
    }
}
