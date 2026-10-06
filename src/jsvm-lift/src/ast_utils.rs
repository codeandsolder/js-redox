use oxc_ast::ast::{AssignmentTarget, Expression};

pub fn expr_ident<'a>(expr: &'a Expression<'a>) -> Option<&'a str> {
    match expr {
        Expression::Identifier(id) => Some(id.name.as_str()),
        Expression::ParenthesizedExpression(paren) => expr_ident(&paren.expression),
        _ => None,
    }
}

pub fn target_ident<'a>(target: &'a AssignmentTarget<'a>) -> Option<&'a str> {
    match target {
        AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.as_str()),
        _ => None,
    }
}

pub fn numeric_u64(expr: &Expression<'_>) -> Option<u64> {
    match expr {
        Expression::NumericLiteral(number)
            if number.value.is_finite() && number.value >= 0.0 && number.value.fract() == 0.0 =>
        {
            Some(number.value as u64)
        }
        Expression::ParenthesizedExpression(paren) => numeric_u64(&paren.expression),
        _ => None,
    }
}
