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

pub fn exact_u64(value: f64) -> Option<u64> {
    if !value.is_finite() || value < 0.0 {
        return None;
    }
    if value == 0.0 {
        return Some(0);
    }

    let bits = value.to_bits();
    let exponent_bits = u16::try_from((bits >> 52) & 0x07ff).ok()?;
    let exponent = i32::from(exponent_bits) - 1023;
    if !(0..=63).contains(&exponent) {
        return None;
    }

    let significand = (bits & ((1_u64 << 52) - 1)) | (1_u64 << 52);
    if exponent >= 52 {
        significand.checked_shl(u32::try_from(exponent - 52).ok()?)
    } else {
        let shift = u32::try_from(52 - exponent).ok()?;
        let fractional_mask = (1_u64 << shift) - 1;
        (significand & fractional_mask == 0).then_some(significand >> shift)
    }
}

pub fn exact_i64(value: f64) -> Option<i64> {
    if value == 0.0 {
        return Some(0);
    }
    let negative = value.is_sign_negative();
    let magnitude = exact_u64(value.abs())?;
    if negative {
        if magnitude == 1_u64 << 63 {
            Some(i64::MIN)
        } else {
            i64::try_from(magnitude).ok()?.checked_neg()
        }
    } else {
        i64::try_from(magnitude).ok()
    }
}

pub fn numeric_u64(expr: &Expression<'_>) -> Option<u64> {
    match expr {
        Expression::NumericLiteral(number) => exact_u64(number.value),
        Expression::ParenthesizedExpression(paren) => numeric_u64(&paren.expression),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{exact_i64, exact_u64};

    #[test]
    fn exact_u64_checks_ieee754_boundaries() {
        assert_eq!(exact_u64(0.0), Some(0));
        assert_eq!(exact_u64(-0.0), Some(0));
        assert_eq!(exact_u64(42.0), Some(42));
        assert_eq!(exact_u64(42.5), None);
        assert_eq!(exact_u64(-1.0), None);
        assert_eq!(exact_u64(f64::NAN), None);
        assert_eq!(exact_u64(f64::INFINITY), None);
        assert_eq!(
            exact_u64(18_446_744_073_709_549_568.0),
            Some(18_446_744_073_709_549_568_u64)
        );
        assert_eq!(exact_u64(18_446_744_073_709_551_616.0), None);
        assert_eq!(exact_i64(-9_223_372_036_854_775_808.0), Some(i64::MIN));
        assert_eq!(exact_i64(9_223_372_036_854_775_808.0), None);
    }
}
