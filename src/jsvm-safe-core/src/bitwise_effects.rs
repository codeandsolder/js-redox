//! Normalize arithmetic around bitwise complement without changing the
//! number, order, or timing of coercions of possibly effectful JS values.
//!
//! For Number bitwise operands, `~x ^ m = -1 - (x ^ m)`. `x` is evaluated
//! exactly once on either side, and `m` must be a primitive Number literal.
//! A BigInt-valued `x` throws on XOR with a Number on either side; no
//! successful BigInt path is changed. The other arithmetic operands must be
//! established primitive numbers so `+` cannot be string concatenation.
use crate::{fragment, numeric::exact_i64};
use oxc_ast::ast::{BinaryExpression, Expression};
use oxc_span::GetSpan;

fn unparen<'e, 'a>(mut expression: &'e Expression<'a>) -> &'e Expression<'a> {
    while let Expression::ParenthesizedExpression(parenthesized) = expression {
        expression = &parenthesized.expression;
    }
    expression
}

fn literal_int(expr: &Expression<'_>) -> Option<i64> {
    match unparen(expr) {
        Expression::NumericLiteral(n) => exact_i64(n.value),
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "-" => {
            literal_int(&unary.argument)?.checked_neg()
        }
        _ => None,
    }
}

/// Expression is known to yield a Number whenever its evaluation succeeds.
/// The checked numeric literal rules out successful BigInt-bitwise results.
fn number_bitwise(expr: &Expression<'_>) -> bool {
    let Expression::BinaryExpression(binary) = unparen(expr) else {
        return false;
    };
    matches!(
        binary.operator.as_str(),
        "&" | "|" | "^" | "<<" | ">>" | ">>>"
    ) && (literal_int(&binary.left).is_some() || literal_int(&binary.right).is_some())
}

pub(crate) fn normalize(expr: &BinaryExpression<'_>, source: &str) -> Option<String> {
    if expr.operator.as_str() != "+" {
        return None;
    }
    let Expression::BinaryExpression(lhs) = unparen(&expr.left) else {
        return None;
    };
    if lhs.operator.as_str() != "+" {
        return None;
    }
    let constant = literal_int(&lhs.left)?;
    // The maximum of three int32 values and this constant must be a precisely
    // represented ECMAScript Number (including the left-associated sum).
    if !(-1_i64 << 42..=1_i64 << 42).contains(&constant) {
        return None;
    }
    if !number_bitwise(&lhs.right) {
        return None;
    }
    let Expression::BinaryExpression(xor) = unparen(&expr.right) else {
        return None;
    };
    if xor.operator.as_str() != "^" || literal_int(&xor.right).is_none() {
        return None;
    }
    let Expression::UnaryExpression(not) = unparen(&xor.left) else {
        return None;
    };
    if not.operator.as_str() != "~" {
        return None;
    }
    let next_constant = constant.checked_sub(1)?;
    let left = fragment(source, lhs.right.span());
    let x = fragment(source, not.argument.span());
    let mask = fragment(source, xor.right.span());
    // Parenthesizing the original operands prevents introducing precedence,
    // tagged-template, or method-receiver changes. Both observable operands
    // still evaluate once each in original left-to-right order.
    Some(format!("({next_constant} + ({left}) - (({x}) ^ ({mask})))"))
}

#[cfg(test)]
mod tests {
    use crate::deobfuscate;
    use work_budget::{BudgetExceeded, WorkBudget};

    fn rewritten(src: &str) -> Result<String, BudgetExceeded> {
        Ok(
            deobfuscate(src, 12, &WorkBudget::unlimited("bitwise-effects"))?
                .map_or_else(|| src.to_owned(), |value| value.source),
        )
    }

    #[test]
    fn preserves_two_coercions_and_exposes_affine_boolean_shape() -> Result<(), BudgetExceeded> {
        let source = "function f(U){return 129+(U&-129)+(~U^128);}";
        let transformed = rewritten(source)?;
        // The transform may add redundant grouping parentheses, but must
        // retain both original dynamic reads and the cheaper XOR shape.
        assert!(transformed.contains("128 + "), "{transformed}");
        assert!(transformed.contains("U&-129"), "{transformed}");
        assert!(transformed.contains(" - ((U) ^ (128))"), "{transformed}");
        assert_eq!(transformed.matches("U").count(), 3, "{transformed}");
        Ok(())
    }

    #[test]
    fn avoids_strings_arbitrary_plus_and_unproven_xor_operands() -> Result<(), BudgetExceeded> {
        for source in [
            "function f(U){return 129+'str'+(~U^128);}",
            "function f(U){return 129+U+(~U^128);}",
            "function f(U,v){return 129+(U&-129)+(~U^v);}",
            "function f(U){return 129+(U&-129)+(~U^128n);}",
        ] {
            let result = rewritten(source)?;
            assert!(!result.contains("128 + ("), "{result}");
        }
        Ok(())
    }
}
