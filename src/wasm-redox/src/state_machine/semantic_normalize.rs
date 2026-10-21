use super::{scalar::eval_i32_scalar_family, semantic_render::SemanticExpression};
use std::collections::BTreeSet;

pub(super) fn normalize_semantic_expression(expression: &SemanticExpression) -> SemanticExpression {
    let mut referenced_values = BTreeSet::new();
    collect_ssa_references(expression, &mut referenced_values);
    normalize(expression, &referenced_values)
}

fn collect_ssa_references(expression: &SemanticExpression, referenced: &mut BTreeSet<usize>) {
    match expression {
        SemanticExpression::SsaValue { value } => {
            referenced.insert(*value);
        }
        SemanticExpression::Operation { arguments, .. } => {
            for argument in arguments {
                collect_ssa_references(argument, referenced);
            }
        }
        SemanticExpression::I32Const { .. }
        | SemanticExpression::Argument { .. }
        | SemanticExpression::Runtime { .. }
        | SemanticExpression::Symbol { .. }
        | SemanticExpression::Opaque { .. } => {}
    }
}

fn normalize(expression: &SemanticExpression, referenced: &BTreeSet<usize>) -> SemanticExpression {
    let SemanticExpression::Operation {
        value,
        operator,
        arguments,
    } = expression
    else {
        return expression.clone();
    };

    let arguments = arguments
        .iter()
        .map(|argument| normalize(argument, referenced))
        .collect::<Vec<_>>();

    // A referenced operation is a definition in the bounded SSA DAG. Replacing
    // it by a child or constant would leave an ssa_value reference dangling.
    if referenced.contains(value) {
        return SemanticExpression::Operation {
            value: *value,
            operator: operator.clone(),
            arguments,
        };
    }

    if let Some(folded) = fold_closed_operation(operator, &arguments) {
        return folded;
    }
    if let Some(simplified) = neutral_identity(operator, &arguments) {
        return simplified;
    }

    SemanticExpression::Operation {
        value: *value,
        operator: operator.clone(),
        arguments,
    }
}

fn constant_value(expression: &SemanticExpression) -> Option<u32> {
    let SemanticExpression::I32Const { value } = expression else {
        return None;
    };
    Some(*value)
}

fn fold_closed_operation(
    operator: &str,
    arguments: &[SemanticExpression],
) -> Option<SemanticExpression> {
    let values = arguments
        .iter()
        .map(constant_value)
        .collect::<Option<Vec<_>>>()?;
    let value = if operator == "reverse_bits32" {
        let [value] = values.as_slice() else {
            return None;
        };
        value.reverse_bits()
    } else {
        eval_i32_scalar_family(operator, &values)?
    };
    Some(SemanticExpression::I32Const { value })
}

fn is_const(expression: &SemanticExpression, expected: u32) -> bool {
    constant_value(expression) == Some(expected)
}

fn neutral_identity(
    operator: &str,
    arguments: &[SemanticExpression],
) -> Option<SemanticExpression> {
    let [left, right] = arguments else {
        return None;
    };
    let result = match operator {
        "i32add" if is_const(left, 0) => right,
        "i32add" | "i32sub" if is_const(right, 0) => left,
        "i32mul" if is_const(left, 1) => right,
        "i32mul" if is_const(right, 1) => left,
        "i32and" if is_const(left, u32::MAX) => right,
        "i32and" if is_const(right, u32::MAX) => left,
        "i32or" | "i32xor" if is_const(left, 0) => right,
        "i32or" | "i32xor" if is_const(right, 0) => left,
        "i32shl" | "i32shrs" | "i32shru" | "i32rotl" | "i32rotr" if is_const(right, 0) => left,
        _ => return None,
    };
    Some(result.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn constant(value: u32) -> SemanticExpression {
        SemanticExpression::I32Const { value }
    }

    fn runtime(value: usize) -> SemanticExpression {
        SemanticExpression::Runtime {
            value,
            name: format!("$runtime{value}"),
        }
    }

    #[test]
    fn folds_only_closed_scalar_subtrees() {
        let expression = SemanticExpression::Operation {
            value: 3,
            operator: "i32mul".to_owned(),
            arguments: vec![
                SemanticExpression::Operation {
                    value: 2,
                    operator: "i32add".to_owned(),
                    arguments: vec![constant(2), constant(3)],
                },
                constant(4),
            ],
        };
        assert_eq!(
            normalize_semantic_expression(&expression),
            SemanticExpression::I32Const { value: 20 }
        );
    }

    #[test]
    fn neutral_identities_preserve_runtime_provenance() {
        let source = runtime(7);
        let expression = SemanticExpression::Operation {
            value: 8,
            operator: "i32add".to_owned(),
            arguments: vec![source.clone(), constant(0)],
        };
        assert_eq!(normalize_semantic_expression(&expression), source);

        let absorbing = SemanticExpression::Operation {
            value: 9,
            operator: "i32mul".to_owned(),
            arguments: vec![runtime(7), constant(0)],
        };
        assert!(matches!(
            normalize_semantic_expression(&absorbing),
            SemanticExpression::Operation { value: 9, .. }
        ));
    }

    #[test]
    fn referenced_operation_definitions_are_not_eliminated() {
        let expression = SemanticExpression::Operation {
            value: 2,
            operator: "i32mul".to_owned(),
            arguments: vec![
                SemanticExpression::Operation {
                    value: 1,
                    operator: "i32add".to_owned(),
                    arguments: vec![SemanticExpression::Argument { index: 0 }, constant(0)],
                },
                SemanticExpression::SsaValue { value: 1 },
            ],
        };
        let normalized = normalize_semantic_expression(&expression);
        assert!(matches!(normalized, SemanticExpression::Operation { .. }));
        if let SemanticExpression::Operation { arguments, .. } = normalized {
            assert!(matches!(
                &arguments[0],
                SemanticExpression::Operation {
                    value: 1,
                    operator,
                    ..
                } if operator == "i32add"
            ));
            assert_eq!(arguments[1], SemanticExpression::SsaValue { value: 1 });
        }
    }
}
