//! Preserve the effects of an expression whose resulting primitive value is
//! statically known, including effects nested inside sequence expressions.
//!
//! This is deliberately distinct from pure constant folding: the effect list
//! is emitted in original evaluation order, and unknown operand outcomes
//! prevent folding the containing operator unless its short-circuit semantics
//! make the operand unreachable.
use crate::{
    fragment,
    value_eval::{eval, eval_binary, eval_logical_left, eval_unary_value, LogicalStep, Value},
};
use oxc_ast::ast::Expression;
use oxc_span::GetSpan;

struct KnownEffects {
    value: Value,
    effects: Vec<String>,
}

fn evaluate(expr: &Expression<'_>, source: &str) -> Option<KnownEffects> {
    if let Some(value) = eval(expr) {
        return Some(KnownEffects {
            value,
            effects: Vec::new(),
        });
    }
    match expr {
        Expression::ParenthesizedExpression(paren) => evaluate(&paren.expression, source),
        Expression::SequenceExpression(seq) => {
            let (last, prefix) = seq.expressions.split_last()?;
            let mut effects = Vec::new();
            for expression in prefix {
                if let Some(known) = evaluate(expression, source) {
                    effects.extend(known.effects);
                } else {
                    // The original syntax is kept intact. Evaluation of a
                    // dynamic prefix can throw, mutate state or run getters.
                    effects.push(fragment(source, expression.span()).to_owned());
                }
            }
            let last = evaluate(last, source)?;
            effects.extend(last.effects);
            Some(KnownEffects {
                value: last.value,
                effects,
            })
        }
        Expression::BinaryExpression(binary) => {
            let mut left = evaluate(&binary.left, source)?;
            let right = evaluate(&binary.right, source)?;
            let value = eval_binary(binary.operator.as_str(), left.value, right.value)?;
            left.effects.extend(right.effects);
            Some(KnownEffects {
                value,
                effects: left.effects,
            })
        }
        Expression::LogicalExpression(logical) => {
            let mut left = evaluate(&logical.left, source)?;
            let value = match eval_logical_left(logical.operator.as_str(), left.value)? {
                LogicalStep::Value(value) => value,
                LogicalStep::EvaluateRight => {
                    let right = evaluate(&logical.right, source)?;
                    left.effects.extend(right.effects);
                    right.value
                }
            };
            Some(KnownEffects {
                value,
                effects: left.effects,
            })
        }
        Expression::ConditionalExpression(conditional) => {
            let mut condition = evaluate(&conditional.test, source)?;
            let branch = if condition.value.truthy() {
                &conditional.consequent
            } else {
                &conditional.alternate
            };
            let result = evaluate(branch, source)?;
            condition.effects.extend(result.effects);
            Some(KnownEffects {
                value: result.value,
                effects: condition.effects,
            })
        }
        Expression::UnaryExpression(unary) => {
            let argument = evaluate(&unary.argument, source)?;
            let value = eval_unary_value(unary.operator.as_str(), argument.value)?;
            Some(KnownEffects {
                value,
                effects: argument.effects,
            })
        }
        _ => None,
    }
}

pub(crate) fn fold(expr: &Expression<'_>, source: &str) -> Option<String> {
    let result = evaluate(expr, source)?;
    if result.effects.is_empty() {
        return None;
    }
    let rendered = result.value.render()?;
    let replacement = format!("({}, {rendered})", result.effects.join(", "));
    (replacement.len() < fragment(source, expr.span()).len()).then_some(replacement)
}

#[cfg(test)]
mod tests {
    use crate::deobfuscate;
    use work_budget::{BudgetExceeded, WorkBudget};

    fn rewritten(source: &str) -> Result<String, BudgetExceeded> {
        Ok(
            deobfuscate(source, 12, &WorkBudget::unlimited("effectful-constant"))?
                .map_or_else(|| source.to_owned(), |result| result.source),
        )
    }

    #[test]
    fn preserves_effectful_prefix_while_eliminating_unreachable_rhs() -> Result<(), BudgetExceeded>
    {
        let source = "function f(events){return (62 ^ (events.push('read'), 7)) >= 68 && (events.push('dead'), 99);}";
        let output = rewritten(source)?;
        assert!(output.contains("events.push('read')"), "{output}");
        assert!(!output.contains("events.push('dead')"), "{output}");
        assert!(output.contains("false"), "{output}");
        Ok(())
    }

    #[test]
    fn preserves_dynamic_prefix_getters_and_exceptions() -> Result<(), BudgetExceeded> {
        let source = "function f(obj){return (62 ^ (obj.key, 7)) >= 68 && obj.sideEffect();}";
        let output = rewritten(source)?;
        assert!(output.contains("obj.key"), "{output}");
        assert!(!output.contains("obj.sideEffect"), "{output}");
        Ok(())
    }

    #[test]
    fn branches_and_unary_ops_preserve_selected_effect_order() -> Result<(), BudgetExceeded> {
        let source = "function f(log){return (!(log.push(1), false) ? (log.push(2),5) : (log.push(3),9)) + 1;}";
        let output = rewritten(source)?;
        assert!(output.contains("log.push(1)"), "{output}");
        assert!(output.contains("log.push(2)"), "{output}");
        assert!(!output.contains("log.push(3)"), "{output}");
        assert!(output.contains("6"), "{output}");
        Ok(())
    }

    #[test]
    fn return_discards_unobserved_primitive_sequence_values() -> Result<(), BudgetExceeded> {
        let source = "function f(u){return false, u;}";
        let output = rewritten(source)?;
        assert!(!output.contains("false, u"), "{output}");
        assert!(output.contains("return u"), "{output}");
        // An indirect eval call is not a return-level sequence expression.
        let output = rewritten("function f(){return (0, eval)('x');}")?;
        assert!(output.contains("(0, eval)"), "{output}");
        Ok(())
    }

    #[test]
    fn leaves_unknown_outcomes_and_effectful_rhs_untouched() -> Result<(), BudgetExceeded> {
        let source = "function f(x, log){return (x, log.push('test')) >= 68 && log.push('next');}";
        let output = rewritten(source)?;
        assert!(output.contains("log.push('test')"), "{output}");
        assert!(output.contains("log.push('next')"), "{output}");
        Ok(())
    }
}
