//! Evaluate constant JavaScript switch dispatch with exact strict-equality
//! selection, fallthrough and lexical/var-hoisting constraints.

use crate::{
    fragment,
    value_eval::{eval, same_value},
};
use oxc_ast::ast::{Expression, Statement, SwitchStatement};
use oxc_ast_visit::{walk, Visit};
use oxc_span::GetSpan;

/// A discarded switch arm can still declare bindings for the entire switch or
/// enclosing function, regardless of whether its statements were executed.
#[derive(Default)]
struct DiscardedBindingHazard(bool);

impl<'a> Visit<'a> for DiscardedBindingHazard {
    fn visit_variable_declaration(&mut self, _: &oxc_ast::ast::VariableDeclaration<'a>) {
        self.0 = true;
    }

    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: oxc_syntax::scope::ScopeFlags) {
        // Includes Annex B function declarations; do not discard bindings.
        self.0 = true;
    }

    fn visit_class(&mut self, _: &oxc_ast::ast::Class<'a>) {
        self.0 = true;
    }
}

/// An unlabeled break in retained switch code might target the switch itself.
/// A terminal top-level `break` is removed explicitly; any other such break
/// must retain its original switch construct. Breaks within nested loops and
/// switches target those nested constructs, not the switch being eliminated.
#[derive(Default)]
struct SwitchBreakHazard(bool);

impl<'a> Visit<'a> for SwitchBreakHazard {
    fn visit_break_statement(&mut self, statement: &oxc_ast::ast::BreakStatement<'a>) {
        if statement.label.is_none() {
            self.0 = true;
        }
    }
    fn visit_for_statement(&mut self, _: &oxc_ast::ast::ForStatement<'a>) {}
    fn visit_for_in_statement(&mut self, _: &oxc_ast::ast::ForInStatement<'a>) {}
    fn visit_for_of_statement(&mut self, _: &oxc_ast::ast::ForOfStatement<'a>) {}
    fn visit_while_statement(&mut self, _: &oxc_ast::ast::WhileStatement<'a>) {}
    fn visit_do_while_statement(&mut self, _: &oxc_ast::ast::DoWhileStatement<'a>) {}
    fn visit_switch_statement(&mut self, _: &oxc_ast::ast::SwitchStatement<'a>) {}
    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: oxc_syntax::scope::ScopeFlags) {
    }
    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}
}

pub(crate) fn select_constant_switch(node: &SwitchStatement<'_>, source: &str) -> Option<String> {
    // eval() only admits pure, statically modeled primitives; an expression
    // that can invoke user JS or observe mutable state isn't folded.
    let discriminant = eval(&node.discriminant)?;
    let mut default = None;
    let mut matched = None;
    for (index, case) in node.cases.iter().enumerate() {
        if let Some(test) = &case.test {
            // Case expressions after a match are never evaluated, so don't
            // demand they be analyzable (or side-effect free).
            let test = eval(test)?;
            if same_value(&discriminant, &test) {
                matched = Some(index);
                break;
            }
        } else {
            default = Some(index);
        }
    }
    let selected = matched.or(default);

    // All switch cases share one lexical environment, including the cases
    // whose bodies are never entered. Do not remove declarations that could
    // change hoisting, TDZ, or direct-eval name resolution.
    let mut retained = Vec::new();
    let mut stopped = selected.is_none();
    for (index, case) in node.cases.iter().enumerate() {
        for statement in &case.consequent {
            let active = selected.is_some_and(|selected| index >= selected) && !stopped;
            if !active {
                let mut hazard = DiscardedBindingHazard::default();
                hazard.visit_statement(statement);
                if hazard.0 {
                    return None;
                }
                continue;
            }
            if let Statement::BreakStatement(brk) = statement {
                if brk.label.is_none() {
                    stopped = true;
                    continue;
                }
            }
            let mut hazard = SwitchBreakHazard::default();
            hazard.visit_statement(statement);
            if hazard.0 {
                return None;
            }
            retained.push(fragment(source, statement.span()));
        }
    }
    // Retain switch lexical scoping and run-time block position, but discard
    // the already-evaluated discriminant and structurally unreachable arms.
    Some(format!("{{\n{}\n}}", retained.join("\n")))
}

/// A JavaScript switch with a provably boolean discriminant and pure boolean
/// labels is ordinary two-way control flow. Preserve the original case-body
/// execution (including fallthrough) rather than re-evaluating the selector.
fn is_boolean_valued(expr: &Expression<'_>) -> bool {
    match expr {
        Expression::BooleanLiteral(_) => true,
        Expression::ParenthesizedExpression(group) => is_boolean_valued(&group.expression),
        Expression::UnaryExpression(unary) => unary.operator.as_str() == "!",
        Expression::BinaryExpression(binary) => matches!(
            binary.operator.as_str(),
            "==" | "===" | "!=" | "!==" | "<" | "<=" | ">" | ">=" | "in" | "instanceof"
        ),
        Expression::LogicalExpression(logical) => {
            is_boolean_valued(&logical.left) && is_boolean_valued(&logical.right)
        }
        Expression::ConditionalExpression(conditional) => {
            is_boolean_valued(&conditional.consequent) && is_boolean_valued(&conditional.alternate)
        }
        Expression::SequenceExpression(sequence) => {
            sequence.expressions.last().is_some_and(is_boolean_valued)
        }
        _ => false,
    }
}

/// Switch cases share a lexical environment. A rewrite to separate if blocks
/// may only happen when no case (including an unselected one) declares a
/// binding in that environment or in the enclosing function. Nested function
/// expressions are separate scopes and are not a hazard.
#[derive(Default)]
struct BooleanSwitchBindingHazard(bool);

impl<'a> Visit<'a> for BooleanSwitchBindingHazard {
    fn visit_statement(&mut self, statement: &Statement<'a>) {
        if matches!(
            statement,
            Statement::FunctionDeclaration(_) | Statement::ClassDeclaration(_)
        ) {
            self.0 = true;
        } else {
            walk::walk_statement(self, statement);
        }
    }

    fn visit_variable_declaration(&mut self, _: &oxc_ast::ast::VariableDeclaration<'a>) {
        self.0 = true;
    }

    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: oxc_syntax::scope::ScopeFlags) {
    }

    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}
    fn visit_class(&mut self, _: &oxc_ast::ast::Class<'a>) {}
}

fn boolean_switch_branch(
    node: &SwitchStatement<'_>,
    start: Option<usize>,
    source: &str,
) -> Option<String> {
    let Some(start) = start else {
        return Some(String::new());
    };
    let mut statements = Vec::new();
    for case in node.cases.iter().skip(start) {
        for (position, statement) in case.consequent.iter().enumerate() {
            if let Statement::BreakStatement(brk) = statement {
                if brk.label.is_none() {
                    // A terminal top-level break exits this switch, not the
                    // surrounding loop; after replacement it must disappear.
                    if position + 1 != case.consequent.len() {
                        return None;
                    }
                    return Some(statements.join("\n"));
                }
            }
            // A conditional break targeting the removed switch cannot be
            // represented by an if; retain the original statement instead.
            let mut hazard = SwitchBreakHazard::default();
            hazard.visit_statement(statement);
            if hazard.0 {
                return None;
            }
            statements.push(fragment(source, statement.span()));
        }
    }
    Some(statements.join("\n"))
}

/// Proof of the *result after evaluation*, not proof that the expression is pure.
///
/// This intentionally does not feed into the ordinary constant folder:
/// array/object literal evaluation can execute spreads, getters, computed keys,
/// or throw on a TDZ reference, even though the resulting object is truthy.
fn value_after_evaluation(expr: &Expression<'_>) -> Option<crate::value_eval::Value> {
    use crate::value_eval::{eval_binary, Value};

    if let Some(value) = eval(expr) {
        return Some(value);
    }
    match expr {
        Expression::ParenthesizedExpression(paren) => value_after_evaluation(&paren.expression),
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "!" => {
            let argument = &unary.argument;
            match argument {
                Expression::ArrayExpression(_)
                | Expression::ObjectExpression(_)
                | Expression::FunctionExpression(_)
                | Expression::ArrowFunctionExpression(_)
                | Expression::ClassExpression(_) => Some(Value::Bool(false)),
                _ => Some(Value::Bool(!value_after_evaluation(argument)?.truthy())),
            }
        }
        Expression::BinaryExpression(binary) => eval_binary(
            binary.operator.as_str(),
            value_after_evaluation(&binary.left)?,
            value_after_evaluation(&binary.right)?,
        ),
        Expression::SequenceExpression(sequence) => {
            value_after_evaluation(sequence.expressions.last()?)
        }
        Expression::ConditionalExpression(conditional) => {
            let yes = value_after_evaluation(&conditional.consequent)?;
            let no = value_after_evaluation(&conditional.alternate)?;
            // JS strict equality equates +0 and -0, but arithmetic does not.
            // A proof carried into enclosing expressions must preserve the sign.
            let equivalent = match (&yes, &no) {
                (Value::Number(left), Value::Number(right)) => left.to_bits() == right.to_bits(),
                _ => same_value(&yes, &no),
            };
            if equivalent {
                Some(yes)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Reconstruct a boolean switch even when a label's value is known only after
/// running its original expression. Each selected path evaluates precisely
/// the labels encountered in the original switch, then executes the matching
/// case body. This avoids repeating a large case body across branches.
fn structure_boolean_switch_with_effectful_known_labels(
    node: &SwitchStatement<'_>,
    source: &str,
) -> Option<String> {
    use crate::value_eval::Value;

    let mut labels = Vec::with_capacity(node.cases.len());
    let mut requires_effect_preservation = false;
    let mut default = None;
    for (index, case) in node.cases.iter().enumerate() {
        let label = if let Some(test) = &case.test {
            let Value::Bool(value) = value_after_evaluation(test)? else {
                return None;
            };
            requires_effect_preservation |= eval(test).is_none();
            Some(value)
        } else {
            default = Some(index);
            None
        };
        labels.push(label);
        for statement in &case.consequent {
            let mut hazard = BooleanSwitchBindingHazard::default();
            hazard.visit_statement(statement);
            if hazard.0 {
                return None;
            }
        }
    }
    if !requires_effect_preservation {
        return None;
    }
    let mut bodies = Vec::new();
    for discriminant in [true, false] {
        let matched = labels.iter().position(|label| *label == Some(discriminant));
        let selected = matched.or(default);
        // When there is no match, the switch evaluates every non-default
        // label, including those after an earlier default position.
        let tested = matched.map_or(node.cases.len(), |index| index + 1);
        let evaluated_labels = node.cases.iter().take(tested).filter_map(|case| {
            case.test.as_ref().map(|test| {
                // Parenthesized expression statement: even an object or
                // function expression cannot become a declaration here.
                format!("({});", fragment(source, test.span()))
            })
        });
        let mut instructions = evaluated_labels.collect::<Vec<_>>();
        instructions.push(boolean_switch_branch(node, selected, source)?);
        bodies.push(instructions.join("\n"));
    }
    let [when_true, when_false] = <[String; 2]>::try_from(bodies).ok()?;
    Some(format!(
        "{{\nif ({}) {{\n{when_true}\n}} else {{\n{when_false}\n}}\n}}",
        fragment(source, node.discriminant.span())
    ))
}

/// When a boolean switch starts with a pure, statically known case, that
/// case consumes one entire side of the boolean domain. Cases after it can
/// be arbitrary dynamic expressions, but are evaluated only on the opposite
/// side, in their exact source order until the first strict-equality match.
///
/// Unlike declaring a synthetic selector variable, this keeps direct eval,
/// scope, and single selector evaluation intact. The matched body is emitted
/// once and fallthrough begins at the exact selected case.
fn structure_boolean_switch_with_dynamic_suffix(
    node: &SwitchStatement<'_>,
    source: &str,
) -> Option<String> {
    let first = node.cases.first()?.test.as_ref()?;
    let crate::value_eval::Value::Bool(first_value) = eval(first)? else {
        return None;
    };
    for case in &node.cases {
        for statement in &case.consequent {
            let mut hazard = BooleanSwitchBindingHazard::default();
            hazard.visit_statement(statement);
            if hazard.0 {
                return None;
            }
        }
    }
    let opposite = !first_value;
    let first_body = boolean_switch_branch(node, Some(0), source)?;
    let mut choices = Vec::new();
    let mut default = None;
    for (index, case) in node.cases.iter().enumerate().skip(1) {
        let Some(test) = &case.test else {
            default = Some(index);
            continue;
        };
        match eval(test) {
            Some(crate::value_eval::Value::Bool(value)) if value == opposite => {
                // Every later case label would be skipped after this match.
                // Earlier dynamic tests must still run first.
                choices.push((None, boolean_switch_branch(node, Some(index), source)?));
                default = None;
                break;
            }
            Some(_) => {
                // A pure, non-boolean primitive cannot be strictly equal to
                // a boolean selector; evaluating it has no visible effect.
            }
            None => choices.push((
                Some(format!(
                    "{opposite} === ({})",
                    fragment(source, test.span())
                )),
                boolean_switch_branch(node, Some(index), source)?,
            )),
        }
    }
    let mut other_body = boolean_switch_branch(node, default, source)?;
    for (condition, body) in choices.into_iter().rev() {
        other_body = match condition {
            Some(condition) => format!("if ({condition}) {{\n{body}\n}} else {{\n{other_body}\n}}"),
            None => format!("{{\n{body}\n}}"),
        };
    }
    let (true_body, false_body) = if first_value {
        (first_body, other_body)
    } else {
        (other_body, first_body)
    };
    Some(format!(
        "{{\nif ({}) {{\n{true_body}\n}} else {{\n{false_body}\n}}\n}}",
        fragment(source, node.discriminant.span())
    ))
}

pub(crate) fn structure_boolean_switch(node: &SwitchStatement<'_>, source: &str) -> Option<String> {
    if !is_boolean_valued(&node.discriminant) || node.cases.is_empty() {
        return None;
    }
    if let Some(recovered) = structure_boolean_switch_with_effectful_known_labels(node, source) {
        return Some(recovered);
    }
    if node.cases.iter().any(|case| {
        case.test
            .as_ref()
            .is_some_and(|expr| !matches!(eval(expr), Some(crate::value_eval::Value::Bool(_))))
    }) {
        return structure_boolean_switch_with_dynamic_suffix(node, source);
    }
    let mut labels = Vec::with_capacity(node.cases.len());
    let mut default_index = None;
    for (index, case) in node.cases.iter().enumerate() {
        let value = match &case.test {
            Some(expr) => match eval(expr)? {
                crate::value_eval::Value::Bool(value) => Some(value),
                _ => return None,
            },
            None => {
                default_index = Some(index);
                None
            }
        };
        labels.push(value);
        for statement in &case.consequent {
            let mut hazard = BooleanSwitchBindingHazard::default();
            hazard.visit_statement(statement);
            if hazard.0 {
                return None;
            }
        }
    }

    let selected = |value: bool| {
        labels
            .iter()
            .position(|label| *label == Some(value))
            .or(default_index)
    };
    let when_true = boolean_switch_branch(node, selected(true), source)?;
    let when_false = boolean_switch_branch(node, selected(false), source)?;
    Some(format!(
        "{{\nif ({}) {{\n{when_true}\n}} else {{\n{when_false}\n}}\n}}",
        fragment(source, node.discriminant.span())
    ))
}

#[cfg(test)]
mod tests {
    use crate::deobfuscate;
    use work_budget::{BudgetExceeded, WorkBudget};

    fn transformed(input: &str) -> Result<String, BudgetExceeded> {
        Ok(
            deobfuscate(input, 12, &WorkBudget::unlimited("constant-switch"))?
                .map_or_else(|| input.to_owned(), |r| r.source),
        )
    }

    #[test]
    fn strict_switch_selection_fallthrough_and_default() -> Result<(), BudgetExceeded> {
        let source = "function f(x){switch(true){case true:x.push(1);break;case sideEffect():x.push(2);break;}return x;}";
        let output = transformed(source)?;
        assert!(!output.contains("switch"), "{output}");
        assert!(!output.contains("sideEffect"), "{output}");
        assert!(output.contains("x.push(1)"), "{output}");
        let source = "function f(x){switch(2){default:x.push(1);case 1:x.push(2);break;case 2:x.push(3);case 3:x.push(4);break;}return x;}";
        let output = transformed(source)?;
        assert!(!output.contains("switch"), "{output}");
        assert!(!output.contains("x.push(1)"), "{output}");
        assert!(output.contains("x.push(3)"), "{output}");
        assert!(output.contains("x.push(4)"), "{output}");
        let output = transformed(
            "function f(x){switch(1){case 1:x.push(1);break;x.push(99);case 2:x.push(2);}}",
        )?;
        assert!(!output.contains("switch"), "{output}");
        assert!(!output.contains("99"), "{output}");
        assert!(!output.contains("x.push(2)"), "{output}");
        Ok(())
    }

    #[test]
    fn preserves_hoisted_bindings_tdz_mutable_tests_and_nested_breaks() -> Result<(), BudgetExceeded>
    {
        for input in [
            "function f(){switch(true){case true:break;case false:var x=1;}return typeof x;}",
            "function f(){switch(true){case true:foo;break;case false:let foo=3;}}",
            "function f(x){switch(x){case 1:sideEffect();break;default:other();}}",
            "function f(x){switch(true){case true:if(x)break;foo();break;}}",
            "function f(x){switch(2){case sideEffect():x();break;case 2:x();break;}}",
        ] {
            let output = transformed(input)?;
            assert!(output.contains("switch"), "{input} -> {output}");
        }
        Ok(())
    }

    #[test]
    fn loose_equal_primitives_fold_both_true_and_false() -> Result<(), BudgetExceeded> {
        let source = "function f(){return [116==68, 116!=68, '12'==12, '12'!=12, null==void 0, false==0, true==2, NaN==NaN];}";
        let output = transformed(source)?;
        assert!(output.contains("false"), "{output}");
        assert!(output.contains("true"), "{output}");
        assert!(!output.contains("116==68"), "{output}");
        assert!(!output.contains("'12'==12"), "{output}");
        Ok(())
    }

    #[test]
    fn restructures_boolean_switch_with_reversed_cases_fallthrough_and_callbacks(
    ) -> Result<(), BudgetExceeded> {
        let source = r#"
            function f(value, events) {
                switch (!(value === 3)) {
                    case false:
                        events.push("matched");
                        break;
                    case true:
                        events.push("other");
                        (function() { events.push("callback"); })();
                        break;
                }
                switch (!(value === 5)) {
                    case true:
                        events.push("first");
                    case false:
                        events.push("after");
                        break;
                }
                return events;
            }
        "#;
        let output = transformed(source)?;
        assert!(!output.contains("switch"), "{output}");
        assert!(output.contains("if ("), "{output}");
        assert!(output.contains("callback"), "{output}");
        assert!(output.contains("after"), "{output}");
        Ok(())
    }

    #[test]
    fn retains_switch_when_boolean_rewrite_cannot_preserve_bindings_or_breaks(
    ) -> Result<(), BudgetExceeded> {
        for source in [
            "function f(v){switch(!v){case true:var x=1;break;case false: return typeof x;}}",
            "function f(v){switch(!v){case true:let x=1;break;case false: return 2;}}",
            "function f(v){switch(!v){case true:function nested(){}break;case false: return 2;}}",
            "function f(v){switch(!v){case true:if(v)break;other();break;case false:return 2;}}",
            "function f(v){switch(!v){case sideEffect():return 1;case true:return 2;}}",
            "function f(v){switch(v){case true:return 1;case false:return 2;}}",
        ] {
            let output = transformed(source)?;
            assert!(output.contains("switch"), "{source} -> {output}");
        }
        Ok(())
    }

    #[test]
    fn dynamically_evaluated_case_after_known_boolean_case_preserves_order(
    ) -> Result<(), BudgetExceeded> {
        let source = r#"
            function f(flag, log) {
                switch (!flag) {
                    case true:
                        log.push("first");
                        break;
                    case (log.push("test"), true == []):
                        log.push("dynamic");
                        break;
                    case false:
                        log.push("fallback");
                        break;
                }
                return log;
            }
        "#;
        let output = transformed(source)?;
        assert!(!output.contains("switch"), "{output}");
        assert!(output.contains("true == []"), "{output}");
        assert!(output.contains("log.push(\"test\")"), "{output}");
        assert!(output.contains("log.push(\"first\")"), "{output}");
        Ok(())
    }

    #[test]
    fn dynamic_first_case_stays_a_switch_without_a_proven_branch_partition(
    ) -> Result<(), BudgetExceeded> {
        let source = r#"
            function f(flag, log) {
                switch (!flag) {
                    case (log.push("test"), true == []): log.push("dynamic"); break;
                    case false: log.push("fallback"); break;
                }
            }
        "#;
        let output = transformed(source)?;
        assert!(output.contains("switch"), "{output}");
        Ok(())
    }

    #[test]
    fn known_effectful_case_label_preserves_evaluation_and_avoids_body_duplication(
    ) -> Result<(), BudgetExceeded> {
        let source = r#"
            function f(flag, events) {
                switch (!(flag == 1)) {
                    case 0 == ![events.push("element")]:
                        events.push("long-body");
                        events.push("long-body");
                        break;
                    case false:
                        events.push("fallback");
                        break;
                }
                return events;
            }
        "#;
        let output = transformed(source)?;
        assert!(!output.contains("switch"), "{output}");
        assert_eq!(
            output.matches("events.push(\"long-body\")").count(),
            2,
            "{output}"
        );
        assert_eq!(
            output.matches("events.push(\"element\")").count(),
            2,
            "{output}"
        );
        assert!(output.contains("events.push(\"fallback\")"), "{output}");
        Ok(())
    }

    #[test]
    fn effectful_boolean_case_handles_default_position_and_sequence_effects(
    ) -> Result<(), BudgetExceeded> {
        let source = r#"
            function f(flag, events) {
                switch (!flag) {
                    default: events.push("default"); break;
                    case (events.push("first"), 0 == ![events.push("second")]):
                        events.push("true"); break;
                    case false: events.push("false"); break;
                }
                return events;
            }
        "#;
        let output = transformed(source)?;
        assert!(!output.contains("switch"), "{output}");
        assert_eq!(
            output.matches("events.push(\"true\")").count(),
            1,
            "{output}"
        );
        assert!(output.contains("events.push(\"first\")"), "{output}");
        assert!(output.contains("events.push(\"second\")"), "{output}");
        Ok(())
    }

    #[test]
    fn effectful_result_proof_does_not_merge_positive_and_negative_zero(
    ) -> Result<(), BudgetExceeded> {
        let source = r#"
            function f(flag, events) {
                switch (!flag) {
                    case 1 / (flag ? 0 : -0) === 1 / 0:
                        events.push("first");
                        break;
                    case false:
                        events.push("second");
                        break;
                }
                return events;
            }
        "#;
        let output = transformed(source)?;
        assert!(output.contains("switch"), "{output}");
        Ok(())
    }

    #[test]
    fn constant_knitsail_style_switch_and_dead_return() -> Result<(), BudgetExceeded> {
        let source = "function f(){switch(!(2==1)){case true:[]==true;break;case sideEffect():doStuff();break;}return 116==68 && sideEffect();}";
        let output = transformed(source)?;
        assert!(!output.contains("switch"), "{output}");
        assert!(!output.contains("sideEffect"), "{output}");
        assert!(output.contains("return false"), "{output}");
        Ok(())
    }
}
