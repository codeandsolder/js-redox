//! Evaluate constant JavaScript switch dispatch with exact strict-equality
//! selection, fallthrough and lexical/var-hoisting constraints.

use crate::{
    fragment,
    value_eval::{eval, same_value},
};
use oxc_ast::ast::{Statement, SwitchStatement};
use oxc_ast_visit::Visit;
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
    fn constant_knitsail_style_switch_and_dead_return() -> Result<(), BudgetExceeded> {
        let source = "function f(){switch(!(2==1)){case true:[]==true;break;case sideEffect():doStuff();break;}return 116==68 && sideEffect();}";
        let output = transformed(source)?;
        assert!(!output.contains("switch"), "{output}");
        assert!(!output.contains("sideEffect"), "{output}");
        assert!(output.contains("return false"), "{output}");
        Ok(())
    }
}
