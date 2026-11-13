//! Extract right-operand comma effects without changing earlier getter/coercion order.
//! Comparison operands are read before the right-side effects, but converted only
//! after those effects. This emits fresh block-local value captures, in order.
//! All output is analyst-only and never replaces the original executable.
use oxc_ast::ast::{CallExpression, Expression, Function, FunctionType, IfStatement};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, Span};
use oxc_syntax::scope::ScopeFlags;

#[derive(Default)]
struct ScopeHazards {
    direct_eval: bool,
    block_functions: bool,
}

impl<'a> Visit<'a> for ScopeHazards {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if matches!(&call.callee, Expression::Identifier(id) if id.name == "eval") {
            self.direct_eval = true;
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if function.r#type == FunctionType::FunctionDeclaration {
            // Annex B function bindings may be affected by another block.
            self.block_functions = true;
        }
        walk::walk_function(self, function, flags);
    }
}

fn slice(source: &str, span: Span) -> Option<&str> {
    source.get(span.start as usize..span.end as usize)
}

fn replace_child(source: &str, parent: Span, child: Span, replacement: &str) -> Option<String> {
    Some(format!(
        "{}{}{}",
        source.get(parent.start as usize..child.start as usize)?,
        replacement,
        source.get(child.end as usize..parent.end as usize)?
    ))
}

struct Linearized {
    expression: String,
    steps: Vec<String>,
}

// Traverse only guaranteed evaluation edges: parentheses, comma tails and
// binary right operands; never guarded logical/conditional expressions.
fn linearize_rhs(
    expression: &Expression<'_>,
    source: &str,
    nonce: &str,
    next: &mut usize,
) -> Option<Linearized> {
    match expression {
        Expression::ParenthesizedExpression(paren) => {
            let inner = linearize_rhs(&paren.expression, source, nonce, next)?;
            Some(Linearized {
                expression: replace_child(
                    source,
                    expression.span(),
                    paren.expression.span(),
                    &inner.expression,
                )?,
                steps: inner.steps,
            })
        }
        Expression::BinaryExpression(binary) => {
            let rhs = linearize_rhs(&binary.right, source, nonce, next)?;
            let name = format!("{nonce}_{}", *next);
            *next += 1;
            // Comma form suppresses assignment-name inference for anonymous
            // function/class expressions while preserving their GetValue.
            let left = slice(source, binary.left.span())?;
            let capture = format!("const {name} = (0, ({left}\n));");
            let span = expression.span();
            let lhs = binary.left.span();
            let rhs_span = binary.right.span();
            let rendered = format!(
                "{}{name}{}{}{}",
                source.get(span.start as usize..lhs.start as usize)?,
                source.get(lhs.end as usize..rhs_span.start as usize)?,
                rhs.expression,
                source.get(rhs_span.end as usize..span.end as usize)?
            );
            let mut steps = Vec::with_capacity(rhs.steps.len() + 1);
            steps.push(capture);
            steps.extend(rhs.steps);
            Some(Linearized {
                expression: rendered,
                steps,
            })
        }
        Expression::SequenceExpression(sequence) => {
            let (last, prefixes) = sequence.expressions.split_last()?;
            if prefixes.is_empty() {
                return None;
            }
            let mut steps = Vec::with_capacity(prefixes.len() + 1);
            let mut previous_end = sequence.span.start as usize;
            for operand in &sequence.expressions {
                let start = operand.span().start as usize;
                // Never silently discard comments between comma operands.
                let gap = source.get(previous_end..start)?;
                if gap.contains("/*") || gap.contains("//") {
                    return None;
                }
                previous_end = operand.span().end as usize;
            }
            let tail = source.get(previous_end..sequence.span.end as usize)?;
            if tail.contains("/*") || tail.contains("//") {
                return None;
            }
            for prefix in prefixes {
                // A newline also protects the closing punctuation from an
                // end-of-line comment belonging to an operand.
                steps.push(format!("({}\n);", slice(source, prefix.span())?));
            }
            let nested = linearize_rhs(last, source, nonce, next);
            let (value, following) = if let Some(nested) = nested {
                (nested.expression, nested.steps)
            } else {
                (slice(source, last.span())?.to_owned(), Vec::new())
            };
            steps.extend(following);
            Some(Linearized {
                expression: format!("({value})"),
                steps,
            })
        }
        _ => None,
    }
}

/// Caller guarantees a sibling if statement in a function/block body.
/// A fresh block prevents newly introduced bindings leaking to siblings.
/// Dynamic eval and Annex-B declarations in the moved subtree are excluded.
pub(crate) fn lower_if_binary_rhs_sequences(
    statement: &IfStatement<'_>,
    source: &str,
) -> Option<String> {
    fn root_is_binary(expression: &Expression<'_>) -> bool {
        match expression {
            Expression::ParenthesizedExpression(paren) => root_is_binary(&paren.expression),
            Expression::BinaryExpression(_) => true,
            _ => false,
        }
    }
    if !root_is_binary(&statement.test) {
        return None;
    }
    let mut hazards = ScopeHazards::default();
    hazards.visit_expression(&statement.test);
    hazards.visit_statement(&statement.consequent);
    if let Some(alternate) = &statement.alternate {
        hazards.visit_statement(alternate);
    }
    if hazards.direct_eval || hazards.block_functions {
        return None;
    }

    // Unused even in textual source, including unresolved references.
    let mut salt = 0;
    let nonce = loop {
        let candidate = format!("__jsvm_binary_rhs_{}_{}", statement.span.start, salt);
        if !source.contains(&candidate) {
            break candidate;
        }
        salt += 1;
    };
    let mut next = 0;
    let result = linearize_rhs(&statement.test, source, &nonce, &mut next)?;
    if result.steps.is_empty() {
        return None;
    }
    let if_code = replace_child(
        source,
        statement.span,
        statement.test.span(),
        &result.expression,
    )?;
    Some(format!("{{\n{}\n{if_code}\n}}", result.steps.join("\n")))
}

#[cfg(test)]
mod tests {
    use super::lower_if_binary_rhs_sequences;
    use crate::deobfuscate;
    use oxc_allocator::Allocator;
    use oxc_ast::ast::{IfStatement, Program, Statement};
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;
    use work_budget::{BudgetExceeded, WorkBudget};

    fn first_if<'p, 'a>(program: &'p Program<'a>) -> Option<&'p IfStatement<'a>> {
        let Statement::FunctionDeclaration(function) = program.body.first()? else {
            return None;
        };
        let Statement::IfStatement(branch) = function.body.as_ref()?.statements.first()? else {
            return None;
        };
        Some(branch)
    }

    fn rewritten(source: &str) -> Result<(String, usize), BudgetExceeded> {
        let result = deobfuscate(source, 20, &WorkBudget::unlimited("binary-rhs-reflow"))?;
        assert!(result.is_some(), "unparsed fixture: {source}");
        let Some(result) = result else {
            return Ok((source.to_owned(), 0));
        };
        let count = result
            .transforms
            .get("if_binary_rhs_effect_lifting")
            .copied()
            .unwrap_or_default();
        Ok((result.source, count))
    }

    #[test]
    fn extracts_nested_binary_right_comma_effects_in_order() -> Result<(), BudgetExceeded> {
        let source = "function f(H,U,log){if(H.length < (H.length < (U.fO=void 0,(U.Bn=[],(log('third'),2))))) log('yes');}";
        let (out, count) = rewritten(source)?;
        assert_eq!(count, 1, "{out}");
        assert!(out.contains("const __jsvm_binary_rhs_"), "{out}");
        let positions = (
            out.find("H.length"),
            out.match_indices("H.length").nth(1).map(|(index, _)| index),
            out.find("U.fO"),
            out.find("U.Bn"),
            out.find("log('third')"),
            out.rfind("if"),
        );
        assert!(
            matches!(
                positions,
                (Some(first), Some(second), Some(f_o), Some(b_n), Some(third), Some(condition))
                    if first < second
                        && second < f_o
                        && f_o < b_n
                        && b_n < third
                        && third < condition
            ),
            "{out}"
        );
        assert!(!out.contains("U.fO=void 0,"), "{out}");
        Ok(())
    }

    #[test]
    fn preserves_unsafe_scopes_and_nonmandatory_branches() -> Result<(), BudgetExceeded> {
        let sources = [
            "function f(o){if(o.value<(side(),2))return eval('o.value');}",
            "function f(o){if(o.value<(eval('o.value'),2))return 1;}",
            "function f(o){if(o.value<(side(),2)){function nested(){return 1;}}}",
            "function f(o,flag){if(flag&&(o.value<(side(),2)))ok();}",
            "function f(o,flag){if(flag?(o.value<(side(),2)):false)ok();}",
            "if(o.value<(side(),2))ok();",
        ];
        for source in sources {
            let (out, count) = rewritten(source)?;
            assert_eq!(count, 0, "{source} -> {out}");
        }
        Ok(())
    }

    #[test]
    fn generated_names_avoid_every_existing_source_occurrence() {
        let initial = "function f(o){if(o.value<(side(),2))ok();}";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, initial, SourceType::default());
        assert!(parsed.is_clean());
        let first = first_if(&parsed.program);
        assert!(first.is_some());
        let Some(first) = first else {
            return;
        };
        let collision = format!("__jsvm_binary_rhs_{}_0", first.span.start);
        let source = format!("{initial} const collision = '{collision}';");
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &source, SourceType::default());
        assert!(parsed.is_clean());
        let branch = first_if(&parsed.program);
        assert!(branch.is_some());
        let Some(branch) = branch else {
            return;
        };
        let rewritten = lower_if_binary_rhs_sequences(branch, &source);
        assert!(rewritten.is_some());
        let Some(rewritten) = rewritten else {
            return;
        };
        assert!(
            rewritten.contains(&format!(
                "const __jsvm_binary_rhs_{}_1_0",
                branch.span.start
            )),
            "{rewritten}"
        );
        assert!(
            !rewritten.contains(&format!(
                "const __jsvm_binary_rhs_{}_0_0",
                branch.span.start
            )),
            "{rewritten}"
        );
    }

    #[test]
    fn fixed_point_does_not_recapture_synthetic_temps() -> Result<(), BudgetExceeded> {
        let source =
            "function f(o,log){if(o.length<(log(1),(o.length<(log(2),3))))return 7;return 8;}";
        let (out, count) = rewritten(source)?;
        assert_eq!(count, 1, "{out}");
        assert_eq!(out.matches("const __jsvm_binary_rhs_").count(), 2, "{out}");
        Ok(())
    }

    #[test]
    fn comments_are_never_dropped_by_the_binary_rhs_pass() {
        let cases = [
            (
                "function f(o){if(o.value<(side()/*prefix*/,2))ok();}",
                false,
            ),
            ("function f(o){if(o.value<(side(),/*tail*/2))ok();}", false),
            (
                "function f(o){if(o.value<(side(),2)/*parent*/ )ok();}",
                true,
            ),
        ];
        for (source, expected_rewrite) in cases {
            let allocator = Allocator::default();
            let parsed = parse_program(&allocator, source, SourceType::default());
            assert!(parsed.is_clean(), "{source}");
            let branch = first_if(&parsed.program);
            assert!(branch.is_some());
            let Some(branch) = branch else {
                continue;
            };
            let rewritten = lower_if_binary_rhs_sequences(branch, source);
            assert_eq!(
                rewritten.is_some(),
                expected_rewrite,
                "{source} -> {rewritten:?}"
            );
            if let Some(rewritten) = rewritten {
                assert!(rewritten.contains("/*parent*/"), "{rewritten}");
            }
        }
    }
}
