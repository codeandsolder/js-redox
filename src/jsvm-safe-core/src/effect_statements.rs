//! Reconstruct statement-level control flow when the value of a JavaScript
//! expression is discarded. No temporary identifiers and no special helper
//! names: only move operations between expression, block and if statements.
//!
//! The returned source is a block to avoid accidentally introducing a string
//! directive prologue (and to preserve dangling-else grammar). Atomically
//! retained expressions remain wrapped so object/function literals are valid
//! statement syntax. Dynamic branches are evaluated exactly once.
use crate::{fragment, statically_resolved_symbol, value_eval::eval};
use oxc_ast::ast::{
    AssignmentExpression, AssignmentTarget, Expression, ExpressionStatement, IfStatement,
    SequenceExpression,
};
use oxc_semantic::Scoping;
use oxc_span::GetSpan;

/// Parentheses are value-neutral here, but the original call syntax is
/// preserved in all emitted fragments so they cannot change direct eval.
fn sequence_rhs<'a, 'e>(expr: &'e Expression<'a>) -> Option<&'e SequenceExpression<'a>> {
    match expr {
        Expression::ParenthesizedExpression(paren) => sequence_rhs(&paren.expression),
        Expression::SequenceExpression(sequence) => Some(sequence),
        _ => None,
    }
}

/// Anonymous function and class expressions can acquire a visible name from
/// an assignment target. A comma expression suppresses that name inference;
/// don't erase this context when splitting assignment RHS expressions.
fn name_inference_hazard(expr: &Expression<'_>) -> bool {
    match expr {
        Expression::ParenthesizedExpression(paren) => name_inference_hazard(&paren.expression),
        Expression::FunctionExpression(_)
        | Expression::ArrowFunctionExpression(_)
        | Expression::ClassExpression(_) => true,
        _ => false,
    }
}

#[derive(Default)]
struct Lowered {
    statements: Vec<String>,
    structured: bool,
}

impl Lowered {
    fn push_expression(&mut self, expression: &Expression<'_>, source: &str) {
        if eval(expression).is_none() {
            self.statements
                .push(format!("({});", fragment(source, expression.span())));
        }
    }

    fn emit(
        &mut self,
        expr: &Expression<'_>,
        source: &str,
        scoping: &Scoping,
        depth: usize,
    ) -> Option<()> {
        if depth > 96 {
            return None;
        }
        match expr {
            Expression::ParenthesizedExpression(paren) => {
                self.emit(&paren.expression, source, scoping, depth + 1)
            }
            Expression::SequenceExpression(sequence) => {
                self.structured = true;
                for item in &sequence.expressions {
                    self.emit(item, source, scoping, depth + 1)?;
                }
                Some(())
            }
            Expression::LogicalExpression(logical)
                if matches!(logical.operator.as_str(), "&&" | "||") =>
            {
                self.structured = true;
                let and = logical.operator.as_str() == "&&";
                if let Some(value) = eval(&logical.left) {
                    if value.truthy() == and {
                        self.emit(&logical.right, source, scoping, depth + 1)?;
                    }
                    return Some(());
                }
                if eval(&logical.right).is_some() {
                    // The result is discarded; this RHS is pure, so only
                    // the LHS's evaluation may have effects or throw.
                    return self.emit(&logical.left, source, scoping, depth + 1);
                }
                let mut branch = Self::default();
                branch.emit(&logical.right, source, scoping, depth + 1)?;
                if branch.statements.is_empty() {
                    return self.emit(&logical.left, source, scoping, depth + 1);
                }
                let test = fragment(source, logical.left.span());
                let test = if and {
                    format!("({test})")
                } else {
                    format!("!({test})")
                };
                self.statements.push(format!(
                    "if ({test}) {{\n{}\n}}",
                    branch.statements.join("\n")
                ));
                Some(())
            }
            Expression::ConditionalExpression(conditional) => {
                self.structured = true;
                if let Some(value) = eval(&conditional.test) {
                    return self.emit(
                        if value.truthy() {
                            &conditional.consequent
                        } else {
                            &conditional.alternate
                        },
                        source,
                        scoping,
                        depth + 1,
                    );
                }
                let mut yes = Self::default();
                let mut no = Self::default();
                yes.emit(&conditional.consequent, source, scoping, depth + 1)?;
                no.emit(&conditional.alternate, source, scoping, depth + 1)?;
                if yes.statements.is_empty() && no.statements.is_empty() {
                    return self.emit(&conditional.test, source, scoping, depth + 1);
                }
                let test = fragment(source, conditional.test.span());
                let body = match (yes.statements.is_empty(), no.statements.is_empty()) {
                    (false, false) => format!(
                        "if ({test}) {{\n{}\n}} else {{\n{}\n}}",
                        yes.statements.join("\n"),
                        no.statements.join("\n")
                    ),
                    (false, true) => format!("if ({test}) {{\n{}\n}}", yes.statements.join("\n")),
                    (true, false) => format!("if (!({test})) {{\n{}\n}}", no.statements.join("\n")),
                    (true, true) => unreachable!(),
                };
                self.statements.push(body);
                Some(())
            }
            Expression::AssignmentExpression(assign) if assign.operator.as_str() == "=" => {
                // LHS reference evaluation may be moved past RHS prefixes
                // only for a stable lexical identifier: a member's getter,
                // computed key, or a dynamic `with` lookup can have effects.
                let AssignmentTarget::AssignmentTargetIdentifier(id) = &assign.left else {
                    self.push_expression(expr, source);
                    return Some(());
                };
                let Some(reference_id) = id.reference_id.get() else {
                    self.push_expression(expr, source);
                    return Some(());
                };
                if statically_resolved_symbol(scoping, reference_id).is_none() {
                    self.push_expression(expr, source);
                    return Some(());
                }
                let Some(sequence) = sequence_rhs(&assign.right) else {
                    self.push_expression(expr, source);
                    return Some(());
                };
                let Some((last, prefixes)) = sequence.expressions.split_last() else {
                    self.push_expression(expr, source);
                    return Some(());
                };
                if prefixes.is_empty() || name_inference_hazard(last) {
                    self.push_expression(expr, source);
                    return Some(());
                }
                self.structured = true;
                for prefix in prefixes {
                    self.emit(prefix, source, scoping, depth + 1)?;
                }
                self.statements.push(format!(
                    "({} = ({}));",
                    fragment(source, assign.left.span()),
                    fragment(source, last.span())
                ));
                Some(())
            }
            _ => {
                self.push_expression(expr, source);
                Some(())
            }
        }
    }
}

/// Peel a comma sequence off the object *of an assignment target* only
/// when the entire assignment is a discarded sibling expression statement.
///
/// `((first(), second(), object).field = rhs)` evaluates each prefix and
/// performs GetValue before it obtains the object used for the property
/// reference. Emitting those prefixes as preceding sibling statements keeps
/// exactly that ordering, without moving a member/element lookup past the
/// RHS or changing the assignment's `this`/name-inference context.
///
/// This is deliberately **not** generic RHS-assignment decomposition: the
/// target reference must be evaluated before the RHS, and its object/key can
/// run arbitrary user code (including proxy traps, getters and direct eval).
/// Call only for an expression already occupying a function/block statement
/// list, never an unbraced if/loop/label or script/eval top level.
pub(crate) fn lower_member_object_sequence(
    statement: &ExpressionStatement<'_>,
    source: &str,
) -> Option<String> {
    fn assignment<'a, 'e>(expr: &'e Expression<'a>) -> Option<&'e AssignmentExpression<'a>> {
        match expr {
            Expression::ParenthesizedExpression(paren) => assignment(&paren.expression),
            Expression::AssignmentExpression(assignment) => Some(assignment),
            _ => None,
        }
    }
    let assign = assignment(&statement.expression)?;
    let object = match &assign.left {
        AssignmentTarget::StaticMemberExpression(member) => &member.object,
        AssignmentTarget::ComputedMemberExpression(member) => &member.object,
        AssignmentTarget::PrivateFieldExpression(member) => &member.object,
        _ => return None,
    };
    let sequence = sequence_rhs(object)?;
    let (last, prefixes) = sequence.expressions.split_last()?;
    if prefixes.is_empty() {
        return None;
    }
    let object_span = object.span();
    let mut previous_end = object_span.start as usize;
    for operand in &sequence.expressions {
        let start = operand.span().start as usize;
        let gap = source.get(previous_end..start)?;
        if gap.contains("/*") || gap.contains("//") {
            return None;
        }
        previous_end = operand.span().end as usize;
    }
    let tail = source.get(previous_end..object_span.end as usize)?;
    if tail.contains("/*") || tail.contains("//") {
        return None;
    }

    let mut text = String::new();
    for prefix in prefixes {
        // Parentheses retain expression syntax (including anonymous function,
        // object literal and strings that must not become directives).
        // Each operand still performs GetValue, including direct eval/getters.
        text.push_str(&format!("({});\n", fragment(source, prefix.span())));
    }
    let statement_span = statement.span;
    text.push_str(source.get(statement_span.start as usize..object_span.start as usize)?);
    // The final comma operand produced a value, not an assignable reference.
    // It remains in the same object-position context after the prefix.
    text.push('(');
    text.push_str(fragment(source, last.span()));
    text.push(')');
    text.push_str(source.get(object_span.end as usize..statement_span.end as usize)?);
    Some(text)
}

/// Only descend through operands evaluated *first*, with no other
/// possibly-effectful expression or reference creation before them.
///
/// In particular, walking a right operand, a computed key, a call callee,
/// or an optional chain could move effects across user code or even change
/// direct/indirect eval and receiver identity. An ordinary property object's
/// comma sequence is a value computation, so the prefix can be evaluated as
/// preceding sibling statements without changing a property reference.
fn first_member_object_sequence<'a, 'e>(
    expr: &'e Expression<'a>,
) -> Option<&'e SequenceExpression<'a>> {
    match expr {
        Expression::ParenthesizedExpression(paren) => {
            first_member_object_sequence(&paren.expression)
        }
        Expression::BinaryExpression(binary) => first_member_object_sequence(&binary.left),
        Expression::LogicalExpression(logical) => first_member_object_sequence(&logical.left),
        Expression::ConditionalExpression(conditional) => {
            first_member_object_sequence(&conditional.test)
        }
        Expression::UnaryExpression(unary) => first_member_object_sequence(&unary.argument),
        Expression::StaticMemberExpression(member) if !member.optional => {
            sequence_rhs(&member.object).or_else(|| first_member_object_sequence(&member.object))
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            sequence_rhs(&member.object).or_else(|| first_member_object_sequence(&member.object))
        }
        Expression::PrivateFieldExpression(member) if !member.optional => {
            sequence_rhs(&member.object).or_else(|| first_member_object_sequence(&member.object))
        }
        _ => None,
    }
}

/// Extract a comma prefix from an unconditionally first-evaluated property
/// object in a sibling if-statement test.
///
/// E.g. if (((initialize(), object).length < bound)) body;
/// becomes (initialize()); if ((((object)).length < bound)) body;
///
/// Nothing from the original test runs before the selected prefix; this is
/// why we only follow the leftmost guaranteed-evaluation path. The original
/// branch source is kept verbatim, with one expression replacement. A
/// function/block statement-list parent is required (verified by the caller).
pub(crate) fn lower_if_test_first_member_object(
    statement: &IfStatement<'_>,
    source: &str,
) -> Option<String> {
    let sequence = first_member_object_sequence(&statement.test)?;
    let (last, prefixes) = sequence.expressions.split_last()?;
    if prefixes.is_empty() {
        return None;
    }
    let sequence_start = sequence.span.start as usize;
    let sequence_end = sequence.span.end as usize;
    let mut previous_end = sequence_start;
    for operand in &sequence.expressions {
        let start = operand.span().start as usize;
        let gap = source.get(previous_end..start)?;
        if gap.contains("/*") || gap.contains("//") {
            return None;
        }
        previous_end = operand.span().end as usize;
    }
    let tail = source.get(previous_end..sequence_end)?;
    if tail.contains("/*") || tail.contains("//") {
        return None;
    }
    let mut result = String::new();
    for prefix in prefixes {
        result.push_str(&format!("({});\n", fragment(source, prefix.span())));
    }
    result.push_str(source.get(statement.span.start as usize..sequence_start)?);
    result.push('(');
    result.push_str(fragment(source, last.span()));
    result.push(')');
    result.push_str(source.get(sequence_end..statement.span.end as usize)?);
    Some(result)
}

/// Split the side-effecting comma prefix of an if test from its final
/// condition. The caller must prove this is a sibling statement in an
/// existing function/block statement list: emitting several statements
/// in-place under an unbraced if/loop/label would change control flow, and
/// inserting a new block could change direct-eval/Annex-B binding behavior.
///
/// Every prefix still performs GetValue and can throw. Keep the exact source
/// of each operand and of the original branches, without changing reference
/// identity, short-circuit behavior, or lexical scope.
pub(crate) fn lower_if_test(statement: &IfStatement<'_>, source: &str) -> Option<String> {
    let sequence = sequence_rhs(&statement.test)?;
    let (condition, prefixes) = sequence.expressions.split_last()?;
    if prefixes.is_empty() {
        return None;
    }
    let test_start = statement.test.span().start as usize;
    let test_end = statement.test.span().end as usize;
    let mut previous_end = test_start;
    for operand in &sequence.expressions {
        // Comments between comma operands belong to the original source
        // narration. Until we can relocate them exactly, leave such tests
        // unchanged rather than losing the comments in an analyst view.
        let gap = source.get(previous_end..operand.span().start as usize)?;
        if gap.contains("/*") || gap.contains("//") {
            return None;
        }
        previous_end = operand.span().end as usize;
    }
    let tail = source.get(previous_end..test_end)?;
    if tail.contains("/*") || tail.contains("//") {
        return None;
    }

    let mut text = String::new();
    for expression in prefixes {
        let original = fragment(source, expression.span());
        // An inert known primitive cannot have observable effects. Keep
        // comments within such an operand rather than deleting annotations.
        if eval(expression).is_none() || original.contains("/*") || original.contains("//") {
            text.push_str(&format!("({original});\n"));
        }
    }
    // Preserve every original byte outside the test itself, including
    // comments between the test and the consequent/alternate statements.
    text.push_str(source.get(statement.span.start as usize..test_start)?);
    text.push_str(fragment(source, condition.span()));
    text.push_str(source.get(test_end..statement.span.end as usize)?);
    Some(text)
}

/// Direct `guard && call()` / `guard || call()` already has readable
/// short-circuit semantics. Retain that idiomatic source shape at statement
/// root rather than expanding it into an `if`; downstream semantic analyzers
/// can then recognize the same source-level guard/call relationship. Nested
/// comma expressions and assignment-heavy dispatch still get restructured.
fn simple_guarded_call(expr: &Expression<'_>) -> bool {
    match expr {
        Expression::ParenthesizedExpression(paren) => simple_guarded_call(&paren.expression),
        Expression::LogicalExpression(logical)
            if matches!(logical.operator.as_str(), "&&" | "||") =>
        {
            matches!(&logical.right, Expression::CallExpression(_))
        }
        _ => false,
    }
}

/// Lower an expression statement only when it actually contains conditional
/// or sequencing structure. Plain assignments, calls, property accesses and
/// existing idiomatic JavaScript expressions remain in their original form.
pub(crate) fn lower(
    statement: &ExpressionStatement<'_>,
    source: &str,
    scoping: &Scoping,
) -> Option<String> {
    if simple_guarded_call(&statement.expression) {
        return None;
    }
    let mut lowered = Lowered::default();
    lowered.emit(&statement.expression, source, scoping, 0)?;
    if !lowered.structured {
        return None;
    }
    Some(format!("{{\n{}\n}}", lowered.statements.join("\n")))
}

#[cfg(test)]
mod tests {
    use crate::deobfuscate;
    use work_budget::{BudgetExceeded, WorkBudget};

    fn rewritten(input: &str) -> Result<String, BudgetExceeded> {
        Ok(
            deobfuscate(input, 12, &WorkBudget::unlimited("statement-lowering"))?
                .map_or_else(|| input.to_owned(), |result| result.source),
        )
    }

    #[test]
    fn lowers_effectful_comma_and_short_circuit_without_repeating_test(
    ) -> Result<(), BudgetExceeded> {
        let input = "function f(Y){true && (U=AM(Y), 129 + (U&-129) + (~U^128) && (U=(L=U&127,v=AM(Y)<<7,~L-2*~(L|v)+(L|~v))),u=U), false;return u;}";
        let output = rewritten(input)?;
        assert!(!output.contains("true &&"), "{output}");
        assert!(output.contains("U=AM(Y)"), "{output}");
        assert!(output.contains("if ("), "{output}");
        assert!(output.contains("u=U"), "{output}");
        assert!(!output.contains("false;"), "{output}");
        Ok(())
    }

    #[test]
    fn splits_lexically_stable_assignment_sequences() -> Result<(), BudgetExceeded> {
        let source = "function f(U,L,v,Y){U=(L=U&127,v=AM(Y)<<7,~L-2*~(L|v)+(L|~v));return U;}";
        let output = rewritten(source)?;
        assert!(output.contains("L=U&127"), "{output}");
        assert!(output.contains("v=AM(Y)<<7"), "{output}");
        // A later generic bitwise pass may further simplify the now-separated
        // RHS; the essential invariant is that the assignment is separate.
        assert!(output.contains("U = "), "{output}");
        assert!(!output.contains("U=(L=U&127,v="), "{output}");
        Ok(())
    }

    #[test]
    fn retains_anonymous_function_name_inference_and_effectful_member_lhs(
    ) -> Result<(), BudgetExceeded> {
        let source =
            "function f(){let assigned;assigned=(sideEffect(),function(){});return assigned.name;}";
        let output = rewritten(source)?;
        assert!(
            output.contains("assigned=(sideEffect(),function(){});"),
            "{output}"
        );
        let source = "function f(o){o.prop=(sideEffect(),value());}";
        let output = rewritten(source)?;
        assert!(output.contains("o.prop=(sideEffect(),value())"), "{output}");
        Ok(())
    }

    #[test]
    fn pure_branches_and_directives_do_not_become_directive_prologue() -> Result<(), BudgetExceeded>
    {
        let input = "function f(x){('use strict', x && call(), false);return this;}";
        let output = rewritten(input)?;
        assert!(!output.contains("'use strict';"), "{output}");
        assert!(output.contains("call()"), "{output}");
        let input = "function f(){'use strict'; eval('x');}";
        let output = rewritten(input)?;
        assert!(output.contains("'use strict'"), "{output}");
        Ok(())
    }

    #[test]
    fn drops_pure_branches_but_preserves_computed_access_and_direct_eval(
    ) -> Result<(), BudgetExceeded> {
        let input = "function f(o){(o.value ? 1 : 2, o.value && (0,eval)('foo'));}";
        let output = rewritten(input)?;
        assert!(output.contains("o.value"), "{output}");
        assert!(output.contains("(0,eval)('foo')"), "{output}");
        assert!(!output.contains("? 1 : 2"), "{output}");
        Ok(())
    }

    #[test]
    fn constant_effectful_result_eliminates_dead_closure_before_statement_lowering(
    ) -> Result<(), BudgetExceeded> {
        let source = "function f(Y){let U; (62 ^ (U=AM(Y),7)) >= 68 && (U=function(){deadCall()});return U;}";
        let output = rewritten(source)?;
        assert!(!output.contains("deadCall"), "{output}");
        assert!(output.contains("AM(Y)"), "{output}");
        Ok(())
    }

    #[test]
    fn retains_idiomatic_guarded_calls_for_semantic_consumers() -> Result<(), BudgetExceeded> {
        let source =
            "function f(offset,view,address){offset === 56708 || view.setUint32(address,1,false);}";
        let output = rewritten(source)?;
        assert!(
            output.contains("offset === 56708 || view.setUint32(address,1,false)"),
            "{output}"
        );
        Ok(())
    }

    #[test]
    fn separates_effectful_object_prefix_before_member_assignment() -> Result<(), BudgetExceeded> {
        let input = "function f(o,key,value){((first(),second(),o)[key()] = value);return o;}";
        let output = rewritten(input)?;
        assert!(output.contains("(first());"), "{output}");
        assert!(output.contains("(second());"), "{output}");
        assert!(output.contains("(o)[key()] = value"), "{output}");
        assert!(
            matches!(
                (
                    output.find("(first());"),
                    output.find("(second());"),
                    output.find("(o)[key()]")
                ),
                (Some(first), Some(second), Some(target)) if first < second && second < target
            ),
            "{output}"
        );
        Ok(())
    }

    #[test]
    fn retains_member_assignment_rhs_name_and_direct_eval_scope() -> Result<(), BudgetExceeded> {
        let input = "function f(o){((eval('var marker = 19'),read(),o).fn = function() { return marker; });return [marker,o.fn.name];}";
        let output = rewritten(input)?;
        assert!(output.contains("(eval('var marker = 19'));"), "{output}");
        assert!(output.contains("(read());"), "{output}");
        assert!(output.contains("(o).fn = function()"), "{output}");
        assert!(!output.contains("{{"), "{output}");
        Ok(())
    }

    #[test]
    fn refuses_ambiguous_comments_and_non_sibling_placements() -> Result<(), BudgetExceeded> {
        let inputs = [
            "function f(o){((first()/*between*/,o).p=1);}",
            "function f(o){((first(),o/*after*/).p=1);}",
            "function f(o){if(ready)((first(),o).p=1);}",
            "function f(o){while(ready)((first(),o).p=1);}",
            "function f(o){label:((first(),o).p=1);}",
            "((first(),o).p=1);",
        ];
        for input in inputs {
            let output = rewritten(input)?;
            assert!(
                !output.contains("(first());"),
                "unsupported placement/comment must not be split: {output}"
            );
        }
        Ok(())
    }

    #[test]
    fn unfolds_unconditionally_first_member_object_in_if_test() -> Result<(), BudgetExceeded> {
        let input = "function f(o,bound){if(((record('prefix'),o).length<bound)){record('yes');}else{record('no');}}";
        let output = rewritten(input)?;
        assert!(output.contains("(record('prefix'));"), "{output}");
        assert!(!output.contains("record('prefix'),o"), "{output}");
        assert!(output.contains(".length<bound"), "{output}");
        assert!(
            matches!(
                (
                    output.find("(record('prefix'));"),
                    output.find("if("),
                    output.find("record('yes')")
                ),
                (Some(prefix), Some(guard), Some(yes)) if prefix < guard && guard < yes
            ),
            "{output}"
        );
        Ok(())
    }

    #[test]
    fn never_hoists_noninitial_guard_effects_or_call_callee() -> Result<(), BudgetExceeded> {
        let inputs = [
            "function f(o,flag){if(flag&&((record('late'),o).length<3))act();}",
            "function f(o,flag){if(flag?((record('late'),o).length<3):false)act();}",
            "function f(o){if(read()+((record('late'),o).length<3))act();}",
            "function f(o){if((record('callee'),eval)('o'))act();}",
            "function f(o){if(obj[(record('key'),name)]<3)act();}",
            "function f(o){if(((record('prefix')/*note*/,o).length<3))act();}",
            "function f(o){if(((record('prefix'),o).length<3))/*branch*/act();}",
        ];
        for (index, input) in inputs.into_iter().enumerate() {
            let output = rewritten(input)?;
            if index == 6 {
                // The branch annotation survives a correct rewrite.
                assert!(output.contains("/*branch*/"), "{output}");
                continue;
            }
            assert!(
                !output.contains("(record('late'));")
                    && !output.contains("(record('key'));")
                    && !output.contains("(record('callee'));")
                    && !output.contains("(record('prefix'));"),
                "must not move guarded or ordered effects: {output}"
            );
        }
        Ok(())
    }

    #[test]
    fn first_member_test_preserves_direct_eval_binding() -> Result<(), BudgetExceeded> {
        let input = "function f(o){if(((eval('var flag = 7'),o).value<3)){return flag;}return 0;}";
        let output = rewritten(input)?;
        assert!(output.contains("(eval('var flag = 7'));"), "{output}");
        assert!(output.contains("return flag"), "{output}");
        assert!(!output.contains("eval('var flag = 7'),o"), "{output}");
        Ok(())
    }

    #[test]
    fn lowers_if_test_comma_effects_without_changing_branch_scope() -> Result<(), BudgetExceeded> {
        let input = r#"function initialize(log, condition) {
            if ((log("one"), log("two"), condition)) {
                log("yes");
            } else {
                log("no");
            }
        }"#;
        let output = rewritten(input)?;
        assert!(output.contains("if (condition)"), "{output}");
        assert!(!output.contains("if ((log("), "{output}");
        for word in ["one", "two", "yes", "no"] {
            assert!(output.contains(word), "{output}");
        }
        assert!(
            matches!(
                (
                    output.find("log(\"one\")"),
                    output.find("log(\"two\")"),
                    output.find("if (condition)")
                ),
                (Some(one), Some(two), Some(test)) if one < two && two < test
            ),
            "{output}"
        );
        assert!(output.contains("} else {"), "{output}");
        Ok(())
    }

    #[test]
    fn if_test_split_preserves_direct_eval_and_property_reads() -> Result<(), BudgetExceeded> {
        let input =
            "function f(o,flag){if((eval('var marker=5'),o.value,flag)){return marker;}return 0;}";
        let output = rewritten(input)?;
        assert!(output.contains("eval('var marker=5')"), "{output}");
        assert!(output.contains("(o.value);"), "{output}");
        assert!(output.contains("if(flag)"), "{output}");
        assert!(output.contains("return marker"), "{output}");
        Ok(())
    }

    #[test]
    fn refuses_unbraced_nested_if_and_script_level_test_splitting() -> Result<(), BudgetExceeded> {
        let inputs = [
            "if((effect(),ready))run();",
            "function f(ready){if(ready)if((effect(),ready))run();}",
            "function f(ready){while(ready)if((effect(),ready))run();}",
            "function f(ready){label:if((effect(),ready))run();}",
        ];
        for input in inputs {
            let output = rewritten(input)?;
            assert!(
                output.contains("if((effect(),ready))"),
                "must not split unsupported statement placement: {output}"
            );
            assert!(
                !output.contains("if (ready)"),
                "should not split comma test in unsupported placement: {output}"
            );
        }
        Ok(())
    }

    #[test]
    fn if_test_split_retains_comments_and_refuses_ambiguous_operand_comments(
    ) -> Result<(), BudgetExceeded> {
        let input = "function f(flag){if((ping(),flag))/*branch note*/act();if((ping()/*operand note*/,flag))other();}";
        let output = rewritten(input)?;
        assert!(output.contains("/*branch note*/"), "{output}");
        assert!(output.contains("if(flag)/*branch note*/act()"), "{output}");
        assert!(
            output.contains("if((ping()/*operand note*/,flag))"),
            "{output}"
        );
        Ok(())
    }

    #[test]
    fn top_level_expression_completion_remains_observable() -> Result<(), BudgetExceeded> {
        let source = "(sideEffect(), 42);";
        let output = rewritten(source)?;
        assert_eq!(output, source);
        Ok(())
    }

    #[test]
    fn dynamic_branches_retain_effectful_arm_order() -> Result<(), BudgetExceeded> {
        let input = "function f(n){n ? (push(1),push(2)) : (push(3),push(4));}";
        let output = rewritten(input)?;
        assert!(output.contains("if (n)"), "{output}");
        assert!(output.contains("else"), "{output}");
        assert!(
            matches!(
                (output.find("push(1)"), output.find("push(2)")),
                (Some(first), Some(second)) if first < second
            ),
            "{output}"
        );
        Ok(())
    }
}
