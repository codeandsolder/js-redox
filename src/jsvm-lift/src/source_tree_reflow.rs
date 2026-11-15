//! Reduce syntactic single-trip loops in analyst-only specialized helpers.
//!
//! A loop whose body terminates with an unlabelled break (either directly
//! or under a provably truthy guard) can execute at most once, unless an
//! earlier branch continues that same loop. Preserve the initialization,
//! condition, and evaluation effects of guarded breaks while eliminating
//! unreachable updates and the loop control frame. Original source is retained.
use anyhow::Result;
use jsvm_safe_core::{is_inert_static_literal, known_static_bool_with_resolver};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    ArrowFunctionExpression, BreakStatement, DoWhileStatement, Expression, ForInStatement,
    ForOfStatement, ForStatement, Function, Statement, SwitchStatement, WhileStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::SemanticBuilder;
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::scope::ScopeFlags;
use rolldown_redox::ecmascript::parse_program;

/// Count the loops removed by replacing one terminating iteration with a block.
#[derive(Debug)]
pub struct ReflowedLoops {
    pub source: String,
    pub rewritten_loops: usize,
}

/// Check that jumps in the body before its terminal break cannot repeat the
/// loop or lose their target when that loop is converted to a conditional.
#[derive(Default)]
struct Escapes {
    invalid: bool,
    break_depth: usize,
    loop_depth: usize,
}

impl<'a> Visit<'a> for Escapes {
    fn visit_break_statement(&mut self, stmt: &BreakStatement<'a>) {
        if stmt.label.is_none() && self.break_depth == 0 {
            self.invalid = true;
        }
    }

    fn visit_continue_statement(&mut self, stmt: &oxc_ast::ast::ContinueStatement<'a>) {
        // Any labelled continue might target the loop being removed.
        if stmt.label.is_some() || self.loop_depth == 0 {
            self.invalid = true;
        }
    }

    fn visit_for_statement(&mut self, stmt: &ForStatement<'a>) {
        self.break_depth += 1;
        self.loop_depth += 1;
        walk::walk_for_statement(self, stmt);
        self.loop_depth -= 1;
        self.break_depth -= 1;
    }

    fn visit_for_in_statement(&mut self, stmt: &ForInStatement<'a>) {
        self.break_depth += 1;
        self.loop_depth += 1;
        walk::walk_for_in_statement(self, stmt);
        self.loop_depth -= 1;
        self.break_depth -= 1;
    }

    fn visit_for_of_statement(&mut self, stmt: &ForOfStatement<'a>) {
        self.break_depth += 1;
        self.loop_depth += 1;
        walk::walk_for_of_statement(self, stmt);
        self.loop_depth -= 1;
        self.break_depth -= 1;
    }

    fn visit_while_statement(&mut self, stmt: &WhileStatement<'a>) {
        self.break_depth += 1;
        self.loop_depth += 1;
        walk::walk_while_statement(self, stmt);
        self.loop_depth -= 1;
        self.break_depth -= 1;
    }

    fn visit_do_while_statement(&mut self, stmt: &DoWhileStatement<'a>) {
        self.break_depth += 1;
        self.loop_depth += 1;
        walk::walk_do_while_statement(self, stmt);
        self.loop_depth -= 1;
        self.break_depth -= 1;
    }

    fn visit_switch_statement(&mut self, stmt: &SwitchStatement<'a>) {
        self.break_depth += 1;
        walk::walk_switch_statement(self, stmt);
        self.break_depth -= 1;
    }

    // Abrupt completion inside another function cannot target this loop.
    fn visit_function(&mut self, _: &Function<'a>, _: ScopeFlags) {}
    fn visit_arrow_function_expression(&mut self, _: &ArrowFunctionExpression<'a>) {}
}

/// A sequence's earlier expressions can be effectful, but its final value
/// determines whether the break is taken. Never evaluate or discard them
/// speculatively: the rewrite emits the full original test as a statement.
fn truthy_after_effects(test: &Expression<'_>) -> bool {
    match test {
        Expression::ParenthesizedExpression(paren) => truthy_after_effects(&paren.expression),
        Expression::SequenceExpression(sequence) => sequence
            .expressions
            .last()
            .is_some_and(truthy_after_effects),
        // Each RegExp literal produces a fresh object (and is truthy), just
        // like a proven inert array/object literal. Its value never escapes.
        Expression::RegExpLiteral(_) => true,
        other => known_static_bool_with_resolver(other, &|_| None) == Some(true),
    }
}

fn unlabelled_break(statement: &Statement<'_>) -> bool {
    match statement {
        Statement::BreakStatement(brk) => brk.label.is_none(),
        Statement::BlockStatement(block) if block.body.len() == 1 => {
            block.body.first().is_some_and(unlabelled_break)
        }
        _ => false,
    }
}

/// The final guard may itself evaluate side effects before a provably truthy
/// value. Preserve the complete test expression in the rewritten first trip.
fn terminal_guard_test<'a>(statement: &'a Statement<'a>) -> Option<&'a Expression<'a>> {
    let Statement::IfStatement(guard) = statement else {
        return None;
    };
    (unlabelled_break(&guard.consequent) && truthy_after_effects(&guard.test))
        .then_some(&guard.test)
}

/// Evaluate only the effects of an expression whose result is discarded.
/// Every comma operand still performs GetValue, including getters and direct
/// eval calls. The shared inert-literal proof allows us to omit only operands
/// that cannot invoke code, read bindings, or throw.
fn discarded_guard_effects(test: &Expression<'_>, source: &str) -> Option<String> {
    if is_inert_static_literal(test) {
        return Some(String::new());
    }
    match test {
        Expression::ParenthesizedExpression(paren) => {
            discarded_guard_effects(&paren.expression, source)
        }
        Expression::SequenceExpression(sequence) => {
            let mut effects = String::new();
            for operand in &sequence.expressions {
                effects.push_str(&discarded_guard_effects(operand, source)?);
            }
            Some(effects)
        }
        _ => {
            let expression = source.get(test.span().start as usize..test.span().end as usize)?;
            Some(format!("({expression});"))
        }
    }
}

fn single_trip_body(
    body: &Statement<'_>,
    source: &str,
    completion_discarded: bool,
) -> Option<String> {
    // At script/eval top level, replacing a while with an if can change the
    // observable completion value even when all expressions still execute.
    if !completion_discarded {
        return None;
    }
    let (prefix, terminal) = if let Statement::BlockStatement(block) = body {
        let last = block.body.last()?;
        let mut escapes = Escapes::default();
        for stmt in &block.body[..block.body.len() - 1] {
            escapes.visit_statement(stmt);
        }
        if escapes.invalid {
            return None;
        }
        (
            source.get(block.span.start as usize + 1..last.span().start as usize)?,
            last,
        )
    } else {
        ("", body)
    };
    if unlabelled_break(terminal) {
        return Some(prefix.to_owned());
    }
    let test = terminal_guard_test(terminal)?;
    Some(format!(
        "{prefix} {}",
        discarded_guard_effects(test, source)?
    ))
}

struct LoopCandidate<'s> {
    source: &'s str,
    edits: Vec<(Span, String)>,
    function_depth: usize,
}

impl LoopCandidate<'_> {
    fn slice(&self, span: Span) -> Option<&str> {
        self.source.get(span.start as usize..span.end as usize)
    }
}

impl<'a> Visit<'a> for LoopCandidate<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.function_depth += 1;
        walk::walk_function(self, function, flags);
        self.function_depth -= 1;
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        self.function_depth += 1;
        walk::walk_arrow_function_expression(self, arrow);
        self.function_depth -= 1;
    }

    fn visit_for_statement(&mut self, stmt: &ForStatement<'a>) {
        if let Some(body) = single_trip_body(&stmt.body, self.source, self.function_depth > 0) {
            // The initializer always runs once. The update cannot run because
            // the final break terminates the first iteration, if reached.
            let init = stmt
                .init
                .as_ref()
                .and_then(|init| self.slice(init.span()))
                .map_or_else(String::new, |source| format!("{source};"));
            let test = stmt
                .test
                .as_ref()
                .and_then(|test| self.slice(test.span()))
                .unwrap_or("true");
            self.edits
                .push((stmt.span, format!("{{ {init} if ({test}) {{{body}}} }}")));
        }
        walk::walk_for_statement(self, stmt);
    }

    fn visit_while_statement(&mut self, stmt: &WhileStatement<'a>) {
        if let Some(body) = single_trip_body(&stmt.body, self.source, self.function_depth > 0) {
            if let Some(test) = self.slice(stmt.test.span()) {
                self.edits
                    .push((stmt.span, format!("if ({test}) {{{body}}}")));
            }
        }
        walk::walk_while_statement(self, stmt);
    }

    fn visit_do_while_statement(&mut self, stmt: &DoWhileStatement<'a>) {
        if let Some(body) = single_trip_body(&stmt.body, self.source, self.function_depth > 0) {
            // A terminating first iteration cannot reach the test.
            self.edits.push((stmt.span, format!("{{{body}}}")));
        }
        walk::walk_do_while_statement(self, stmt);
    }
}

/// Structurally recover single-trip loops without guessing the values of
/// arbitrary JavaScript expressions. Reparse each pass so nested candidates
/// become eligible after the containing loop has been rewritten.
pub fn reflow_single_trip_loops(source: &str) -> Result<ReflowedLoops> {
    let mut output = source.to_owned();
    let mut rewritten_loops = 0;
    loop {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &output, SourceType::unambiguous());
        // A detached helper can depend on its original lexical parse context.
        // Keep its source unchanged if it cannot be parsed independently.
        if !parsed.is_clean() {
            break;
        }
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        if !semantic.diagnostics.is_empty() {
            break;
        }
        let mut candidates = LoopCandidate {
            source: &output,
            edits: Vec::new(),
            function_depth: 0,
        };
        candidates.visit_program(&parsed.program);
        // One innermost loop per pass: no overlapping text edits, and each
        // successful pass strictly decreases the source's loop count.
        candidates
            .edits
            .sort_by_key(|(span, _)| (span.end - span.start, span.start));
        let mut changed = false;
        for (span, replacement) in candidates.edits {
            let mut updated = output.clone();
            updated.replace_range(span.start as usize..span.end as usize, &replacement);
            let check_allocator = Allocator::default();
            let check = parse_program(&check_allocator, &updated, SourceType::unambiguous());
            if !check.is_clean()
                || !SemanticBuilder::new()
                    .with_check_syntax_error(true)
                    .build(&check.program)
                    .diagnostics
                    .is_empty()
            {
                continue;
            }
            output = updated;
            rewritten_loops += 1;
            changed = true;
            break;
        }
        if !changed {
            break;
        }
    }
    Ok(ReflowedLoops {
        source: output,
        rewritten_loops,
    })
}

#[cfg(test)]
mod tests {
    use super::reflow_single_trip_loops;
    use anyhow::Result;

    #[test]
    fn reflow_const_function_with_resolved_outer_lexical_and_guarded_break() -> Result<()> {
        let src = r#"const oU = function(log) {
            log.push("step");
            Hm = 42;
            while ({}) if (log.push("loop"), true) break;
            return Hm;
        };"#;
        let out = reflow_single_trip_loops(src)?;
        assert_eq!(out.rewritten_loops, 1, "{:?}", out);
        assert!(!out.source.contains("while"), "{}", out.source);
        assert!(out.source.contains("log.push"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn for_preserves_initializer_and_guard_but_eliminates_update() -> Result<()> {
        let src = "function f(t){for (init(); t; update()) { work(); break; } return 2;}";
        let out = reflow_single_trip_loops(src)?;
        assert_eq!(out.rewritten_loops, 1);
        assert!(
            out.source.contains("init(); if (t) { work();"),
            "{}",
            out.source
        );
        assert!(!out.source.contains("update()"));
        Ok(())
    }

    #[test]
    fn labeled_original_helper_breaks_remain_legal() -> Result<()> {
        let src = "const O=function(J,Q,Y,q){for(0;(Q&90)==Q;true){a:{if(J.Y){q=w8(J,J.D);break a;}q=Y;}break;}return q;};";
        let out = reflow_single_trip_loops(src)?;
        assert_eq!(out.rewritten_loops, 1);
        assert!(out.source.contains("a:{if(J.Y)"), "{}", out.source);
        assert!(out.source.contains("if ((Q&90)==Q)"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn nested_loops_reflow_and_preserve_inner_continue() -> Result<()> {
        let src = "function f(x){while(x){for(let i=0;i<3;i++){if(i)continue;}emit();break;}}";
        let out = reflow_single_trip_loops(src)?;
        assert_eq!(out.rewritten_loops, 1);
        assert!(
            out.source.contains("for(let i=0;i<3;i++)"),
            "{}",
            out.source
        );
        assert!(out.source.contains("if (x)"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn while_and_do_while_guard_evaluation() -> Result<()> {
        let src = "function f(x){while(check(x)){if(x)return 4;break;}do{work(x);break;}while(shouldNotRun());}";
        let out = reflow_single_trip_loops(src)?;
        assert_eq!(out.rewritten_loops, 2);
        assert!(out.source.contains("if (check(x))"), "{}", out.source);
        assert!(!out.source.contains("shouldNotRun()"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn reflows_effectful_but_truthy_guarded_breaks() -> Result<()> {
        let source = r#"function f(){
            while ({}) if ((trace.push("while"), {})) break;
            while ("X") if ((trace.push("again"), true)) {break;}
            for (init(); enabled(); update()) {
                trace.push("prefix");
                if ((trace.push("guard"), [])) break;
            }
            do if ((trace.push("do"), {})) break; while (never());
        }"#;
        let out = reflow_single_trip_loops(source)?;
        assert_eq!(out.rewritten_loops, 4, "{}", out.source);
        assert!(!out.source.contains("while ("), "{}", out.source);
        assert!(!out.source.contains("update()"), "{}", out.source);
        assert!(!out.source.contains("never()"), "{}", out.source);
        for preserved in [
            "trace.push(\"while\")",
            "trace.push(\"again\")",
            "trace.push(\"prefix\")",
            "trace.push(\"guard\")",
            "trace.push(\"do\")",
            "init()",
            "enabled()",
        ] {
            assert!(
                out.source.contains(preserved),
                "{preserved}: {}",
                out.source
            );
        }
        Ok(())
    }

    #[test]
    fn discards_inert_guard_values_but_keeps_every_effect() -> Result<()> {
        let source = r#"function f(log, obj){
            while (true) if ((log.push("first"), (obj.value, {}))) break;
            while ("X") if ((log.push("second"), [])) break;
            while (2) if ((log.push("third"), 17)) break;
            while (true) if ((log.push("fourth"), "always")) break;
            while (true) if ((log.push("fifth"), /x/)) break;
        }"#;
        let out = reflow_single_trip_loops(source)?;
        assert_eq!(out.rewritten_loops, 5, "{}", out.source);
        for preserved in [
            "log.push(\"first\")",
            "obj.value",
            "log.push(\"second\")",
            "log.push(\"third\")",
            "log.push(\"fourth\")",
            "log.push(\"fifth\")",
        ] {
            assert!(
                out.source.contains(preserved),
                "{preserved}: {}",
                out.source
            );
        }
        for inert in ["({});", "[];", "(17);", "(\"always\");", "(/x/);"] {
            assert!(!out.source.contains(inert), "{inert}: {}", out.source);
        }
        Ok(())
    }

    #[test]
    fn retains_completion_sensitive_guards_at_script_level() -> Result<()> {
        let source = "while(true)if((trace(),{}))break;";
        let out = reflow_single_trip_loops(source)?;
        assert_eq!(out.rewritten_loops, 0);
        assert_eq!(out.source, source);
        Ok(())
    }

    #[test]
    fn preserves_direct_eval_and_accessor_effects_in_guard_prefixes() -> Result<()> {
        let source = "function f(obj){while(true)if((eval('obj.seen=1'),obj.value,{}))break;}";
        let out = reflow_single_trip_loops(source)?;
        assert_eq!(out.rewritten_loops, 1);
        assert!(
            out.source.contains("(eval('obj.seen=1'));"),
            "{}",
            out.source
        );
        assert!(out.source.contains("(obj.value);"), "{}", out.source);
        assert!(!out.source.contains("({});"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn does_not_assume_effectful_or_false_guards_are_truthy() -> Result<()> {
        for source in [
            "function f(x){while('X')if(x)break;}",
            "function f(){while('X')if((effect(),false))break;}",
            "function f(){while('X')if((effect(),unknown))break;}",
            "function f(){while('X')if((effect(),{get prop(){return 3;}}))break;}",
            "function f(){while('X'){if(x)break;}}",
            "function f(){while('X'){if((effect(),{}))continue;}}",
            "function f(){while('X'){if((effect(),{}))break outer;}}",
        ] {
            let out = reflow_single_trip_loops(source)?;
            assert_eq!(out.rewritten_loops, 0, "{source}: {}", out.source);
            assert_eq!(out.source, source);
        }
        Ok(())
    }

    #[test]
    fn one_trip_guarded_break_rejects_outer_loop_escapes() -> Result<()> {
        for source in [
            "function f(x){outer:while(x){if(x)continue outer;if((tick(),{}))break;}}",
            "function f(x){while(x){if(x)continue;if((tick(),{}))break;}}",
            "function f(x){while(x){if(x)break;if((tick(),{}))break;}}",
        ] {
            let out = reflow_single_trip_loops(source)?;
            assert_eq!(out.rewritten_loops, 0, "{source}: {}", out.source);
        }
        Ok(())
    }

    #[test]
    fn unsupported_detached_syntax_does_not_fail_the_source_tree() -> Result<()> {
        let src = "function f( { this is not valid";
        let out = reflow_single_trip_loops(src)?;
        assert_eq!(out.source, src);
        assert_eq!(out.rewritten_loops, 0);
        Ok(())
    }

    #[test]
    fn rejects_paths_that_can_break_early_or_repeat_loop() -> Result<()> {
        for src in [
            "function f(x){while(x){if(x)continue;break;}}",
            "function f(x){for(;x;update()){if(x)break;work();break;}}",
            "function f(x){outer:while(x){if(x)continue outer;break;}}",
            "function f(x){while(x){switch(x){case 1: continue;}break;}}",
        ] {
            let out = reflow_single_trip_loops(src)?;
            assert_eq!(out.rewritten_loops, 0, "{src}: {}", out.source);
            assert_eq!(out.source, src);
        }
        Ok(())
    }
}
