//! Reduce syntactic single-trip loops in analyst-only specialized helpers.
//!
//! A loop whose block ends in an unconditional, unlabelled break can execute
//! its body at most once, unless an earlier branch continues that same loop.
//! Preserve the initialization and condition, but eliminate the unreachable
//! update and the loop control frame. The original helper remains available.
use anyhow::Result;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    ArrowFunctionExpression, BreakStatement, DoWhileStatement, ForInStatement, ForOfStatement,
    ForStatement, Function, Statement, SwitchStatement, WhileStatement,
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

fn single_trip_body<'a>(body: &'a Statement<'a>, source: &'a str) -> Option<&'a str> {
    let Statement::BlockStatement(block) = body else {
        return None;
    };
    let Some(Statement::BreakStatement(brk)) = block.body.last() else {
        return None;
    };
    if brk.label.is_some() {
        return None;
    }
    let mut escapes = Escapes::default();
    for stmt in &block.body[..block.body.len() - 1] {
        escapes.visit_statement(stmt);
    }
    if escapes.invalid {
        return None;
    }
    source.get(block.span.start as usize + 1..brk.span.start as usize)
}

struct LoopCandidate<'s> {
    source: &'s str,
    edits: Vec<(Span, String)>,
}

impl LoopCandidate<'_> {
    fn slice(&self, span: Span) -> Option<&str> {
        self.source.get(span.start as usize..span.end as usize)
    }
}

impl<'a> Visit<'a> for LoopCandidate<'_> {
    fn visit_for_statement(&mut self, stmt: &ForStatement<'a>) {
        if let Some(body) = single_trip_body(&stmt.body, self.source) {
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
        if let Some(body) = single_trip_body(&stmt.body, self.source) {
            if let Some(test) = self.slice(stmt.test.span()) {
                self.edits
                    .push((stmt.span, format!("if ({test}) {{{body}}}")));
            }
        }
        walk::walk_while_statement(self, stmt);
    }

    fn visit_do_while_statement(&mut self, stmt: &DoWhileStatement<'a>) {
        if let Some(body) = single_trip_body(&stmt.body, self.source) {
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
