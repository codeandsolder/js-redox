//! Symbol-resolved terminal return dataflow in original lexical helper views.
//!
//! A function-owned return temporary can be eliminated at a terminal store
//! when no escaped closure, dynamic scope, or argument alias can observe it.
//! Earlier local reads and writes remain intact; branch joins are handled
//! without assuming the temporary was otherwise unused.
//! This is an analyst-only source view, never a rewrite of captured executable
//! reconstruction. Never infer values from spelling alone.
use anyhow::Result;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    ArrowFunctionExpression, AssignmentTarget, Expression, Function, FunctionBody,
    IdentifierReference, Statement, WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{
    operator::AssignmentOperator,
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use rolldown_redox::ecmascript::parse_program;

#[derive(Debug)]
pub struct RecoveredReturns {
    pub source: String,
    pub adjacent_returns: usize,
    pub labeled_joins: usize,
    pub guarded_joins: usize,
}

#[derive(Default)]
struct DynamicScope {
    present: bool,
}

impl<'a> Visit<'a> for DynamicScope {
    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        if matches!(id.name.as_str(), "arguments" | "eval") {
            self.present = true;
        }
    }

    fn visit_with_statement(&mut self, _: &WithStatement<'a>) {
        self.present = true;
    }
}

/// References from nested functions can observe a terminal store after
/// the enclosing function returns, so a captured binding is never inlined.
struct CapturedBinding<'s> {
    scoping: &'s Scoping,
    symbol: SymbolId,
    nested_functions: usize,
    captured: bool,
}

impl<'a> Visit<'a> for CapturedBinding<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.nested_functions += 1;
        walk::walk_function(self, function, flags);
        self.nested_functions -= 1;
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        self.nested_functions += 1;
        walk::walk_arrow_function_expression(self, arrow);
        self.nested_functions -= 1;
    }

    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        if self.nested_functions > 0 && binding(self.scoping, id) == Some(self.symbol) {
            self.captured = true;
        }
    }
}

fn binding(scoping: &Scoping, id: &IdentifierReference<'_>) -> Option<SymbolId> {
    id.reference_id
        .get()
        .and_then(|reference| scoping.get_reference(reference).symbol_id())
}

fn assignment<'a>(
    statement: &'a Statement<'a>,
) -> Option<(&'a IdentifierReference<'a>, &'a Expression<'a>)> {
    let Statement::ExpressionStatement(statement) = statement else {
        return None;
    };
    let Expression::AssignmentExpression(assignment) = &statement.expression else {
        return None;
    };
    if assignment.operator != AssignmentOperator::Assign {
        return None;
    }
    let AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left else {
        return None;
    };
    Some((target, &assignment.right))
}

fn ident_return<'a>(statement: &'a Statement<'a>) -> Option<&'a IdentifierReference<'a>> {
    let Statement::ReturnStatement(statement) = statement else {
        return None;
    };
    let Expression::Identifier(id) = statement.argument.as_ref()? else {
        return None;
    };
    Some(id)
}

fn snippet(source: &str, span: Span) -> Option<&str> {
    source.get(span.start as usize..span.end as usize)
}

enum Kind {
    Adjacent,
    LabeledJoin,
    GuardedJoin,
}

struct Candidate {
    span: Span,
    replacement: String,
    kind: Kind,
}

struct ReturnFlow<'s> {
    scoping: &'s Scoping,
    source: &'s str,
    function_scope: Option<ScopeId>,
    edits: Vec<Candidate>,
}

impl ReturnFlow<'_> {
    /// Recover both edges of a labeled branch join, preserving the original
    /// condition, intervening effects and lexical block scope.
    fn labeled_join(&self, statement: &Statement<'_>, symbol: SymbolId) -> Option<String> {
        let Statement::LabeledStatement(label) = statement else {
            return None;
        };
        let Statement::BlockStatement(block) = &label.body else {
            return None;
        };
        if block.body.len() < 2 {
            return None;
        }
        let Statement::IfStatement(branch) = block.body.first()? else {
            return None;
        };
        if branch.alternate.is_some() {
            return None;
        }
        let Statement::BlockStatement(consequent) = &branch.consequent else {
            return None;
        };
        let [first, Statement::BreakStatement(jump)] = consequent.body.as_slice() else {
            return None;
        };
        if jump
            .label
            .as_ref()
            .is_none_or(|name| name.name != label.label.name)
        {
            return None;
        }
        let (branch_target, branch_rhs) = assignment(first)?;
        let (last_target, last_rhs) = assignment(block.body.last()?)?;
        if binding(self.scoping, branch_target) != Some(symbol)
            || binding(self.scoping, last_target) != Some(symbol)
        {
            return None;
        }
        let condition = snippet(self.source, branch.test.span())?;
        let branch_value = snippet(self.source, branch_rhs.span())?;
        let last_value = snippet(self.source, last_rhs.span())?;
        let middle = if block.body.len() > 2 {
            snippet(
                self.source,
                Span::new(
                    block.body[1].span().start,
                    block.body[block.body.len() - 2].span().end,
                ),
            )?
        } else {
            ""
        };
        // A second break to this label will fail syntax validation when the
        // label is removed. Do not infer anything about unknown expressions.
        Some(format!(
            "{{ if ({condition}) {{ return ({branch_value}); }} {middle} return ({last_value}); }}"
        ))
    }

    /// Preserve an entire branch, including lexical scope and every prefix
    /// statement. Replace only its last plain assignment with a return.
    /// A normal fallthrough path must reach the assignment; early abrupt
    /// completions retain their behavior because the prefix is unchanged.
    fn branch_direct_return(&self, statement: &Statement<'_>, symbol: SymbolId) -> Option<String> {
        let tail = match statement {
            Statement::BlockStatement(block) => block.body.last()?,
            other => other,
        };
        let (target, rhs) = assignment(tail)?;
        if binding(self.scoping, target) != Some(symbol) {
            return None;
        }
        let value = snippet(self.source, rhs.span())?;
        let source = snippet(self.source, statement.span())?;
        let start = (tail.span().start - statement.span().start) as usize;
        let end = (tail.span().end - statement.span().start) as usize;
        let mut rewritten = source.to_owned();
        rewritten.replace_range(start..end, &format!("return ({value});"));
        if matches!(statement, Statement::BlockStatement(_)) {
            Some(rewritten)
        } else {
            Some(format!("{{ {rewritten} }}"))
        }
    }

    fn recover_body(&mut self, body: &FunctionBody<'_>) {
        let statements = &body.statements;
        let Some(returned) = statements.last().and_then(ident_return) else {
            return;
        };
        let mut dynamic = DynamicScope::default();
        dynamic.visit_function_body(body);
        if dynamic.present {
            return;
        }
        let Some(symbol) = binding(self.scoping, returned) else {
            return;
        };
        // A symbol defined in an enclosing function/module is externally
        // observable even when only the current function writes and returns it.
        // Only rewrite a binding owned by THIS function's lexical environment.
        if self.function_scope != Some(self.scoping.symbol_scope_id(symbol)) {
            return;
        }
        // Earlier reads and writes have already executed before the terminal
        // store, so only future observers matter. An escaped closure could
        // still read that variable after this function returns.
        let mut capture = CapturedBinding {
            scoping: self.scoping,
            symbol,
            nested_functions: 0,
            captured: false,
        };
        capture.visit_function_body(body);
        if capture.captured {
            return;
        }
        let Some(before) = statements.get(statements.len().saturating_sub(2)) else {
            return;
        };
        let Some(return_statement) = statements.last() else {
            return;
        };

        if let Some((target, rhs)) = assignment(before) {
            if binding(self.scoping, target) == Some(symbol) {
                if let Some(expr) = snippet(self.source, rhs.span()) {
                    self.edits.push(Candidate {
                        span: Span::new(before.span().start, return_statement.span().end),
                        replacement: format!("return ({expr});"),
                        kind: Kind::Adjacent,
                    });
                }
            }
            return;
        }

        if let Some(replacement) = self.labeled_join(before, symbol) {
            self.edits.push(Candidate {
                span: Span::new(before.span().start, return_statement.span().end),
                replacement,
                kind: Kind::LabeledJoin,
            });
            return;
        }

        let Statement::IfStatement(branch) = before else {
            return;
        };
        let Some(condition) = snippet(self.source, branch.test.span()) else {
            return;
        };

        // If both edges assign the returned temporary, replace the entire
        // join. Otherwise keep the original terminal return as the false
        // path's value (especially relevant for formal parameters).
        if let Some(alternate) = branch.alternate.as_ref() {
            let (Some(yes), Some(no)) = (
                self.branch_direct_return(&branch.consequent, symbol),
                self.branch_direct_return(alternate, symbol),
            ) else {
                return;
            };
            self.edits.push(Candidate {
                span: Span::new(before.span().start, return_statement.span().end),
                replacement: format!("if ({condition}) {yes} else {no}"),
                kind: Kind::GuardedJoin,
            });
            return;
        }

        let new_consequent = self
            .branch_direct_return(&branch.consequent, symbol)
            .or_else(|| {
                let labeled = match &branch.consequent {
                    Statement::LabeledStatement(_) => Some(&branch.consequent),
                    Statement::BlockStatement(block) if block.body.len() == 1 => block.body.first(),
                    _ => None,
                };
                labeled.and_then(|stmt| self.labeled_join(stmt, symbol))
            });
        if let Some(consequent) = new_consequent {
            self.edits.push(Candidate {
                span: before.span(),
                replacement: format!("if ({condition}) {consequent}"),
                kind: Kind::GuardedJoin,
            });
        }
    }
}

impl<'a> Visit<'a> for ReturnFlow<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        let enclosing = self.function_scope;
        self.function_scope = function.scope_id.get();
        walk::walk_function(self, function, flags);
        self.function_scope = enclosing;
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        let enclosing = self.function_scope;
        self.function_scope = arrow.scope_id.get();
        walk::walk_arrow_function_expression(self, arrow);
        self.function_scope = enclosing;
    }

    fn visit_function_body(&mut self, body: &FunctionBody<'a>) {
        self.recover_body(body);
        walk::walk_function_body(self, body);
    }
}

/// Recover direct return values through a provably unobservable terminal
/// temporary. Independently reparse/re-resolve each edit to avoid overlaps.
pub fn recover_terminal_returns(source: &str) -> Result<RecoveredReturns> {
    let mut output = source.to_owned();
    let mut adjacent_returns = 0;
    let mut labeled_joins = 0;
    let mut guarded_joins = 0;
    loop {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &output, SourceType::unambiguous());
        if !parsed.is_clean() {
            break;
        }
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        if !semantic.diagnostics.is_empty() {
            break;
        }
        let mut analyzer = ReturnFlow {
            scoping: semantic.semantic.scoping(),
            source: &output,
            function_scope: None,
            edits: Vec::new(),
        };
        analyzer.visit_program(&parsed.program);
        analyzer
            .edits
            .sort_by_key(|edit| (edit.span.end - edit.span.start, edit.span.start));

        let mut changed = false;
        for edit in analyzer.edits {
            let mut next = output.clone();
            next.replace_range(
                edit.span.start as usize..edit.span.end as usize,
                &edit.replacement,
            );
            let verification = Allocator::default();
            let parsed_next = parse_program(&verification, &next, SourceType::unambiguous());
            if !parsed_next.is_clean()
                || !SemanticBuilder::new()
                    .with_check_syntax_error(true)
                    .build(&parsed_next.program)
                    .diagnostics
                    .is_empty()
            {
                continue;
            }
            output = next;
            match edit.kind {
                Kind::Adjacent => adjacent_returns += 1,
                Kind::LabeledJoin => labeled_joins += 1,
                Kind::GuardedJoin => guarded_joins += 1,
            }
            changed = true;
            break;
        }
        if !changed {
            break;
        }
    }
    Ok(RecoveredReturns {
        source: output,
        adjacent_returns,
        labeled_joins,
        guarded_joins,
    })
}

#[cfg(test)]
mod tests {
    use super::recover_terminal_returns;
    use anyhow::Result;

    #[test]
    fn rewrites_adjacent_assignment_when_unused_elsewhere() -> Result<()> {
        let src = "const f = function(q, x){sideEffect();q = x+3;return q;};";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.adjacent_returns, 1);
        assert_eq!(out.labeled_joins, 0);
        assert!(
            out.source.contains("sideEffect();return (x+3);"),
            "{}",
            out.source
        );
        Ok(())
    }

    #[test]
    fn rewrites_labeled_join_with_independent_side_effects() -> Result<()> {
        let src = "const V=function(J,Y,H){a:{if(J.Y){H=w8(J,J.D);break a;}if((Y=$X(8,J,true),Y)&128){Y^=128;}H=Y;}return H;};";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.labeled_joins, 1);
        assert!(out.source.contains("return (w8(J,J.D));"), "{}", out.source);
        assert!(out.source.contains("return (Y);"), "{}", out.source);
        assert!(!out.source.contains("break a"), "{}", out.source);
        assert!(!out.source.contains("return H"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn never_remove_writes_observed_through_aliases_or_dynamic_scope() -> Result<()> {
        let unsafe_cases = [
            "function f(q){const g=()=>q;q=2;return q;}",
            "function f(q){q=2;console.log(q);return q;}",
            "function f(q){const a=arguments;q=2;return q;}",
            "function f(q){eval('q=9');q=2;return q;}",
            "function f(q){with({}){}q=2;return q;}",
            "function f(q){q=2;return arguments[0];}",
        ];
        for src in unsafe_cases {
            let out = recover_terminal_returns(src)?;
            assert_eq!(out.source, src, "{src} -> {}", out.source);
            assert_eq!(out.adjacent_returns, 0);
        }
        Ok(())
    }

    #[test]
    fn terminal_store_is_dead_after_earlier_reads_and_writes() -> Result<()> {
        for (source, expected_kind) in [
            ("function f(q){q++;q=2;return q;}", "adjacent"),
            ("function f(q){log(q);q=3;return q;}", "adjacent"),
            ("function f(q,x){q=3;if(x)q=touch(q);return q;}", "guarded"),
            (
                "function f(q,x){q=3;if(x){q=left(q);}else{q=right(q);}return q;}",
                "guarded",
            ),
            (
                "function f(q,x){q++;a:{if(x){q=left(q);break a;}q=right(q);}return q;}",
                "labeled",
            ),
        ] {
            let out = recover_terminal_returns(source)?;
            let count = match expected_kind {
                "adjacent" => out.adjacent_returns,
                "guarded" => out.guarded_joins,
                "labeled" => out.labeled_joins,
                _ => unreachable!(),
            };
            assert_eq!(count, 1, "{source}: {}", out.source);
        }
        Ok(())
    }

    #[test]
    fn closure_capture_keeps_terminal_assignments_observable() -> Result<()> {
        for source in [
            "function f(q){const g=function(){return q;};q=3;return q;}",
            "function f(q){const g=()=>()=>q;q=3;return q;}",
            "function f(q){const obj={get x(){return q;}};q=3;return q;}",
            "function f(q,x){const obj={m(){return q;}};if(x){q=left();}return q;}",
            "function f(q,x){const g=(x=q)=>x;if(x){q=left();}return q;}",
        ] {
            let out = recover_terminal_returns(source)?;
            assert_eq!(out.source, source, "{source}: {}", out.source);
        }
        Ok(())
    }

    #[test]
    fn respect_reference_identity_and_preserve_early_exit_behavior() -> Result<()> {
        let cases = [
            "function f(q,x){let q=2;q=x;return q;}",
            "const f=function(H){a:{if(x){H=first();break a;}H=second();}other();return H;};",
            "function f(H){a:{if(x){H=first();break a;}H=second();}return arguments[0];}",
        ];
        for src in cases {
            let out = recover_terminal_returns(src)?;
            assert_eq!(out.source, src, "{src} -> {}", out.source);
        }
        Ok(())
    }

    #[test]
    fn guarded_assignment_preserves_initial_return_value_on_false_path() -> Result<()> {
        let src = "function f(q, x){if(x){q=touch(x);}return q;}";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.guarded_joins, 1);
        assert!(out.source.contains("return (touch(x));"), "{}", out.source);
        assert!(out.source.ends_with("return q;}"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn complete_if_else_join_returns_each_branch_directly() -> Result<()> {
        let src = "function f(q, x){if(x)q=left();else{q=right();}return q;}";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.guarded_joins, 1);
        assert!(out.source.contains("return (left());"), "{}", out.source);
        assert!(out.source.contains("return (right());"), "{}", out.source);
        assert!(!out.source.contains("return q;"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn guarded_labeled_join_recovers_original_multimode_helper() -> Result<()> {
        let src = "const V=function(J,Q,Y,L,H){if((Q>>2&5)==1){a:{if(J.Y){H=w8(J,J.D);break a;}if((Y=$X(8,J,true),Y)&128){Y^=128;L=$X(2,J,true);Y=(Y<<2)+(L|0);}H=Y;}}return H;};";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.guarded_joins, 1, "{}", out.source);
        assert_eq!(out.labeled_joins, 0);
        assert!(out.source.contains("return (w8(J,J.D));"), "{}", out.source);
        assert!(out.source.contains("return (Y);"), "{}", out.source);
        assert!(out.source.contains("return H;"), "{}", out.source);
        assert!(!out.source.contains("break a;"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn guarded_joins_reject_intermediate_effects_or_observable_bindings() -> Result<()> {
        for src in [
            "function f(x,q){if(x){q=left();after();}return q;}",
            "function f(x,q){if(x){q=left();}else{right();}return q;}",
            "function f(x,q){if(x){q=left();}else{q=right();observe(q);}return q;}",
            "function f(x,q){if(x){q=left();}console.log(q);return q;}",
            "function f(x,q){if(x){try{q=left();}finally{other();}}return q;}",
            "function f(x,q){if(x){a:{if(x){q=left();break a;}q=right();}other();}return q;}",
            "function f(x,q){if(x){q=left();}return arguments[0];}",
        ] {
            let out = recover_terminal_returns(src)?;
            assert_eq!(out.source, src, "{src} -> {}", out.source);
            assert_eq!(out.guarded_joins, 0);
        }
        Ok(())
    }

    #[test]
    fn enclosing_lexical_assignments_are_observable_and_must_remain() -> Result<()> {
        for src in [
            "let shared;function f(){shared=touch();return shared;}",
            "let shared;const f=()=>{shared=touch();return shared;};",
            "function outer(){let q;function inner(){q=touch();return q;}return inner;}",
            "function outer(){let q;const inner=()=>{if(flag){q=touch();}return q;};return inner;}",
            "let state;function f(flag){if(flag){state=one();}else{state=two();}return state;}",
        ] {
            let out = recover_terminal_returns(src)?;
            assert_eq!(out.source, src, "{src} -> {}", out.source);
            assert_eq!(
                out.adjacent_returns + out.labeled_joins + out.guarded_joins,
                0
            );
        }
        Ok(())
    }

    #[test]
    fn function_owned_bindings_work_in_arrows_methods_and_nested_functions() -> Result<()> {
        for src in [
            "const f=(q,x)=>{if(x){q=touch(x);}return q;};",
            "class C{method(q,x){if(x){q=touch(x);}return q;}}",
            "function outer(){const f=function(q,x){if(x){q=touch(x);}return q;};return f;}",
        ] {
            let out = recover_terminal_returns(src)?;
            assert_eq!(out.guarded_joins, 1, "{src}: {}", out.source);
        }
        Ok(())
    }

    #[test]
    fn guarded_return_keeps_effectful_prefix_and_local_block_scope() -> Result<()> {
        let src = "function f(q,x){if(x){log('prefix');let local=touch();if(local<0)return -1;q=combine(local,q);}return q;}";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.guarded_joins, 1, "{}", out.source);
        assert!(
            out.source
                .contains("log('prefix');let local=touch();if(local<0)return -1;"),
            "{}",
            out.source
        );
        assert!(
            out.source.contains("return (combine(local,q));"),
            "{}",
            out.source
        );
        assert!(out.source.ends_with("return q;}"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn complete_if_else_joins_keep_both_effectful_prefixes() -> Result<()> {
        let src = "function f(q,x){if(x){log(1);const v=a();q=left(v,q);}else{log(2);const v=b();q=right(v,q);}return q;}";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.guarded_joins, 1, "{}", out.source);
        assert!(out
            .source
            .contains("log(1);const v=a();return (left(v,q));"));
        assert!(out
            .source
            .contains("log(2);const v=b();return (right(v,q));"));
        assert!(!out.source.contains("return q;"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn knitsail_hv_callback_prefix_is_preserved() -> Result<()> {
        let src = "const hV=function(J,Q,Y,u){if(!(J-5&14)){Q(function(n){n(Y);});u=[function(){return Y;},function(){}];}return u;};";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.guarded_joins, 1, "{}", out.source);
        assert!(
            out.source
                .contains("Q(function(n){n(Y);});return ([function(){return Y;},function(){}]);"),
            "{}",
            out.source
        );
        assert!(out.source.contains("return u;"), "{}", out.source);
        assert!(!out.source.contains("u=[function()"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn prefix_early_exits_or_loop_controls_keep_their_original_order() -> Result<()> {
        for src in [
            "function f(q,x){if(x){if(q)return 7;trace();q=one();}return q;}",
            "function f(q,x){if(x){label:{if(q)break label;trace();}q=one();}return q;}",
            "function f(q,x){if(x){for(let n=0;n<3;n++){trace(n);if(n===1)break;}q=one();}return q;}",
        ] {
            let out = recover_terminal_returns(src)?;
            assert_eq!(out.guarded_joins, 1, "{src}: {}", out.source);
            assert!(out.source.contains("return (one());"), "{}", out.source);
            assert!(!out.source.contains("q=one();"), "{}", out.source);
        }
        Ok(())
    }

    #[test]
    fn nonterminal_assignment_still_must_remain() -> Result<()> {
        for src in [
            "function f(q,x){if(x){q=one();trace();}return q;}",
            "function f(q,x){if(x){trace();q=one();trace();}return q;}",
            "function f(q,x){if(x){q=one();trace();}else{q=two();}return q;}",
            "function f(q,x){if(x){q=one();}else{q=two();trace();}return q;}",
            "function f(q,x){const saved=()=>q;if(x){trace();q=one();}return q;}",
        ] {
            let out = recover_terminal_returns(src)?;
            assert_eq!(out.source, src, "{src}: {}", out.source);
            assert_eq!(out.guarded_joins, 0);
        }
        Ok(())
    }

    #[test]
    fn detached_invalid_source_is_unchanged() -> Result<()> {
        let src = "function f ( { not valid";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.source, src);
        Ok(())
    }
}
