//! Symbol-resolved terminal return dataflow in original lexical helper views.
//!
//! A function-owned return temporary can be eliminated at a terminal store
//! when assignment completion, implicit naming and deferred observers are preserved.
//! Earlier local reads and writes remain intact; branch joins are handled
//! without assuming the temporary was otherwise unused.
//! This is an analyst-only source view, never a rewrite of captured executable
//! reconstruction. Never infer values from spelling alone.
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    AccessorProperty, ArrowFunctionBody, ArrowFunctionExpression, AssignmentExpression,
    AssignmentTarget, Expression, FormalParameters, Function, FunctionBody, IdentifierReference,
    PropertyDefinition, Statement, WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{
    operator::AssignmentOperator,
    scope::{ScopeFlags, ScopeId},
    symbol::{SymbolFlags, SymbolId},
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
    deferred_depth: usize,
    captured: bool,
}

impl CapturedBinding<'_> {
    fn field_initializer(&mut self, is_static: bool, value: Option<&Expression<'_>>) {
        if let Some(value) = value {
            self.deferred_depth += usize::from(!is_static);
            self.visit_expression(value);
            self.deferred_depth -= usize::from(!is_static);
        }
    }
}

impl<'a> Visit<'a> for CapturedBinding<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.deferred_depth += 1;
        walk::walk_function(self, function, flags);
        self.deferred_depth -= 1;
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        self.deferred_depth += 1;
        walk::walk_arrow_function_expression(self, arrow);
        self.deferred_depth -= 1;
    }

    fn visit_property_definition(&mut self, field: &PropertyDefinition<'a>) {
        self.visit_decorators(&field.decorators);
        self.visit_property_key(&field.key);
        // Only instance initialization is deferred; computed keys and static
        // field initialization occur during class definition.
        self.field_initializer(field.r#static, field.value.as_ref());
    }

    fn visit_accessor_property(&mut self, field: &AccessorProperty<'a>) {
        self.visit_decorators(&field.decorators);
        self.visit_property_key(&field.key);
        self.field_initializer(field.r#static, field.value.as_ref());
    }

    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        if self.deferred_depth > 0 && binding(self.scoping, id) == Some(self.symbol) {
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
) -> Option<(&'a IdentifierReference<'a>, &'a AssignmentExpression<'a>)> {
    let Statement::ExpressionStatement(statement) = statement else {
        return None;
    };
    let Expression::AssignmentExpression(assignment) = statement.expression.without_parentheses()
    else {
        return None;
    };
    if assignment.operator != AssignmentOperator::Assign {
        return None;
    }
    let AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left else {
        return None;
    };
    Some((target, assignment))
}

fn ident_return<'a>(statement: &'a Statement<'a>) -> Option<&'a IdentifierReference<'a>> {
    let Statement::ReturnStatement(statement) = statement else {
        return None;
    };
    let Expression::Identifier(id) = statement.argument.as_ref()?.without_parentheses() else {
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
    edits: Vec<Candidate>,
}

impl ReturnFlow<'_> {
    /// Keep NamedEvaluation in its original assignment context. Naming an
    /// anonymous class explicitly would introduce a new lexical name binding
    /// and may change what its static initializers observe.
    fn terminal_value(&self, assignment: &AssignmentExpression<'_>) -> Option<&str> {
        let span = if assignment.right.is_anonymous_function_definition() {
            assignment.span
        } else {
            assignment.right.span()
        };
        snippet(self.source, span)
    }

    /// The assigned value equals the subsequently read binding only for a
    /// mutable local. Include parameter initializers in the observer proof:
    /// they can create closures or use eval before the body is entered.
    fn terminal_symbol(
        &self,
        body: &FunctionBody<'_>,
        params: &FormalParameters<'_>,
        scope: Option<ScopeId>,
    ) -> Option<SymbolId> {
        let returned = body.statements.last().and_then(ident_return)?;
        let symbol = binding(self.scoping, returned)?;
        if scope != Some(self.scoping.symbol_scope_id(symbol)) {
            return None;
        }
        let flags = self.scoping.symbol_flags(symbol);
        if !flags.intersects(SymbolFlags::Variable | SymbolFlags::Function | SymbolFlags::Class)
            || flags.intersects(SymbolFlags::ConstVariable | SymbolFlags::FunctionExpression)
        {
            return None;
        }
        let mut dynamic = DynamicScope::default();
        dynamic.visit_formal_parameters(params);
        dynamic.visit_function_body(body);
        if dynamic.present {
            return None;
        }
        let mut capture = CapturedBinding {
            scoping: self.scoping,
            symbol,
            deferred_depth: 0,
            captured: false,
        };
        capture.visit_formal_parameters(params);
        capture.visit_function_body(body);
        (!capture.captured).then_some(symbol)
    }

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
        let branch_value = self.terminal_value(branch_rhs)?;
        let last_value = self.terminal_value(last_rhs)?;
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
        let value = self.terminal_value(rhs)?;
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

    fn recover_body(
        &mut self,
        body: &FunctionBody<'_>,
        params: &FormalParameters<'_>,
        scope: Option<ScopeId>,
    ) {
        let statements = &body.statements;
        let Some(symbol) = self.terminal_symbol(body, params, scope) else {
            return;
        };
        let Some(before) = statements.get(statements.len().saturating_sub(2)) else {
            return;
        };
        let Some(return_statement) = statements.last() else {
            return;
        };

        if let Some((target, rhs)) = assignment(before) {
            if binding(self.scoping, target) == Some(symbol) {
                if let Some(expr) = self.terminal_value(rhs) {
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
        if let Some(body) = &function.body {
            self.recover_body(body, &function.params, function.scope_id.get());
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        if let ArrowFunctionBody::FunctionBody(body) = &arrow.body {
            self.recover_body(body, &arrow.params, arrow.scope_id.get());
        }
        walk::walk_arrow_function_expression(self, arrow);
    }
}

/// Recover direct return values through a provably unobservable terminal
/// temporary. Independently reparse/re-resolve each edit to avoid overlaps.
///
/// Unsupported or invalid source is returned unchanged instead of raising an error.
#[must_use = "Use the returned source and recovery evidence; the input is unchanged"]
pub fn recover_terminal_returns(source: &str) -> RecoveredReturns {
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
    RecoveredReturns {
        source: output,
        adjacent_returns,
        labeled_joins,
        guarded_joins,
    }
}

#[cfg(test)]
mod tests {
    use super::recover_terminal_returns;

    #[test]
    fn rewrites_adjacent_assignment_when_unused_elsewhere() {
        let src = "const f = function(q, x){sideEffect();q = x+3;return q;};";
        let out = recover_terminal_returns(src);
        assert_eq!(out.adjacent_returns, 1);
        assert_eq!(out.labeled_joins, 0);
        assert!(
            out.source.contains("sideEffect();return (x+3);"),
            "{}",
            out.source
        );
    }

    #[test]
    fn rewrites_labeled_join_with_independent_side_effects() {
        let src = "const V=function(J,Y,H){a:{if(J.Y){H=w8(J,J.D);break a;}if((Y=$X(8,J,true),Y)&128){Y^=128;}H=Y;}return H;};";
        let out = recover_terminal_returns(src);
        assert_eq!(out.labeled_joins, 1);
        assert!(out.source.contains("return (w8(J,J.D));"), "{}", out.source);
        assert!(out.source.contains("return (Y);"), "{}", out.source);
        assert!(!out.source.contains("break a"), "{}", out.source);
        assert!(!out.source.contains("return H"), "{}", out.source);
    }

    #[test]
    fn never_remove_writes_observed_through_aliases_or_dynamic_scope() {
        let unsafe_cases = [
            "function f(q){const g=()=>q;q=2;return q;}",
            "function f(q){q=2;console.log(q);return q;}",
            "function f(q){const a=arguments;q=2;return q;}",
            "function f(q){eval('q=9');q=2;return q;}",
            "function f(q){with({}){}q=2;return q;}",
            "function f(q){q=2;return arguments[0];}",
        ];
        for src in unsafe_cases {
            let out = recover_terminal_returns(src);
            assert_eq!(out.source, src, "{src} -> {}", out.source);
            assert_eq!(out.adjacent_returns, 0);
        }
    }

    #[test]
    fn terminal_store_is_dead_after_earlier_reads_and_writes() {
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
            let out = recover_terminal_returns(source);
            let count = match expected_kind {
                "adjacent" => out.adjacent_returns,
                "guarded" => out.guarded_joins,
                "labeled" => out.labeled_joins,
                _ => unreachable!(),
            };
            assert_eq!(count, 1, "{source}: {}", out.source);
        }
    }

    #[test]
    fn closure_capture_keeps_terminal_assignments_observable() {
        for source in [
            "function f(q){const g=function(){return q;};q=3;return q;}",
            "function f(q){const g=()=>()=>q;q=3;return q;}",
            "function f(q){const obj={get x(){return q;}};q=3;return q;}",
            "function f(q,x){const obj={m(){return q;}};if(x){q=left();}return q;}",
            "function f(q,x){const g=(x=q)=>x;if(x){q=left();}return q;}",
        ] {
            let out = recover_terminal_returns(source);
            assert_eq!(out.source, source, "{source}: {}", out.source);
        }
    }

    #[test]
    fn respect_reference_identity_and_preserve_early_exit_behavior() {
        let cases = [
            "function f(q,x){let q=2;q=x;return q;}",
            "const f=function(H){a:{if(x){H=first();break a;}H=second();}other();return H;};",
            "function f(H){a:{if(x){H=first();break a;}H=second();}return arguments[0];}",
        ];
        for src in cases {
            let out = recover_terminal_returns(src);
            assert_eq!(out.source, src, "{src} -> {}", out.source);
        }
    }

    #[test]
    fn guarded_assignment_preserves_initial_return_value_on_false_path() {
        let src = "function f(q, x){if(x){q=touch(x);}return q;}";
        let out = recover_terminal_returns(src);
        assert_eq!(out.guarded_joins, 1);
        assert!(out.source.contains("return (touch(x));"), "{}", out.source);
        assert!(out.source.ends_with("return q;}"), "{}", out.source);
    }

    #[test]
    fn complete_if_else_join_returns_each_branch_directly() {
        let src = "function f(q, x){if(x)q=left();else{q=right();}return q;}";
        let out = recover_terminal_returns(src);
        assert_eq!(out.guarded_joins, 1);
        assert!(out.source.contains("return (left());"), "{}", out.source);
        assert!(out.source.contains("return (right());"), "{}", out.source);
        assert!(!out.source.contains("return q;"), "{}", out.source);
    }

    #[test]
    fn guarded_labeled_join_recovers_original_multimode_helper() {
        let src = "const V=function(J,Q,Y,L,H){if((Q>>2&5)==1){a:{if(J.Y){H=w8(J,J.D);break a;}if((Y=$X(8,J,true),Y)&128){Y^=128;L=$X(2,J,true);Y=(Y<<2)+(L|0);}H=Y;}}return H;};";
        let out = recover_terminal_returns(src);
        assert_eq!(out.guarded_joins, 1, "{}", out.source);
        assert_eq!(out.labeled_joins, 0);
        assert!(out.source.contains("return (w8(J,J.D));"), "{}", out.source);
        assert!(out.source.contains("return (Y);"), "{}", out.source);
        assert!(out.source.contains("return H;"), "{}", out.source);
        assert!(!out.source.contains("break a;"), "{}", out.source);
    }

    #[test]
    fn guarded_joins_reject_intermediate_effects_or_observable_bindings() {
        for src in [
            "function f(x,q){if(x){q=left();after();}return q;}",
            "function f(x,q){if(x){q=left();}else{right();}return q;}",
            "function f(x,q){if(x){q=left();}else{q=right();observe(q);}return q;}",
            "function f(x,q){if(x){q=left();}console.log(q);return q;}",
            "function f(x,q){if(x){try{q=left();}finally{other();}}return q;}",
            "function f(x,q){if(x){a:{if(x){q=left();break a;}q=right();}other();}return q;}",
            "function f(x,q){if(x){q=left();}return arguments[0];}",
        ] {
            let out = recover_terminal_returns(src);
            assert_eq!(out.source, src, "{src} -> {}", out.source);
            assert_eq!(out.guarded_joins, 0);
        }
    }

    #[test]
    fn enclosing_lexical_assignments_are_observable_and_must_remain() {
        for src in [
            "let shared;function f(){shared=touch();return shared;}",
            "let shared;const f=()=>{shared=touch();return shared;};",
            "function outer(){let q;function inner(){q=touch();return q;}return inner;}",
            "function outer(){let q;const inner=()=>{if(flag){q=touch();}return q;};return inner;}",
            "let state;function f(flag){if(flag){state=one();}else{state=two();}return state;}",
        ] {
            let out = recover_terminal_returns(src);
            assert_eq!(out.source, src, "{src} -> {}", out.source);
            assert_eq!(
                out.adjacent_returns + out.labeled_joins + out.guarded_joins,
                0
            );
        }
    }

    #[test]
    fn function_owned_bindings_work_in_arrows_methods_and_nested_functions() {
        for src in [
            "const f=(q,x)=>{if(x){q=touch(x);}return q;};",
            "class C{method(q,x){if(x){q=touch(x);}return q;}}",
            "function outer(){const f=function(q,x){if(x){q=touch(x);}return q;};return f;}",
        ] {
            let out = recover_terminal_returns(src);
            assert_eq!(out.guarded_joins, 1, "{src}: {}", out.source);
        }
    }

    #[test]
    fn guarded_return_keeps_effectful_prefix_and_local_block_scope() {
        let src = "function f(q,x){if(x){log('prefix');let local=touch();if(local<0)return -1;q=combine(local,q);}return q;}";
        let out = recover_terminal_returns(src);
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
    }

    #[test]
    fn complete_if_else_joins_keep_both_effectful_prefixes() {
        let src = "function f(q,x){if(x){log(1);const v=a();q=left(v,q);}else{log(2);const v=b();q=right(v,q);}return q;}";
        let out = recover_terminal_returns(src);
        assert_eq!(out.guarded_joins, 1, "{}", out.source);
        assert!(out
            .source
            .contains("log(1);const v=a();return (left(v,q));"));
        assert!(out
            .source
            .contains("log(2);const v=b();return (right(v,q));"));
        assert!(!out.source.contains("return q;"), "{}", out.source);
    }

    #[test]
    fn knitsail_hv_callback_prefix_is_preserved() {
        let src = "const hV=function(J,Q,Y,u){if(!(J-5&14)){Q(function(n){n(Y);});u=[function(){return Y;},function(){}];}return u;};";
        let out = recover_terminal_returns(src);
        assert_eq!(out.guarded_joins, 1, "{}", out.source);
        assert!(
            out.source
                .contains("Q(function(n){n(Y);});return ([function(){return Y;},function(){}]);"),
            "{}",
            out.source
        );
        assert!(out.source.contains("return u;"), "{}", out.source);
        assert!(!out.source.contains("u=[function()"), "{}", out.source);
    }

    #[test]
    fn prefix_early_exits_or_loop_controls_keep_their_original_order() {
        for src in [
            "function f(q,x){if(x){if(q)return 7;trace();q=one();}return q;}",
            "function f(q,x){if(x){label:{if(q)break label;trace();}q=one();}return q;}",
            "function f(q,x){if(x){for(let n=0;n<3;n++){trace(n);if(n===1)break;}q=one();}return q;}",
        ] {
            let out = recover_terminal_returns(src);
            assert_eq!(out.guarded_joins, 1, "{src}: {}", out.source);
            assert!(out.source.contains("return (one());"), "{}", out.source);
            assert!(!out.source.contains("q=one();"), "{}", out.source);
        }
    }

    #[test]
    fn nonterminal_assignment_still_must_remain() {
        for src in [
            "function f(q,x){if(x){q=one();trace();}return q;}",
            "function f(q,x){if(x){trace();q=one();trace();}return q;}",
            "function f(q,x){if(x){q=one();trace();}else{q=two();}return q;}",
            "function f(q,x){if(x){q=one();}else{q=two();trace();}return q;}",
            "function f(q,x){const saved=()=>q;if(x){trace();q=one();}return q;}",
        ] {
            let out = recover_terminal_returns(src);
            assert_eq!(out.source, src, "{src}: {}", out.source);
            assert_eq!(out.guarded_joins, 0);
        }
    }

    #[test]
    fn immutable_terminal_targets_keep_abrupt_or_ignored_writes() {
        for source in [
            "function f(){const q=0;q=effect();return q;}",
            "function f(x){const q=0;if(x)q=effect();return q;}",
            "const f=function q(){q=effect();return q;};",
            "const f=function q(){'use strict';q=effect();return q;};",
        ] {
            let out = recover_terminal_returns(source);
            assert_eq!(out.source, source);
        }
    }

    #[test]
    fn terminal_assignment_preserves_named_evaluation() {
        for (source, expected) in [
            (
                "function f(q){q=function(){};return q;}",
                "return (q=function(){});",
            ),
            (
                "function f(q){q=(async()=>0);return q;}",
                "return (q=(async()=>0));",
            ),
            (
                "function f(q,x){if(x)q=class{static seen=this.name};return q;}",
                "return (q=class{static seen=this.name});",
            ),
            (
                "function f(q,x){a:{if(x){q=()=>1;break a;}q=function(){};}return q;}",
                "return (q=()=>1);",
            ),
            (
                "function f(q){q=function named(){};return q;}",
                "return (function named(){});",
            ),
            (
                "function f(q){q=(0,function(){});return q;}",
                "return ((0,function(){}));",
            ),
        ] {
            let out = recover_terminal_returns(source);
            assert!(out.source.contains(expected), "{source}: {}", out.source);
            assert_eq!(
                out.adjacent_returns + out.labeled_joins + out.guarded_joins,
                1
            );
        }
    }

    #[test]
    fn parenthesized_terminal_assignment_and_return_preserve_named_evaluation() {
        let source = "function f(q){(q = function(){});return (q);}";
        let out = recover_terminal_returns(source);
        assert_eq!(out.adjacent_returns, 1, "{}", out.source);
        assert!(
            out.source.contains("return (q = function(){});"),
            "{}",
            out.source
        );
    }

    #[test]
    fn deferred_initializers_keep_terminal_binding_observable() {
        for source in [
            "function f(q,read=()=>q){saved=read;q=9;return q;}",
            "const f=(q,read=()=>q)=>{saved=read;q=9;return q;};",
            "function f(q,read=eval('()=>q')){saved=read;q=9;return q;}",
            "function f(q){saved=class {field=q};q=9;return q;}",
            "function f(q){saved=class {#field=q;read(){return this.#field}};q=9;return q;}",
            "function f(q){saved=class {static nested=class{field=q}};q=9;return q;}",
        ] {
            let out = recover_terminal_returns(source);
            assert_eq!(out.source, source, "{source}: {}", out.source);
        }
    }

    #[test]
    fn eager_class_keys_and_static_initializers_do_not_capture_local() {
        for source in [
            "function f(q){saved=class {[q]=1};q=9;return q;}",
            "function f(q){saved=class {static field=q};q=9;return q;}",
            "function f(q=1){q=9;return q;}",
            "function f(){let q=1;q=9;return q;}",
            "function f(){var q=1;q=9;return q;}",
        ] {
            let out = recover_terminal_returns(source);
            assert_eq!(out.adjacent_returns, 1, "{source}: {}", out.source);
            assert!(out.source.contains("return (9);"), "{}", out.source);
        }
    }

    #[test]
    #[ignore = "requires installed Node; terminal return semantics oracle"]
    fn node_confirms_terminal_return_observability() -> anyhow::Result<()> {
        use std::process::Command;
        let cases = [
            (
                "function f(){const q=0;q=(events.push('rhs'),7);return q;}",
                "try{f()}catch(e){events.push(e.name)}",
            ),
            (
                "const f=function q(){q=(events.push('rhs'),7);return q;};",
                "events.push(f()===f, f().name)",
            ),
            (
                "const f=function q(){'use strict';q=(events.push('rhs'),7);return q;};",
                "try{f()}catch(e){events.push(e.name)}",
            ),
            (
                "function f(q,read=()=>q){saved=read;q=9;return q;}",
                "events.push(f(2),saved())",
            ),
            (
                "function f(q){saved=class{field=q};q=9;return q;}",
                "events.push(f(2),new saved().field)",
            ),
            (
                "function f(q){saved=class{static field=q;[q]=3};q=9;return q;}",
                "events.push(f(2),saved.field,new saved()[2])",
            ),
            (
                "function f(q){q=class{static seen=this.name};return q;}",
                "const c=f();events.push(c.name,c.seen)",
            ),
            (
                "function f(q){(q=async()=>0);return(q);}",
                "events.push(f().name)",
            ),
            (
                "function f(q,x){if(x)q=()=>1;else q=function(){};return q;}",
                "events.push(f(0,true).name,f(0,false).name)",
            ),
            (
                "function f(q){q=class{static seen=q};return q;}",
                "events.push(f(7).seen,f(7).name)",
            ),
        ];
        for (definition, observation) in cases {
            let source = format!("const events=[];let saved;{definition}{observation};console.log(JSON.stringify(events));");
            let recovered = recover_terminal_returns(&source);
            let original = Command::new("node").arg("-e").arg(&source).output()?;
            let derived = Command::new("node")
                .arg("-e")
                .arg(&recovered.source)
                .output()?;
            assert!(original.status.success(), "{source}: {original:?}");
            assert!(
                derived.status.success(),
                "{}: {derived:?}",
                recovered.source
            );
            assert_eq!(
                original.stdout, derived.stdout,
                "{source} -> {}",
                recovered.source
            );
        }
        Ok(())
    }

    #[test]
    fn detached_invalid_source_is_unchanged() {
        let src = "function f ( { not valid";
        let out = recover_terminal_returns(src);
        assert_eq!(out.source, src);
    }
}
