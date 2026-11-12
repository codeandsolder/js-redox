//! Symbol-resolved terminal return dataflow in original lexical helper views.
//!
//! A return temporary whose only references are the assignments feeding its
//! terminal return can be eliminated, even across a simple labeled join.
//! This is an analyst-only source view, never a rewrite of captured executable
//! reconstruction. Never infer values from spelling alone.
use anyhow::Result;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    AssignmentTarget, Expression, FunctionBody, IdentifierReference, Statement, WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{operator::AssignmentOperator, symbol::SymbolId};
use rolldown_redox::ecmascript::parse_program;

#[derive(Debug)]
pub struct RecoveredReturns {
    pub source: String,
    pub adjacent_returns: usize,
    pub labeled_joins: usize,
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
    fn recover_body(&mut self, body: &FunctionBody<'_>) {
        let statements = &body.statements;
        let Some(returned) = statements.last().and_then(ident_return) else {
            return;
        };
        // Direct eval / with / arguments may observe or mutate formals without
        // explicit lexical references. Don't erase those assignments.
        let mut dynamic = DynamicScope::default();
        dynamic.visit_function_body(body);
        if dynamic.present {
            return;
        }
        let Some(symbol) = binding(self.scoping, returned) else {
            return;
        };
        let references = self.scoping.get_resolved_reference_ids(symbol);
        let Some(before) = statements.get(statements.len().saturating_sub(2)) else {
            return;
        };
        let Some(return_statement) = statements.last() else {
            return;
        };

        // The only references must be the assignment write + terminal read.
        if let Some((target, rhs)) = assignment(before) {
            if binding(self.scoping, target) == Some(symbol) && references.len() == 2 {
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

        // A last labeled block may use a branch exit followed by a terminal
        // assignment feeding the final return:
        //
        // label: { if (predicate) { tmp = first; break label; }
        //          <independent statements>; tmp = second; }
        // return tmp;
        //
        // Keep the block scope, run predicate and expressions in their
        // original order, replace the two join edges with direct returns.
        let Statement::LabeledStatement(label) = before else {
            return;
        };
        let Statement::BlockStatement(block) = &label.body else {
            return;
        };
        let Some(first) = block.body.first() else {
            return;
        };
        let Statement::IfStatement(branch) = first else {
            return;
        };
        if branch.alternate.is_some() {
            return;
        }
        let Statement::BlockStatement(consequent) = &branch.consequent else {
            return;
        };
        let [branch_assignment, Statement::BreakStatement(jump)] = consequent.body.as_slice()
        else {
            return;
        };
        if jump
            .label
            .as_ref()
            .is_none_or(|name| name.name != label.label.name)
        {
            return;
        }
        let Some((branch_target, branch_rhs)) = assignment(branch_assignment) else {
            return;
        };
        let Some(last_assignment) = block.body.last() else {
            return;
        };
        let Some((last_target, last_rhs)) = assignment(last_assignment) else {
            return;
        };
        if binding(self.scoping, branch_target) != Some(symbol)
            || binding(self.scoping, last_target) != Some(symbol)
            || references.len() != 3
        {
            return;
        }
        // Label must have at least the branch and fallthrough assignment.
        if block.body.len() < 2 {
            return;
        }
        let Some(condition) = snippet(self.source, branch.test.span()) else {
            return;
        };
        let Some(branch_value) = snippet(self.source, branch_rhs.span()) else {
            return;
        };
        let Some(last_value) = snippet(self.source, last_rhs.span()) else {
            return;
        };
        let middle = if block.body.len() > 2 {
            snippet(
                self.source,
                Span::new(
                    block.body[1].span().start,
                    block.body[block.body.len() - 2].span().end,
                ),
            )
        } else {
            Some("")
        };
        let Some(middle) = middle else {
            return;
        };
        // An extra break to the removed label would fail the semantic
        // verification below; nothing beyond the validated source is emitted.
        self.edits.push(Candidate {
            span: Span::new(before.span().start, return_statement.span().end),
            replacement: format!(
                "{{ if ({condition}) {{ return ({branch_value}); }} {middle} return ({last_value}); }}"
            ),
            kind: Kind::LabeledJoin,
        });
    }
}

impl<'a> Visit<'a> for ReturnFlow<'_> {
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
            "function f(q){q++;q=2;return q;}",
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
    fn detached_invalid_source_is_unchanged() -> Result<()> {
        let src = "function f ( { not valid";
        let out = recover_terminal_returns(src)?;
        assert_eq!(out.source, src);
        Ok(())
    }
}
