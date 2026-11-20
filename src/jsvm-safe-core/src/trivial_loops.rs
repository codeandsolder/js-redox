//! Simplify syntactically inert loops left by constant specialization.
//! This is not an arbitrary bounded-loop evaluator: it recognizes loops
//! whose precise number of iterations is established by their own AST.

use crate::{
    completion, fragment,
    statement_hazards::DeclarationHazard,
    value_eval::{inert_literal_value, known_bool},
};
use oxc_ast::ast::{
    BlockStatement, DoWhileStatement, Expression, ForStatement, ForStatementInit, IfStatement,
    SequenceExpression, Statement, VariableDeclarationKind, WhileStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::{GetSpan, Span};

/// Only transfers targeting the loop being removed matter. Nested switches
/// consume unlabeled breaks but not continues; nested iteration statements
/// consume both. Named continues are resolved by their attached iteration
/// statement's exact source span, including chains of labels on one loop.
struct LoopBodyControl<'s> {
    labels: &'s [(Span, String)],
    target: Span,
    breakable_depth: usize,
    iteration_depth: usize,
    exits_loop: bool,
    continues_loop: bool,
}

impl<'a> Visit<'a> for LoopBodyControl<'_> {
    fn visit_statement(&mut self, statement: &Statement<'a>) {
        let iteration = matches!(
            statement,
            Statement::ForStatement(_)
                | Statement::ForInStatement(_)
                | Statement::ForOfStatement(_)
                | Statement::WhileStatement(_)
                | Statement::DoWhileStatement(_)
        );
        let breakable = iteration || matches!(statement, Statement::SwitchStatement(_));
        self.iteration_depth += usize::from(iteration);
        self.breakable_depth += usize::from(breakable);
        walk::walk_statement(self, statement);
        self.iteration_depth -= usize::from(iteration);
        self.breakable_depth -= usize::from(breakable);
    }

    fn visit_break_statement(&mut self, statement: &oxc_ast::ast::BreakStatement<'a>) {
        self.exits_loop |= statement.label.is_none() && self.breakable_depth == 0;
    }

    fn visit_continue_statement(&mut self, statement: &oxc_ast::ast::ContinueStatement<'a>) {
        if let Some(label) = &statement.label {
            self.continues_loop |= self
                .labels
                .iter()
                .any(|(target, name)| *target == self.target && name == label.name.as_str());
        } else {
            self.continues_loop |= self.iteration_depth == 0;
        }
    }

    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: oxc_syntax::scope::ScopeFlags) {
    }
    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}
    fn visit_class(&mut self, _: &oxc_ast::ast::Class<'a>) {}
}

/// Discard a primitive literal statement only if it cannot be a directive.
pub fn inert_literal_statement(expr: &Expression<'_>) -> bool {
    match expr {
        Expression::BooleanLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::BigIntLiteral(_) => true,
        Expression::ParenthesizedExpression(paren) => inert_literal_statement(&paren.expression),
        // String literals can be directive prologues; never remove them.
        _ => false,
    }
}

/// A comma expression discards its operands' values but preserves their
/// effects, and `GetValue` on the final operand. Dropping the final comma
/// entirely can change direct eval and member-method receiver identity.
/// Only collapse to the final expression if its AST produces a value, not a
/// Reference. Otherwise keep an effectful prefix to retain comma semantics.
fn inherently_value(expr: &Expression<'_>) -> bool {
    match expr {
        Expression::ParenthesizedExpression(paren) => inherently_value(&paren.expression),
        Expression::BooleanLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::BigIntLiteral(_)
        | Expression::RegExpLiteral(_)
        | Expression::StringLiteral(_)
        | Expression::TemplateLiteral(_)
        | Expression::ArrayExpression(_)
        | Expression::ArrowFunctionExpression(_)
        | Expression::AssignmentExpression(_)
        | Expression::AwaitExpression(_)
        | Expression::BinaryExpression(_)
        | Expression::CallExpression(_)
        | Expression::ClassExpression(_)
        | Expression::ConditionalExpression(_)
        | Expression::FunctionExpression(_)
        | Expression::ImportExpression(_)
        | Expression::LogicalExpression(_)
        | Expression::NewExpression(_)
        | Expression::ObjectExpression(_)
        | Expression::SequenceExpression(_)
        | Expression::TaggedTemplateExpression(_)
        | Expression::ThisExpression(_)
        | Expression::UnaryExpression(_)
        | Expression::UpdateExpression(_)
        | Expression::YieldExpression(_)
        | Expression::PrivateInExpression(_)
        | Expression::ImportMeta(_)
        | Expression::NewTarget(_) => true,
        // Identifier, member, super, optional chain and unmodelled syntax
        // may produce a Reference. Do not turn an indirect eval into direct
        // eval or change the this-binding of an extracted method.
        _ => false,
    }
}

pub fn prune_inert_sequence_values(expr: &SequenceExpression<'_>, source: &str) -> Option<String> {
    let (last, preceding) = expr.expressions.split_last()?;
    let mut retained = Vec::new();
    let mut removed = 0usize;
    for candidate in preceding {
        if inert_literal_statement(candidate) || matches!(candidate, Expression::StringLiteral(_)) {
            removed += 1;
        } else {
            retained.push(fragment(source, candidate.span()));
        }
    }
    // Removing the final comma would expose a NamedEvaluation context if
    // a const or assignment receives an anonymous function/class/arrow.
    // Retain the comma when it is the only thing suppressing name inference.
    if removed == 0
        || (retained.is_empty()
            && (!inherently_value(last)
                || crate::effect_statements::conditional_has_name_hazard(last, 0)))
    {
        return None;
    }
    retained.push(fragment(source, last.span()));
    Some(format!("({})", retained.join(", ")))
}

fn empty_statement(stmt: &Statement<'_>) -> bool {
    match stmt {
        Statement::EmptyStatement(_) => true,
        Statement::BlockStatement(block) => block.body.is_empty(),
        _ => false,
    }
}

/// Lift a standalone, nonempty lexical block into its parent statement list
/// only when its own scope has no block-local declarations. Var belongs to the
/// containing function and does not create a block-local lexical binding.
///
/// Preserve nested control-flow syntax (if/loop/switch/label/try) unchanged:
/// the caller invokes this only on direct children of a function body or
/// another `BlockStatement`, never on a branch or labeled statement body.
/// String expression statements are retained inside braces because lifting
/// them to the beginning of a function can create a new strict directive.
/// Comments and formatting inside the braces are preserved byte-for-byte.
pub fn flatten_standalone_block(
    block: &BlockStatement<'_>,
    source: &str,
    scoping: &Scoping,
) -> Option<String> {
    // The actual semantic scope must not introduce any binding. This catches
    // contextual Annex-B/function bindings and declarations beyond direct
    // statement forms before removing the scope, not just syntactic let/const.
    if !scoping.get_bindings(block.scope_id.get()?).is_empty() {
        return None;
    }
    if block.body.is_empty()
        || block.body.iter().any(|statement| match statement {
            Statement::VariableDeclaration(declaration) => {
                declaration.kind != VariableDeclarationKind::Var
            }
            Statement::FunctionDeclaration(_) | Statement::ClassDeclaration(_) => true,
            _ => false,
        })
    {
        return None;
    }
    // A string-literal statement can become a directive at a new position
    // in its parent statement list. Preserve that scope boundary instead.
    if block.body.iter().any(|statement| match statement {
        Statement::ExpressionStatement(expression) => {
            matches!(&expression.expression, Expression::StringLiteral(_))
        }
        _ => false,
    }) {
        return None;
    }
    let inner = source.get(block.span.start as usize + 1..block.span.end as usize - 1)?;
    // Both original braces separated statements even where no semicolon
    // was present. Preserve that boundary when an adjacent `(`, `[`,
    // template or other continuation token would otherwise change the parse.
    Some(format!("\n;{inner}\n;\n"))
}

/// Turn empty `if` branches into ordinary, readable control flow while still
/// evaluating the test exactly once. The surrounding block is essential when
/// this statement is the consequent of another `if`: otherwise removing an
/// `else` creates a different dangling-else parse. A retained branch keeps its
/// original braces, lexical bindings, and control transfers.
pub fn normalize_empty_if(
    stmt: &IfStatement<'_>,
    source: &str,
    completion_live: bool,
) -> Option<String> {
    let then_empty = empty_statement(&stmt.consequent);
    let else_empty = stmt
        .alternate
        .as_ref()
        .is_some_and(|alt| empty_statement(alt));
    if !then_empty && !else_empty {
        return None;
    }
    let test = fragment(source, stmt.test.span());
    if then_empty && (stmt.alternate.is_none() || else_empty) {
        return Some(if completion_live {
            format!("({test}, void 0);")
        } else {
            format!("({test});")
        });
    }
    if then_empty {
        let alternative = stmt.alternate.as_ref()?;
        return Some(format!(
            "{{ if (!({test})) {} }}",
            fragment(source, alternative.span())
        ));
    }
    // Only the alternate is empty. A block around the revised `if` retains
    // which `else` binds to its enclosing conditional.
    Some(format!(
        "{{ if ({test}) {} }}",
        fragment(source, stmt.consequent.span())
    ))
}

/// A pure false test never enters the body. Preserve hoisted declarations
/// rather than discarding binding effects along with unreachable statements.
pub fn never_entered_while(it: &WhileStatement<'_>) -> Option<String> {
    if known_bool(&it.test) != Some(false) {
        return None;
    }
    (!DeclarationHazard::Discard.present(&[&it.body])).then_some("{}".to_owned())
}

struct SingleIterationBody {
    text: String,
    needs_loop: bool,
}

impl SingleIterationBody {
    /// Prove that the body either reaches a terminal local break or the
    /// loop's test is pure false after the first iteration. Preserve every
    /// earlier abrupt transfer and every original lexical block.
    fn analyze(
        body: &Statement<'_>,
        source: &str,
        false_after_body: bool,
        target: Span,
        labels: &[(Span, String)],
    ) -> Option<Self> {
        let statements = match body {
            Statement::BlockStatement(block) => block.body.as_slice(),
            _ => std::slice::from_ref(body),
        };
        let tail = statements
            .last()
            .filter(|stmt| matches!(stmt, Statement::BreakStatement(brk) if brk.label.is_none()));
        if tail.is_none() && !false_after_body {
            return None;
        }
        let retained = &statements[..statements.len() - usize::from(tail.is_some())];
        let mut control = LoopBodyControl {
            labels,
            target,
            breakable_depth: 0,
            iteration_depth: 0,
            exits_loop: false,
            continues_loop: false,
        };
        for statement in retained {
            control.visit_statement(statement);
        }
        if control.continues_loop && !false_after_body {
            return None;
        }
        let needs_loop = control.exits_loop || control.continues_loop;
        // An already single-iteration do-while with a necessary break/continue
        // region has no control-flow simplification beyond its terminal break.
        if false_after_body && tail.is_none() && needs_loop {
            return None;
        }
        let text = match (body, tail) {
            (Statement::BlockStatement(block), Some(last)) => {
                let head = source.get(block.span.start as usize..last.span().start as usize)?;
                let end = source.get(last.span().end as usize..block.span.end as usize)?;
                format!("{head}{end}")
            }
            (Statement::BlockStatement(block), None) => fragment(source, block.span).to_owned(),
            (_, Some(_)) => "{}".to_owned(),
            // A direct Annex B declaration requires its original statement
            // context. A block around ordinary statements is transparent.
            (Statement::FunctionDeclaration(_), None) => return None,
            (_, None) => format!("{{\n{}\n}}", fragment(source, body.span())),
        };
        Some(Self { text, needs_loop })
    }

    fn render(self, completion_live: bool) -> String {
        if self.needs_loop {
            // Retain the original local break/continue targets without
            // inventing new labels or bindings. The omitted backedge is
            // proven unreachable, and a pure false test adds no effects.
            format!("do {} while (false);", self.text)
        } else if completion_live {
            completion::seed_undefined(&self.text)
        } else {
            self.text
        }
    }
}

pub fn single_iteration_for(
    it: &ForStatement<'_>,
    source: &str,
    completion_live: bool,
    labels: &[(Span, String)],
) -> Option<String> {
    if it
        .test
        .as_ref()
        .is_some_and(|test| known_bool(test) != Some(true))
    {
        return None;
    }
    let body = SingleIterationBody::analyze(&it.body, source, false, it.span, labels)?;
    let init = match &it.init {
        None => String::new(),
        Some(ForStatementInit::VariableDeclaration(decl))
            if decl.kind == VariableDeclarationKind::Var =>
        {
            format!("{};", fragment(source, decl.span))
        }
        Some(ForStatementInit::VariableDeclaration(decl)) => {
            // `let` loop variables have a distinct first-iteration environment.
            // In particular a closure created in the initializer observes the
            // original binding, not its per-iteration clone. Keep this lexical
            // loop, but remove the pure test and unreachable update.
            if it.test.is_none() && it.update.is_none() {
                return None;
            }
            return Some(format!(
                "for ({};;) {}",
                fragment(source, decl.span),
                fragment(source, it.body.span())
            ));
        }
        Some(init) => {
            let expr = init.as_expression()?;
            if inert_literal_value(expr) {
                String::new()
            } else {
                format!("void ({});", fragment(source, expr.span()))
            }
        }
    };
    let body = body.render(completion_live);
    if init.is_empty() {
        Some(body)
    } else {
        Some(format!("{{\n{init}\n{body}\n}}"))
    }
}

pub fn single_iteration_while(
    it: &WhileStatement<'_>,
    source: &str,
    completion_live: bool,
    labels: &[(Span, String)],
) -> Option<String> {
    if known_bool(&it.test) != Some(true) {
        return None;
    }
    Some(
        SingleIterationBody::analyze(&it.body, source, false, it.span, labels)?
            .render(completion_live),
    )
}

pub fn single_iteration_do_while(
    it: &DoWhileStatement<'_>,
    source: &str,
    completion_live: bool,
    labels: &[(Span, String)],
) -> Option<String> {
    Some(
        SingleIterationBody::analyze(
            &it.body,
            source,
            known_bool(&it.test) == Some(false),
            it.span,
            labels,
        )?
        .render(completion_live),
    )
}

#[cfg(test)]
mod tests {
    use crate::deobfuscate;
    use work_budget::{BudgetExceeded, WorkBudget};

    fn rewritten(input: &str) -> Result<String, BudgetExceeded> {
        Ok(
            deobfuscate(input, 12, &WorkBudget::unlimited("trivial-loops"))?
                .map_or_else(|| input.to_owned(), |result| result.source),
        )
    }

    #[test]
    fn strips_inert_sequence_prefix_without_dropping_effects() -> Result<(), BudgetExceeded> {
        let source = "function f(){let n=0;const x=(n++,false,7);return [x,n];}";
        let result = rewritten(source)?;
        assert!(!result.contains("false,7"), "{result}");
        assert!(result.contains("n++"), "{result}");
        let source = "function f(){const x=(false,68)==68;return x;}";
        let result = rewritten(source)?;
        assert!(!result.contains("false,68"), "{result}");
        // Removing the final comma would change method receiver identity and
        // convert an indirect eval into a direct eval.
        let source = "function f(obj){return (0,obj.method)();}";
        let result = rewritten(source)?;
        assert!(result.contains("(0,obj.method)"), "{result}");
        let source = "function f(){return (0,eval)('2+2');}";
        let result = rewritten(source)?;
        assert!(result.contains("(0,eval)"), "{result}");
        Ok(())
    }

    #[test]
    fn drops_inert_primitive_statements_but_preserves_directives() -> Result<(), BudgetExceeded> {
        let source = "function f(){'use strict';false;123;null;return this;}";
        let result = rewritten(source)?;
        assert!(result.contains("'use strict'"), "{result}");
        assert!(!result.contains("false;"), "{result}");
        assert!(!result.contains("123;"), "{result}");
        assert!(!result.contains("null;"), "{result}");
        Ok(())
    }

    #[test]
    fn removes_unreachable_body_without_hoisted_binding() -> Result<(), BudgetExceeded> {
        let result = rewritten("function f(){let x=2;while(false){x=9;}return x;}")?;
        assert!(!result.contains("while"), "{result}");
        assert!(result.contains("return x"), "{result}");

        let hoisted = rewritten("function f(){while(false){var x=9;}return typeof x;}")?;
        assert!(hoisted.contains("while(false)"), "{hoisted}");
        Ok(())
    }

    #[test]
    fn normalizes_empty_if_arms_without_changing_condition_effects() -> Result<(), BudgetExceeded> {
        let input = "function f(x){if (check(x)) {} else {return x;} }";
        let output = rewritten(input)?;
        assert!(output.contains("if (!(check(x)))"), "{output}");
        assert!(!output.contains("else"), "{output}");

        let input = "function f(x){if(x){call();}else{} return 0;}";
        let output = rewritten(input)?;
        assert!(!output.contains("else"), "{output}");
        assert!(output.contains("call()"), "{output}");

        let input = "function f(x){if(inc(x)){}else{}return x;}";
        let output = rewritten(input)?;
        assert!(!output.contains("if("), "{output}");
        assert!(output.contains("inc(x)"), "{output}");
        Ok(())
    }

    #[test]
    fn normalizes_nested_empty_if_without_stealing_outer_else() -> Result<(), BudgetExceeded> {
        let input = "function f(a,b){if(a)if(b){}else{run();}else{fallback();}}";
        let output = rewritten(input)?;
        assert!(output.contains("if (!(b))"), "{output}");
        assert!(output.contains("else{fallback();}"), "{output}");
        Ok(())
    }

    #[test]
    fn single_iteration_proof_tracks_the_actual_break_and_continue_targets(
    ) -> Result<(), BudgetExceeded> {
        for input in [
            "function f(x){while(1){switch(x){case 1:work();break;}break;}}",
            "function f(){for(;;){for(var i=0;i<2;i++){continue;}work();break;}}",
            "function f(){do {work();break;}while(effect());}",
            "function f(){do {work();}while(0);}",
            "function f(){while(true)break;}",
            "function f(){outer:for(var i=0;i<2;i++){while(true){work();continue outer;break;}}}",
            "function f(){again:do {if(check())continue again;break;}while(false);}",
        ] {
            let result = deobfuscate(input, 16, &WorkBudget::unlimited("single-iteration"))?
                .unwrap_or_else(|| unreachable!());
            assert!(
                result
                    .transforms
                    .keys()
                    .any(|kind| kind.starts_with("single_iteration_")),
                "{input} -> {}",
                result.source
            );
            assert!(result.analysis_complete, "{}", result.source);
        }
        for input in [
            "function f(x){while(true){switch(x){case 1:continue;}break;}}",
            "function f(x){again:for(;;){if(x)continue again;break;}}",
            "function f(x){first:second:while(true){while(x){continue first;}break;}}",
        ] {
            let result = deobfuscate(input, 16, &WorkBudget::unlimited("single-iteration"))?
                .unwrap_or_else(|| unreachable!());
            assert!(
                !result
                    .transforms
                    .keys()
                    .any(|kind| kind.starts_with("single_iteration_")),
                "{input} -> {}",
                result.source
            );
        }
        Ok(())
    }

    #[test]
    fn unwraps_exactly_one_iteration_but_not_a_possible_second_iteration(
    ) -> Result<(), BudgetExceeded> {
        let source = "function f(x){for(0;true;true){x++;break;}return x;}";
        let result = rewritten(source)?;
        assert!(!result.contains("for(0;"), "{result}");
        assert!(result.contains("x++"), "{result}");

        let labeled = rewritten(
            "function f(x){for(0;true;true){done:{if(x){break done;}x++;}break;}return x;}",
        )?;
        assert!(!labeled.contains("for("), "{labeled}");
        assert!(labeled.contains("break done"), "{labeled}");

        let repeated =
            rewritten("function f(x){for(0;true;true){if(x)continue;x++;break;}return x;}")?;
        assert!(repeated.contains("for("), "{repeated}");
        let early_exit =
            rewritten("function f(x){for(0;true;true){if(x)break;x++;break;}return x;}")?;
        assert!(!early_exit.contains("for("), "{early_exit}");
        assert!(early_exit.contains("while (false)"), "{early_exit}");
        let effectful_init = rewritten("function f(x){for(x=0;true;true){x++;break;}return x;}")?;
        assert!(!effectful_init.contains("for("), "{effectful_init}");
        assert!(effectful_init.contains("x=0"), "{effectful_init}");
        let lexical =
            rewritten("function f(){for(let x=0,g=()=>x;true;effect()){x++;return g();break;}}")?;
        assert!(lexical.contains("for (let x=0,g=()=>x;;)"), "{lexical}");
        assert!(!lexical.contains("effect()"), "{lexical}");
        Ok(())
    }
}
