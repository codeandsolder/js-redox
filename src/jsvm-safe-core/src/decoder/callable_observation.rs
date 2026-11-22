//! A self-installing callable has an observable write even when its returned
//! value is pure. Eliding the call is valid only when source-local references
//! cannot observe the identity of the installed function object.
use super::{assignment_identifier, unparenthesized, DecoderBindingContext};
use crate::completion::CompletionLiveness;
use oxc_ast::ast::{
    CallExpression, Expression, ExpressionStatement, ForStatement, VariableDeclaration,
    VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::ReferenceId;
use oxc_syntax::symbol::SymbolId;
use std::collections::{HashMap, HashSet, VecDeque};
use work_budget::BudgetExceeded;

pub(super) struct CallableUses<'c, 'p> {
    context: &'c DecoderBindingContext<'p>,
    completion: CompletionLiveness,
    calls: HashSet<ReferenceId>,
    copies: HashMap<ReferenceId, SymbolId>,
}

impl<'c, 'p> CallableUses<'c, 'p> {
    pub(super) fn collect(
        program: &oxc_ast::ast::Program<'_>,
        context: &'c DecoderBindingContext<'p>,
    ) -> Self {
        let mut uses = Self {
            context,
            completion: CompletionLiveness::analyze(program),
            calls: HashSet::new(),
            copies: HashMap::new(),
        };
        uses.visit_program(program);
        uses
    }

    fn copy(&mut self, destination: SymbolId, expression: &Expression<'_>) {
        if let Expression::Identifier(source) = unparenthesized(expression) {
            if let Some(reference) = source.reference_id.get() {
                self.copies.insert(reference, destination);
            }
        }
    }

    /// A discarded assignment result cannot expose the captured identity
    /// through an additional enclosing expression. Sequence arms before the
    /// last are discarded as well; this entry point only accepts expressions
    /// whose outer result is already discarded.
    fn discarded(&mut self, expression: &Expression<'_>) {
        if let Expression::SequenceExpression(sequence) = unparenthesized(expression) {
            for expression in &sequence.expressions {
                self.discarded(expression);
            }
        } else if let Some((target, source)) = assignment_identifier(expression) {
            if let Some(symbol) = target.reference_id.get().and_then(|reference| {
                self.context
                    .facts
                    .fixed_assignment_reference(self.context.scoping, reference)
            }) {
                self.copy(symbol, source);
            }
        }
    }

    pub(super) fn installation_unobservable(
        &self,
        callable: SymbolId,
        installation: ReferenceId,
    ) -> Result<bool, BudgetExceeded> {
        let DecoderBindingContext {
            scoping,
            facts,
            budget,
            ..
        } = *self.context;
        let mut pending = VecDeque::from([callable]);
        let mut seen = HashSet::new();
        while let Some(symbol) = pending.pop_front() {
            budget.checkpoint()?;
            if !seen.insert(symbol) {
                continue;
            }
            if facts.is_exported_binding(symbol)
                || facts.is_eval_exposed(scoping, symbol)
                || facts.is_mapped_arguments_exposed(scoping, symbol)
                || !scoping.symbol_redeclarations(symbol).is_empty()
            {
                return Ok(false);
            }
            let references = scoping.get_resolved_reference_ids(symbol);
            budget.consume(u64::try_from(references.len()).unwrap_or(u64::MAX))?;
            for &reference in references {
                let info = scoping.get_reference(reference);
                if facts.resolved_symbol(scoping, reference) != Some(symbol) {
                    return Ok(false);
                }
                if symbol == callable && reference == installation {
                    continue;
                }
                // Overwriting a local copy without reading its previous
                // value does not observe the prior function object.
                if symbol != callable
                    && info.is_write()
                    && !info.is_read()
                    && !info.flags().is_member_write_target()
                {
                    continue;
                }
                if !info.is_read() || info.is_write() || info.flags().is_member_write_target() {
                    return Ok(false);
                }
                if self.calls.contains(&reference) {
                    continue;
                }
                let Some(&destination) = self.copies.get(&reference) else {
                    return Ok(false);
                };
                pending.push_back(destination);
            }
        }
        Ok(true)
    }
}

impl<'a> Visit<'a> for CallableUses<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if let Expression::Identifier(identifier) = unparenthesized(&call.callee) {
            self.calls.extend(identifier.reference_id.get());
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        if matches!(
            declaration.kind,
            VariableDeclarationKind::Const
                | VariableDeclarationKind::Let
                | VariableDeclarationKind::Var
        ) {
            for declarator in &declaration.declarations {
                if let (Some(symbol), Some(initializer)) = (
                    declarator
                        .id
                        .get_binding_identifier()
                        .and_then(|identifier| identifier.symbol_id.get()),
                    declarator.init.as_ref(),
                ) {
                    self.copy(symbol, initializer);
                }
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_expression_statement(&mut self, statement: &ExpressionStatement<'a>) {
        if !self.completion.needs_value(statement.span) {
            self.discarded(&statement.expression);
        }
        walk::walk_expression_statement(self, statement);
    }

    fn visit_expression(&mut self, expression: &Expression<'a>) {
        // Nonfinal sequence operands and void operands have discarded
        // values even when their enclosing script completion is live.
        match expression {
            Expression::SequenceExpression(sequence) => {
                if let Some((_, prefix)) = sequence.expressions.split_last() {
                    for expression in prefix {
                        self.discarded(expression);
                    }
                }
            }
            Expression::UnaryExpression(unary) if unary.operator.as_str() == "void" => {
                self.discarded(&unary.argument);
            }
            _ => {}
        }
        walk::walk_expression(self, expression);
    }

    fn visit_for_statement(&mut self, statement: &ForStatement<'a>) {
        if let Some(expression) = statement
            .init
            .as_ref()
            .and_then(|initializer| initializer.as_expression())
        {
            self.discarded(expression);
        }
        if let Some(update) = &statement.update {
            self.discarded(update);
        }
        walk::walk_for_statement(self, statement);
    }
}
