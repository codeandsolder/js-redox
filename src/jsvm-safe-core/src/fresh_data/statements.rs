//! Ordered statement evaluation with explicit normal and abrupt completions.
use super::{
    flow::{CompletionValue, Flow, Transfer},
    Analyzer, Environment, Fact, Value,
};
use oxc_ast::ast::{BlockStatement, Declaration, IfStatement, Statement, SwitchStatement};
use oxc_span::GetSpan;

/// Unsupported syntax may contain a transfer to an enclosing modeled
/// region. Do not reinterpret that path as a normal completion.
pub(super) fn unmodeled_transfer(statement: &Statement<'_>) -> bool {
    let summary = crate::control_flow::statement_transfers(statement);
    summary.returns || summary.jumps == crate::control_flow::JumpSummary::External
}

pub(super) fn may_exit_loop(body: &Statement<'_>) -> bool {
    let summary = crate::control_flow::statement_transfers(body);
    summary.returns || summary.throws || summary.jumps == crate::control_flow::JumpSummary::External
}

impl Analyzer<'_, '_> {
    pub(super) fn statements(
        &mut self,
        statements: &[Statement<'_>],
        environment: &mut Environment,
    ) -> Option<Flow> {
        let mut flow = Flow::empty();
        self.statement_list(statements, &mut flow, environment)?;
        Some(flow)
    }

    pub(super) fn statement_list(
        &mut self,
        statements: &[Statement<'_>],
        flow: &mut Flow,
        environment: &mut Environment,
    ) -> Option<()> {
        if let (Some(first), Some(last)) = (statements.first(), statements.last()) {
            self.visited_lists
                .insert((first.span().start, last.span().end));
        }
        for statement in statements {
            if flow.normal.is_none() {
                break;
            }
            let next = self.statement(statement, environment)?;
            self.sequence_flow(flow, next)?;
            if flow.normal.is_some() && !self.collect_heap(environment) {
                return None;
            }
        }
        Some(())
    }

    pub(super) fn sequence_flow(&mut self, flow: &mut Flow, mut next: Flow) -> Option<()> {
        let inherited = flow.normal.take()?;
        self.heap_result(next.update_empty(&inherited, self.budget))?;
        flow.normal = next.normal.take();
        self.heap_result(flow.merge_abrupt(next, self.budget))
    }

    /// Dispose on every path leaving the resource-owning scope, not only
    /// the ordinary continuation or a return from the current activation.
    pub(super) fn dispose_paths(
        &mut self,
        disposes: bool,
        flow: &mut Flow,
        environment: &mut Environment,
    ) {
        if disposes {
            if flow.normal.is_some() {
                self.invalidate(environment);
            }
            for path in flow.abrupt.values_mut().flatten() {
                self.invalidate(&mut path.environment);
            }
        }
    }

    fn block_statement(
        &mut self,
        block: &BlockStatement<'_>,
        environment: &mut Environment,
    ) -> Option<Flow> {
        let ticket = self.enter_instance(block.scope_id.get(), environment);
        let disposes = block
            .scope_id
            .get()
            .is_some_and(|scope| self.bindings.scope_may_dispose(scope));
        let flow = self.statements(&block.body, environment);
        let flow = flow.map(|mut flow| {
            self.dispose_paths(disposes, &mut flow, environment);
            flow
        });
        let exited = self.leave_instance(ticket, environment);
        flow.filter(|flow| exited && (flow.normal.is_none() || self.collect_heap(environment)))
    }

    fn if_statement(
        &mut self,
        branch: &IfStatement<'_>,
        environment: &mut Environment,
    ) -> Option<Flow> {
        let test = self.expression(&branch.test, environment);
        let mut flow = if let Some(value) = &test.fact {
            if value.truthy() {
                self.statement(&branch.consequent, environment)?
            } else {
                self.alternate(branch, environment)?
            }
        } else {
            let mut other = environment.clone();
            let first_new = self.next_identity;
            let previous_floor = environment.protect_before(first_new);
            other.protect_before(first_new);
            let left = self.statement(&branch.consequent, environment);
            let right = self.alternate(branch, &mut other);
            environment.protect_before(previous_floor);
            other.protect_before(previous_floor);
            let mut left = left?;
            let mut right = right?;
            left.restore_floor(previous_floor);
            right.restore_floor(previous_floor);
            left.normal = match (left.normal.take(), right.normal.take()) {
                (Some(left), Some(right)) => {
                    if !self.join_heap(environment, &other, first_new) {
                        return None;
                    }
                    Some(self.heap_result(left.join(&right, self.budget))?)
                }
                (Some(left), None) => Some(left),
                (None, Some(right)) => {
                    *environment = other;
                    Some(right)
                }
                (None, None) => None,
            };
            self.heap_result(left.merge_abrupt(right, self.budget))?;
            left
        };
        self.heap_result(flow.update_empty(&CompletionValue::undefined(), self.budget))?;
        Some(flow)
    }

    fn alternate(
        &mut self,
        branch: &IfStatement<'_>,
        environment: &mut Environment,
    ) -> Option<Flow> {
        branch.alternate.as_ref().map_or_else(
            || Some(Flow::empty()),
            |alternate| self.statement(alternate, environment),
        )
    }

    fn switch_statement(
        &mut self,
        switch: &SwitchStatement<'_>,
        environment: &mut Environment,
    ) -> Option<Flow> {
        // Discriminant evaluation precedes switch lexical instantiation.
        let discriminant = self.expression(&switch.discriminant, environment).fact;
        let ticket = self.enter_instance(switch.scope_id.get(), environment);
        let disposes = switch
            .scope_id
            .get()
            .is_some_and(|scope| self.bindings.scope_may_dispose(scope));
        let flow = discriminant.and_then(|discriminant| {
            let selection = self.select_cases(switch, &discriminant, false, environment)?;
            let mut flow = Flow::normal(CompletionValue::undefined());
            if let super::dispatch::Selection::Case(start) = selection {
                for case in switch.cases.iter().skip(start) {
                    self.statement_list(&case.consequent, &mut flow, environment)?;
                    if flow.normal.is_none() {
                        break;
                    }
                }
            }
            self.heap_result(flow.consume(&Transfer::Break(None), environment, self.budget))?;
            self.dispose_paths(disposes, &mut flow, environment);
            Some(flow)
        });
        let exited = self.leave_instance(ticket, environment);
        flow.filter(|_| exited)
    }

    fn labelled_statement(
        &mut self,
        statement: &Statement<'_>,
        environment: &mut Environment,
    ) -> Option<Flow> {
        let mut body = statement;
        let mut labels = Vec::new();
        while let Statement::LabeledStatement(labelled) = body {
            self.heap_result(self.budget.consume(1))?;
            labels.push(labelled.label.name.as_str());
            body = &labelled.body;
        }
        let mut flow = if super::loops::Loop::new(body).is_some() {
            self.bounded_loop(body, &labels, environment)?
        } else {
            self.statement(body, environment)?
        };
        for label in labels.into_iter().rev() {
            self.heap_result(flow.consume(
                &Transfer::Break(Some(label.to_owned())),
                environment,
                self.budget,
            ))?;
        }
        Some(flow)
    }

    pub(super) fn opaque_statement(
        &mut self,
        statement: &Statement<'_>,
        environment: &mut Environment,
    ) -> Flow {
        self.unobserved(statement.span());
        self.invalidate(environment);
        Flow::opaque(unmodeled_transfer(statement))
    }

    pub(super) fn statement(
        &mut self,
        statement: &Statement<'_>,
        environment: &mut Environment,
    ) -> Option<Flow> {
        if !self.checkpoint() {
            return None;
        }
        self.heap_result(self.budget.consume(1))?;
        match statement {
            Statement::VariableDeclaration(declaration) => {
                self.declaration(declaration, environment);
            }
            Statement::ExportDeclaration(export) => {
                if let Declaration::VariableDeclaration(declaration) = &export.declaration {
                    self.declaration(declaration, environment);
                } else {
                    return Some(self.opaque_statement(statement, environment));
                }
            }
            Statement::ExpressionStatement(statement) => {
                let value = self.expression(&statement.expression, environment).fact;
                return Some(Flow::normal(CompletionValue::value(value)));
            }
            Statement::BlockStatement(block) => return self.block_statement(block, environment),
            Statement::ForStatement(_)
            | Statement::WhileStatement(_)
            | Statement::DoWhileStatement(_) => {
                return self.bounded_loop(statement, &[], environment)
            }
            Statement::IfStatement(branch) => return self.if_statement(branch, environment),
            Statement::SwitchStatement(switch) => {
                return Some(
                    self.switch_statement(switch, environment)
                        .unwrap_or_else(|| self.opaque_statement(statement, environment)),
                );
            }
            Statement::LabeledStatement(_) => {
                return self.labelled_statement(statement, environment)
            }
            Statement::ReturnStatement(ret) => {
                let value = ret
                    .argument
                    .as_ref()
                    .map_or(Some(Fact::Primitive(Value::Undefined)), |argument| {
                        self.expression(argument, environment).fact
                    });
                return Some(Flow::abrupt(
                    Transfer::Return,
                    CompletionValue::value(value),
                    environment,
                ));
            }
            Statement::ThrowStatement(throw) => {
                let value = self.expression(&throw.argument, environment).fact;
                return Some(Flow::abrupt(
                    Transfer::Throw,
                    CompletionValue::value(value),
                    environment,
                ));
            }
            Statement::BreakStatement(jump) => {
                let label = jump.label.as_ref().map(|label| label.name.to_string());
                return Some(Flow::abrupt(
                    Transfer::Break(label),
                    CompletionValue::Empty,
                    environment,
                ));
            }
            Statement::ContinueStatement(jump) => {
                let label = jump.label.as_ref().map(|label| label.name.to_string());
                return Some(Flow::abrupt(
                    Transfer::Continue(label),
                    CompletionValue::Empty,
                    environment,
                ));
            }
            Statement::FunctionDeclaration(function)
                if self
                    .bindings
                    .inert_function_declaration(self.scoping, function) => {}
            Statement::EmptyStatement(_) => {}
            _ => return Some(self.opaque_statement(statement, environment)),
        }
        Some(Flow::empty())
    }
}
