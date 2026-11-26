//! Shared bounded loop execution and target-aware completion accumulation.
use super::{
    flow::{CompletionValue, Flow, Path, Transfer},
    Analyzer, Environment, FreshDataReads, Observation,
};
use oxc_ast::ast::{
    DoWhileStatement, Expression, ForStatement, ForStatementInit, Statement,
    VariableDeclarationKind, WhileStatement,
};
use oxc_span::GetSpan;
use oxc_syntax::scope::ScopeId;
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Clone, Copy)]
pub(super) enum Loop<'a, 'ast> {
    For(&'a ForStatement<'ast>),
    While(&'a WhileStatement<'ast>),
    DoWhile(&'a DoWhileStatement<'ast>),
}

impl<'a, 'ast> Loop<'a, 'ast> {
    pub(super) fn new(statement: &'a Statement<'ast>) -> Option<Self> {
        match statement {
            Statement::ForStatement(statement) => Some(Self::For(statement)),
            Statement::WhileStatement(statement) => Some(Self::While(statement)),
            Statement::DoWhileStatement(statement) => Some(Self::DoWhile(statement)),
            _ => None,
        }
    }

    const fn scope(self) -> Option<ScopeId> {
        match self {
            Self::For(statement) => statement.scope_id.get(),
            Self::While(_) | Self::DoWhile(_) => None,
        }
    }

    const fn body(self) -> &'a Statement<'ast> {
        match self {
            Self::For(statement) => &statement.body,
            Self::While(statement) => &statement.body,
            Self::DoWhile(statement) => &statement.body,
        }
    }

    const fn test(self) -> Option<&'a Expression<'ast>> {
        match self {
            Self::For(statement) => statement.test.as_ref(),
            Self::While(statement) => Some(&statement.test),
            Self::DoWhile(statement) => Some(&statement.test),
        }
    }
}

/// Brent-style exponentially spaced checkpoints bound retained heap
/// snapshots while detecting stalled or cyclic abstract continuations.
/// An identical abstract state may represent different concrete states,
/// so stop speculation and leave the source unchanged rather than infer
/// termination or divergence.
struct ProgressProbe {
    checkpoint: Environment,
    interval: usize,
    elapsed: usize,
}

impl ProgressProbe {
    fn new(environment: &Environment) -> Self {
        Self {
            checkpoint: environment.clone(),
            interval: 1,
            elapsed: 0,
        }
    }

    fn stalled(
        &mut self,
        environment: &Environment,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        if self.checkpoint.same_reaching_state(environment, budget)? {
            return Ok(true);
        }
        self.elapsed += 1;
        if self.elapsed == self.interval {
            self.checkpoint = environment.clone();
            self.interval = self.interval.saturating_mul(2);
            self.elapsed = 0;
        }
        Ok(false)
    }
}

struct LoopRun {
    flow: Flow,
    normal_exit: Option<Path>,
}

impl LoopRun {
    fn new() -> Self {
        Self {
            flow: Flow::normal(CompletionValue::undefined()),
            normal_exit: None,
        }
    }

    fn record_test_exit(
        &mut self,
        environment: &Environment,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if let Some(value) = self.flow.normal.take() {
            Path::accumulate(
                &mut self.normal_exit,
                Path {
                    value,
                    environment: environment.clone(),
                },
                budget,
            )?;
        }
        Ok(())
    }

    fn accept_body(
        &mut self,
        mut body: Flow,
        labels: &[Transfer],
        environment: &mut Environment,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if let Some(inherited) = self.flow.normal.take() {
            body.update_empty(&inherited, budget)?;
        }
        body.consume(&Transfer::Continue(None), environment, budget)?;
        for label in labels {
            budget.consume(1)?;
            body.consume(label, environment, budget)?;
        }
        if let Some(paths) = body.abrupt.remove(&Transfer::Break(None)) {
            for path in paths {
                Path::accumulate(&mut self.normal_exit, path, budget)?;
            }
        }
        self.flow.normal = body.normal.take();
        self.flow.merge_abrupt(body, budget)
    }

    fn finish(
        mut self,
        environment: &mut Environment,
        budget: &WorkBudget,
    ) -> Result<Flow, BudgetExceeded> {
        if let Some(exit) = self.normal_exit {
            self.flow.merge_normal(exit, environment, budget)?;
        }
        Ok(self.flow)
    }
}

impl Analyzer<'_, '_> {
    pub(super) fn refresh_iteration_scope(
        &mut self,
        statement: &ForStatement<'_>,
        environment: &mut Environment,
    ) -> Option<()> {
        if matches!(&statement.init,
            Some(ForStatementInit::VariableDeclaration(declaration))
                if declaration.kind == VariableDeclarationKind::Let)
        {
            let scope = statement.scope_id.get()?;
            let id = self.fresh_identity();
            let old = self.scope_instances.refresh(scope, id)?;
            self.heap_result(environment.copy_instance(old, id, self.budget))?;
        }
        Some(())
    }

    pub(super) fn for_initializer(
        &mut self,
        statement: &ForStatement<'_>,
        environment: &mut Environment,
    ) -> Option<()> {
        if let Some(initializer) = &statement.init {
            match initializer {
                ForStatementInit::VariableDeclaration(declaration) => {
                    self.declaration(declaration, environment);
                }
                expression => {
                    self.expression(expression.as_expression()?, environment);
                }
            }
        }
        Some(())
    }

    pub(super) fn consume_iteration(&mut self) -> Option<()> {
        let fuel = self.loop_fuel.as_mut()?;
        *fuel = fuel.checked_sub(1)?;
        self.heap_result(self.budget.consume(1))
    }

    fn loop_test(&mut self, node: Loop<'_, '_>, environment: &mut Environment) -> Option<bool> {
        node.test().map_or(Some(true), |test| {
            self.expression(test, environment)
                .fact
                .as_ref()
                .map(super::Fact::truthy)
        })
    }

    fn simulate_loop(
        &mut self,
        node: Loop<'_, '_>,
        labels: &[Transfer],
        environment: &mut Environment,
    ) -> Option<Flow> {
        if let Loop::For(statement) = node {
            self.for_initializer(statement, environment)?;
            self.refresh_iteration_scope(statement, environment)?;
        }
        // A constant truthy (or absent) test without a syntactic exit
        // cannot reach a normal continuation. Avoid spending the full
        // iteration budget on such a loop.
        if node
            .test()
            .is_none_or(|test| crate::value_eval::eval(test).is_some_and(|value| value.truthy()))
            && !super::statements::may_exit_loop(node.body())
        {
            return None;
        }
        let mut run = LoopRun::new();
        let mut progress = ProgressProbe::new(environment);
        while run.flow.normal.is_some() {
            self.consume_iteration()?;
            if !matches!(node, Loop::DoWhile(_)) && !self.loop_test(node, environment)? {
                self.heap_result(run.record_test_exit(environment, self.budget))?;
                break;
            }
            let body = self.statement(node.body(), environment)?;
            if body.unproved || self.loop_failed {
                return None;
            }
            self.heap_result(run.accept_body(body, labels, environment, self.budget))?;
            if run.flow.normal.is_none() {
                break;
            }
            if let Loop::For(statement) = node {
                self.refresh_iteration_scope(statement, environment)?;
                if let Some(update) = &statement.update {
                    self.expression(update, environment);
                }
            }
            if matches!(node, Loop::DoWhile(_)) && !self.loop_test(node, environment)? {
                self.heap_result(run.record_test_exit(environment, self.budget))?;
                break;
            }
            if !self.collect_heap(environment)
                || self.heap_result(progress.stalled(environment, self.budget))?
            {
                return None;
            }
        }
        self.heap_result(run.finish(environment, self.budget))
    }

    fn execute_loop_attempt(
        &mut self,
        node: Loop<'_, '_>,
        labels: &[Transfer],
        dispatch: bool,
        environment: &mut Environment,
    ) -> Option<Flow> {
        let scope = node.scope();
        let ticket = self.enter_instance(scope, environment);
        let disposes = scope.is_some_and(|scope| self.bindings.scope_may_dispose(scope));
        let flow = match node {
            Loop::For(statement) if dispatch => self.simulate_dispatch(statement, environment),
            _ => self.simulate_loop(node, labels, environment),
        }
        .filter(|flow| !flow.unproved && !self.loop_failed);
        let flow = flow.map(|mut flow| {
            self.dispose_paths(disposes, &mut flow, environment);
            flow
        });
        let scope_exit = self.leave_instance(ticket, environment);
        flow.filter(|_| scope_exit)
    }

    /// Speculation is shared by all loop forms, nested invocations, and
    /// exact dispatch traces. A failed transaction publishes neither partial
    /// source observations nor partial abrupt-path summaries.
    pub(super) fn bounded_loop(
        &mut self,
        statement: &Statement<'_>,
        labels: &[&str],
        environment: &mut Environment,
    ) -> Option<Flow> {
        let node = Loop::new(statement)?;
        let labels = labels
            .iter()
            .map(|label| Transfer::Continue(Some((*label).to_owned())))
            .collect::<Vec<_>>();
        let outermost = self.loop_fuel.is_none();
        if outermost {
            self.loop_fuel = Some(4096);
        }
        let mut candidate = environment.clone();
        let observations = self.begin_observations(true);
        let dispatch = matches!(node, Loop::For(statement) if labels.is_empty() && self.has_dispatch_shape(statement));
        let previous_failure = self.loop_failed;
        let mut flow = self.execute_loop_attempt(node, &labels, dispatch, &mut candidate);
        if flow.is_none() && dispatch && self.failure.is_none() && !previous_failure {
            // Trace emission is stricter than heap interpretation: a
            // switch with effectful case tests, for example, can still
            // establish reaching facts without removing any tests.
            self.reads = FreshDataReads::default();
            self.visited_lists.clear();
            self.loop_failed = false;
            candidate = environment.clone();
            flow = self.execute_loop_attempt(node, &labels, false, &mut candidate);
        }
        // Publish only a complete normal-path certificate. Failed loop
        // attempts contribute Unknown, including in a repeated outer scope.
        let value = flow.as_ref().and_then(Flow::exact_normal_primitive);
        let observation = if let Some(value) = value {
            if !self.charge_values([value]) {
                return None;
            }
            Observation::Exact(value.clone())
        } else {
            Observation::Unknown
        };
        self.finish_observations(observations, flow.is_some())?;
        let span = statement.span();
        self.reads.loop_completions.observe(
            (span.start, span.end),
            observation,
            crate::value_eval::identical_primitive_value,
        );
        if outermost {
            self.loop_fuel = None;
            self.loop_failed = false;
        } else if flow.is_none() {
            self.loop_failed = true;
        }
        if let Some(flow) = flow {
            *environment = candidate;
            Some(flow)
        } else {
            Some(self.opaque_statement(statement, environment))
        }
    }
}
