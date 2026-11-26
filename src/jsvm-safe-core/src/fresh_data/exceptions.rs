//! Exception handlers and cleanup consume the same completion paths as loops.
//! Unknown operations can throw at any evaluation prefix; retain an opaque
//! exceptional alternative rather than treating successful evaluation as a
//! guarantee that the handler or finalizer never runs.
use super::{
    flow::{CompletionValue, Flow, Path, Transfer},
    Analyzer, Environment,
};
use oxc_ast::ast::{BlockStatement, CatchClause, TryStatement};

impl Analyzer<'_, '_> {
    /// A statement or speculative attempt owns its expression exception
    /// edges until it has established a usable completion. Nested statement
    /// flows already own their edges. Abandoned speculation must not leak
    /// exceptional heaps into a different attempt.
    pub(super) fn capture_expression_exceptions(
        &mut self,
        environment: &mut Environment,
        evaluate: impl FnOnce(&mut Self, &mut Environment) -> Option<Flow>,
    ) -> Option<Flow> {
        let outer = std::mem::replace(&mut self.expression_exceptions, Flow::no_paths());
        let flow = evaluate(self, environment);
        let exceptions = std::mem::replace(&mut self.expression_exceptions, outer);
        let mut flow = flow?;
        if !environment.reachable() {
            flow.normal = None;
        }
        self.heap_result(flow.merge_abrupt(exceptions, self.budget))?;
        Some(flow)
    }

    pub(super) fn record_expression_throws(&mut self, paths: Vec<Path>) -> Option<()> {
        let result = self
            .expression_exceptions
            .extend_abrupt(Transfer::Throw, paths, self.budget);
        self.heap_result(result)
    }

    /// Intrinsic error allocation does not invoke user code. Preserve the
    /// exact reaching heap and leave the newly created error value opaque.
    pub(super) fn intrinsic_throw_path(&mut self, environment: &Environment) -> Option<()> {
        if environment.reachable() {
            self.record_expression_throws(vec![Path {
                value: CompletionValue::value(None),
                environment: environment.clone(),
            }])?;
        }
        Some(())
    }

    pub(super) fn intrinsic_throw(&mut self, environment: &mut Environment) -> Option<()> {
        self.intrinsic_throw_path(environment)?;
        environment.terminate();
        Some(())
    }

    pub(super) fn intrinsic_failure(&mut self, environment: &mut Environment) -> super::Evaluation {
        if self.intrinsic_throw(environment).is_none() {
            return self.barrier(environment);
        }
        super::Evaluation::default()
    }

    /// Resolve a descriptor operation's normal value while retaining
    /// every intrinsic exceptional alternative at the pre-effect heap.
    pub(super) fn access_normal<T>(
        &mut self,
        access: super::Access<T>,
        environment: &mut Environment,
    ) -> Option<T> {
        match access {
            super::Access::Normal(value) => Some(value),
            super::Access::NormalOrThrow(value) => {
                self.intrinsic_throw_path(environment)?;
                Some(value)
            }
            super::Access::Throw => {
                self.intrinsic_throw(environment)?;
                None
            }
            super::Access::Opaque => None,
        }
    }

    pub(super) fn protected_region(
        &mut self,
        environment: &mut Environment,
        evaluate: impl FnOnce(&mut Self, &mut Environment) -> Option<Flow>,
    ) -> Option<Flow> {
        let before = self.exception_generation;
        let flow = self.capture_expression_exceptions(environment, evaluate);
        let uncertain = self.exception_generation != before;
        // Explicit exceptional paths now represent this region's failures.
        self.exception_generation = before;
        let mut flow = flow.filter(|flow| !flow.unproved)?;
        if uncertain {
            let path = Path {
                value: CompletionValue::value(None),
                environment: environment.unknown_exception(self.next_identity),
            };
            self.heap_result(flow.extend_abrupt(Transfer::Throw, vec![path], self.budget))?;
        }
        Some(flow)
    }

    fn catch_path(
        &mut self,
        handler: &CatchClause<'_>,
        path: Path,
        environment: &mut Environment,
        flow: &mut Flow,
    ) -> Option<()> {
        let mut candidate = path.environment;
        let floor = candidate.protect_before(self.next_identity);
        let ticket = self.enter_instance(handler.scope_id.get(), &mut candidate)?;
        let result = self.protected_region(&mut candidate, |analyzer, candidate| {
            if let Some(param) = &handler.param {
                let value = analyzer.heap_result(path.value.into_fact(analyzer.budget))?;
                analyzer.bind_pattern(&param.pattern, value, candidate)?;
            }
            analyzer.block_statement(&handler.body, candidate)
        });
        let exited = self.leave_instance(Some(ticket), &mut candidate);
        let mut result = result.filter(|_| exited)?;
        candidate.protect_before(floor);
        result.restore_floor(floor);
        if let Some(value) = result.normal.take() {
            self.heap_result(flow.merge_normal(
                Path {
                    value,
                    environment: candidate,
                },
                environment,
                self.budget,
            ))?;
        }
        self.heap_result(flow.merge_abrupt(result, self.budget))
    }

    fn finalize_path(
        &mut self,
        finalizer: &BlockStatement<'_>,
        kind: Option<Transfer>,
        path: Path,
        environment: &mut Environment,
        result: &mut Flow,
    ) -> Option<()> {
        let mut candidate = path.environment;
        // The pending value is a temporary across cleanup, even if no live
        // lexical binding refers to it. Preserve its reachable allocations.
        let floor = candidate.protect_before(self.next_identity);
        let mut cleanup = self.protected_region(&mut candidate, |analyzer, candidate| {
            analyzer.block_statement(finalizer, candidate)
        })?;
        candidate.protect_before(floor);
        cleanup.restore_floor(floor);
        if cleanup.normal.take().is_some() {
            let resumed = Path {
                value: path.value,
                environment: candidate,
            };
            if let Some(kind) = kind {
                self.heap_result(result.extend_abrupt(kind, vec![resumed], self.budget))?;
            } else {
                self.heap_result(result.merge_normal(resumed, environment, self.budget))?;
            }
        }
        // Abrupt cleanup overrides the pending completion on that path.
        self.heap_result(result.merge_abrupt(cleanup, self.budget))
    }

    fn evaluate_try(
        &mut self,
        statement: &TryStatement<'_>,
        environment: &mut Environment,
    ) -> Option<Flow> {
        let mut flow = self.protected_region(environment, |analyzer, candidate| {
            analyzer.block_statement(&statement.block, candidate)
        })?;
        if let Some(handler) = &statement.handler {
            if let Some(paths) = flow.abrupt.remove(&Transfer::Throw) {
                for thrown in paths {
                    self.catch_path(handler, thrown, environment, &mut flow)?;
                }
            }
        }
        if let Some(finalizer) = &statement.finalizer {
            let mut result = Flow::no_paths();
            if let Some(value) = flow.normal.take() {
                let path = Path {
                    value,
                    environment: environment.clone(),
                };
                self.finalize_path(finalizer, None, path, environment, &mut result)?;
            }
            for (kind, paths) in flow.abrupt {
                for path in paths {
                    self.finalize_path(
                        finalizer,
                        Some(kind.clone()),
                        path,
                        environment,
                        &mut result,
                    )?;
                }
            }
            flow = result;
        }
        self.heap_result(flow.update_empty(&CompletionValue::undefined(), self.budget))?;
        Some(flow)
    }

    pub(super) fn try_statement(
        &mut self,
        statement: &TryStatement<'_>,
        environment: &mut Environment,
    ) -> Option<Flow> {
        let observations = self.begin_observations(true);
        let mut candidate = environment.clone();
        let flow = self.evaluate_try(statement, &mut candidate);
        self.finish_observations(observations, flow.is_some())?;
        let flow = flow?;
        *environment = candidate;
        Some(flow)
    }
}
