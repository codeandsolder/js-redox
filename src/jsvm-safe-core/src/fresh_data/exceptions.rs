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
    fn protected_region(
        &mut self,
        environment: &mut Environment,
        evaluate: impl FnOnce(&mut Self, &mut Environment) -> Option<Flow>,
    ) -> Option<Flow> {
        let before = self.exception_generation;
        let flow = evaluate(self, environment);
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
