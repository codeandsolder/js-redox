//! Ordered iterator protocol boundaries, without an ambient intrinsic
//! identity assumption. Even a fresh array may select a user iterator.
//! Unknown protocol calls invalidate the heap; the rest array itself is
//! nevertheless a fresh ordinary allocation after successful exhaustion.
use super::{
    flow::{CompletionValue, Flow, Path, Transfer},
    AllocationKind, Analyzer, Environment, Fact, OwnData,
};

impl Analyzer<'_, '_> {
    /// Nullish values and receivers with a proven missing iterator method
    /// fail `GetIterator` without calling user code. The `TypeError` is opaque,
    /// but the pre-error heap is unchanged. Other values may invoke a
    /// user-defined iterator, even when the receiver is a fresh literal.
    pub(super) fn acquire_iterator(
        &mut self,
        source: Option<&Fact>,
        environment: &mut Environment,
    ) -> Option<()> {
        if !environment.reachable() {
            return Some(());
        }
        let missing = if let Some(source) = source {
            self.heap_result(environment.definitely_noniterable(source, self.budget))?
        } else {
            false
        };
        if missing {
            self.record_expression_throws(vec![Path {
                value: CompletionValue::value(None),
                environment: environment.clone(),
            }])?;
            environment.terminate();
        } else {
            self.invalidate(environment);
        }
        Some(())
    }

    /// `IteratorStepValue` (or `IteratorStep` for an elision) may execute next
    /// and accessors. A previously exhausted iterator would instead supply
    /// undefined without effects; the opaque join covers both possibilities.
    pub(super) fn advance_iterator(&mut self, environment: &mut Environment) {
        self.invalidate(environment);
    }

    /// Exhaustion happens before the fresh rest array is delivered to
    /// its target. No further `IteratorClose` occurs for the exhausted record.
    pub(super) fn exhaust_iterator(&mut self, environment: &mut Environment) {
        self.invalidate(environment);
    }

    pub(super) fn iterator_rest(&mut self, environment: &mut Environment) -> Option<Fact> {
        self.exhaust_iterator(environment);
        let mut data = OwnData::new(AllocationKind::Array);
        data.unknown_array_tail();
        data.define_data("length".into(), None);
        self.allocate(environment, data, false).fact
    }

    /// The prefix can throw while an iterator is still open. `IteratorClose`
    /// preserves an existing throw completion, but its return method may
    /// mutate reachable objects and cells. Apply that possible effect to
    /// the captured exceptional snapshots, never to the successful prefix.
    /// A normal close can itself throw; model it as a separate opaque effect.
    pub(super) fn iterator_prefix<T>(
        &mut self,
        environment: &mut Environment,
        evaluate: impl FnOnce(&mut Self, &mut Environment) -> Option<T>,
    ) -> Option<T> {
        let outer = std::mem::replace(&mut self.expression_exceptions, Flow::no_paths());
        let result = evaluate(self, environment);
        let mut pending = std::mem::replace(&mut self.expression_exceptions, outer);
        let mut throws = pending.abrupt.remove(&Transfer::Throw).unwrap_or_default();
        self.heap_result(super::heap::charge(self.budget, throws.len()))?;
        for path in &mut throws {
            path.environment.clear();
        }
        self.record_expression_throws(throws)?;
        result
    }

    pub(super) fn close_iterator(&mut self, environment: &mut Environment) {
        self.invalidate(environment);
    }

    pub(super) fn consume_iterable(
        &mut self,
        source: Option<&Fact>,
        environment: &mut Environment,
    ) -> Option<()> {
        self.acquire_iterator(source, environment)?;
        self.exhaust_iterator(environment);
        Some(())
    }
}
