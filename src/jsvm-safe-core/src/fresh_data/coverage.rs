//! Source regions whose potential evaluations were not fully interpreted.
//!
//! Repeated execution needs both value agreement and observation coverage.
//! An opaque operation may clear the heap while a saved primitive still
//! allows the enclosing loop to reach its normal exit.

use oxc_span::Span;
use std::collections::HashSet;
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Default)]
pub(super) struct CoverageGaps {
    spans: HashSet<(u32, u32)>,
}

impl CoverageGaps {
    pub(super) fn insert(&mut self, span: Span) {
        self.spans.insert((span.start, span.end));
    }

    pub(super) fn merge(&mut self, other: Self) {
        self.spans.extend(other.spans);
    }

    pub(super) fn normalize(
        self,
        observations: usize,
        budget: &WorkBudget,
    ) -> Result<Option<ExcludedRegions>, BudgetExceeded> {
        let count = self.spans.len();
        if count == 0 {
            return Ok(None);
        }
        // Account for the sort and subsequent binary searches before
        // constructing the interval index.
        let width = usize::try_from(count.bit_width()).unwrap_or(usize::MAX);
        let units = count
            .saturating_add(observations)
            .saturating_mul(width.saturating_add(1));
        budget.consume(u64::try_from(units).unwrap_or(u64::MAX))?;
        let mut spans = self.spans.into_iter().collect::<Vec<_>>();
        spans.sort_unstable();
        let mut merged: Vec<(u32, u32)> = Vec::with_capacity(spans.len());
        for (start, end) in spans {
            if let Some(last) = merged.last_mut() {
                if start <= last.1 {
                    last.1 = last.1.max(end);
                    continue;
                }
            }
            merged.push((start, end));
        }
        Ok(Some(ExcludedRegions(merged)))
    }
}

pub(super) struct ExcludedRegions(Vec<(u32, u32)>);

impl ExcludedRegions {
    pub(super) fn contains(&self, (start, end): (u32, u32)) -> bool {
        let index = self.0.partition_point(|&(lower, _)| lower <= start);
        index > 0 && end <= self.0[index - 1].1
    }
}
