//! Allocation existence on arbitrary reaching paths.
//!
//! An absent descriptor alone cannot distinguish a branch-local allocation
//! from a previously created object whose contents became unproved. The
//! interpreter allocates monotonically numbered identities, so contiguous
//! runs of births are represented by one interval rather than one tombstone
//! per object. Track them only while an arbitrary return-path join is open.
use super::heap::{charge, AllocationId};
use std::{ops::Range, rc::Rc};
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Clone)]
pub(super) struct AllocationOrigins {
    floor: AllocationId,
    births: Rc<Vec<Range<AllocationId>>>,
}

impl AllocationOrigins {
    pub(super) fn new(floor: AllocationId) -> Self {
        Self {
            floor,
            births: Rc::default(),
        }
    }

    /// Identities older than this history may have existed on every path.
    pub(super) fn may_exist(&self, id: AllocationId) -> bool {
        if id < self.floor {
            return true;
        }
        let index = self.births.partition_point(|range| range.start <= id);
        index > 0 && self.births[index - 1].contains(&id)
    }

    pub(super) fn search_cost(&self) -> usize {
        usize::try_from(self.births.len().bit_width())
            .unwrap_or(usize::MAX)
            .saturating_add(1)
    }

    pub(super) fn record(
        &mut self,
        id: AllocationId,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        charge(budget, 1)?;
        if id < self.floor {
            return Ok(());
        }
        if Rc::strong_count(&self.births) > 1 {
            charge(budget, self.births.len())?;
        }
        let births = Rc::make_mut(&mut self.births);
        // The interpreter never reuses an allocation ID, including across
        // discarded speculative paths and subsequent loop iterations.
        if let Some(last) = births.last_mut() {
            debug_assert!(id >= last.end);
            if last.end == id {
                last.end = id + 1;
                return Ok(());
            }
        }
        births.push(id..id + 1);
        Ok(())
    }

    pub(super) fn join(&mut self, other: &Self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        self.floor = self.floor.max(other.floor);
        if Rc::ptr_eq(&self.births, &other.births) {
            return Ok(());
        }
        charge(budget, self.births.len().saturating_add(other.births.len()))?;
        let mut left = self.births.iter().peekable();
        let mut right = other.births.iter().peekable();
        let mut merged = Vec::<Range<AllocationId>>::with_capacity(
            self.births.len().saturating_add(other.births.len()),
        );
        loop {
            let next = match (left.peek(), right.peek()) {
                (Some(a), Some(b)) if a.start <= b.start => left.next(),
                (_, Some(_)) => right.next(),
                (Some(_), None) => left.next(),
                (None, None) => break,
            };
            let Some(range) = next else { break };
            if range.end <= self.floor {
                continue;
            }
            let start = range.start.max(self.floor);
            if let Some(last) = merged.last_mut() {
                if start <= last.end {
                    last.end = last.end.max(range.end);
                    continue;
                }
            }
            merged.push(start..range.end);
        }
        self.births = Rc::new(merged);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn origins_merge_path_births_without_inventing_intermediate_objects(
    ) -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("allocation-origins");
        let mut left = AllocationOrigins::new(10);
        for id in [10, 11, 14, 15, 18] {
            left.record(id, &budget)?;
        }
        let mut right = AllocationOrigins::new(10);
        for id in [11, 12, 14, 17, 18, 19] {
            right.record(id, &budget)?;
        }
        let retained = left.clone();
        assert!(!left.may_exist(12));
        assert!(!right.may_exist(10));
        left.join(&right, &budget)?;
        assert!(left.may_exist(9));
        assert!(left.may_exist(10));
        assert!(left.may_exist(12));
        assert!(!left.may_exist(13));
        assert!(!left.may_exist(16));
        assert!(!left.may_exist(20));
        assert_eq!(left.births.as_slice(), &[10..13, 14..16, 17..20]);
        assert!(!retained.may_exist(12));
        Ok(())
    }

    #[test]
    fn contiguous_births_are_compressed_and_work_is_charged() -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("allocation-origins");
        let mut origins = AllocationOrigins::new(0);
        for id in 0..1024 {
            origins.record(id, &budget)?;
        }
        assert_eq!(origins.births.len(), 1);
        assert_eq!(origins.births.first(), Some(&(0..1024)));
        let mut other = origins.clone();
        let bounded = WorkBudget::new("origin-copy", work_budget::BudgetLimits::work(1));
        assert!(other.record(1024, &bounded).is_err());
        assert!(!other.may_exist(1024));
        Ok(())
    }
}
