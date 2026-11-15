//! Exact cycle detection across multi-pass source rewrites.
//!
//! A no-op only detects fixed points (period 1); syntactically valid
//! transformations can also oscillate A -> B -> A or over longer periods.
//! Hash each distinct source only once per observed iteration, and retain its
//! bytes for collision-safe equality. At Knitsail size (~100 KiB, ~50 passes),
//! the history uses only a few MiB and hashing is negligible versus parsing.

use sha2::{Digest, Sha256};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IterationCycle {
    pub first_seen_iteration: usize,
    pub repeated_at_iteration: usize,
    pub period: usize,
    pub source_sha256: String,
}

#[derive(Default)]
pub(crate) struct IterationHistory {
    by_sha256: HashMap<[u8; 32], Vec<(usize, String)>>,
}

impl IterationHistory {
    pub(crate) fn new(original: &str) -> Self {
        let mut history = Self::default();
        let _ = history.observe(0, original);
        history
    }

    pub(crate) fn observe(&mut self, iteration: usize, source: &str) -> Option<IterationCycle> {
        let fingerprint: [u8; 32] = Sha256::digest(source.as_bytes()).into();
        self.observe_fingerprint(iteration, source, fingerprint)
    }

    fn observe_fingerprint(
        &mut self,
        iteration: usize,
        source: &str,
        fingerprint: [u8; 32],
    ) -> Option<IterationCycle> {
        let candidates = self.by_sha256.entry(fingerprint).or_default();
        if let Some((first, _)) = candidates.iter().find(|(_, previous)| previous == source) {
            return Some(IterationCycle {
                first_seen_iteration: *first,
                repeated_at_iteration: iteration,
                period: iteration.saturating_sub(*first),
                source_sha256: fingerprint
                    .iter()
                    .map(|byte| format!("{byte:02x}"))
                    .collect(),
            });
        }
        candidates.push((iteration, source.to_owned()));
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_two_state_cycle_from_initial_input() {
        let mut history = IterationHistory::new("A");
        assert_eq!(history.observe(1, "B"), None);
        let Some(cycle) = history.observe(2, "A") else {
            unreachable!("A -> B -> A must be detected");
        };
        assert_eq!(cycle.first_seen_iteration, 0);
        assert_eq!(cycle.repeated_at_iteration, 2);
        assert_eq!(cycle.period, 2);
        assert_eq!(cycle.source_sha256.len(), 64);
    }

    #[test]
    fn detects_longer_cycle_not_starting_at_initial_source() {
        let mut history = IterationHistory::new("A");
        for (index, value) in ["B", "C", "D"].iter().enumerate() {
            assert_eq!(history.observe(index + 1, value), None);
        }
        let Some(cycle) = history.observe(4, "B") else {
            unreachable!("B -> C -> D -> B must be detected");
        };
        assert_eq!(cycle.first_seen_iteration, 1);
        assert_eq!(cycle.period, 3);
    }

    #[test]
    fn hash_collision_never_reports_a_false_cycle() {
        let mut history = IterationHistory::default();
        let same_digest = [11_u8; 32];
        assert_eq!(history.observe_fingerprint(0, "A", same_digest), None);
        assert_eq!(history.observe_fingerprint(1, "B", same_digest), None);
        let Some(cycle) = history.observe_fingerprint(2, "B", same_digest) else {
            unreachable!("exact matching bytes must be detected even on hash collision");
        };
        assert_eq!(cycle.first_seen_iteration, 1);
        assert_eq!(cycle.period, 1);
    }

    #[test]
    fn distinct_50_pass_history_does_not_report_cycle() {
        let mut history = IterationHistory::new("input");
        for iteration in 1..=50 {
            assert_eq!(
                history.observe(iteration, &format!("state-{iteration}")),
                None
            );
        }
    }
}
