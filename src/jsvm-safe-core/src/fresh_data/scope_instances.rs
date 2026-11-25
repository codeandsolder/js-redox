//! Dynamic identities for currently executing lexical environments.
//!
//! A closure keeps the environment instances present at creation, not
//! just the static scope IDs. In particular, each iteration of a lexical
//! for loop can have distinct cells with the same semantic symbol IDs.
use oxc_semantic::Scoping;
use oxc_syntax::scope::ScopeId;
use std::{collections::HashMap, rc::Rc};
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Clone, Copy, PartialEq, Eq)]
struct Instance {
    scope: ScopeId,
    serial: usize,
}

#[derive(Clone)]
pub(super) struct ClosureOrigin {
    pub(super) scope: ScopeId,
    ancestors: Rc<[Instance]>,
}

pub(super) struct ScopeTicket {
    scope: ScopeId,
    previous: Option<usize>,
}

#[derive(Default)]
pub(super) struct ScopeInstances {
    active: HashMap<ScopeId, usize>,
    next: usize,
}

impl ScopeInstances {
    pub(super) fn enter(&mut self, scope: ScopeId) -> ScopeTicket {
        let serial = self.next;
        self.next += 1;
        ScopeTicket {
            scope,
            previous: self.active.insert(scope, serial),
        }
    }

    pub(super) fn leave(&mut self, ticket: &ScopeTicket) {
        if let Some(previous) = ticket.previous {
            self.active.insert(ticket.scope, previous);
        } else {
            self.active.remove(&ticket.scope);
        }
    }

    /// `CreatePerIterationEnvironment` copies the current binding values
    /// but old closures still reference the previous cells.
    pub(super) fn refresh(&mut self, scope: ScopeId) {
        if let Some(serial) = self.active.get_mut(&scope) {
            *serial = self.next;
            self.next += 1;
        }
    }

    pub(super) fn scopes(&self) -> impl Iterator<Item = ScopeId> + '_ {
        self.active.keys().copied()
    }

    pub(super) fn capture(
        &self,
        scope: ScopeId,
        scoping: &Scoping,
        budget: &WorkBudget,
    ) -> Result<Option<ClosureOrigin>, BudgetExceeded> {
        let mut ancestors = Vec::new();
        for parent in scoping.scope_ancestors(scope).skip(1) {
            budget.consume(1)?;
            let Some(&serial) = self.active.get(&parent) else {
                return Ok(None);
            };
            ancestors.push(Instance {
                scope: parent,
                serial,
            });
        }
        Ok(Some(ClosureOrigin {
            scope,
            ancestors: ancestors.into(),
        }))
    }

    pub(super) fn matches(
        &self,
        origin: &ClosureOrigin,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        budget.consume(u64::try_from(origin.ancestors.len()).unwrap_or(u64::MAX))?;
        Ok(origin
            .ancestors
            .iter()
            .all(|instance| self.active.get(&instance.scope) == Some(&instance.serial)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_syntax::scope::ScopeId;

    #[test]
    fn scope_tickets_restore_instances_and_iteration_refresh_does_not_reuse_them() {
        let mut scopes = ScopeInstances::default();
        let scope = ScopeId::new(0);
        let outer = scopes.enter(scope);
        let first = scopes.active[&scope];
        scopes.refresh(scope);
        let second = scopes.active[&scope];
        assert_ne!(first, second);
        let inner = scopes.enter(scope);
        assert_ne!(scopes.active[&scope], second);
        scopes.leave(&inner);
        assert_eq!(scopes.active[&scope], second);
        scopes.leave(&outer);
        assert!(!scopes.active.contains_key(&scope));
        let next = scopes.enter(scope);
        assert_ne!(scopes.active[&scope], second);
        scopes.leave(&next);
    }
}
