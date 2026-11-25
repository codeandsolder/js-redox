//! Dynamic identities for currently executing lexical environments.
//!
//! A closure keeps the environment instances present at creation, not
//! just the static scope IDs. In particular, each iteration of a lexical
//! for loop can have distinct cells with the same semantic symbol IDs.
use super::cells::InstanceId;
use oxc_semantic::Scoping;
use oxc_syntax::scope::ScopeId;
use std::{collections::HashMap, rc::Rc};
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Clone, Copy, PartialEq, Eq)]
struct Instance {
    scope: ScopeId,
    serial: InstanceId,
}

#[derive(Clone)]
pub(super) struct ClosureOrigin {
    pub(super) scope: ScopeId,
    ancestors: Rc<[Instance]>,
}

pub(super) struct ScopeTicket {
    scope: ScopeId,
    previous: Option<InstanceId>,
}

impl ScopeTicket {
    pub(super) const fn scope(&self) -> ScopeId {
        self.scope
    }
}

#[derive(Default)]
pub(super) struct ScopeInstances {
    active: HashMap<ScopeId, InstanceId>,
}

impl ScopeInstances {
    pub(super) fn enter(&mut self, scope: ScopeId, serial: InstanceId) -> ScopeTicket {
        ScopeTicket {
            scope,
            previous: self.active.insert(scope, serial),
        }
    }

    pub(super) fn leave(&mut self, ticket: &ScopeTicket) -> Option<InstanceId> {
        if let Some(previous) = ticket.previous {
            self.active.insert(ticket.scope, previous)
        } else {
            self.active.remove(&ticket.scope)
        }
    }

    /// `CreatePerIterationEnvironment` copies values into distinct cells.
    pub(super) fn refresh(&mut self, scope: ScopeId, serial: InstanceId) -> Option<InstanceId> {
        let previous = self.active.get_mut(&scope)?;
        Some(std::mem::replace(previous, serial))
    }

    pub(super) fn get(&self, scope: ScopeId) -> Option<InstanceId> {
        self.active.get(&scope).copied()
    }

    pub(super) fn roots(&self) -> impl Iterator<Item = InstanceId> + '_ {
        self.active.values().copied()
    }

    /// Select the closure's original environment chain while its code
    /// executes. The caller's visible instances are restored on return.
    /// Collection is suspended throughout the activation.
    pub(super) fn select(
        &mut self,
        origin: &ClosureOrigin,
        budget: &WorkBudget,
    ) -> Result<Vec<ScopeTicket>, BudgetExceeded> {
        budget.consume(u64::try_from(origin.ancestors.len()).unwrap_or(u64::MAX))?;
        Ok(origin
            .ancestors
            .iter()
            .map(|instance| self.enter(instance.scope, instance.serial))
            .collect())
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
}

impl ClosureOrigin {
    pub(super) fn instances(&self) -> impl Iterator<Item = InstanceId> + '_ {
        self.ancestors.iter().map(|instance| instance.serial)
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
        let outer = scopes.enter(scope, 1);
        let first = scopes.active[&scope];
        assert_eq!(scopes.refresh(scope, 2), Some(first));
        let second = scopes.active[&scope];
        assert_ne!(first, second);
        let inner = scopes.enter(scope, 3);
        assert_ne!(scopes.active[&scope], second);
        assert_eq!(scopes.leave(&inner), Some(3));
        assert_eq!(scopes.active[&scope], second);
        assert_eq!(scopes.leave(&outer), Some(second));
        assert!(!scopes.active.contains_key(&scope));
        let next = scopes.enter(scope, 4);
        assert_ne!(scopes.active[&scope], second);
        assert_eq!(scopes.leave(&next), Some(4));
    }
}
