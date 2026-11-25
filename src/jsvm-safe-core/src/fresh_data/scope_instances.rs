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

/// Oxc uses one static function scope for both parameter and body
/// bindings. Default initializers can create closures over the parameter
/// environment before the separate body variable environment is created.
#[derive(Clone, Copy, PartialEq, Eq)]
struct EnvironmentIdentity {
    body: InstanceId,
    parameters: Option<InstanceId>,
}

impl EnvironmentIdentity {
    const fn single(id: InstanceId) -> Self {
        Self {
            body: id,
            parameters: None,
        }
    }

    fn binding(self, parameter: impl FnOnce() -> bool) -> InstanceId {
        self.parameters.filter(|_| parameter()).unwrap_or(self.body)
    }

    fn roots(self) -> impl Iterator<Item = InstanceId> {
        std::iter::once(self.body).chain(self.parameters)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Instance {
    scope: ScopeId,
    identity: EnvironmentIdentity,
}

#[derive(Clone)]
pub(super) struct ClosureOrigin {
    pub(super) scope: ScopeId,
    ancestors: Rc<[Instance]>,
}

pub(super) struct ScopeTicket {
    scope: ScopeId,
    previous: Option<EnvironmentIdentity>,
}

impl ScopeTicket {
    pub(super) const fn scope(&self) -> ScopeId {
        self.scope
    }
}

#[derive(Default)]
pub(super) struct ScopeInstances {
    active: HashMap<ScopeId, EnvironmentIdentity>,
}

impl ScopeInstances {
    pub(super) fn enter(&mut self, scope: ScopeId, serial: InstanceId) -> ScopeTicket {
        self.enter_environment(scope, EnvironmentIdentity::single(serial))
    }

    fn enter_environment(&mut self, scope: ScopeId, identity: EnvironmentIdentity) -> ScopeTicket {
        ScopeTicket {
            scope,
            previous: self.active.insert(scope, identity),
        }
    }

    pub(super) fn leave(&mut self, ticket: &ScopeTicket) -> Option<InstanceId> {
        let previous = if let Some(previous) = ticket.previous {
            self.active.insert(ticket.scope, previous)
        } else {
            self.active.remove(&ticket.scope)
        };
        previous.map(|identity| identity.body)
    }

    /// `CreatePerIterationEnvironment` copies values into distinct cells.
    pub(super) fn refresh(&mut self, scope: ScopeId, serial: InstanceId) -> Option<InstanceId> {
        let previous = self.active.get_mut(&scope)?;
        if previous.parameters.is_some() {
            return None;
        }
        Some(std::mem::replace(previous, EnvironmentIdentity::single(serial)).body)
    }

    /// Establish the body variable environment without changing the
    /// identities already captured by closures in default initializers.
    pub(super) fn split_parameters(
        &mut self,
        scope: ScopeId,
        body: InstanceId,
    ) -> Option<InstanceId> {
        let identity = self.active.get_mut(&scope)?;
        if identity.parameters.is_some() {
            return None;
        }
        let parameters = identity.body;
        *identity = EnvironmentIdentity {
            body,
            parameters: Some(parameters),
        };
        Some(parameters)
    }

    pub(super) fn get(
        &self,
        scope: ScopeId,
        parameter: impl FnOnce() -> bool,
    ) -> Option<InstanceId> {
        Some(self.active.get(&scope)?.binding(parameter))
    }

    pub(super) fn roots(&self) -> impl Iterator<Item = InstanceId> + '_ {
        self.active
            .values()
            .copied()
            .flat_map(EnvironmentIdentity::roots)
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
            .map(|instance| self.enter_environment(instance.scope, instance.identity))
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
            let Some(&identity) = self.active.get(&parent) else {
                return Ok(None);
            };
            ancestors.push(Instance {
                scope: parent,
                identity,
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
        self.ancestors
            .iter()
            .flat_map(|instance| instance.identity.roots())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_syntax::scope::ScopeId;

    #[test]
    fn split_parameters_preserve_outer_cells_and_restore_prior_instance() {
        let mut scopes = ScopeInstances::default();
        let scope = ScopeId::new(0);
        let outer = scopes.enter(scope, 1);
        let inner = scopes.enter(scope, 2);
        assert_eq!(scopes.split_parameters(scope, 3), Some(2));
        assert_eq!(scopes.get(scope, || false), Some(3));
        assert_eq!(scopes.get(scope, || true), Some(2));
        assert_eq!(scopes.roots().collect::<Vec<_>>(), vec![3, 2]);
        assert_eq!(scopes.leave(&inner), Some(3));
        assert_eq!(scopes.get(scope, || false), Some(1));
        assert_eq!(scopes.get(scope, || true), Some(1));
        assert_eq!(scopes.leave(&outer), Some(1));
    }

    #[test]
    fn scope_tickets_restore_instances_and_iteration_refresh_does_not_reuse_them() {
        let mut scopes = ScopeInstances::default();
        let scope = ScopeId::new(0);
        let outer = scopes.enter(scope, 1);
        let first = scopes.active[&scope].body;
        assert_eq!(scopes.refresh(scope, 2), Some(first));
        let second = scopes.active[&scope].body;
        assert_ne!(first, second);
        let inner = scopes.enter(scope, 3);
        assert_ne!(scopes.active[&scope].body, second);
        assert_eq!(scopes.leave(&inner), Some(3));
        assert_eq!(scopes.active[&scope].body, second);
        assert_eq!(scopes.leave(&outer), Some(second));
        assert!(!scopes.active.contains_key(&scope));
        let next = scopes.enter(scope, 4);
        assert_ne!(scopes.active[&scope].body, second);
        assert_eq!(scopes.leave(&next), Some(4));
    }
}
