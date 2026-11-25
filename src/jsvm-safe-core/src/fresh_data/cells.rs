//! Declarative cells belong to dynamic lexical environment instances.
//!
//! Copy-on-write maps are partitioned by environment, so changing one
//! activation or copying a loop's per-iteration environment does not clone
//! the captured cells of unrelated live closures.
use super::heap::{charge, clear_shared, Fact, MIN_COLLECTION_SIZE};
use oxc_syntax::symbol::SymbolId;
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};
use work_budget::{BudgetExceeded, WorkBudget};

pub(super) type InstanceId = usize;

#[derive(Clone, Copy)]
pub(super) struct CellId {
    pub(super) instance: InstanceId,
    pub(super) symbol: SymbolId,
}

type InstanceCells = HashMap<SymbolId, Fact>;

#[derive(Clone, Default)]
pub(super) struct CellStore {
    instances: Rc<HashMap<InstanceId, Rc<InstanceCells>>>,
}

fn charge_cells(cells: &InstanceCells, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
    charge(budget, cells.capacity())?;
    for value in cells.values() {
        charge(budget, value.clone_weight())?;
    }
    Ok(())
}

impl CellStore {
    fn charge_copy(&self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        if Rc::strong_count(&self.instances) > 1 {
            charge(budget, self.instances.capacity())?;
        }
        Ok(())
    }

    fn mutable_instance(
        &mut self,
        id: InstanceId,
        budget: &WorkBudget,
    ) -> Result<&mut InstanceCells, BudgetExceeded> {
        self.charge_copy(budget)?;
        let cells = Rc::make_mut(&mut self.instances).entry(id).or_default();
        if Rc::strong_count(cells) > 1 {
            charge_cells(cells, budget)?;
        }
        Ok(Rc::make_mut(cells))
    }

    pub(super) fn get(&self, id: CellId) -> Option<&Fact> {
        self.instances.get(&id.instance)?.get(&id.symbol)
    }

    pub(super) fn insert(
        &mut self,
        id: CellId,
        value: Fact,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        self.mutable_instance(id.instance, budget)?
            .insert(id.symbol, value);
        Ok(())
    }

    pub(super) fn remove(&mut self, id: CellId, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        if self.get(id).is_some() {
            self.mutable_instance(id.instance, budget)?
                .remove(&id.symbol);
        }
        Ok(())
    }

    pub(super) fn copy_instance(
        &mut self,
        from: InstanceId,
        to: InstanceId,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if let Some(cells) = self.instances.get(&from).cloned() {
            self.charge_copy(budget)?;
            Rc::make_mut(&mut self.instances).insert(to, cells);
        }
        Ok(())
    }

    pub(super) fn clear(&mut self) {
        clear_shared(&mut self.instances);
    }

    pub(super) fn len(&self) -> usize {
        self.instances.len()
    }

    pub(super) fn capacity(&self) -> usize {
        self.instances.capacity()
    }

    pub(super) fn ids(&self) -> impl Iterator<Item = InstanceId> + '_ {
        self.instances.keys().copied()
    }

    pub(super) fn instance(&self, id: InstanceId) -> Option<&InstanceCells> {
        self.instances.get(&id).map(Rc::as_ref)
    }

    pub(super) fn retain(
        &mut self,
        marked: &HashSet<InstanceId>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        charge(budget, self.instances.capacity())?;
        if self.instances.keys().any(|id| !marked.contains(id)) {
            self.charge_copy(budget)?;
            Rc::make_mut(&mut self.instances).retain(|id, _| marked.contains(id));
        }
        if self.instances.capacity()
            > self
                .instances
                .len()
                .saturating_mul(4)
                .max(MIN_COLLECTION_SIZE)
        {
            self.charge_copy(budget)?;
            Rc::make_mut(&mut self.instances).shrink_to_fit();
        }
        Ok(())
    }

    /// Preserve an absent instance's cells only when the instance was
    /// never born on that path. Absence of an individual cell in a shared
    /// instance always means its value is not proved.
    pub(super) fn join(
        &mut self,
        other: &Self,
        absent_left: impl Fn(InstanceId) -> bool,
        absent_right: impl Fn(InstanceId) -> bool,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if Rc::ptr_eq(&self.instances, &other.instances) {
            return Ok(());
        }
        self.charge_copy(budget)?;
        charge(budget, self.capacity().saturating_add(other.capacity()))?;
        let instances = Rc::make_mut(&mut self.instances);
        let mut failure = Ok(());
        instances.retain(|&id, left| {
            if failure.is_err() {
                return true;
            }
            let Some(right) = other.instances.get(&id) else {
                return absent_right(id);
            };
            if Rc::ptr_eq(left, right) {
                return true;
            }
            failure = join_cells(left, right, budget);
            true
        });
        failure?;
        for (&id, cells) in other.instances.iter() {
            if absent_left(id) {
                instances.entry(id).or_insert_with(|| Rc::clone(cells));
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn shares(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.instances, &other.instances)
    }
}

fn join_cells(
    left: &mut Rc<InstanceCells>,
    right: &InstanceCells,
    budget: &WorkBudget,
) -> Result<(), BudgetExceeded> {
    charge(budget, left.capacity())?;
    if Rc::strong_count(left) > 1 {
        charge_cells(left, budget)?;
    }
    let mut failure = Ok(());
    Rc::make_mut(left).retain(|symbol, fact| {
        if failure.is_err() {
            return true;
        }
        let Some(right) = right.get(symbol) else {
            return false;
        };
        match fact.join(right, budget) {
            Ok(Some(joined)) => {
                *fact = joined;
                true
            }
            Ok(None) => false,
            Err(error) => {
                failure = Err(error);
                true
            }
        }
    });
    failure
}
