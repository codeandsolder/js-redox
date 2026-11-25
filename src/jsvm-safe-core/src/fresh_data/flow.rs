//! ECMAScript completion values and reaching abrupt paths.
//!
//! Empty and an explicit unknown value are different: UpdateEmpty uses
//! the prior completion only for the former. The normal heap remains in
//! the caller; abrupt paths own their snapshots until their target consumes
//! them. A value carried by a return is never reconstructed from the heap.
use super::{Environment, Fact, Value};
use std::{collections::HashMap, rc::Rc};
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Clone)]
pub(super) enum NonEmpty {
    Known(Rc<Fact>),
    Unknown,
}

impl NonEmpty {
    fn join(self, other: &Self, budget: &WorkBudget) -> Result<Self, BudgetExceeded> {
        match (self, other) {
            (Self::Known(left), Self::Known(right)) => {
                if Rc::ptr_eq(&left, right) {
                    Ok(Self::Known(left))
                } else {
                    Ok(Self::from_fact(left.join(right, budget)?))
                }
            }
            _ => Ok(Self::Unknown),
        }
    }

    fn from_fact(value: Option<Fact>) -> Self {
        value.map_or(Self::Unknown, |value| Self::Known(Rc::new(value)))
    }

    fn into_fact(self, budget: &WorkBudget) -> Result<Option<Fact>, BudgetExceeded> {
        match self {
            Self::Known(value) => match Rc::try_unwrap(value) {
                Ok(fact) => Ok(Some(fact)),
                Err(value) => Ok(Some(value.copy(budget)?)),
            },
            Self::Unknown => Ok(None),
        }
    }
}

#[derive(Clone)]
pub(super) enum CompletionValue {
    Empty,
    Value(NonEmpty),
    MaybeEmpty(NonEmpty),
}

impl CompletionValue {
    pub(super) fn value(value: Option<Fact>) -> Self {
        Self::Value(NonEmpty::from_fact(value))
    }

    pub(super) fn undefined() -> Self {
        Self::value(Some(Fact::Primitive(Value::Undefined)))
    }

    pub(super) const fn opaque() -> Self {
        Self::MaybeEmpty(NonEmpty::Unknown)
    }

    pub(super) fn join(self, other: &Self, budget: &WorkBudget) -> Result<Self, BudgetExceeded> {
        match (self, other) {
            (Self::Empty, Self::Empty) => Ok(Self::Empty),
            (Self::Empty, Self::Value(value) | Self::MaybeEmpty(value)) => {
                Ok(Self::MaybeEmpty(value.clone()))
            }
            (Self::Value(value) | Self::MaybeEmpty(value), Self::Empty) => {
                Ok(Self::MaybeEmpty(value))
            }
            (Self::Value(left), Self::Value(right)) => Ok(Self::Value(left.join(right, budget)?)),
            (Self::Value(left) | Self::MaybeEmpty(left), Self::MaybeEmpty(right))
            | (Self::MaybeEmpty(left), Self::Value(right)) => {
                Ok(Self::MaybeEmpty(left.join(right, budget)?))
            }
        }
    }

    pub(super) fn update_empty(
        self,
        inherited: &Self,
        budget: &WorkBudget,
    ) -> Result<Self, BudgetExceeded> {
        match self {
            Self::Empty => Ok(inherited.clone()),
            Self::Value(_) => Ok(self),
            Self::MaybeEmpty(value) => Self::Value(value).join(inherited, budget),
        }
    }

    pub(super) fn into_fact(self, budget: &WorkBudget) -> Result<Option<Fact>, BudgetExceeded> {
        match self {
            Self::Value(value) => value.into_fact(budget),
            Self::Empty | Self::MaybeEmpty(_) => Ok(None),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) enum Transfer {
    Break(Option<String>),
    Continue(Option<String>),
    Return,
    Throw,
}

pub(super) struct Path {
    pub(super) value: CompletionValue,
    pub(super) environment: Environment,
}

impl Path {
    pub(super) fn join(&mut self, other: Self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        self.environment.join_returns(&other.environment, budget)?;
        self.value = std::mem::replace(&mut self.value, CompletionValue::Empty)
            .join(&other.value, budget)?;
        Ok(())
    }

    pub(super) fn accumulate(
        slot: &mut Option<Self>,
        path: Self,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if let Some(previous) = slot {
            previous.join(path, budget)
        } else {
            *slot = Some(path);
            Ok(())
        }
    }
}

pub(super) struct Flow {
    pub(super) normal: Option<CompletionValue>,
    pub(super) abrupt: HashMap<Transfer, Path>,
    pub(super) unproved: bool,
}

impl Flow {
    pub(super) fn normal(value: CompletionValue) -> Self {
        Self {
            normal: Some(value),
            abrupt: HashMap::new(),
            unproved: false,
        }
    }

    pub(super) fn empty() -> Self {
        Self::normal(CompletionValue::Empty)
    }

    pub(super) fn abrupt(
        kind: Transfer,
        value: CompletionValue,
        environment: &Environment,
    ) -> Self {
        Self {
            normal: None,
            abrupt: HashMap::from([(
                kind,
                Path {
                    value,
                    environment: environment.clone(),
                },
            )]),
            unproved: false,
        }
    }

    pub(super) fn opaque(unproved: bool) -> Self {
        Self {
            unproved,
            ..Self::normal(CompletionValue::opaque())
        }
    }

    pub(super) fn merge_abrupt(
        &mut self,
        other: Self,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        self.unproved |= other.unproved;
        for (kind, path) in other.abrupt {
            budget.consume(1)?;
            match self.abrupt.entry(kind) {
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    entry.get_mut().join(path, budget)?
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(path);
                }
            }
        }
        Ok(())
    }

    /// Compose StatementListEvaluation: abrupt Empty values inherit the
    /// preceding normal value just as normal Empty completions do.
    pub(super) fn update_empty(
        &mut self,
        inherited: &CompletionValue,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if let Some(value) = self.normal.take() {
            self.normal = Some(value.update_empty(inherited, budget)?);
        }
        for path in self.abrupt.values_mut() {
            budget.consume(1)?;
            path.value = std::mem::replace(&mut path.value, CompletionValue::Empty)
                .update_empty(inherited, budget)?;
        }
        Ok(())
    }

    pub(super) fn restore_floor(&mut self, floor: usize) {
        for path in self.abrupt.values_mut() {
            path.environment.protect_before(floor);
        }
    }

    /// Consume a jump as an ordinary continuation. The same target can
    /// also be reached normally, so both the value and heap must join.
    pub(super) fn consume(
        &mut self,
        kind: &Transfer,
        environment: &mut Environment,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        let Some(path) = self.abrupt.remove(kind) else {
            return Ok(());
        };
        self.merge_normal(path, environment, budget)
    }

    pub(super) fn merge_normal(
        &mut self,
        path: Path,
        environment: &mut Environment,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if let Some(value) = self.normal.take() {
            environment.join_returns(&path.environment, budget)?;
            self.normal = Some(value.join(&path.value, budget)?);
        } else {
            *environment = path.environment;
            self.normal = Some(path.value);
        }
        Ok(())
    }
}
