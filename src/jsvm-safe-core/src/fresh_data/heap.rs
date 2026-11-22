//! Abstract heap for flow-local ordinary allocations. References are sets of
//! allocation identities, never snapshots of object contents. Consequently an
//! effect or a write through an alias also affects previously captured refs.
use crate::numeric::exact_u32;
use crate::value_eval::{canonical_array_index_key, same_value, Value};
use oxc_syntax::symbol::SymbolId;
use std::collections::HashMap;
use std::rc::Rc;

pub(super) type AllocationId = usize;
pub(super) type Locations = Rc<[AllocationId]>;
type Properties = HashMap<String, Option<Fact>>;

#[derive(Clone)]
pub(super) enum Fact {
    Primitive(Value),
    Objects(Locations),
}

impl Fact {
    pub(super) fn join(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Primitive(a), Self::Primitive(b)) => {
                let equal = match (a, b) {
                    (Value::Number(a), Value::Number(b)) => a.to_bits() == b.to_bits(),
                    _ => same_value(a, b),
                };
                equal.then(|| self.clone())
            }
            (Self::Objects(a), Self::Objects(b)) => {
                if a == b {
                    return Some(self.clone());
                }
                let mut ids = Vec::with_capacity(a.len() + b.len());
                ids.extend_from_slice(a);
                ids.extend_from_slice(b);
                ids.sort_unstable();
                ids.dedup();
                Some(Self::Objects(ids.into()))
            }
            _ => None,
        }
    }

    pub(super) fn truthy(&self) -> bool {
        match self {
            Self::Primitive(value) => value.truthy(),
            Self::Objects(_) => true,
        }
    }

    pub(super) fn strict_equal(&self, other: &Self) -> Option<bool> {
        match (self, other) {
            (Self::Primitive(a), Self::Primitive(b)) => Some(same_value(a, b)),
            (Self::Objects(a), Self::Objects(b)) => {
                if a.len() == 1 && b.len() == 1 {
                    return Some(a == b);
                }
                // Disjoint possible allocations cannot be the same object.
                if a.iter().all(|id| b.binary_search(id).is_err()) {
                    return Some(false);
                }
                None
            }
            _ => Some(false),
        }
    }

    pub(super) fn primitive(&self) -> Option<&Value> {
        match self {
            Self::Primitive(value) => Some(value),
            Self::Objects(_) => None,
        }
    }
}

/// None represents an unknown value, not an unknown descriptor. The key
/// remains known to be own, writable data whenever it appears in Properties.
fn join_value(left: &Option<Fact>, right: &Option<Fact>) -> Option<Fact> {
    left.as_ref()?.join(right.as_ref()?)
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum AllocationKind {
    Ordinary,
    Array,
}

#[derive(Clone)]
pub(super) struct OwnData {
    kind: AllocationKind,
    properties: Properties,
}

impl OwnData {
    pub(super) fn new(kind: AllocationKind) -> Self {
        Self {
            kind,
            properties: HashMap::new(),
        }
    }

    pub(super) fn insert(&mut self, key: String, value: Option<Fact>) {
        self.properties.insert(key, value);
    }

    pub(super) fn remove(&mut self, key: &str) {
        self.properties.remove(key);
    }

    pub(super) fn clear(&mut self) {
        self.properties.clear();
    }

    fn join(&mut self, other: &Self) {
        self.properties.retain(|key, value| {
            let Some(right) = other.properties.get(key) else {
                return false;
            };
            *value = join_value(value, right);
            true
        });
    }

    fn is_length(&self, key: &str) -> bool {
        self.kind == AllocationKind::Array && key == "length"
    }

    fn length_value(value: &Option<Fact>) -> Option<u32> {
        exact_u32(value.as_ref()?.primitive()?.number()?)
    }

    fn can_write(&self, key: &str, value: &Option<Fact>) -> bool {
        self.properties.contains_key(key)
            && (!self.is_length(key) || Self::length_value(value).is_some())
    }

    fn write(&mut self, key: &str, value: Option<Fact>) {
        if self.is_length(key) {
            let Some(length) = Self::length_value(&value) else {
                return;
            };
            // All indexed properties of a still-fresh Array literal are
            // configurable. ArraySetLength only removes indices >= length.
            self.properties
                .retain(|key, _| canonical_array_index_key(key).is_none_or(|index| index < length));
            self.insert(
                key.to_owned(),
                Some(Fact::Primitive(Value::Number(f64::from(length)))),
            );
        } else {
            self.insert(key.to_owned(), value);
        }
    }
}

#[derive(Clone, Default)]
pub(super) struct Environment {
    bindings: HashMap<SymbolId, Fact>,
    allocations: HashMap<AllocationId, Rc<OwnData>>,
}

impl Environment {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn clear(&mut self) {
        self.bindings.clear();
        self.allocations.clear();
    }

    pub(super) fn get(&self, symbol: &SymbolId) -> Option<&Fact> {
        self.bindings.get(symbol)
    }

    pub(super) fn insert(&mut self, symbol: SymbolId, fact: Fact) {
        self.bindings.insert(symbol, fact);
    }

    pub(super) fn remove(&mut self, symbol: &SymbolId) {
        self.bindings.remove(symbol);
    }

    pub(super) fn allocate(&mut self, id: AllocationId, data: OwnData) -> Fact {
        self.allocations.insert(id, Rc::new(data));
        Fact::Objects(Rc::from([id]))
    }

    /// Join normal reaching paths. Allocations created after the fork exist
    /// only in the branch that created them. Older allocations must still
    /// be valid in both branches: a missing entry means effects invalidated
    /// that proof, not that the allocation never existed.
    pub(super) fn join(&mut self, other: &Self, first_new: AllocationId) {
        self.bindings.retain(|symbol, fact| {
            let Some(joined) = other
                .bindings
                .get(symbol)
                .and_then(|right| fact.join(right))
            else {
                return false;
            };
            *fact = joined;
            true
        });
        self.allocations.retain(|id, data| {
            let Some(right) = other.allocations.get(id) else {
                return *id >= first_new;
            };
            if !Rc::ptr_eq(data, right) {
                Rc::make_mut(data).join(right);
            }
            true
        });
        for (&id, data) in &other.allocations {
            if id >= first_new {
                self.allocations
                    .entry(id)
                    .or_insert_with(|| Rc::clone(data));
            }
        }
    }

    /// Outer None means potential inherited/accessor/missing property read.
    /// Inner None means a known own-data read of an unknown value.
    pub(super) fn read(&self, locations: &Locations, key: &str) -> Option<Option<Fact>> {
        let (&first, rest) = locations.split_first()?;
        let mut value = self.allocations.get(&first)?.properties.get(key)?.clone();
        for id in rest {
            let right = self.allocations.get(id)?.properties.get(key)?;
            value = join_value(&value, right);
        }
        Some(value)
    }

    fn update(
        &mut self,
        locations: &Locations,
        can_update: impl Fn(&OwnData) -> bool,
        mut apply: impl FnMut(&mut OwnData),
    ) -> bool {
        if locations.is_empty()
            || !locations.iter().all(|id| {
                self.allocations
                    .get(id)
                    .is_some_and(|data| can_update(data))
            })
        {
            return false;
        }

        let weak = locations.len() != 1;
        for id in locations.iter() {
            let Some(data) = self.allocations.get_mut(id) else {
                return false;
            };
            if weak {
                // The receiver may refer to any one of these allocations.
                // Join modified and unmodified states for every possibility.
                let mut updated = data.as_ref().clone();
                apply(&mut updated);
                Rc::make_mut(data).join(&updated);
            } else {
                apply(Rc::make_mut(data));
            }
        }
        true
    }

    pub(super) fn write(&mut self, locations: &Locations, key: &str, value: Option<Fact>) -> bool {
        self.update(
            locations,
            |data| data.can_write(key, &value),
            |data| data.write(key, value.clone()),
        )
    }

    /// Deletion on an ordinary allocation cannot invoke an inherited setter
    /// or getter. Fresh literal properties are configurable, except length.
    pub(super) fn delete(&mut self, locations: &Locations, key: &str) -> bool {
        self.update(
            locations,
            |data| !data.is_length(key),
            |data| data.remove(key),
        )
    }
}
