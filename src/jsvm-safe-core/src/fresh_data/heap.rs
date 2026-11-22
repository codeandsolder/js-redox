//! Abstract heap for flow-local ordinary allocations. References are sets of
//! allocation identities, never snapshots of object contents. Consequently an
//! effect or a write through an alias also affects previously captured refs.
use crate::numeric::exact_u32;
use crate::value_eval::{canonical_array_index_key, same_value, Value};
use oxc_syntax::symbol::SymbolId;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use work_budget::{BudgetExceeded, WorkBudget};

pub(super) type AllocationId = usize;
pub(super) type Locations = Rc<[AllocationId]>;

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

/// The value lattice is separate from the descriptor lattice. Unknown data
/// values do not imply arbitrary getters or setters. MaybeData means either
/// an absent own property or a writable own data property on every path.
fn join_value(left: &Option<Fact>, right: &Option<Fact>) -> Option<Fact> {
    left.as_ref()?.join(right.as_ref()?)
}

#[derive(Clone)]
enum Property {
    Absent,
    Data(Option<Fact>),
    MaybeData(Option<Fact>),
    Opaque,
}

impl Property {
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Absent, Self::Absent) => Self::Absent,
            (Self::Data(left), Self::Data(right)) => Self::Data(join_value(left, right)),
            (Self::Absent, Self::Data(value) | Self::MaybeData(value))
            | (Self::Data(value) | Self::MaybeData(value), Self::Absent) => {
                Self::MaybeData(value.clone())
            }
            (Self::Data(left) | Self::MaybeData(left), Self::MaybeData(right))
            | (Self::MaybeData(left), Self::Data(right)) => {
                Self::MaybeData(join_value(left, right))
            }
            _ => Self::Opaque,
        }
    }
}

/// Enumerably copied properties are always writable own data on the
/// fresh destination, regardless of the source's prototype. Reuse the
/// same sparse descriptor lattice for source joins and destination overlays.
#[derive(Clone)]
struct Properties {
    listed: HashMap<String, Property>,
    unlisted: Property,
}

impl Default for Properties {
    fn default() -> Self {
        Self {
            listed: HashMap::new(),
            unlisted: Property::Absent,
        }
    }
}

impl Property {
    fn copied_over(&self, previous: &Self) -> Self {
        match self {
            Self::Absent => previous.clone(),
            Self::Data(value) => Self::Data(value.clone()),
            Self::MaybeData(value) => previous.join(&Self::Data(value.clone())),
            Self::Opaque => Self::Opaque,
        }
    }
}

impl Properties {
    fn get(&self, key: &str) -> &Property {
        self.listed.get(key).unwrap_or(&self.unlisted)
    }

    fn insert(&mut self, key: String, property: Property) {
        self.listed.insert(key, property);
    }

    fn charge(&self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        budget.consume(u64::try_from(self.listed.len()).unwrap_or(u64::MAX))
    }

    fn data_only(&self) -> bool {
        !matches!(self.unlisted, Property::Opaque)
            && self
                .listed
                .values()
                .all(|property| !matches!(property, Property::Opaque))
    }

    fn define_unknown(&mut self, definition: &Property) {
        for property in self.listed.values_mut() {
            *property = property.join(definition);
        }
        self.unlisted = self.unlisted.join(definition);
    }

    fn combine(&mut self, other: &Self, operation: impl Fn(&Property, &Property) -> Property) {
        for (key, property) in &mut self.listed {
            *property = operation(property, other.get(key));
        }
        for (key, property) in &other.listed {
            self.listed
                .entry(key.clone())
                .or_insert_with(|| operation(&self.unlisted, property));
        }
        self.unlisted = operation(&self.unlisted, &other.unlisted);
    }

    fn join(&mut self, other: &Self) {
        self.combine(other, Property::join);
    }

    fn copy_from(&mut self, other: &Self) {
        self.combine(other, |previous, source| source.copied_over(previous));
    }
}

/// Explicit prototypes of fresh allocations are known by identity. The
/// ordinary intrinsic prototype is deliberately unknown: its properties
/// may have been modified before a literal was even evaluated.
#[derive(Clone)]
enum Prototype {
    Unknown,
    Null,
    Objects(Locations),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum AllocationKind {
    Ordinary,
    Array,
}

#[derive(Clone)]
pub(super) struct OwnData {
    kind: AllocationKind,
    prototype: Prototype,
    properties: Properties,
}

impl OwnData {
    pub(super) fn new(kind: AllocationKind) -> Self {
        Self {
            kind,
            prototype: Prototype::Unknown,
            properties: Properties::default(),
        }
    }

    pub(super) fn define_data(&mut self, key: String, value: Option<Fact>) {
        self.properties.insert(key, Property::Data(value));
    }

    pub(super) fn define_accessor(&mut self, key: String) {
        self.properties.insert(key, Property::Opaque);
    }

    pub(super) fn set_literal_prototype(&mut self, value: Option<Fact>) {
        match value {
            Some(Fact::Primitive(Value::Null)) => self.prototype = Prototype::Null,
            Some(Fact::Objects(locations)) => self.prototype = Prototype::Objects(locations),
            None => self.prototype = Prototype::Unknown,
            // The special colon form ignores non-object, non-null values.
            Some(Fact::Primitive(_)) => {}
        }
    }

    fn delete_own(&mut self, key: &str) {
        self.properties.insert(key.to_owned(), Property::Absent);
    }

    /// An unknown computed definition can overwrite any one own key,
    /// and an unknown spread can overwrite any subset. Both join with the
    /// previous descriptor instead of conflating unknown values with accessors.
    pub(super) fn define_unknown_key(&mut self, is_data: bool, value: Option<Fact>) {
        let definition = if is_data {
            Property::Data(value)
        } else {
            Property::Opaque
        };
        self.properties.define_unknown(&definition);
    }

    /// Array spread cannot overwrite any of the already created prefix
    /// elements. Unknown later indices are data or absent, never accessors.
    pub(super) fn unknown_array_tail(&mut self) {
        self.properties.unlisted = Property::MaybeData(None);
    }

    fn property(&self, key: &str) -> &Property {
        self.properties.get(key)
    }

    fn join(&mut self, other: &Self) {
        // A single allocation's prototype cannot change on any modeled
        // path. Unknown prototype mutation invalidates the allocation.
        self.properties.join(&other.properties);
    }

    fn enumerable_data(&self, budget: &WorkBudget) -> Result<Option<Properties>, BudgetExceeded> {
        self.properties.charge(budget)?;
        let mut properties = self.properties.clone();
        if self.kind == AllocationKind::Array {
            // All tracked ordinary literal properties are enumerable,
            // except the intrinsic own Array length descriptor.
            properties.insert("length".to_owned(), Property::Absent);
        }
        Ok(properties.data_only().then_some(properties))
    }

    /// CopyDataProperties ignores inherited data, uses own enumerability,
    /// and defines rather than sets the destination's property. We can
    /// model it only if all possible source descriptors are data/absent.
    pub(super) fn spread(
        &mut self,
        environment: &Environment,
        source: &Fact,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        let Some(properties) = environment.enumerable_data(source, budget)? else {
            return Ok(false);
        };
        self.properties.charge(budget)?;
        properties.charge(budget)?;
        self.properties.copy_from(&properties);
        Ok(true)
    }

    fn is_length(&self, key: &str) -> bool {
        self.kind == AllocationKind::Array && key == "length"
    }

    fn length_value(value: &Option<Fact>) -> Option<u32> {
        exact_u32(value.as_ref()?.primitive()?.number()?)
    }

    fn exact_length(&self) -> Option<u32> {
        let Property::Data(value) = self.property("length") else {
            return None;
        };
        Self::length_value(value)
    }

    fn can_write(&self, key: &str, value: &Option<Fact>) -> bool {
        !self.is_length(key) || Self::length_value(value).is_some()
    }

    fn write(&mut self, key: &str, value: Option<Fact>) {
        if self.is_length(key) {
            let Some(length) = Self::length_value(&value) else {
                return;
            };
            // All indexed properties of a still-fresh Array literal are
            // configurable. ArraySetLength only removes indices >= length.
            for (key, property) in &mut self.properties.listed {
                if canonical_array_index_key(key).is_some_and(|index| index >= length) {
                    *property = Property::Absent;
                }
            }
            self.define_data(
                key.to_owned(),
                Some(Fact::Primitive(Value::Number(f64::from(length)))),
            );
        } else {
            if self.kind == AllocationKind::Array {
                if let Some(index) = canonical_array_index_key(key) {
                    let length = self.exact_length().map(|length| {
                        Fact::Primitive(Value::Number(f64::from(length.max(index + 1))))
                    });
                    self.define_data("length".to_owned(), length);
                }
            }
            self.define_data(key.to_owned(), value);
        }
    }
}

/// Outer None means no proved normal lookup yet; inner None is an
/// effect-free data lookup whose value is unknown.
fn join_lookup(result: &mut Option<Option<Fact>>, value: Option<Fact>) {
    *result = Some(match result.take() {
        Some(previous) => join_value(&previous, &value),
        None => value,
    });
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

    fn enumerable_data(
        &self,
        source: &Fact,
        budget: &WorkBudget,
    ) -> Result<Option<Properties>, BudgetExceeded> {
        match source {
            Fact::Objects(locations) => {
                let mut merged: Option<Properties> = None;
                for id in locations.iter() {
                    let Some(data) = self.allocations.get(id) else {
                        return Ok(None);
                    };
                    let Some(properties) = data.enumerable_data(budget)? else {
                        return Ok(None);
                    };
                    if let Some(merged) = &mut merged {
                        merged.charge(budget)?;
                        properties.charge(budget)?;
                        merged.join(&properties);
                    } else {
                        merged = Some(properties);
                    }
                }
                Ok(merged)
            }
            Fact::Primitive(value) => {
                let mut properties = Properties::default();
                // CopyDataProperties skips null/undefined, and primitive
                // wrappers other than String have no enumerable own keys.
                if let Value::String(value) = value {
                    budget.consume(u64::try_from(value.len()).unwrap_or(u64::MAX))?;
                    for (index, unit) in value.encode_utf16().enumerate() {
                        if index % 256 == 0 {
                            budget.checkpoint()?;
                        }
                        // A supplementary character is two indexed UTF-16
                        // code units. Preserve unrepresentable surrogate
                        // values as unknown data rather than replacing them.
                        let fact = char::from_u32(u32::from(unit))
                            .map(|character| Fact::Primitive(Value::String(character.to_string())));
                        properties.insert(index.to_string(), Property::Data(fact));
                    }
                }
                Ok(Some(properties))
            }
        }
    }

    /// Resolve ordinary [[Get]] from every possible receiver and prototype.
    /// Every successful path must reach either known ordinary writable data
    /// or a null prototype, without an opaque descriptor or unknown object.
    /// This is also sufficient to establish ordinary [[Set]] eligibility.
    pub(super) fn read(&self, locations: &Locations, key: &str) -> Option<Option<Fact>> {
        if let [id] = locations.as_ref() {
            if let Property::Data(value) = self.allocations.get(id)?.property(key) {
                return Some(value.clone());
            }
        }
        let mut pending = locations.to_vec();
        let mut visited = HashSet::new();
        let mut result = None;
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            let data = self.allocations.get(&id)?;
            match data.property(key) {
                Property::Data(value) => {
                    join_lookup(&mut result, value.clone());
                    continue;
                }
                Property::MaybeData(value) => join_lookup(&mut result, value.clone()),
                Property::Absent => {}
                Property::Opaque => return None,
            }
            match &data.prototype {
                Prototype::Unknown => return None,
                Prototype::Null => {
                    join_lookup(&mut result, Some(Fact::Primitive(Value::Undefined)));
                }
                Prototype::Objects(prototypes) => {
                    // Literal prototypes already existed at allocation.
                    // Check the invariant before following any edges.
                    if prototypes.is_empty() || prototypes.iter().any(|&prototype| prototype >= id)
                    {
                        return None;
                    }
                    pending.extend(prototypes.iter().copied());
                }
            }
        }
        result
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
        // Own data, inherited writable data, and missing properties on a
        // fully known prototype chain all define/update own data without
        // an arbitrary setter. The receiver still needs its exotic Array
        // length rules checked separately.
        if self.read(locations, key).is_none() {
            return false;
        }
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
            |data| data.delete_own(key),
        )
    }
}
