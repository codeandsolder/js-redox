//! Abstract heap for flow-local ordinary allocations. References are sets of
//! allocation identities, never snapshots of object contents. Consequently an
//! effect or a write through an alias also affects previously captured refs.
use super::{
    cells::{CellId, CellStore, InstanceId},
    origins::IdentityOrigins,
    scope_instances::ClosureOrigin,
};
use crate::numeric::{exact_u32, js_number_from_u64};
use crate::value_eval::{
    canonical_array_index_key, identical_primitive_value, strict_primitive_equal, Value,
};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use work_budget::{BudgetExceeded, WorkBudget};

/// Charge variable-sized operations before allocating or iterating.
pub(super) fn charge(budget: &WorkBudget, units: usize) -> Result<(), BudgetExceeded> {
    budget.consume(u64::try_from(units).unwrap_or(u64::MAX))
}

pub(super) type AllocationId = usize;
pub(super) type Locations = Rc<[AllocationId]>;

#[derive(Clone)]
pub(super) enum Fact {
    Primitive(Value),
    Objects(Locations),
}

impl Fact {
    pub(super) fn same_fact(
        &self,
        other: &Self,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        self.charge_merge(other, budget)?;
        Ok(match (self, other) {
            (Self::Primitive(left), Self::Primitive(right)) => {
                identical_primitive_value(left, right)
            }
            (Self::Objects(left), Self::Objects(right)) => Rc::ptr_eq(left, right) || left == right,
            _ => false,
        })
    }

    pub(super) fn join(
        &self,
        other: &Self,
        budget: &WorkBudget,
    ) -> Result<Option<Self>, BudgetExceeded> {
        self.charge_merge(other, budget)?;
        Ok(self.join_proven(other))
    }

    pub(super) fn copy(&self, budget: &WorkBudget) -> Result<Self, BudgetExceeded> {
        charge(budget, self.clone_weight())?;
        Ok(self.clone())
    }

    pub(super) const fn clone_weight(&self) -> usize {
        match self {
            Self::Primitive(value) => value_weight(value),
            Self::Objects(_) => 1,
        }
    }

    fn merge_weight(&self) -> usize {
        match self {
            Self::Objects(locations) => locations.len().saturating_add(1),
            Self::Primitive(_) => self.clone_weight(),
        }
    }

    fn charge_merge(&self, other: &Self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        if let (Self::Objects(a), Self::Objects(b)) = (self, other) {
            if Rc::ptr_eq(a, b) {
                return Ok(());
            }
        }
        charge(
            budget,
            self.merge_weight().saturating_add(other.merge_weight()),
        )
    }

    fn join_proven(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Primitive(a), Self::Primitive(b)) => {
                identical_primitive_value(a, b).then(|| self.clone())
            }
            (Self::Objects(a), Self::Objects(b)) => {
                if Rc::ptr_eq(a, b) || a == b {
                    return Some(self.clone());
                }
                let mut ids = Vec::with_capacity(a.len() + b.len());
                let mut left = a.iter().copied().peekable();
                let mut right = b.iter().copied().peekable();
                while let (Some(&x), Some(&y)) = (left.peek(), right.peek()) {
                    match x.cmp(&y) {
                        std::cmp::Ordering::Less => ids.extend(left.next()),
                        std::cmp::Ordering::Greater => ids.extend(right.next()),
                        std::cmp::Ordering::Equal => {
                            ids.push(x);
                            left.next();
                            right.next();
                        }
                    }
                }
                ids.extend(left);
                ids.extend(right);
                Some(Self::Objects(ids.into()))
            }
            _ => None,
        }
    }

    pub(super) const fn is_nullish(&self) -> bool {
        matches!(self, Self::Primitive(Value::Null | Value::Undefined))
    }

    pub(super) fn truthy(&self) -> bool {
        match self {
            Self::Primitive(value) => value.truthy(),
            Self::Objects(_) => true,
        }
    }

    pub(super) fn strict_equal(
        &self,
        other: &Self,
        budget: &WorkBudget,
    ) -> Result<Option<bool>, BudgetExceeded> {
        self.charge_merge(other, budget)?;
        Ok(match (self, other) {
            (Self::Primitive(a), Self::Primitive(b)) => Some(strict_primitive_equal(a, b)),
            (Self::Objects(a), Self::Objects(b)) => {
                if a.len() == 1 && b.len() == 1 {
                    return Ok(Some(a == b));
                }
                if Rc::ptr_eq(a, b) {
                    return Ok(None);
                }
                let mut left = a.iter().peekable();
                let mut right = b.iter().peekable();
                while let (Some(x), Some(y)) = (left.peek(), right.peek()) {
                    match x.cmp(y) {
                        std::cmp::Ordering::Less => {
                            left.next();
                        }
                        std::cmp::Ordering::Greater => {
                            right.next();
                        }
                        std::cmp::Ordering::Equal => return Ok(None),
                    }
                }
                Some(false)
            }
            _ => Some(false),
        })
    }

    pub(super) const fn primitive(&self) -> Option<&Value> {
        match self {
            Self::Primitive(value) => Some(value),
            Self::Objects(_) => None,
        }
    }
}

pub(super) const fn value_weight(value: &Value) -> usize {
    match value {
        Value::String(value) => value.len().saturating_add(1),
        _ => 1,
    }
}

/// Strings are indexed by UTF-16 code units, not Unicode scalar values.
/// A surrogate is still an own data property, even though its value is
/// outside the current UTF-8 proof domain.
fn string_code_unit(unit: u16) -> Option<Fact> {
    char::from_u32(u32::from(unit))
        .map(|character| Fact::Primitive(Value::String(character.to_string())))
}

/// Prove only the mandatory own properties of a primitive string wrapper.
/// All other lookups can reach a modified String.prototype.
fn read_string_own(text: &str, key: &str, budget: &WorkBudget) -> Result<Lookup, BudgetExceeded> {
    charge(budget, key.len())?;
    if key == "length" {
        charge(budget, text.len())?;
        let length = text.encode_utf16().count();
        // ECMAScript string lengths are bounded by the largest safe integer.
        let Ok(length) = u64::try_from(length) else {
            return Ok(Err(UnprovenLookup));
        };
        if length >= (1_u64 << 53) {
            return Ok(Err(UnprovenLookup));
        }
        let number = js_number_from_u64(length);
        return Ok(Ok(Some(Fact::Primitive(Value::Number(number)))));
    }
    let Ok(index) = key.parse::<usize>() else {
        return Ok(Err(UnprovenLookup));
    };
    // Unlike array indexes, string exotic indexes have no uint32 bound.
    // A canonical nonnegative decimal below the actual length suffices.
    if index.to_string() != key || index >= text.len() {
        return Ok(Err(UnprovenLookup));
    }
    charge(
        budget,
        text.len().min(index.saturating_add(1).saturating_mul(3)),
    )?;
    Ok(text
        .encode_utf16()
        .nth(index)
        .map(string_code_unit)
        .ok_or(UnprovenLookup))
}

/// The value lattice is separate from the descriptor lattice. Unknown data
/// values do not imply arbitrary getters or setters. `MaybeData` means either
/// an absent own property or a writable own data property on every path.
fn join_value(left: Option<&Fact>, right: Option<&Fact>) -> Option<Fact> {
    left?.join_proven(right?)
}

/// All modeled data properties are writable. Enumerability is independent
/// of presence and value, and a mapped argument descriptor stores a cell
/// reference rather than a snapshot. Non-configurable opaque accessors
/// (the unmapped arguments callee poison) are represented separately.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Enumerable {
    Yes,
    No,
    Maybe,
}

impl Enumerable {
    fn join(self, other: Self) -> Self {
        if self == other {
            self
        } else {
            Self::Maybe
        }
    }
}

#[derive(Clone)]
enum DataStorage {
    Value(Option<Fact>),
    Cell(CellId),
}

#[derive(Clone)]
struct DataDescriptor {
    storage: DataStorage,
    enumerable: Enumerable,
}

impl DataDescriptor {
    const fn plain(value: Option<Fact>, enumerable: Enumerable) -> Self {
        Self {
            storage: DataStorage::Value(value),
            enumerable,
        }
    }

    const fn mapped(cell: CellId) -> Self {
        Self {
            storage: DataStorage::Cell(cell),
            enumerable: Enumerable::Yes,
        }
    }

    const fn fact(&self) -> Option<&Fact> {
        match &self.storage {
            DataStorage::Value(value) => value.as_ref(),
            DataStorage::Cell(_) => None,
        }
    }

    const fn cell(&self) -> Option<CellId> {
        match self.storage {
            DataStorage::Cell(cell) => Some(cell),
            DataStorage::Value(_) => None,
        }
    }

    fn value<'a>(&'a self, cells: &'a CellStore) -> Option<&'a Fact> {
        match &self.storage {
            DataStorage::Value(value) => value.as_ref(),
            DataStorage::Cell(cell) => cells.get(*cell),
        }
    }

    fn join(&self, other: &Self) -> Option<Self> {
        let storage = match (&self.storage, &other.storage) {
            (DataStorage::Value(left), DataStorage::Value(right)) => {
                DataStorage::Value(join_value(left.as_ref(), right.as_ref()))
            }
            (DataStorage::Cell(left), DataStorage::Cell(right)) if left == right => {
                DataStorage::Cell(*left)
            }
            _ => return None,
        };
        Some(Self {
            storage,
            enumerable: self.enumerable.join(other.enumerable),
        })
    }

    fn into_enumerable(
        self,
        maybe_absent: bool,
        cells: &CellStore,
        budget: &WorkBudget,
    ) -> Result<Property, BudgetExceeded> {
        if self.enumerable == Enumerable::No {
            return Ok(Property::Absent);
        }
        let maybe = maybe_absent || self.enumerable == Enumerable::Maybe;
        let value = match self.storage {
            DataStorage::Value(value) => value,
            DataStorage::Cell(cell) => cells.get(cell).map(|fact| fact.copy(budget)).transpose()?,
        };
        let descriptor = Self::plain(value, Enumerable::Yes);
        Ok(if maybe {
            Property::MaybeData(descriptor)
        } else {
            Property::Data(descriptor)
        })
    }
}

#[derive(Clone)]
enum Property {
    Absent,
    Data(DataDescriptor),
    MaybeData(DataDescriptor),
    Opaque,
    Restricted,
}

impl Property {
    const fn data(value: Option<Fact>) -> Self {
        Self::Data(DataDescriptor::plain(value, Enumerable::Yes))
    }

    const fn maybe_data(value: Option<Fact>) -> Self {
        Self::MaybeData(DataDescriptor::plain(value, Enumerable::Yes))
    }

    const fn fact(&self) -> Option<&Fact> {
        match self {
            Self::Data(value) | Self::MaybeData(value) => value.fact(),
            Self::Absent | Self::Opaque | Self::Restricted => None,
        }
    }

    const fn mapped_cell(&self) -> Option<CellId> {
        match self {
            Self::Data(value) => value.cell(),
            _ => None,
        }
    }

    const fn clone_weight(&self) -> usize {
        match self.fact() {
            Some(fact) => fact.clone_weight(),
            None => 1,
        }
    }

    fn charge_pair(&self, other: &Self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        match (self.fact(), other.fact()) {
            (Some(left), Some(right)) => left.charge_merge(right, budget),
            _ => charge(
                budget,
                self.clone_weight().saturating_add(other.clone_weight()),
            ),
        }
    }

    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Absent, Self::Absent) => Self::Absent,
            (Self::Restricted, Self::Restricted) => Self::Restricted,
            (Self::Data(left), Self::Data(right)) => {
                left.join(right).map_or(Self::Opaque, Self::Data)
            }
            (Self::Absent, Self::Data(value) | Self::MaybeData(value))
            | (Self::Data(value) | Self::MaybeData(value), Self::Absent)
                if value.cell().is_none() =>
            {
                Self::MaybeData(value.clone())
            }
            (Self::Data(left) | Self::MaybeData(left), Self::MaybeData(right))
            | (Self::MaybeData(left), Self::Data(right)) => {
                left.join(right).map_or(Self::Opaque, Self::MaybeData)
            }
            _ => Self::Opaque,
        }
    }

    fn assigned(&self, value: Option<Fact>) -> Self {
        let enumerable = match self {
            Self::Data(descriptor) => descriptor.enumerable,
            Self::MaybeData(descriptor) => descriptor.enumerable.join(Enumerable::Yes),
            _ => Enumerable::Yes,
        };
        Self::Data(DataDescriptor::plain(value, enumerable))
    }

    fn into_enumerable(
        self,
        cells: &CellStore,
        budget: &WorkBudget,
    ) -> Result<Self, BudgetExceeded> {
        match self {
            Self::Data(descriptor) => descriptor.into_enumerable(false, cells, budget),
            Self::MaybeData(descriptor) => descriptor.into_enumerable(true, cells, budget),
            Self::Absent | Self::Restricted => Ok(Self::Absent),
            Self::Opaque => Ok(Self::Opaque),
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
            Self::Opaque | Self::Restricted => Self::Opaque,
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

    fn replace(
        &mut self,
        key: &str,
        next: Property,
        strength: Strength,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        charge(budget, key.len().saturating_add(next.clone_weight()))?;
        let replacement = strength.replace(self.get(key), next, budget)?;
        self.insert(key.to_owned(), replacement);
        Ok(())
    }

    fn charge_clone(&self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        charge(budget, self.listed.capacity())?;
        for (key, property) in &self.listed {
            charge(budget, key.len().saturating_add(property.clone_weight()))?;
        }
        charge(budget, self.unlisted.clone_weight())
    }

    fn data_only(&self) -> bool {
        !matches!(self.unlisted, Property::Opaque)
            && self
                .listed
                .values()
                .all(|property| !matches!(property, Property::Opaque))
    }

    fn define_unknown(
        &mut self,
        definition: &Property,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        charge(budget, self.listed.capacity())?;
        for property in self.listed.values_mut() {
            property.charge_pair(definition, budget)?;
            *property = property.join(definition);
        }
        self.unlisted.charge_pair(definition, budget)?;
        self.unlisted = self.unlisted.join(definition);
        Ok(())
    }

    fn combine(
        &mut self,
        other: &Self,
        budget: &WorkBudget,
        operation: impl Fn(&Property, &Property) -> Property,
    ) -> Result<(), BudgetExceeded> {
        charge(
            budget,
            self.listed
                .capacity()
                .saturating_add(other.listed.capacity()),
        )?;
        for (key, property) in &mut self.listed {
            charge(budget, key.len())?;
            let right = other.get(key);
            property.charge_pair(right, budget)?;
            *property = operation(property, right);
        }
        for (key, property) in &other.listed {
            charge(budget, key.len())?;
            if !self.listed.contains_key(key) {
                self.unlisted.charge_pair(property, budget)?;
                self.listed
                    .insert(key.clone(), operation(&self.unlisted, property));
            }
        }
        self.unlisted.charge_pair(&other.unlisted, budget)?;
        self.unlisted = operation(&self.unlisted, &other.unlisted);
        Ok(())
    }

    fn join(&mut self, other: &Self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        self.combine(other, budget, Property::join)
    }

    fn copy_from(&mut self, other: &Self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        self.combine(other, budget, |previous, source| {
            source.copied_over(previous)
        })
    }
}

/// A possible receiver retains both the old and new descriptor states.
#[derive(Clone, Copy)]
enum Strength {
    Strong,
    Weak,
}

impl Strength {
    fn replace(
        self,
        previous: &Property,
        next: Property,
        budget: &WorkBudget,
    ) -> Result<Property, BudgetExceeded> {
        match self {
            Self::Strong => Ok(next),
            Self::Weak => {
                previous.charge_pair(&next, budget)?;
                Ok(previous.join(&next))
            }
        }
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
    Callable,
}

#[derive(Clone)]
pub(super) struct OwnData {
    kind: AllocationKind,
    prototype: Prototype,
    properties: Properties,
    closure: Option<ClosureOrigin>,
}

impl OwnData {
    pub(super) fn new(kind: AllocationKind) -> Self {
        Self {
            kind,
            prototype: Prototype::Unknown,
            properties: Properties::default(),
            closure: None,
        }
    }

    pub(super) fn callable(origin: Option<ClosureOrigin>) -> Self {
        let mut data = Self::new(AllocationKind::Callable);
        // Function-specific own descriptors (name, length, prototype,
        // arguments and caller) are not ordinary writable literal slots.
        data.properties.unlisted = Property::Opaque;
        data.closure = origin;
        data
    }

    pub(super) fn define_data(&mut self, key: String, value: Option<Fact>) {
        self.properties.insert(key, Property::data(value));
    }

    pub(super) fn define_hidden_data(&mut self, key: String, value: Option<Fact>) {
        self.properties.insert(
            key,
            Property::Data(DataDescriptor::plain(value, Enumerable::No)),
        );
    }

    pub(super) fn define_mapped(&mut self, key: String, cell: CellId) {
        self.properties
            .insert(key, Property::Data(DataDescriptor::mapped(cell)));
    }

    pub(super) fn define_restricted(&mut self, key: String) {
        self.properties.insert(key, Property::Restricted);
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

    fn delete_own(
        &mut self,
        key: &str,
        strength: Strength,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        self.properties
            .replace(key, Property::Absent, strength, budget)
    }

    /// An unknown computed definition can overwrite any one own key,
    /// and an unknown spread can overwrite any subset. Both join with the
    /// previous descriptor instead of conflating unknown values with accessors.
    pub(super) fn define_unknown_key(
        &mut self,
        is_data: bool,
        value: Option<Fact>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        let definition = if is_data {
            Property::data(value)
        } else {
            Property::Opaque
        };
        self.properties.define_unknown(&definition, budget)
    }

    /// Array spread cannot overwrite any of the already created prefix
    /// elements. Unknown later indices are data or absent, never accessors.
    pub(super) fn unknown_array_tail(&mut self) {
        self.properties.unlisted = Property::maybe_data(None);
    }

    fn property(&self, key: &str) -> &Property {
        self.properties.get(key)
    }

    fn join(&mut self, other: &Self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        // A single allocation's prototype cannot change on any modeled
        // path. Unknown prototype mutation invalidates the allocation.
        self.properties.join(&other.properties, budget)
    }

    fn enumerable_data(
        &self,
        cells: &CellStore,
        excluded: &HashSet<String>,
        budget: &WorkBudget,
    ) -> Result<Option<Properties>, BudgetExceeded> {
        self.properties.charge_clone(budget)?;
        let mut properties = self.properties.clone();
        if self.kind == AllocationKind::Callable {
            return Ok(None);
        }
        if self.kind == AllocationKind::Array {
            // All tracked ordinary literal properties are enumerable,
            // except the intrinsic own Array length descriptor.
            properties.insert("length".to_owned(), Property::Absent);
        }
        for key in excluded {
            charge(budget, key.len())?;
            properties.insert(key.clone(), Property::Absent);
        }
        for property in properties
            .listed
            .values_mut()
            .chain(std::iter::once(&mut properties.unlisted))
        {
            *property =
                std::mem::replace(property, Property::Absent).into_enumerable(cells, budget)?;
        }
        Ok(properties.data_only().then_some(properties))
    }

    /// `CopyDataProperties` ignores inherited data, uses own enumerability,
    /// and defines rather than sets the destination's property. We can
    /// model it only if all possible source descriptors are data/absent.
    pub(super) fn spread(
        &mut self,
        environment: &Environment,
        source: &Fact,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        self.spread_excluding(environment, source, &HashSet::new(), budget)
    }

    pub(super) fn spread_excluding(
        &mut self,
        environment: &Environment,
        source: &Fact,
        excluded: &HashSet<String>,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        let Some(properties) = environment.enumerable_data(source, excluded, budget)? else {
            return Ok(false);
        };
        self.properties.copy_from(&properties, budget)?;
        Ok(true)
    }

    fn is_length(&self, key: &str) -> bool {
        self.kind == AllocationKind::Array && key == "length"
    }

    fn length_value(value: Option<&Fact>) -> Option<u32> {
        exact_u32(value?.primitive()?.number())
    }

    fn exact_length(&self) -> Option<u32> {
        let Property::Data(value) = self.property("length") else {
            return None;
        };
        Self::length_value(value.fact())
    }

    fn can_write(&self, key: &str, value: Option<&Fact>) -> bool {
        !self.is_length(key) || Self::length_value(value).is_some()
    }

    fn write(
        &mut self,
        key: &str,
        value: Option<Fact>,
        strength: Strength,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if self.property(key).mapped_cell().is_some() {
            // The environment applies the cell write exactly once. Its
            // mapped descriptor and attributes remain unchanged.
            return Ok(());
        }
        if self.is_length(key) {
            let Some(length) = Self::length_value(value.as_ref()) else {
                return Ok(());
            };
            // Truncation changes only the removed indices and length.
            charge(budget, self.properties.listed.capacity())?;
            for (key, property) in &mut self.properties.listed {
                charge(budget, key.len())?;
                if canonical_array_index_key(key).is_some_and(|index| index >= length) {
                    *property = strength.replace(property, Property::Absent, budget)?;
                }
            }
            self.properties.replace(
                key,
                Property::data(Some(Fact::Primitive(Value::Number(f64::from(length))))),
                strength,
                budget,
            )
        } else {
            if self.kind == AllocationKind::Array {
                if let Some(index) = canonical_array_index_key(key) {
                    let length = self.exact_length().map(|length| {
                        Fact::Primitive(Value::Number(f64::from(length.max(index + 1))))
                    });
                    self.properties
                        .replace("length", Property::data(length), strength, budget)?;
                }
            }
            let replacement = self.property(key).assigned(value);
            self.properties.replace(key, replacement, strength, budget)
        }
    }
}

/// Symbol keys are not individually tracked yet. Their descriptors are
/// covered by the existing unlisted-property lattice, including unknown
/// computed definitions and spreads. Query it without conflating a symbol
/// with its description or with a string key.
#[derive(Clone, Copy)]
enum LookupKey<'a> {
    String(&'a str),
    UntrackedSymbol,
}

impl LookupKey<'_> {
    fn property(self, data: &OwnData) -> &Property {
        match self {
            Self::String(key) => data.property(key),
            Self::UntrackedSymbol => &data.properties.unlisted,
        }
    }

    const fn weight(self) -> usize {
        match self {
            Self::String(key) => key.len(),
            Self::UntrackedSymbol => 1,
        }
    }
}

/// An ordinary lookup may be unproved or proved with an unknown data value.
#[derive(Clone, Copy, Debug)]
pub(super) struct UnprovenLookup;

pub(super) type Lookup = Result<Option<Fact>, UnprovenLookup>;

/// Merge an arbitrary number of possible property values without
/// repeatedly allocating growing sorted location unions. Preserve the
/// original shared fact until a genuinely different location set arrives.
#[derive(Default)]
enum LookupValues {
    #[default]
    Unseen,
    Unknown,
    Single(Fact),
    Union(HashSet<AllocationId>),
}

impl LookupValues {
    fn add(&mut self, value: Option<&Fact>, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        if matches!(self, Self::Unknown) {
            return Ok(());
        }
        let Some(value) = value else {
            *self = Self::Unknown;
            return Ok(());
        };
        match self {
            Self::Unseen => {
                *self = Self::Single(value.copy(budget)?);
            }
            Self::Single(previous) => {
                if let (Fact::Objects(left), Fact::Objects(right)) = (&*previous, value) {
                    if Rc::ptr_eq(left, right) {
                        return Ok(());
                    }
                    charge(budget, left.len().saturating_add(right.len()))?;
                    if left != right {
                        let mut union = HashSet::new();
                        union.extend(left.iter().copied());
                        union.extend(right.iter().copied());
                        *self = Self::Union(union);
                    }
                } else if let (Fact::Primitive(left), Fact::Primitive(right)) = (&*previous, value)
                {
                    charge(
                        budget,
                        value_weight(left).saturating_add(value_weight(right)),
                    )?;
                    if !identical_primitive_value(left, right) {
                        *self = Self::Unknown;
                    }
                } else {
                    *self = Self::Unknown;
                }
            }
            Self::Union(union) => {
                if let Fact::Objects(locations) = value {
                    charge(budget, locations.len())?;
                    union.extend(locations.iter().copied());
                } else {
                    *self = Self::Unknown;
                }
            }
            Self::Unknown => {}
        }
        Ok(())
    }

    fn finish(self, budget: &WorkBudget) -> Result<Option<Fact>, BudgetExceeded> {
        match self {
            Self::Unseen | Self::Unknown => Ok(None),
            Self::Single(value) => Ok(Some(value)),
            Self::Union(union) => {
                charge(
                    budget,
                    union.capacity().saturating_add(
                        union.len().saturating_mul(
                            usize::try_from(union.len().max(1).ilog2())
                                .unwrap_or(usize::MAX)
                                .saturating_add(1),
                        ),
                    ),
                )?;
                let mut locations = union.into_iter().collect::<Vec<_>>();
                locations.sort_unstable();
                Ok(Some(Fact::Objects(locations.into())))
            }
        }
    }
}

/// Bound dead allocation retention without tracing the entire live heap
/// after every statement. Collection is amortized against heap growth;
/// the first threshold avoids overhead on ordinary short functions.
pub(super) const MIN_COLLECTION_SIZE: usize = 64;

#[derive(Clone)]
pub(super) struct Environment {
    reachable: bool,
    bindings: CellStore,
    allocations: Rc<HashMap<AllocationId, Rc<OwnData>>>,
    collection_threshold: usize,
    collection_floor: AllocationId,
    collection_suspended: bool,
    origins: Option<IdentityOrigins>,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            reachable: true,
            bindings: CellStore::default(),
            allocations: Rc::default(),
            collection_threshold: MIN_COLLECTION_SIZE,
            collection_floor: 0,
            collection_suspended: false,
            origins: None,
        }
    }
}

/// One trace owns its frontier and marks. Charge all traversed edges,
/// including location unions, rather than merely charging visited nodes.
struct Reachability<'b> {
    marked: HashSet<AllocationId>,
    pending: Vec<AllocationId>,
    marked_instances: HashSet<InstanceId>,
    pending_instances: Vec<InstanceId>,
    weight: usize,
    budget: &'b WorkBudget,
}

struct ExitProjection<'a, 'b> {
    entry: AllocationId,
    left: &'a Reachability<'b>,
    right: &'a Reachability<'b>,
}

impl<'b> Reachability<'b> {
    fn new(budget: &'b WorkBudget) -> Self {
        Self {
            marked: HashSet::new(),
            pending: Vec::new(),
            marked_instances: HashSet::new(),
            pending_instances: Vec::new(),
            weight: 0,
            budget,
        }
    }

    fn charge(&mut self, weight: usize) -> Result<(), BudgetExceeded> {
        self.budget
            .consume(u64::try_from(weight).unwrap_or(u64::MAX))?;
        self.weight = self.weight.saturating_add(weight);
        Ok(())
    }

    fn mark(&mut self, id: AllocationId) {
        if self.marked.insert(id) {
            self.pending.push(id);
        }
    }

    fn mark_instance(&mut self, id: InstanceId) {
        if self.marked_instances.insert(id) {
            self.pending_instances.push(id);
        }
    }

    fn locations(&mut self, locations: &Locations) -> Result<(), BudgetExceeded> {
        self.charge(locations.len())?;
        for &id in locations.iter() {
            self.mark(id);
        }
        Ok(())
    }

    fn fact(&mut self, fact: &Fact) -> Result<(), BudgetExceeded> {
        if let Fact::Objects(locations) = fact {
            self.locations(locations)?;
        }
        Ok(())
    }

    fn property(&mut self, property: &Property) -> Result<(), BudgetExceeded> {
        if let Some(fact) = property.fact() {
            self.fact(fact)?;
        }
        if let Some(cell) = property.mapped_cell() {
            self.charge(1)?;
            self.mark_instance(cell.instance());
        }
        Ok(())
    }

    fn object(&mut self, data: &OwnData) -> Result<(), BudgetExceeded> {
        self.charge(data.properties.listed.capacity().saturating_add(1))?;
        if let Some(closure) = &data.closure {
            for instance in closure.instances() {
                self.charge(1)?;
                self.mark_instance(instance);
            }
        }
        if let Prototype::Objects(locations) = &data.prototype {
            self.locations(locations)?;
        }
        for property in data.properties.listed.values() {
            self.property(property)?;
        }
        self.property(&data.properties.unlisted)
    }
}

// Avoid cloning an entire shared map merely to discard its contents.
pub(super) fn clear_shared<K, V>(map: &mut Rc<HashMap<K, V>>)
where
    K: std::hash::Hash + Eq,
{
    if let Some(unique) = Rc::get_mut(map) {
        unique.clear();
        unique.shrink_to(MIN_COLLECTION_SIZE);
    } else {
        *map = Rc::default();
    }
}

impl Environment {
    pub(super) fn new() -> Self {
        Self::default()
    }

    /// This heap is the state of the ordinary continuation. An expression
    /// whose every modeled outcome throws has no such continuation; its
    /// exceptional snapshots are owned by the surrounding completion flow.
    pub(super) const fn reachable(&self) -> bool {
        self.reachable
    }

    pub(super) const fn terminate(&mut self) {
        self.reachable = false;
    }

    /// Recognize a repeated abstract state cheaply. This is only a
    /// speculation stop condition, never a proof that the concrete loop
    /// diverges. Ignore allocation-birth history and collector bookkeeping.
    /// Descriptor sharing is sufficient for equality; changed descriptors
    /// deliberately prevent this fast path.
    pub(super) fn same_reaching_state(
        &self,
        other: &Self,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        if !Rc::ptr_eq(&self.allocations, &other.allocations) {
            if self.allocations.len() != other.allocations.len() {
                return Ok(false);
            }
            charge(budget, self.allocations.capacity())?;
            if self.allocations.iter().any(|(id, data)| {
                !other
                    .allocations
                    .get(id)
                    .is_some_and(|other| Rc::ptr_eq(data, other))
            }) {
                return Ok(false);
            }
        }
        self.bindings.same_state(&other.bindings, budget)
    }

    pub(super) fn clear(&mut self) {
        self.bindings.clear();
        clear_shared(&mut self.allocations);
        self.collection_threshold = MIN_COLLECTION_SIZE;
    }

    /// An opaque exception can occur anywhere in the protected evaluation.
    /// All identities allocated so far may exist on that path, but no
    /// descriptor or binding fact can be carried across it.
    pub(super) fn unknown_exception(&self, next_identity: usize) -> Self {
        let mut environment = self.clone();
        environment.reachable = true;
        environment.clear();
        environment.origins = Some(IdentityOrigins::new(next_identity));
        environment
    }

    /// An exact ordinary function object's internal call target cannot be
    /// replaced by an own-property write. Unknown effects still erase
    /// its descriptor proof along with other heap information.
    pub(super) fn callable_origin(&self, id: AllocationId) -> Option<ClosureOrigin> {
        self.allocations.get(&id)?.closure.clone()
    }

    pub(super) fn allocation_kind(&self, id: AllocationId) -> Option<AllocationKind> {
        Some(self.allocations.get(&id)?.kind)
    }

    pub(super) fn reference_type(
        &self,
        locations: &Locations,
        budget: &WorkBudget,
    ) -> Result<Option<&'static str>, BudgetExceeded> {
        charge(budget, locations.len())?;
        let mut callable = None;
        for id in locations.iter() {
            let Some(data) = self.allocations.get(id) else {
                return Ok(None);
            };
            let kind = data.kind == AllocationKind::Callable;
            if callable.is_some_and(|previous| previous != kind) {
                return Ok(None);
            }
            callable = Some(kind);
        }
        Ok(callable.map(|kind| if kind { "function" } else { "object" }))
    }

    pub(super) fn get(&self, cell: CellId) -> Option<&Fact> {
        self.bindings.get(cell)
    }

    pub(super) fn read_binding(
        &self,
        cell: CellId,
        budget: &WorkBudget,
    ) -> Result<Option<Fact>, BudgetExceeded> {
        self.get(cell).map(|fact| fact.copy(budget)).transpose()
    }

    fn charge_allocation_copy(&self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        if Rc::strong_count(&self.allocations) > 1 {
            charge(budget, self.allocations.capacity())?;
        }
        Ok(())
    }

    pub(super) fn insert(
        &mut self,
        cell: CellId,
        fact: Fact,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        self.bindings.insert(cell, fact, budget)
    }

    pub(super) fn remove(
        &mut self,
        cell: CellId,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        self.bindings.remove(cell, budget)
    }

    pub(super) fn record_birth(
        &mut self,
        id: usize,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if let Some(origins) = &mut self.origins {
            origins.record(id, budget)?;
        }
        Ok(())
    }

    pub(super) fn copy_instance(
        &mut self,
        from: InstanceId,
        to: InstanceId,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        self.record_birth(to, budget)?;
        self.bindings.copy_instance(from, to, budget)
    }

    pub(super) fn allocate(
        &mut self,
        id: AllocationId,
        data: OwnData,
        budget: &WorkBudget,
    ) -> Result<Fact, BudgetExceeded> {
        self.charge_allocation_copy(budget)?;
        self.record_birth(id, budget)?;
        Rc::make_mut(&mut self.allocations).insert(id, Rc::new(data));
        Ok(Fact::Objects(Rc::from([id])))
    }

    /// The caller can have pending receiver/argument/return temporaries
    /// which are not represented by a lexical binding in the callee.
    pub(super) fn track_paths(&mut self, next_identity: usize) {
        self.origins
            .get_or_insert_with(|| IdentityOrigins::new(next_identity));
    }

    pub(super) fn enter_activation(&mut self, next_identity: usize) {
        self.collection_suspended = true;
        // An enclosing activation needs the entire nested creation
        // history, including allocations invalidated before a return.
        self.track_paths(next_identity);
    }

    pub(super) fn leave_activation(&mut self, caller: &Self) {
        self.collection_suspended = caller.collection_suspended;
        self.collection_floor = caller.collection_floor;
        if caller.origins.is_none() {
            self.origins = None;
        }
    }

    /// Preserve allocations that existed before an outstanding branch
    /// fork. The join interprets an absent pre-fork entry as invalidation,
    /// so ordinary unreachability must not erase that distinction.
    pub(super) const fn protect_before(&mut self, first_new: AllocationId) -> AllocationId {
        std::mem::replace(&mut self.collection_floor, first_new)
    }

    /// This may run only at statement boundaries, when no caller-held
    /// expression temporaries, pending assignment receivers or in-progress
    /// object literals need to be kept alive. Lexical bindings and their
    /// transitive (own-property and prototype) edges are the roots.
    pub(super) fn collect_if_needed(
        &mut self,
        roots: impl Iterator<Item = InstanceId>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if self.collection_suspended
            || self.allocations.len().saturating_add(self.bindings.len())
                < self.collection_threshold
        {
            return Ok(());
        }
        self.collect(roots, budget)
    }

    pub(super) fn collect_after_scope_exit(
        &mut self,
        retired: InstanceId,
        roots: impl Iterator<Item = InstanceId>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        if self.collection_suspended {
            return Ok(());
        }
        let retired_cells = self.bindings.instance(retired).map_or(0, HashMap::len);
        if retired_cells >= MIN_COLLECTION_SIZE
            && retired_cells >= self.allocations.len().div_ceil(2)
        {
            self.collect(roots, budget)?;
        }
        Ok(())
    }

    fn collect(
        &mut self,
        roots: impl Iterator<Item = InstanceId>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        let trace = self.trace_reachable(roots, self.collection_floor, None, budget)?;
        self.retain_reachable(&trace, budget)
    }

    fn trace_reachable<'b>(
        &self,
        roots: impl Iterator<Item = InstanceId>,
        floor: AllocationId,
        value: Option<&Fact>,
        budget: &'b WorkBudget,
    ) -> Result<Reachability<'b>, BudgetExceeded> {
        let mut trace = Reachability::new(budget);
        if let Some(value) = value {
            trace.fact(value)?;
        }
        for instance in roots {
            trace.charge(1)?;
            trace.mark_instance(instance);
        }
        if floor != 0 {
            trace.charge(
                self.allocations
                    .capacity()
                    .saturating_add(self.bindings.capacity()),
            )?;
            for &id in self.allocations.keys() {
                if id < floor {
                    trace.mark(id);
                }
            }
            for id in self.bindings.ids() {
                if id < floor {
                    trace.mark_instance(id);
                }
            }
        }
        loop {
            if let Some(instance) = trace.pending_instances.pop() {
                if let Some(cells) = self.bindings.instance(instance) {
                    trace.charge(cells.capacity())?;
                    for fact in cells.values() {
                        trace.fact(fact)?;
                    }
                }
            } else if let Some(id) = trace.pending.pop() {
                if let Some(data) = self.allocations.get(&id) {
                    trace.object(data)?;
                }
            } else {
                break;
            }
        }
        Ok(trace)
    }

    fn retain_reachable(
        &mut self,
        trace: &Reachability<'_>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        self.bindings.retain(&trace.marked_instances, budget)?;
        charge(budget, self.allocations.capacity())?;
        if self.allocations.keys().any(|id| !trace.marked.contains(id)) {
            self.charge_allocation_copy(budget)?;
            Rc::make_mut(&mut self.allocations).retain(|id, _| trace.marked.contains(id));
        }
        if self.allocations.capacity()
            > self
                .allocations
                .len()
                .saturating_mul(4)
                .max(MIN_COLLECTION_SIZE)
        {
            self.charge_allocation_copy(budget)?;
            Rc::make_mut(&mut self.allocations).shrink_to_fit();
        }
        let live = self.allocations.len().saturating_add(self.bindings.len());
        self.collection_threshold = live
            .saturating_add(trace.weight.max(live))
            .max(MIN_COLLECTION_SIZE);
        Ok(())
    }

    /// Join normal reaching paths. Allocations created after the fork exist
    /// only in the branch that created them. Older allocations must still
    /// be valid in both branches: a missing entry means effects invalidated
    /// that proof, not that the allocation never existed.
    pub(super) fn join(
        &mut self,
        other: &Self,
        first_new: AllocationId,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        match (self.reachable, other.reachable) {
            (true, true) => self.join_paths(other, Some(first_new), None, budget),
            (false, true) => {
                *self = other.clone();
                Ok(())
            }
            (_, false) => Ok(()),
        }
    }

    /// Return paths may diverge at different points in a function or loop.
    /// Absence must be established by per-path creation history, not by
    /// assuming every object created after the call began is branch-local.
    pub(super) fn join_returns(
        &mut self,
        other: &Self,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        self.join_paths(other, None, None, budget)
    }

    /// Project each completed invocation onto every caller-held identity
    /// and the returned value before joining. A local identity inaccessible
    /// through all tracked roots on one path cannot contribute contents to
    /// a read through a known reference on that path. Unknown edges remain
    /// unknown (and effects through them still invalidate the heap).
    ///
    /// Keep all pre-call identities, including caller temporaries, and mark
    /// referenced identities even when their descriptors were invalidated.
    /// This distinguishes an inaccessible local allocation from a live
    /// reference whose contents are unknown. Do not change birth history.
    pub(super) fn join_activation_exits(
        &mut self,
        other: &Self,
        left_value: Option<&Fact>,
        right_value: Option<&Fact>,
        entry: AllocationId,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        let left = self.trace_reachable(std::iter::empty(), entry, left_value, budget)?;
        let right = other.trace_reachable(std::iter::empty(), entry, right_value, budget)?;
        self.retain_reachable(&left, budget)?;
        let mut other = other.clone();
        other.retain_reachable(&right, budget)?;
        let projection = ExitProjection {
            entry,
            left: &left,
            right: &right,
        };
        self.join_paths(&other, None, Some(&projection), budget)
    }

    fn join_paths(
        &mut self,
        other: &Self,
        first_new: Option<AllocationId>,
        projection: Option<&ExitProjection<'_, '_>>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        // A failed join is not a usable abstract state: its caller aborts
        // the analysis. Stop merging immediately at the first budget error.
        let left_origins = self.origins.as_ref();
        let right_origins = other.origins.as_ref();
        let absent = |id, origins: Option<&IdentityOrigins>, trace: Option<&Reachability<'_>>| {
            trace.is_some_and(|trace| {
                projection.is_some_and(|projection| id >= projection.entry)
                    && !trace.marked.contains(&id)
                    && !trace.marked_instances.contains(&id)
            }) || first_new.map_or_else(
                || origins.is_some_and(|history| !history.may_exist(id)),
                |floor| id >= floor,
            )
        };
        let absent_left = |id| absent(id, left_origins, projection.map(|p| p.left));
        let absent_right = |id| absent(id, right_origins, projection.map(|p| p.right));
        if first_new.is_none() {
            charge(
                budget,
                self.allocations
                    .len()
                    .saturating_add(self.bindings.len())
                    .saturating_mul(right_origins.map_or(1, IdentityOrigins::search_cost))
                    .saturating_add(
                        other
                            .allocations
                            .len()
                            .saturating_add(other.bindings.len())
                            .saturating_mul(left_origins.map_or(1, IdentityOrigins::search_cost)),
                    ),
            )?;
        }
        self.bindings
            .join(&other.bindings, absent_left, absent_right, budget)?;
        if !Rc::ptr_eq(&self.allocations, &other.allocations) {
            self.charge_allocation_copy(budget)?;
            charge(
                budget,
                self.allocations
                    .capacity()
                    .saturating_add(other.allocations.capacity()),
            )?;
            let allocations = Rc::make_mut(&mut self.allocations);
            let mut failure = Ok(());
            allocations.retain(|id, data| {
                if failure.is_err() {
                    return true;
                }
                let Some(right) = other.allocations.get(id) else {
                    return absent_right(*id);
                };
                if !Rc::ptr_eq(data, right) {
                    failure = (|| {
                        if Rc::strong_count(data) > 1 {
                            data.properties.charge_clone(budget)?;
                        }
                        Rc::make_mut(data).join(right, budget)
                    })();
                }
                true
            });
            failure?;
            for (&id, data) in other.allocations.iter() {
                if absent_left(id) {
                    allocations.entry(id).or_insert_with(|| Rc::clone(data));
                }
            }
        }
        // Ordinary branch joins also combine creation history: losing a
        // birth here would let a later return join resurrect invalid data.
        if let (Some(left), Some(right)) = (&mut self.origins, &other.origins) {
            left.join(right, budget)?;
        } else {
            self.origins = None;
        }
        Ok(())
    }

    fn enumerable_data(
        &self,
        source: &Fact,
        excluded: &HashSet<String>,
        budget: &WorkBudget,
    ) -> Result<Option<Properties>, BudgetExceeded> {
        match source {
            Fact::Objects(locations) => {
                charge(budget, locations.len())?;
                let mut merged: Option<Properties> = None;
                for id in locations.iter() {
                    let Some(data) = self.allocations.get(id) else {
                        return Ok(None);
                    };
                    let Some(properties) =
                        data.enumerable_data(&self.bindings, excluded, budget)?
                    else {
                        return Ok(None);
                    };
                    if let Some(merged) = &mut merged {
                        merged.join(&properties, budget)?;
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
                        let fact = string_code_unit(unit);
                        let key = index.to_string();
                        if !excluded.contains(&key) {
                            properties.insert(key, Property::data(fact));
                        }
                    }
                }
                Ok(Some(properties))
            }
        }
    }

    /// Prove ordinary property resolution on every possible receiver.
    /// The caller chooses whether to materialize data values or merely
    /// establish that no opaque descriptor can intercept the operation.
    fn visit_resolved_data(
        &self,
        locations: &Locations,
        key: LookupKey<'_>,
        budget: &WorkBudget,
        mut visit: impl FnMut(Option<&Fact>) -> Result<(), BudgetExceeded>,
    ) -> Result<bool, BudgetExceeded> {
        if let [id] = locations.as_ref() {
            charge(budget, key.weight())?;
            let Some(data) = self.allocations.get(id) else {
                return Ok(false);
            };
            if let Property::Data(value) = key.property(data) {
                visit(value.value(&self.bindings))?;
                return Ok(true);
            }
        }
        charge(budget, locations.len())?;
        let mut pending = locations.to_vec();
        let mut visited = HashSet::new();
        let undefined = Fact::Primitive(Value::Undefined);
        let mut found = false;
        while let Some(id) = pending.pop() {
            charge(budget, 1)?;
            if !visited.insert(id) {
                continue;
            }
            let Some(data) = self.allocations.get(&id) else {
                return Ok(false);
            };
            charge(budget, key.weight())?;
            match key.property(data) {
                Property::Data(value) => {
                    visit(value.value(&self.bindings))?;
                    found = true;
                    continue;
                }
                Property::MaybeData(value) => {
                    visit(value.value(&self.bindings))?;
                    found = true;
                }
                Property::Absent => {}
                Property::Opaque | Property::Restricted => return Ok(false),
            }
            match &data.prototype {
                Prototype::Unknown => return Ok(false),
                Prototype::Null => {
                    visit(Some(&undefined))?;
                    found = true;
                }
                Prototype::Objects(prototypes) => {
                    charge(budget, prototypes.len())?;
                    if prototypes.is_empty() || prototypes.iter().any(|&prototype| prototype >= id)
                    {
                        return Ok(false);
                    }
                    pending.extend(prototypes.iter().copied());
                }
            }
        }
        Ok(found)
    }

    /// No well-known symbol can resolve to a method if its summarized
    /// descriptor is absent/nullish throughout a proven prototype chain.
    /// Never assume the ambient Symbol binding or an intrinsic prototype.
    pub(super) fn definitely_noniterable(
        &self,
        source: &Fact,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        match source {
            Fact::Primitive(value) => Ok(matches!(value, Value::Null | Value::Undefined)),
            Fact::Objects(locations) => {
                let mut absent = true;
                let resolved = self.visit_resolved_data(
                    locations,
                    LookupKey::UntrackedSymbol,
                    budget,
                    |value| {
                        absent &= matches!(
                            value.and_then(Fact::primitive),
                            Some(Value::Null | Value::Undefined)
                        );
                        Ok(())
                    },
                )?;
                Ok(resolved && absent)
            }
        }
    }

    pub(super) fn read_value(
        &self,
        receiver: &Fact,
        key: &str,
        budget: &WorkBudget,
    ) -> Result<Lookup, BudgetExceeded> {
        match receiver {
            Fact::Objects(locations) => self.read(locations, key, budget),
            Fact::Primitive(Value::String(text)) => read_string_own(text, key, budget),
            Fact::Primitive(_) => Ok(Err(UnprovenLookup)),
        }
    }

    pub(super) fn read(
        &self,
        locations: &Locations,
        key: &str,
        budget: &WorkBudget,
    ) -> Result<Lookup, BudgetExceeded> {
        let mut values = LookupValues::default();
        if self.visit_resolved_data(locations, LookupKey::String(key), budget, |value| {
            values.add(value, budget)
        })? {
            Ok(Ok(values.finish(budget)?))
        } else {
            Ok(Err(UnprovenLookup))
        }
    }

    fn update(
        &mut self,
        locations: &Locations,
        budget: &WorkBudget,
        apply: impl Fn(&mut OwnData, Strength) -> Result<(), BudgetExceeded>,
    ) -> Result<bool, BudgetExceeded> {
        charge(budget, locations.len())?;
        let strength = match locations.as_ref() {
            [] => return Ok(false),
            [_] => Strength::Strong,
            _ => Strength::Weak,
        };
        self.charge_allocation_copy(budget)?;
        let allocations = Rc::make_mut(&mut self.allocations);
        for id in locations.iter() {
            let Some(data) = allocations.get_mut(id) else {
                return Ok(false);
            };
            if Rc::strong_count(data) > 1 {
                data.properties.charge_clone(budget)?;
            }
            apply(Rc::make_mut(data), strength)?;
        }
        Ok(true)
    }

    fn write_mapped_cells(
        &mut self,
        locations: &Locations,
        key: &str,
        value: Option<&Fact>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        let mut cells = HashSet::new();
        let mut plain = false;
        for id in locations.iter() {
            charge(budget, 1)?;
            let cell = self
                .allocations
                .get(id)
                .and_then(|data| data.property(key).mapped_cell());
            if let Some(cell) = cell {
                cells.insert(cell);
            } else {
                plain = true;
            }
        }
        let strong = !plain && cells.len() == 1;
        for cell in cells {
            let next = if strong {
                value.map(|fact| fact.copy(budget)).transpose()?
            } else if let (Some(old), Some(value)) = (self.bindings.get(cell), value) {
                old.join(value, budget)?
            } else {
                None
            };
            if let Some(next) = next {
                self.bindings.insert(cell, next, budget)?;
            } else {
                self.bindings.remove(cell, budget)?;
            }
        }
        Ok(())
    }

    pub(super) fn write(
        &mut self,
        locations: &Locations,
        key: &str,
        value: Option<&Fact>,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        if !self.visit_resolved_data(locations, LookupKey::String(key), budget, |_| Ok(()))? {
            return Ok(false);
        }
        charge(budget, locations.len())?;
        if key == "length" {
            charge(
                budget,
                locations
                    .len()
                    .saturating_mul(value.map_or(1, Fact::clone_weight)),
            )?;
        }
        if !locations.iter().all(|id| {
            self.allocations
                .get(id)
                .is_some_and(|data| data.can_write(key, value))
        }) {
            return Ok(false);
        }
        self.write_mapped_cells(locations, key, value, budget)?;
        self.update(locations, budget, |data, strength| {
            if let Some(value) = value {
                charge(budget, value.clone_weight())?;
            }
            data.write(key, value.cloned(), strength, budget)
        })
    }

    /// Deletion of an ordinary allocation never invokes an inherited
    /// accessor. Array length is non-configurable.
    pub(super) fn delete(
        &mut self,
        locations: &Locations,
        key: &str,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        charge(budget, locations.len())?;
        if !locations.iter().all(|id| {
            self.allocations.get(id).is_some_and(|data| {
                data.kind != AllocationKind::Callable
                    && !data.is_length(key)
                    && !matches!(data.property(key), Property::Restricted)
            })
        }) {
            return Ok(false);
        }
        self.update(locations, budget, |data, strength| {
            data.delete_own(key, strength, budget)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_syntax::symbol::SymbolId;

    const ROOT: InstanceId = 0;
    fn cell(index: usize) -> CellId {
        CellId::symbol(ROOT, SymbolId::new(index))
    }

    fn descriptor_shape(property: &Property) -> (u8, Option<String>) {
        match property {
            Property::Absent => (0, None),
            Property::Data(value) => (
                1,
                value
                    .fact()
                    .and_then(Fact::primitive)
                    .and_then(Value::render),
            ),
            Property::MaybeData(value) => (
                2,
                value
                    .fact()
                    .and_then(Fact::primitive)
                    .and_then(Value::render),
            ),
            Property::Opaque | Property::Restricted => (3, None),
        }
    }

    #[test]
    fn return_joins_keep_disjoint_births_but_never_resurrect_invalidated_data(
    ) -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("return-heap-join");
        let mut data = OwnData::new(AllocationKind::Ordinary);
        data.define_data("x".into(), Some(Fact::Primitive(Value::Number(7.0))));
        let mut heap = Environment::new();
        heap.allocate(0, data.clone(), &budget)?;
        heap.enter_activation(1);
        let mut left = heap.clone();
        let mut right = heap.clone();
        left.allocate(1, data.clone(), &budget)?;
        right.allocate(2, data.clone(), &budget)?;
        left.join_returns(&right, &budget)?;
        assert!(matches!(
            left.read(&Rc::from([0, 1, 2]), "x", &budget)?,
            Ok(Some(Fact::Primitive(Value::Number(7.0))))
        ));

        // Both sides can contain allocation 3; one side loses its data
        // after an effect. A third return from the original state must
        // not revive that descriptor through the first two returns.
        left.allocate(3, data.clone(), &budget)?;
        let third = left.clone();
        let mut invalidated = left.clone();
        invalidated.clear();
        left.join_returns(&invalidated, &budget)?;
        left.join_returns(&third, &budget)?;
        assert!(left.read(&Rc::from([3]), "x", &budget)?.is_err());

        // A nested activation shares the parent birth history and a
        // normal structured branch join must preserve invalidated births.
        let mut nested = heap.clone();
        nested.enter_activation(4);
        nested.allocate(4, data.clone(), &budget)?;
        nested.leave_activation(&heap);
        let original = nested.clone();
        let mut cleared = nested.clone();
        cleared.clear();
        let mut sibling = heap;
        sibling.allocate(5, data, &budget)?;
        cleared.join(&sibling, 4, &budget)?;
        cleared.join_returns(&original, &budget)?;
        assert!(cleared.read(&Rc::from([4]), "x", &budget)?.is_err());
        assert!(matches!(
            cleared.read(&Rc::from([5]), "x", &budget)?,
            Ok(Some(Fact::Primitive(Value::Number(7.0))))
        ));
        Ok(())
    }

    #[test]
    fn activation_exit_projection_distinguishes_unreachable_from_unknown(
    ) -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("activation-exit-projection");
        let mut data = OwnData::new(AllocationKind::Ordinary);
        data.define_data("x".into(), Some(Fact::Primitive(Value::Number(0.0))));
        let mut base = Environment::new();
        base.enter_activation(1);
        let local = base.allocate(1, data.clone(), &budget)?;
        let mut left = base.clone();
        let mut right = base;
        data.define_data("x".into(), Some(Fact::Primitive(Value::Number(7.0))));
        let alternative = left.allocate(2, data, &budget)?;
        assert!(right.write(
            &Rc::from([1]),
            "x",
            Some(&Fact::Primitive(Value::Number(7.0))),
            &budget
        )?);

        let mut projected = left.clone();
        projected.join_activation_exits(&right, Some(&alternative), Some(&local), 1, &budget)?;
        assert!(matches!(
            projected.read(&Rc::from([1, 2]), "x", &budget)?,
            Ok(Some(Fact::Primitive(Value::Number(7.0))))
        ));

        // A caller-held cell keeps the otherwise local object observable.
        left.insert(cell(0), local.clone(), &budget)?;
        right.insert(cell(0), local.clone(), &budget)?;
        let mut escaped = left.clone();
        escaped.join_activation_exits(&right, Some(&alternative), Some(&local), 1, &budget)?;
        assert!(matches!(
            escaped.read(&Rc::from([1]), "x", &budget)?,
            Ok(None)
        ));

        // A known reference may outlive its invalidated descriptor.
        // Projection must mark it even when no data entry remains.
        left.clear();
        left.join_activation_exits(&right, Some(&local), Some(&local), 1, &budget)?;
        assert!(left.read(&Rc::from([1]), "x", &budget)?.is_err());
        Ok(())
    }

    #[test]
    fn instance_joins_preserve_births_and_copy_on_write_isolation() -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("instance-cell-join");
        let first = CellId::symbol(1, SymbolId::new(0));
        let second = CellId::symbol(2, SymbolId::new(0));
        let third = CellId::symbol(3, SymbolId::new(0));
        let mut base = Environment::new();
        base.enter_activation(1);
        base.record_birth(1, &budget)?;
        base.insert(first, Fact::Primitive(Value::Number(7.0)), &budget)?;
        let mut left = base.clone();
        let mut right = base.clone();
        left.copy_instance(1, 2, &budget)?;
        left.insert(second, Fact::Primitive(Value::Number(9.0)), &budget)?;
        right.copy_instance(1, 3, &budget)?;
        assert!(matches!(
            left.read_binding(first, &budget)?,
            Some(Fact::Primitive(Value::Number(7.0)))
        ));
        left.join_returns(&right, &budget)?;
        assert!(matches!(
            left.read_binding(second, &budget)?,
            Some(Fact::Primitive(Value::Number(9.0)))
        ));
        assert!(matches!(
            left.read_binding(third, &budget)?,
            Some(Fact::Primitive(Value::Number(7.0)))
        ));
        let original = left.clone();
        let mut invalidated = left.clone();
        invalidated.clear();
        left.join_returns(&invalidated, &budget)?;
        left.join_returns(&original, &budget)?;
        for cell in [first, second, third] {
            assert!(left.read_binding(cell, &budget)?.is_none());
        }
        Ok(())
    }

    #[test]
    fn binding_reads_charge_primitive_copies_but_not_shared_location_contents(
    ) -> Result<(), BudgetExceeded> {
        let unlimited = WorkBudget::unlimited("binding-setup");
        let mut heap = Environment::new();
        let symbol = cell(0);
        heap.insert(
            symbol,
            Fact::Primitive(Value::String("x".repeat(8192))),
            &unlimited,
        )?;
        let bounded = WorkBudget::new("binding-read", work_budget::BudgetLimits::work(32));
        assert!(heap.read_binding(symbol, &bounded).is_err());
        let locations = Rc::from((0..1024).collect::<Vec<_>>());
        heap.insert(symbol, Fact::Objects(Rc::clone(&locations)), &unlimited)?;
        let bounded = WorkBudget::new("binding-read", work_budget::BudgetLimits::work(32));
        let Some(Fact::Objects(read)) = heap.read_binding(symbol, &bounded)? else {
            unreachable!()
        };
        assert!(Rc::ptr_eq(&read, &locations));
        Ok(())
    }

    #[test]
    fn lookup_accumulates_many_object_values_in_one_set() -> Result<(), BudgetExceeded> {
        let unlimited = WorkBudget::unlimited("lookup-setup");
        let mut heap = Environment::new();
        let mut receivers = Vec::new();
        let count = 1024;
        for index in 0..count {
            let target = heap.allocate(
                index * 2,
                OwnData::new(AllocationKind::Ordinary),
                &unlimited,
            )?;
            let mut receiver = OwnData::new(AllocationKind::Ordinary);
            receiver.define_data("x".into(), Some(target));
            heap.allocate(index * 2 + 1, receiver, &unlimited)?;
            receivers.push(index * 2 + 1);
        }
        let receivers = Rc::from(receivers);
        // A sequential union would traverse more than 500,000 IDs.
        let bounded = WorkBudget::new("lookup-many-values", work_budget::BudgetLimits::work(32768));
        let Ok(Some(Fact::Objects(result))) = heap.read(&receivers, "x", &bounded)? else {
            unreachable!()
        };
        assert_eq!(result.len(), count);
        assert!(result.iter().copied().eq((0..count).map(|index| index * 2)));
        let mut values = LookupValues::default();
        let fact = Fact::Objects(Rc::clone(&result));
        values.add(Some(&fact), &unlimited)?;
        values.add(Some(&fact), &unlimited)?;
        let Some(Fact::Objects(shared)) = values.finish(&unlimited)? else {
            unreachable!()
        };
        assert!(Rc::ptr_eq(&shared, &result));
        Ok(())
    }

    #[test]
    fn descriptor_proof_does_not_materialize_unused_inherited_values() -> Result<(), BudgetExceeded>
    {
        let unlimited = WorkBudget::unlimited("lookup-setup");
        let mut heap = Environment::new();
        for id in 0..2 {
            let mut data = OwnData::new(AllocationKind::Ordinary);
            data.define_data(
                "x".into(),
                Some(Fact::Primitive(Value::String("a".repeat(8192)))),
            );
            let parent = heap.allocate(id * 2, data, &unlimited)?;
            let mut child = OwnData::new(AllocationKind::Ordinary);
            child.set_literal_prototype(Some(parent));
            heap.allocate(id * 2 + 1, child, &unlimited)?;
        }
        let locations = Rc::from([1, 3]);
        let bounded = WorkBudget::new(
            "write-with-large-inherited-value",
            work_budget::BudgetLimits::work(128),
        );
        assert!(heap.write(
            &locations,
            "x",
            Some(&Fact::Primitive(Value::Number(9.0))),
            &bounded
        )?);
        assert!(matches!(heap.read(&locations, "x", &unlimited)?, Ok(None)));
        // An opaque path must still reject a write, even when earlier
        // paths have already established unknown ordinary data.
        let mut opaque = OwnData::new(AllocationKind::Ordinary);
        opaque.define_accessor("x".into());
        heap.allocate(4, opaque, &unlimited)?;
        assert!(!heap.write(&Rc::from([1, 3, 4]), "x", None, &unlimited)?);
        let bounded = WorkBudget::new("read-large-value", work_budget::BudgetLimits::work(128));
        assert!(heap.read(&Rc::from([0]), "x", &bounded).is_err());
        Ok(())
    }

    #[test]
    fn local_weak_mutations_match_full_object_join() -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("weak-update-oracle");
        for kind in [AllocationKind::Ordinary, AllocationKind::Array] {
            for unknown_tail in [false, true] {
                let mut original = OwnData::new(kind);
                for key in ["0", "1", "3", "x"] {
                    original.define_data(key.into(), Some(Fact::Primitive(Value::Number(7.0))));
                }
                original.define_data("length".into(), Some(Fact::Primitive(Value::Number(4.0))));
                original.define_accessor("getter".into());
                if unknown_tail {
                    original.unknown_array_tail();
                }
                for (key, value) in [
                    ("0", Some(Fact::Primitive(Value::Number(8.0)))),
                    ("3", None),
                    ("9", Some(Fact::Primitive(Value::Number(8.0)))),
                    ("length", Some(Fact::Primitive(Value::Number(1.0)))),
                    ("x", None),
                    ("new", None),
                ] {
                    let mut changed = original.clone();
                    changed.write(key, value.clone(), Strength::Strong, &budget)?;
                    let mut expected = original.clone();
                    expected.join(&changed, &budget)?;
                    let mut actual = original.clone();
                    actual.write(key, value, Strength::Weak, &budget)?;
                    for key in [
                        "0", "1", "3", "9", "length", "x", "new", "getter", "unlisted",
                    ] {
                        assert_eq!(
                            descriptor_shape(actual.property(key)),
                            descriptor_shape(expected.property(key)),
                            "{key}"
                        );
                    }
                }
                for key in ["0", "3", "x", "getter", "new"] {
                    let mut changed = original.clone();
                    changed.delete_own(key, Strength::Strong, &budget)?;
                    let mut expected = original.clone();
                    expected.join(&changed, &budget)?;
                    let mut actual = original.clone();
                    actual.delete_own(key, Strength::Weak, &budget)?;
                    for key in ["0", "1", "3", "length", "x", "new", "getter", "unlisted"] {
                        assert_eq!(
                            descriptor_shape(actual.property(key)),
                            descriptor_shape(expected.property(key)),
                            "{key}"
                        );
                    }
                }
            }
        }
        Ok(())
    }

    #[test]
    fn budget_accounts_for_prototype_edges_and_weak_descriptor_updates(
    ) -> Result<(), BudgetExceeded> {
        let unlimited = WorkBudget::unlimited("heap-setup");
        let mut heap = Environment::new();
        let mut base = OwnData::new(AllocationKind::Ordinary);
        base.define_data("x".into(), Some(Fact::Primitive(Value::Number(7.0))));
        let mut prior = heap.allocate(0, base, &unlimited)?;
        for id in 1..128 {
            let mut next = OwnData::new(AllocationKind::Ordinary);
            next.set_literal_prototype(Some(prior));
            prior = heap.allocate(id, next, &unlimited)?;
        }
        let Fact::Objects(locations) = prior else {
            unreachable!()
        };
        let bounded = WorkBudget::new("prototype", work_budget::BudgetLimits::work(32));
        assert!(heap.read(&locations, "x", &bounded).is_err());
        assert!(matches!(
            heap.read(&locations, "x", &unlimited)?,
            Ok(Some(Fact::Primitive(Value::Number(7.0))))
        ));

        let mut data = OwnData::new(AllocationKind::Ordinary);
        for index in 0..128 {
            data.define_data(
                format!("key{index}"),
                Some(Fact::Primitive(Value::Number(7.0))),
            );
        }
        heap.allocate(128, data.clone(), &unlimited)?;
        heap.allocate(129, data, &unlimited)?;
        let locations = Rc::from([128, 129]);
        let shared = heap.clone();
        let bounded = WorkBudget::new("weak-write-copy", work_budget::BudgetLimits::work(32));
        assert!(heap
            .write(
                &locations,
                "key0",
                Some(&Fact::Primitive(Value::Number(9.0))),
                &bounded
            )
            .is_err());
        assert!(matches!(
            heap.read(&locations, "key0", &unlimited)?,
            Ok(Some(Fact::Primitive(Value::Number(7.0))))
        ));
        drop(shared);
        let bounded = WorkBudget::new("weak-write-local", work_budget::BudgetLimits::work(128));
        assert!(heap.write(
            &locations,
            "key0",
            Some(&Fact::Primitive(Value::Number(9.0))),
            &bounded
        )?);
        assert!(matches!(
            heap.read(&locations, "key0", &unlimited)?,
            Ok(None)
        ));
        Ok(())
    }

    #[test]
    fn budget_charges_changed_maps_without_charging_identical_forks() -> Result<(), BudgetExceeded>
    {
        let unlimited = WorkBudget::unlimited("heap-setup");
        let mut heap = Environment::new();
        let mut data = OwnData::new(AllocationKind::Ordinary);
        data.define_data("x".into(), Some(Fact::Primitive(Value::Number(7.0))));
        for id in 0..128 {
            let fact = heap.allocate(id, data.clone(), &unlimited)?;
            heap.insert(cell(id), fact, &unlimited)?;
        }
        let mut fork = heap.clone();
        let bounded = WorkBudget::new("unchanged-join", work_budget::BudgetLimits::work(0));
        heap.join(&fork, 128, &bounded)?;
        let bounded = WorkBudget::new("map-detach", work_budget::BudgetLimits::work(16));
        assert!(fork
            .insert(cell(0), Fact::Primitive(Value::Null), &bounded)
            .is_err());
        fork.insert(cell(0), Fact::Primitive(Value::Null), &unlimited)?;
        let bounded = WorkBudget::new("changed-join", work_budget::BudgetLimits::work(16));
        assert!(heap.join(&fork, 128, &bounded).is_err());
        assert!(matches!(heap.get(cell(0)), Some(Fact::Objects(_))));
        heap.join(&fork, 128, &unlimited)?;
        assert!(heap.get(cell(0)).is_none());
        Ok(())
    }

    #[test]
    fn location_join_is_ordered_unique_and_preserves_exact_identity() -> Result<(), BudgetExceeded>
    {
        let budget = WorkBudget::unlimited("heap-join");
        let left = Fact::Objects(Rc::from([0, 2, 4, 6]));
        let right = Fact::Objects(Rc::from([1, 2, 3, 6, 7]));
        let Some(Fact::Objects(joined)) = left.join(&right, &budget)? else {
            unreachable!()
        };
        assert_eq!(joined.as_ref(), &[0, 1, 2, 3, 4, 6, 7]);
        assert_eq!(left.strict_equal(&right, &budget)?, None);
        assert_eq!(
            left.strict_equal(&Fact::Objects(Rc::from([1, 3])), &budget)?,
            Some(false)
        );
        let same = left.join(&left, &budget)?;
        let (Fact::Objects(original), Some(Fact::Objects(same))) = (left, same) else {
            unreachable!()
        };
        assert!(Rc::ptr_eq(&original, &same));
        Ok(())
    }

    #[test]
    fn fork_shares_unchanged_maps_and_isolates_the_first_mutation() -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("heap-fork");
        let symbol = cell(0);
        let mut heap = Environment::new();
        let mut data = OwnData::new(AllocationKind::Ordinary);
        data.define_data("x".into(), Some(Fact::Primitive(Value::Number(7.0))));
        let object = heap.allocate(0, data, &budget)?;
        let Fact::Objects(locations) = &object else {
            unreachable!()
        };
        heap.insert(symbol, object.clone(), &budget)?;

        let unchanged = heap.clone();
        assert!(heap.bindings.shares(&unchanged.bindings));
        assert!(Rc::ptr_eq(&heap.allocations, &unchanged.allocations));
        heap.join(&unchanged, 1, &budget)?;
        assert!(heap.bindings.shares(&unchanged.bindings));
        assert!(Rc::ptr_eq(&heap.allocations, &unchanged.allocations));

        let mut changed = heap.clone();
        assert!(changed.write(
            locations,
            "x",
            Some(&Fact::Primitive(Value::Number(9.0))),
            &budget
        )?);
        assert!(heap.bindings.shares(&changed.bindings));
        assert!(!Rc::ptr_eq(&heap.allocations, &changed.allocations));
        assert!(matches!(
            heap.read(locations, "x", &budget)?,
            Ok(Some(Fact::Primitive(Value::Number(7.0))))
        ));
        heap.join(&changed, 1, &budget)?;
        assert!(matches!(heap.read(locations, "x", &budget)?, Ok(None)));

        let mut invalidated = heap.clone();
        invalidated.clear();
        assert_eq!(invalidated.bindings.len(), 0);
        assert!(invalidated.allocations.is_empty());
        assert!(heap.get(symbol).is_some());
        assert!(heap.allocations.contains_key(&0));
        heap.join(&invalidated, 1, &budget)?;
        assert!(heap.get(symbol).is_none());
        assert!(heap.allocations.is_empty());
        Ok(())
    }

    #[test]
    fn collection_bounds_churn_and_preserves_reachable_cycles() -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("heap-collection");
        let mut heap = Environment::new();
        let mut parent = OwnData::new(AllocationKind::Ordinary);
        parent.define_data("next".into(), None);
        let root = heap.allocate(0, parent, &budget)?;
        let child = heap.allocate(1, OwnData::new(AllocationKind::Ordinary), &budget)?;
        let Fact::Objects(root_locations) = &root else {
            unreachable!()
        };
        assert!(heap.write(root_locations, "next", Some(&child), &budget)?);
        let mut child_data = OwnData::new(AllocationKind::Ordinary);
        child_data.set_literal_prototype(Some(root.clone()));
        Rc::make_mut(&mut heap.allocations).insert(1, Rc::new(child_data));
        heap.insert(cell(0), root, &budget)?;
        let mut uncollected = heap.clone();
        let mut peak = 0usize;
        let (mut collected_entries, mut original_entries) = (0usize, 0usize);
        for id in 2..4096 {
            heap.allocate(id, OwnData::new(AllocationKind::Ordinary), &budget)?;
            uncollected.allocate(id, OwnData::new(AllocationKind::Ordinary), &budget)?;
            heap.collect_if_needed(std::iter::once(ROOT), &budget)?;
            peak = peak.max(heap.allocations.len());
            // Both maps would be copied at an unknown conditional branch.
            collected_entries += heap.allocations.len();
            original_entries += uncollected.allocations.len();
        }
        assert!(peak < MIN_COLLECTION_SIZE);
        assert!(collected_entries < original_entries / 32);
        eprintln!("peak retained allocations: {peak} vs {}; cumulative fork entries: {collected_entries} vs {original_entries}", uncollected.allocations.len());
        heap.collect(std::iter::once(ROOT), &budget)?;
        assert_eq!(heap.allocations.len(), 2);
        heap.remove(cell(0), &budget)?;
        heap.collect(std::iter::once(ROOT), &budget)?;
        assert!(heap.allocations.is_empty());
        Ok(())
    }

    #[test]
    fn retiring_entire_scope_releases_large_allocation_graph() -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("heap-collection");
        let mut heap = Environment::new();
        let symbols = (0..256).map(cell).collect::<Vec<_>>();
        for (id, &symbol) in symbols.iter().enumerate() {
            let object = heap.allocate(id, OwnData::new(AllocationKind::Ordinary), &budget)?;
            heap.insert(symbol, object, &budget)?;
            heap.collect_if_needed(std::iter::once(ROOT), &budget)?;
        }
        assert_eq!(heap.allocations.len(), symbols.len());
        heap.collect_after_scope_exit(ROOT, std::iter::empty(), &budget)?;
        assert!(heap.allocations.is_empty());
        assert_eq!(heap.collection_threshold, MIN_COLLECTION_SIZE);
        Ok(())
    }

    #[test]
    fn collection_distinguishes_unreachable_branch_data_from_invalidation(
    ) -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("heap-collection");
        let symbol = cell(0);
        let mut heap = Environment::new();
        let mut data = OwnData::new(AllocationKind::Ordinary);
        data.define_data("x".into(), Some(Fact::Primitive(Value::Number(7.0))));
        let root = heap.allocate(0, data.clone(), &budget)?;
        heap.insert(symbol, root.clone(), &budget)?;
        let mut other = heap.clone();
        let first_new = 1;
        heap.protect_before(first_new);
        other.protect_before(first_new);
        let replacement = heap.allocate(first_new, data, &budget)?;
        heap.insert(symbol, replacement, &budget)?;
        heap.collect(std::iter::once(ROOT), &budget)?;
        assert!(heap.allocations.contains_key(&0));
        heap.protect_before(0);
        other.protect_before(0);
        heap.join(&other, first_new, &budget)?;
        let Some(Fact::Objects(locations)) = heap.get(symbol) else {
            unreachable!()
        };
        assert!(matches!(
            heap.read(locations, "x", &budget)?,
            Ok(Some(Fact::Primitive(Value::Number(7.0))))
        ));
        let mut invalidated = other.clone();
        invalidated.clear();
        invalidated.insert(symbol, root, &budget)?;
        other.join(&invalidated, first_new, &budget)?;
        assert!(!other.allocations.contains_key(&0));
        Ok(())
    }
}
