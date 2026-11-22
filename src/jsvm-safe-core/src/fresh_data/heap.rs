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

/// Bound dead allocation retention without tracing the entire live heap
/// after every statement. Collection is amortized against heap growth;
/// the first threshold avoids overhead on ordinary short functions.
const MIN_COLLECTION_SIZE: usize = 64;

#[derive(Clone)]
pub(super) struct Environment {
    bindings: HashMap<SymbolId, Fact>,
    allocations: HashMap<AllocationId, Rc<OwnData>>,
    collection_threshold: usize,
    collection_floor: AllocationId,
}

impl Default for Environment {
    fn default() -> Self {
        Self {
            bindings: HashMap::new(),
            allocations: HashMap::new(),
            collection_threshold: MIN_COLLECTION_SIZE,
            collection_floor: 0,
        }
    }
}

/// One trace owns its frontier and marks. Charge all traversed edges,
/// including location unions, rather than merely charging visited nodes.
struct Reachability<'b> {
    marked: HashSet<AllocationId>,
    pending: Vec<AllocationId>,
    weight: usize,
    budget: &'b WorkBudget,
}

impl<'b> Reachability<'b> {
    fn new(budget: &'b WorkBudget) -> Self {
        Self {
            marked: HashSet::new(),
            pending: Vec::new(),
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
        if let Property::Data(Some(fact)) | Property::MaybeData(Some(fact)) = property {
            self.fact(fact)?;
        }
        Ok(())
    }

    fn object(&mut self, data: &OwnData) -> Result<(), BudgetExceeded> {
        self.charge(data.properties.listed.capacity().saturating_add(1))?;
        if let Prototype::Objects(locations) = &data.prototype {
            self.locations(locations)?;
        }
        for property in data.properties.listed.values() {
            self.property(property)?;
        }
        self.property(&data.properties.unlisted)
    }
}

impl Environment {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn clear(&mut self) {
        self.bindings.clear();
        self.allocations.clear();
        self.bindings.shrink_to(MIN_COLLECTION_SIZE);
        self.allocations.shrink_to(MIN_COLLECTION_SIZE);
        self.collection_threshold = MIN_COLLECTION_SIZE;
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

    pub(super) fn retire_bindings<'a>(
        &mut self,
        symbols: impl Iterator<Item = &'a SymbolId>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        let mut retired = 0usize;
        for symbol in symbols {
            if let Some(Fact::Objects(locations)) = self.bindings.remove(symbol) {
                retired = retired.saturating_add(locations.len());
            }
        }
        if self.bindings.is_empty() && self.collection_floor == 0 {
            self.clear();
        } else if self.allocations.len() >= MIN_COLLECTION_SIZE
            && retired >= self.allocations.len().div_ceil(2)
        {
            self.collect(budget)?;
        }
        Ok(())
    }

    /// Preserve allocations that existed before an outstanding branch
    /// fork. The join interprets an absent pre-fork entry as invalidation,
    /// so ordinary unreachability must not erase that distinction.
    pub(super) fn protect_before(&mut self, first_new: AllocationId) -> AllocationId {
        std::mem::replace(&mut self.collection_floor, first_new)
    }

    /// This may run only at statement boundaries, when no caller-held
    /// expression temporaries, pending assignment receivers or in-progress
    /// object literals need to be kept alive. Lexical bindings and their
    /// transitive (own-property and prototype) edges are the roots.
    pub(super) fn collect_if_needed(&mut self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        if self.allocations.len() < self.collection_threshold {
            return Ok(());
        }
        self.collect(budget)
    }

    fn collect(&mut self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        let mut trace = Reachability::new(budget);
        trace.charge(self.bindings.capacity())?;
        if self.collection_floor != 0 {
            budget.consume(u64::try_from(self.allocations.capacity()).unwrap_or(u64::MAX))?;
            for &id in self.allocations.keys() {
                if id < self.collection_floor {
                    trace.mark(id);
                }
            }
        }
        for fact in self.bindings.values() {
            trace.fact(fact)?;
        }
        while let Some(id) = trace.pending.pop() {
            // A captured identity can survive the invalidation of its
            // descriptor proof. Missing objects have no traversable edges.
            if let Some(data) = self.allocations.get(&id) {
                trace.object(data)?;
            }
        }
        budget.consume(u64::try_from(self.allocations.capacity()).unwrap_or(u64::MAX))?;
        self.allocations.retain(|id, _| trace.marked.contains(id));
        // HashMap iteration follows capacity, not just length. Release
        // excess capacity after a large transient expression or scope.
        if self.allocations.capacity()
            > self
                .allocations
                .len()
                .saturating_mul(4)
                .max(MIN_COLLECTION_SIZE)
        {
            self.allocations.shrink_to_fit();
        }
        if self.bindings.capacity()
            > self
                .bindings
                .len()
                .saturating_mul(4)
                .max(MIN_COLLECTION_SIZE)
        {
            self.bindings.shrink_to_fit();
        }
        // Make the next trace proportional to the surviving graph, not
        // just the number of nodes. A single large object or many live
        // primitive bindings must not incur a full scan every 64 literals.
        self.collection_threshold = self
            .allocations
            .len()
            .saturating_add(trace.weight.max(self.allocations.len()))
            .max(MIN_COLLECTION_SIZE);
        Ok(())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collection_bounds_churn_and_preserves_reachable_cycles() -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("heap-collection");
        let mut heap = Environment::new();
        let mut parent = OwnData::new(AllocationKind::Ordinary);
        parent.define_data("next".into(), None);
        let root = heap.allocate(0, parent);
        let child = heap.allocate(1, OwnData::new(AllocationKind::Ordinary));
        let Fact::Objects(root_locations) = &root else {
            unreachable!()
        };
        assert!(heap.write(root_locations, "next", Some(child)));
        let mut child_data = OwnData::new(AllocationKind::Ordinary);
        child_data.set_literal_prototype(Some(root.clone()));
        heap.allocations.insert(1, Rc::new(child_data));
        heap.insert(SymbolId::new(0), root);
        let mut uncollected = heap.clone();
        let mut peak = 0usize;
        let (mut collected_entries, mut original_entries) = (0usize, 0usize);
        for id in 2..4096 {
            heap.allocate(id, OwnData::new(AllocationKind::Ordinary));
            uncollected.allocate(id, OwnData::new(AllocationKind::Ordinary));
            heap.collect_if_needed(&budget)?;
            peak = peak.max(heap.allocations.len());
            // Both maps would be copied at an unknown conditional branch.
            collected_entries += heap.allocations.len();
            original_entries += uncollected.allocations.len();
        }
        assert!(peak < MIN_COLLECTION_SIZE);
        assert!(collected_entries < original_entries / 32);
        eprintln!("peak retained allocations: {peak} vs {}; cumulative fork entries: {collected_entries} vs {original_entries}", uncollected.allocations.len());
        heap.collect(&budget)?;
        assert_eq!(heap.allocations.len(), 2);
        heap.remove(&SymbolId::new(0));
        heap.collect(&budget)?;
        assert!(heap.allocations.is_empty());
        Ok(())
    }

    #[test]
    fn retiring_entire_scope_releases_large_allocation_graph() -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("heap-collection");
        let mut heap = Environment::new();
        let symbols = (0..256).map(SymbolId::new).collect::<Vec<_>>();
        for (id, &symbol) in symbols.iter().enumerate() {
            let object = heap.allocate(id, OwnData::new(AllocationKind::Ordinary));
            heap.insert(symbol, object);
            heap.collect_if_needed(&budget)?;
        }
        assert_eq!(heap.allocations.len(), symbols.len());
        heap.retire_bindings(symbols.iter(), &budget)?;
        assert!(heap.allocations.is_empty());
        assert_eq!(heap.collection_threshold, MIN_COLLECTION_SIZE);
        Ok(())
    }

    #[test]
    fn collection_distinguishes_unreachable_branch_data_from_invalidation(
    ) -> Result<(), BudgetExceeded> {
        let budget = WorkBudget::unlimited("heap-collection");
        let symbol = SymbolId::new(0);
        let mut heap = Environment::new();
        let mut data = OwnData::new(AllocationKind::Ordinary);
        data.define_data("x".into(), Some(Fact::Primitive(Value::Number(7.0))));
        let root = heap.allocate(0, data.clone());
        heap.insert(symbol, root.clone());
        let mut other = heap.clone();
        let first_new = 1;
        heap.protect_before(first_new);
        other.protect_before(first_new);
        let replacement = heap.allocate(first_new, data);
        heap.insert(symbol, replacement);
        heap.collect(&budget)?;
        assert!(heap.allocations.contains_key(&0));
        heap.protect_before(0);
        other.protect_before(0);
        heap.join(&other, first_new);
        let Some(Fact::Objects(locations)) = heap.get(&symbol) else {
            unreachable!()
        };
        assert!(matches!(
            heap.read(locations, "x"),
            Some(Some(Fact::Primitive(Value::Number(7.0))))
        ));
        let mut invalidated = other.clone();
        invalidated.clear();
        invalidated.insert(symbol, root);
        other.join(&invalidated, first_new);
        assert!(!other.allocations.contains_key(&0));
        Ok(())
    }
}
