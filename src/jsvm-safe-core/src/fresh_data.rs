//! Flow-local facts about freshly constructed own data properties.
//!
//! Whole-lifetime confinement is useful for captured objects, but it is not
//! required for reads before a possible escape. This analysis walks actual
//! evaluation prefixes. Unknown evaluation invalidates reaching facts;
//! branch joins keep only facts common to the reaching normal paths. Deferred
//! bodies and unsupported control regions are analyzed from an empty state.
use crate::binding_facts::BindingFacts;
use crate::pure_function::PureFunction;
use crate::value_eval::{
    eval, eval_binary, eval_unary_value, identical_primitive_value, is_prototype_setter,
    literal_property_key, Value,
};
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, BindingPattern, Declaration, Expression, ForStatement,
    ForStatementInit, IdentifierReference, MemberExpression, ObjectPropertyKind, Program,
    PropertyKind, SimpleAssignmentTarget, Statement, VariableDeclaration, VariableDeclarationKind,
    VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::{GetSpan, Span};
use oxc_syntax::{
    operator::AssignmentOperator,
    scope::{ScopeFlags, ScopeId},
    symbol::{SymbolFlags, SymbolId},
};
use std::collections::{HashMap, HashSet};
use work_budget::{BudgetExceeded, WorkBudget};

mod activation;
mod arguments;
mod cells;
mod coverage;
mod dispatch;
mod heap;
mod origins;
mod parameters;
mod scope_instances;
use cells::CellId;
use heap::{
    value_weight, AllocationId, AllocationKind, Environment, Fact, Locations, Lookup, OwnData,
};

enum Reference {
    Binding(CellId),
    Member { locations: Locations, key: String },
}

impl Reference {
    fn read(
        &self,
        environment: &Environment,
        budget: &WorkBudget,
    ) -> Result<Lookup, BudgetExceeded> {
        match self {
            Self::Binding(symbol) => Ok(Ok(environment.read_binding(*symbol, budget)?)),
            Self::Member { locations, key } => environment.read(locations, key, budget),
        }
    }

    fn write(
        &self,
        environment: &mut Environment,
        value: Option<&Fact>,
        budget: &WorkBudget,
    ) -> Result<bool, BudgetExceeded> {
        match self {
            Self::Binding(symbol) => {
                if let Some(value) = value {
                    environment.insert(*symbol, value.copy(budget)?, budget)?;
                } else {
                    environment.remove(*symbol, budget)?;
                }
                Ok(true)
            }
            Self::Member { locations, key } => environment.write(locations, key, value, budget),
        }
    }
}

#[derive(Default)]
struct Evaluation {
    fact: Option<Fact>,
    inert: bool,
}

impl Evaluation {
    const fn primitive(value: Value, inert: bool) -> Self {
        Self {
            fact: Some(Fact::Primitive(value)),
            inert,
        }
    }

    fn primitive_value(&self) -> Option<&Value> {
        self.fact.as_ref()?.primitive()
    }

    const fn unknown_inert() -> Self {
        Self {
            fact: None,
            inert: true,
        }
    }
}

/// A source occurrence can execute more than once in a proven finite loop.
/// A rewrite is valid only when every reaching evaluation has the same
/// inert value, not merely when one of the iterations supplied a fact.
enum Observation<T> {
    Exact(T),
    Unknown,
}

struct ReachingObservations<T> {
    values: HashMap<(u32, u32), Observation<T>>,
}

impl<T> Default for ReachingObservations<T> {
    fn default() -> Self {
        Self {
            values: HashMap::new(),
        }
    }
}

impl<T> ReachingObservations<T> {
    fn observe(
        &mut self,
        key: (u32, u32),
        observation: Observation<T>,
        equivalent: impl Fn(&T, &T) -> bool,
    ) {
        use std::collections::hash_map::Entry;
        match self.values.entry(key) {
            Entry::Vacant(entry) => {
                entry.insert(observation);
            }
            Entry::Occupied(mut entry) => {
                if !matches!((entry.get(), &observation),
                    (Observation::Exact(left), Observation::Exact(right))
                    if equivalent(left, right))
                {
                    entry.insert(Observation::Unknown);
                }
            }
        }
    }

    fn get(&self, span: Span) -> Option<&T> {
        match self.values.get(&(span.start, span.end))? {
            Observation::Exact(value) => Some(value),
            Observation::Unknown => None,
        }
    }

    fn merge(&mut self, other: Self, equivalent: impl Fn(&T, &T) -> bool) {
        for (key, observation) in other.values {
            self.observe(key, observation, &equivalent);
        }
    }
}

#[derive(Default)]
pub struct FreshDataReads {
    members: ReachingObservations<Value>,
    comparisons: ReachingObservations<Value>,
    dispatches: ReachingObservations<dispatch::DispatchTrace>,
    gaps: coverage::CoverageGaps,
}

impl FreshDataReads {
    pub(crate) fn analyze(
        program: &Program<'_>,
        scoping: &Scoping,
        bindings: &BindingFacts,
        pure_functions: &HashMap<SymbolId, PureFunction>,
        budget: &WorkBudget,
    ) -> Result<Self, BudgetExceeded> {
        let mut analyzer = Analyzer {
            scoping,
            bindings,
            pure_functions,
            callables: activation::CallableIndex::collect(program, budget)?,
            scope_instances: scope_instances::ScopeInstances::default(),
            lexical_scopes: Vec::new(),
            activation_depth: 0,
            activation_fuel: 0,
            reads: Self::default(),
            visited_lists: HashSet::new(),
            budget,
            failure: None,
            next_identity: 0,
            loop_fuel: None,
            loop_failed: false,
            opaque_generation: 0,
            pending_disposals: 0,
            return_frame: None,
        };
        analyzer.visit_program(program);
        analyzer.failure.map_or(Ok(analyzer.reads), Err)
    }

    pub(crate) fn get(&self, span: Span) -> Option<&Value> {
        self.members.get(span)
    }

    pub(crate) fn comparison(&self, span: Span) -> Option<&Value> {
        self.comparisons.get(span)
    }

    pub(crate) fn dispatch_replacement(
        &self,
        statement: &ForStatement<'_>,
        scoping: &Scoping,
        source: &str,
    ) -> Option<String> {
        dispatch::render_reaching_dispatch(&self.dispatches, statement, scoping, source)
    }

    fn merge(&mut self, other: Self) {
        self.members.merge(other.members, identical_primitive_value);
        self.comparisons
            .merge(other.comparisons, identical_primitive_value);
        self.dispatches.merge(other.dispatches, PartialEq::eq);
        self.gaps.merge(other.gaps);
    }

    fn discard_unobserved(
        &mut self,
        visited: &mut HashSet<(u32, u32)>,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        let count = self
            .members
            .values
            .capacity()
            .saturating_add(self.comparisons.values.capacity())
            .saturating_add(self.dispatches.values.capacity())
            .saturating_add(visited.capacity());
        let Some(excluded) = std::mem::take(&mut self.gaps).normalize(count, budget)? else {
            return Ok(());
        };
        self.members
            .values
            .retain(|&key, _| !excluded.contains(key));
        self.comparisons
            .values
            .retain(|&key, _| !excluded.contains(key));
        self.dispatches
            .values
            .retain(|&key, _| !excluded.contains(key));
        // Independently analyzed bodies can still establish facts without
        // the discarded contextual state.
        visited.retain(|&key| !excluded.contains(key));
        Ok(())
    }
}

struct Analyzer<'c, 'ast> {
    scoping: &'c Scoping,
    bindings: &'c BindingFacts,
    pure_functions: &'c HashMap<SymbolId, PureFunction>,
    callables: activation::CallableIndex<'ast>,
    scope_instances: scope_instances::ScopeInstances,
    lexical_scopes: Vec<Option<scope_instances::ScopeTicket>>,
    activation_depth: usize,
    activation_fuel: usize,
    reads: FreshDataReads,
    visited_lists: HashSet<(u32, u32)>,
    budget: &'c WorkBudget,
    failure: Option<BudgetExceeded>,
    next_identity: AllocationId,
    loop_fuel: Option<usize>,
    loop_failed: bool,
    opaque_generation: u64,
    pending_disposals: usize,
    return_frame: Option<activation::ReturnFrame>,
}

impl Analyzer<'_, '_> {
    fn unobserved(&mut self, span: Span) {
        if self.loop_fuel.is_some() && self.heap_result(self.budget.consume(1)).is_some() {
            self.reads.gaps.insert(span);
        }
    }

    fn checkpoint(&mut self) -> bool {
        if self.failure.is_some() {
            return false;
        }
        if let Err(failure) = self.budget.checkpoint() {
            self.failure = Some(failure);
            false
        } else {
            true
        }
    }

    fn charge_values<'a>(&mut self, values: impl IntoIterator<Item = &'a Value>) -> bool {
        let units = values
            .into_iter()
            .map(value_weight)
            .fold(0usize, usize::saturating_add);
        self.heap_result(
            self.budget
                .consume(u64::try_from(units).unwrap_or(u64::MAX)),
        )
        .is_some()
    }

    fn heap_result<T>(&mut self, result: Result<T, BudgetExceeded>) -> Option<T> {
        match result {
            Ok(value) => Some(value),
            Err(failure) => {
                if self.failure.is_none() {
                    self.failure = Some(failure);
                }
                None
            }
        }
    }

    fn join_heap(
        &mut self,
        environment: &mut Environment,
        other: &Environment,
        first_new: AllocationId,
    ) -> bool {
        self.heap_result(environment.join(other, first_new, self.budget))
            .is_some()
    }

    fn invalidate(&mut self, environment: &mut Environment) {
        self.opaque_generation = self.opaque_generation.saturating_add(1);
        environment.clear();
    }

    fn barrier(&mut self, environment: &mut Environment) -> Evaluation {
        self.invalidate(environment);
        Evaluation::default()
    }

    fn lexical_reference(&self, identifier: &IdentifierReference<'_>) -> Option<SymbolId> {
        let reference = identifier.reference_id.get()?;
        let symbol = crate::statically_resolved_symbol(self.scoping, reference)?;
        if !self.bindings.has_declarative_storage(self.scoping, symbol) {
            return None;
        }
        self.bindings
            .proves_reference_identity(
                self.scoping,
                symbol,
                self.scoping.get_reference(reference).scope_id(),
            )
            .then_some(symbol)
    }

    fn cell_id(&self, symbol: SymbolId) -> Option<CellId> {
        let owner = self.scoping.symbol_scope_id(symbol);
        let instance = self.scope_instances.get(owner, || {
            self.bindings
                .parameter_binding_survives_body(self.scoping, symbol)
        })?;
        if self
            .bindings
            .implicit_arguments_symbol(self.scoping, symbol)
            && self.scope_instances.get(owner, || true) == Some(instance)
        {
            return Some(CellId::arguments(instance));
        }
        Some(CellId::symbol(instance, symbol))
    }

    fn implicit_arguments_cell(&self, identifier: &IdentifierReference<'_>) -> Option<CellId> {
        if identifier.name != "arguments" {
            return None;
        }
        let owner = self
            .bindings
            .implicit_arguments_owner(self.scoping, identifier.reference_id.get()?)?;
        Some(CellId::arguments(self.scope_instances.get(owner, || true)?))
    }

    fn identifier(
        &mut self,
        identifier: &IdentifierReference<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some(reference) = identifier.reference_id.get() else {
            return self.barrier(environment);
        };
        let reference_flags = self.scoping.get_reference(reference);
        // MemberWriteTarget marks the containing operation, not a write to
        // the receiver binding itself.
        if !reference_flags.is_read() || reference_flags.is_write() {
            return self.barrier(environment);
        }
        let symbol = self.lexical_reference(identifier);
        let Some(cell) = symbol
            .and_then(|symbol| self.cell_id(symbol))
            .or_else(|| self.implicit_arguments_cell(identifier))
        else {
            return self.barrier(environment);
        };
        let Some(fact) = self.heap_result(environment.read_binding(cell, self.budget)) else {
            return self.barrier(environment);
        };
        if let Some(fact) = fact {
            return Evaluation {
                fact: Some(fact),
                inert: true,
            };
        }
        let scope = reference_flags.scope_id();
        Evaluation {
            fact: None,
            inert: symbol.is_some_and(|symbol| {
                self.bindings
                    .proves_value_initialized(self.scoping, symbol, scope, identifier.span)
                    || self.bindings.proves_initialized(
                        self.scoping,
                        symbol,
                        scope,
                        identifier.span,
                    )
            }),
        }
    }

    const fn fresh_identity(&mut self) -> usize {
        let id = self.next_identity;
        self.next_identity += 1;
        id
    }

    fn enter_empty_instance(
        &mut self,
        scope: ScopeId,
        environment: &mut Environment,
    ) -> Option<scope_instances::ScopeTicket> {
        let id = self.fresh_identity();
        self.heap_result(environment.record_birth(id, self.budget))?;
        Some(self.scope_instances.enter(scope, id))
    }

    fn enter_instance(
        &mut self,
        scope: Option<ScopeId>,
        environment: &mut Environment,
    ) -> Option<scope_instances::ScopeTicket> {
        let scope = scope?;
        let ticket = self.enter_empty_instance(scope, environment)?;
        if self
            .initialize_hoisted_callables(scope, environment)
            .is_none()
        {
            let _ = self.scope_instances.leave(&ticket);
            return None;
        }
        Some(ticket)
    }

    fn leave_instance(
        &mut self,
        ticket: Option<scope_instances::ScopeTicket>,
        environment: &mut Environment,
    ) -> bool {
        if let Some(retired) = ticket.and_then(|ticket| self.scope_instances.leave(&ticket)) {
            let result = environment.collect_after_scope_exit(
                retired,
                self.scope_instances.roots(),
                self.budget,
            );
            return self.heap_result(result).is_some();
        }
        true
    }

    fn allocate(
        &mut self,
        environment: &mut Environment,
        data: OwnData,
        inert: bool,
    ) -> Evaluation {
        let id = self.fresh_identity();
        let Some(fact) = self.heap_result(environment.allocate(id, data, self.budget)) else {
            return self.barrier(environment);
        };
        Evaluation {
            fact: Some(fact),
            inert,
        }
    }

    fn key(&mut self, expression: &Expression<'_>, environment: &mut Environment) -> Evaluation {
        if let Expression::BigIntLiteral(literal) = expression.without_parentheses() {
            return Evaluation::primitive(Value::String(literal.value.to_string()), true);
        }
        self.expression(expression, environment)
    }

    fn member(
        &mut self,
        object: Evaluation,
        key: &Evaluation,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some(name) = key.primitive_value().map(Value::js_string) else {
            return self.barrier(environment);
        };
        let Some(Fact::Objects(locations)) = object.fact else {
            return self.barrier(environment);
        };
        // The receiver was evaluated before the key, but its contents must
        // be read *after* key evaluation, including any effects on aliases.
        let Some(fact) = self
            .heap_result(environment.read(&locations, &name, self.budget))
            .and_then(Result::ok)
        else {
            return self.barrier(environment);
        };
        let inert = object.inert && key.inert;
        Evaluation { fact, inert }
    }

    /// Evaluate the receiver before the key, for reads, assignment targets,
    /// updates and delete alike. Never evaluate an optional member as an
    /// unconditional reference, or a private member as a public own key.
    fn member_components(
        &mut self,
        member: &MemberExpression<'_>,
        environment: &mut Environment,
    ) -> Option<(Evaluation, Evaluation)> {
        if member.optional() {
            return None;
        }
        let object = self.expression(member.object(), environment);
        let key = match member {
            MemberExpression::StaticMemberExpression(member) => {
                Evaluation::primitive(Value::String(member.property.name.to_string()), true)
            }
            MemberExpression::ComputedMemberExpression(member) => {
                self.key(&member.expression, environment)
            }
            MemberExpression::PrivateFieldExpression(_) => return None,
        };
        Some((object, key))
    }

    fn member_reference(
        &mut self,
        member: &MemberExpression<'_>,
        environment: &mut Environment,
    ) -> Option<Reference> {
        let (object, key) = self.member_components(member, environment)?;
        let key = key.primitive_value()?.js_string();
        let Fact::Objects(locations) = object.fact? else {
            return None;
        };
        Some(Reference::Member { locations, key })
    }

    fn reference(
        &mut self,
        target: &SimpleAssignmentTarget<'_>,
        environment: &mut Environment,
    ) -> Option<Reference> {
        if let SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) = target {
            if let Some(cell) = self.implicit_arguments_cell(identifier) {
                return Some(Reference::Binding(cell));
            }
            let symbol = self.lexical_reference(identifier)?;
            let flags = self.scoping.symbol_flags(symbol);
            // Declaration bindings are mutable; a named function expression's
            // self name is an immutable binding outside its parameter cells.
            let mutable = (flags.is_variable() || flags.is_function())
                && !flags.intersects(SymbolFlags::ConstVariable | SymbolFlags::FunctionExpression);
            return mutable
                .then(|| self.cell_id(symbol).map(Reference::Binding))
                .flatten();
        }
        self.member_reference(target.as_member_expression()?, environment)
    }

    fn logical_decision(operator: &str, fact: &Fact) -> Option<bool> {
        match operator {
            "&&" => Some(fact.truthy()),
            "||" => Some(!fact.truthy()),
            "??" => Some(matches!(
                fact.primitive(),
                Some(Value::Null | Value::Undefined)
            )),
            _ => None,
        }
    }

    fn assignment(
        &mut self,
        assignment: &oxc_ast::ast::AssignmentExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some(reference) = assignment
            .left
            .as_simple_assignment_target()
            .and_then(|target| self.reference(target, environment))
        else {
            self.unobserved(assignment.span);
            return self.barrier(environment);
        };
        let operator = assignment.operator;
        if operator == AssignmentOperator::Assign {
            let value = self.expression(&assignment.right, environment);
            if !self
                .heap_result(reference.write(environment, value.fact.as_ref(), self.budget))
                .unwrap_or(false)
            {
                self.invalidate(environment);
            }
            return Evaluation {
                fact: value.fact,
                inert: false,
            };
        }

        let Some(previous) = self
            .heap_result(reference.read(environment, self.budget))
            .and_then(Result::ok)
        else {
            self.unobserved(assignment.right.span());
            return self.barrier(environment);
        };
        if let Some(logical) = operator.to_logical_operator() {
            let decision = previous
                .as_ref()
                .and_then(|fact| Self::logical_decision(logical.as_str(), fact));
            if decision == Some(false) {
                return Evaluation {
                    fact: previous,
                    inert: false,
                };
            }
            let skipped = (decision.is_none()).then(|| (environment.clone(), self.next_identity));
            let value = self.expression(&assignment.right, environment);
            if !self
                .heap_result(reference.write(environment, value.fact.as_ref(), self.budget))
                .unwrap_or(false)
            {
                self.invalidate(environment);
            }
            if let Some((skipped, first_new)) = skipped {
                if !self.join_heap(environment, &skipped, first_new) {
                    return self.barrier(environment);
                }
                return Evaluation {
                    fact: None,
                    inert: false,
                };
            }
            return Evaluation {
                fact: value.fact,
                inert: false,
            };
        }

        let right = self.expression(&assignment.right, environment);
        let value = if let (Some(binary), Some(left), Some(right)) = (
            operator.to_binary_operator(),
            previous.as_ref().and_then(Fact::primitive),
            right.primitive_value(),
        ) {
            if !self.charge_values([left, right]) {
                return self.barrier(environment);
            }
            eval_binary(binary.as_str(), left, right)
        } else {
            None
        };
        let Some(value) = value else {
            return self.barrier(environment);
        };
        let fact = Fact::Primitive(value);
        if !self
            .heap_result(reference.write(environment, Some(&fact), self.budget))
            .unwrap_or(false)
        {
            self.invalidate(environment);
        }
        Evaluation {
            fact: Some(fact),
            inert: false,
        }
    }

    fn update_expression(
        &mut self,
        update: &oxc_ast::ast::UpdateExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some(reference) = self.reference(&update.argument, environment) else {
            self.unobserved(update.span);
            return self.barrier(environment);
        };
        let Some(previous) = self
            .heap_result(reference.read(environment, self.budget))
            .and_then(Result::ok)
            .flatten()
            .and_then(|fact| Some(fact.primitive()?.number()))
        else {
            return self.barrier(environment);
        };
        let next = if update.operator.as_str() == "++" {
            previous + 1.0
        } else {
            previous - 1.0
        };
        if !self
            .heap_result(reference.write(
                environment,
                Some(&Fact::Primitive(Value::Number(next))),
                self.budget,
            ))
            .unwrap_or(false)
        {
            self.invalidate(environment);
        }
        Evaluation::primitive(
            Value::Number(if update.prefix { next } else { previous }),
            false,
        )
    }

    fn delete_expression(
        &mut self,
        argument: &Expression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let reference = argument
            .without_parentheses()
            .as_member_expression()
            .and_then(|member| self.member_reference(member, environment));
        let Some(Reference::Member { locations, key }) = reference else {
            self.unobserved(argument.span());
            return self.barrier(environment);
        };
        if self
            .heap_result(environment.delete(&locations, &key, self.budget))
            .unwrap_or(false)
        {
            Evaluation::primitive(Value::Bool(true), false)
        } else {
            self.barrier(environment)
        }
    }

    fn unary_expression(
        &mut self,
        unary: &oxc_ast::ast::UnaryExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let operator = unary.operator.as_str();
        if operator == "delete" {
            return self.delete_expression(&unary.argument, environment);
        }
        let argument = self.expression(&unary.argument, environment);
        let value = if let Some(value) = argument.primitive_value() {
            if !self.charge_values([value]) {
                return self.barrier(environment);
            }
            eval_unary_value(operator, value)
        } else {
            None
        };
        if let Some(value) = value {
            return Evaluation::primitive(value, argument.inert);
        }
        match operator {
            "!" => argument.fact.as_ref().map_or(
                Evaluation {
                    fact: None,
                    inert: argument.inert,
                },
                |value| Evaluation::primitive(Value::Bool(!value.truthy()), argument.inert),
            ),
            "void" => Evaluation::primitive(Value::Undefined, argument.inert),
            "typeof" => {
                let fact = if let Some(Fact::Objects(locations)) = argument.fact {
                    self.heap_result(environment.reference_type(&locations, self.budget))
                        .flatten()
                        .map(|kind| Fact::Primitive(Value::String(kind.into())))
                } else {
                    None
                };
                Evaluation {
                    fact,
                    inert: argument.inert,
                }
            }
            _ => self.barrier(environment),
        }
    }

    fn binary_expression(
        &mut self,
        binary: &oxc_ast::ast::BinaryExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let left = self.expression(&binary.left, environment);
        let right = self.expression(&binary.right, environment);
        let operator = binary.operator.as_str();
        if let (Some(left_value), Some(right_value)) =
            (left.primitive_value(), right.primitive_value())
        {
            if !self.charge_values([left_value, right_value]) {
                return self.barrier(environment);
            }
            if let Some(value) = eval_binary(operator, left_value, right_value) {
                return Evaluation::primitive(value, left.inert && right.inert);
            }
        }
        let object_pair = matches!(left.fact, Some(Fact::Objects(_)))
            && matches!(right.fact, Some(Fact::Objects(_)));
        if matches!(operator, "===" | "!==") || (object_pair && matches!(operator, "==" | "!=")) {
            let equal = if let (Some(left), Some(right)) = (left.fact.as_ref(), right.fact.as_ref())
            {
                self.heap_result(left.strict_equal(right, self.budget))
                    .flatten()
            } else {
                None
            };
            Evaluation {
                fact: equal.map(|equal| {
                    Fact::Primitive(Value::Bool(equal == matches!(operator, "===" | "==")))
                }),
                inert: left.inert && right.inert,
            }
        } else {
            self.barrier(environment)
        }
    }

    fn logical_expression(
        &mut self,
        logical: &oxc_ast::ast::LogicalExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let left = self.expression(&logical.left, environment);
        let decision = left
            .fact
            .as_ref()
            .and_then(|fact| Self::logical_decision(logical.operator.as_str(), fact));
        match decision {
            Some(false) => left,
            Some(true) => {
                let mut right = self.expression(&logical.right, environment);
                right.inert &= left.inert;
                right
            }
            None => {
                let skip = environment.clone();
                let first_new = self.next_identity;
                let right = self.expression(&logical.right, environment);
                if !self.join_heap(environment, &skip, first_new) {
                    return self.barrier(environment);
                }
                Evaluation {
                    fact: None,
                    inert: left.inert && right.inert,
                }
            }
        }
    }

    fn conditional_expression(
        &mut self,
        conditional: &oxc_ast::ast::ConditionalExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let test = self.expression(&conditional.test, environment);
        if let Some(fact) = &test.fact {
            let selected = if fact.truthy() {
                &conditional.consequent
            } else {
                &conditional.alternate
            };
            let mut result = self.expression(selected, environment);
            result.inert &= test.inert;
            return result;
        }
        let mut other = environment.clone();
        let first_new = self.next_identity;
        let left = self.expression(&conditional.consequent, environment);
        let right = self.expression(&conditional.alternate, &mut other);
        if !self.join_heap(environment, &other, first_new) {
            return self.barrier(environment);
        }
        let fact = if let (Some(left), Some(right)) = (left.fact.as_ref(), right.fact.as_ref()) {
            self.heap_result(left.join(right, self.budget)).flatten()
        } else {
            None
        };
        Evaluation {
            fact,
            inert: test.inert && left.inert && right.inert,
        }
    }

    fn array_expression(
        &mut self,
        array: &oxc_ast::ast::ArrayExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let mut data = OwnData::new(AllocationKind::Array);
        let mut inert = true;
        let mut known_index = true;
        for (index, element) in array.elements.iter().enumerate() {
            match element {
                ArrayExpressionElement::Elision(_) => {}
                ArrayExpressionElement::SpreadElement(spread) => {
                    self.expression(&spread.argument, environment);
                    self.invalidate(environment);
                    known_index = false;
                    data.unknown_array_tail();
                    inert = false;
                }
                _ => {
                    let Some(value) = element.as_expression() else {
                        return self.barrier(environment);
                    };
                    let result = self.expression(value, environment);
                    inert &= result.inert;
                    if known_index {
                        data.define_data(index.to_string(), result.fact);
                    }
                }
            }
        }
        let length = known_index
            .then(|| u32::try_from(array.elements.len()).ok())
            .flatten()
            .map(|length| Fact::Primitive(Value::Number(f64::from(length))));
        data.define_data("length".into(), length);
        self.allocate(environment, data, inert)
    }

    fn object_expression(
        &mut self,
        object: &oxc_ast::ast::ObjectExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let mut data = OwnData::new(AllocationKind::Ordinary);
        let mut inert = true;
        for item in &object.properties {
            match item {
                ObjectPropertyKind::SpreadProperty(spread) => {
                    let value = self.expression(&spread.argument, environment);
                    let copied = match value.fact.as_ref() {
                        Some(fact) => match data.spread(environment, fact, self.budget) {
                            Ok(copied) => copied,
                            Err(failure) => {
                                self.failure = Some(failure);
                                return self.barrier(environment);
                            }
                        },
                        None => false,
                    };
                    if copied {
                        inert &= value.inert;
                    } else {
                        self.invalidate(environment);
                        if self
                            .heap_result(data.define_unknown_key(true, None, self.budget))
                            .is_none()
                        {
                            return self.barrier(environment);
                        }
                        inert = false;
                    }
                }
                ObjectPropertyKind::ObjectProperty(property) => {
                    let key = if property.computed {
                        let result = property
                            .key
                            .as_expression()
                            .map_or_default(|key| self.key(key, environment));
                        inert &= result.inert;
                        let key = result.primitive_value().map(Value::js_string);
                        if key.is_none() {
                            self.invalidate(environment);
                            inert = false;
                        }
                        key
                    } else {
                        literal_property_key(&property.key)
                    };
                    let value = self.expression(&property.value, environment);
                    inert &= value.inert;
                    let is_data = property.kind == PropertyKind::Init;
                    let Some(key) = key else {
                        if self
                            .heap_result(data.define_unknown_key(is_data, value.fact, self.budget))
                            .is_none()
                        {
                            return self.barrier(environment);
                        }
                        continue;
                    };
                    if is_prototype_setter(property, &key) {
                        data.set_literal_prototype(value.fact);
                    } else if is_data {
                        data.define_data(key, value.fact);
                    } else {
                        data.define_accessor(key);
                    }
                }
            }
        }
        self.allocate(environment, data, inert)
    }

    fn expression(
        &mut self,
        expression: &Expression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let evaluation = self.evaluate_expression(expression, environment);
        self.observe_expression(expression, evaluation, environment)
    }

    fn observe_expression(
        &mut self,
        expression: &Expression<'_>,
        evaluation: Evaluation,
        environment: &mut Environment,
    ) -> Evaluation {
        let member = expression.is_member_expression();
        let comparison = matches!(expression, Expression::BinaryExpression(binary)
            if matches!(binary.operator.as_str(), "==" | "!=" | "===" | "!=="));
        if member || comparison {
            if self.heap_result(self.budget.consume(1)).is_none() {
                return self.barrier(environment);
            }
            let observation =
                if let Some(value) = evaluation.primitive_value().filter(|_| evaluation.inert) {
                    if !self.charge_values([value]) {
                        return self.barrier(environment);
                    }
                    Observation::Exact(value.clone())
                } else {
                    Observation::Unknown
                };
            let observations = if member {
                &mut self.reads.members
            } else {
                &mut self.reads.comparisons
            };
            let span = expression.span();
            observations.observe(
                (span.start, span.end),
                observation,
                identical_primitive_value,
            );
        }
        evaluation
    }

    /// `GetValue` on a callee retains its reference receiver until after
    /// argument evaluation. Parentheses preserve a reference; sequences,
    /// assignments and conditional expressions produce ordinary values.
    fn evaluate_callee(
        &mut self,
        callee: &Expression<'_>,
        environment: &mut Environment,
    ) -> (Evaluation, Option<Fact>) {
        let callee = callee.without_parentheses();
        let Some(member) = callee.as_member_expression() else {
            return (
                self.expression(callee, environment),
                Some(Fact::Primitive(Value::Undefined)),
            );
        };
        let Some((object, key)) = self.member_components(member, environment) else {
            self.unobserved(callee.span());
            return (self.barrier(environment), None);
        };
        let receiver = object
            .fact
            .as_ref()
            .and_then(|fact| self.heap_result(fact.copy(self.budget)));
        let evaluation = self.member(object, &key, environment);
        (
            self.observe_expression(callee, evaluation, environment),
            receiver,
        )
    }

    fn this_expression(
        &mut self,
        expression: &oxc_ast::ast::ThisExpression,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some(instance) = self
            .callables
            .this_owner(expression)
            .and_then(|owner| self.scope_instances.get(owner, || true))
        else {
            return self.barrier(environment);
        };
        let Some(Some(fact)) =
            self.heap_result(environment.read_binding(CellId::receiver(instance), self.budget))
        else {
            return self.barrier(environment);
        };
        Evaluation {
            fact: Some(fact),
            inert: true,
        }
    }

    fn evaluate_expression(
        &mut self,
        expression: &Expression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        if !self.checkpoint() {
            return self.barrier(environment);
        }
        match expression {
            Expression::Identifier(identifier) => self.identifier(identifier, environment),
            Expression::ThisExpression(expression) => self.this_expression(expression, environment),
            Expression::ParenthesizedExpression(paren) => {
                self.expression(&paren.expression, environment)
            }
            expression if expression.is_member_expression() => {
                let Some((object, key)) = expression
                    .as_member_expression()
                    .and_then(|member| self.member_components(member, environment))
                else {
                    self.unobserved(expression.span());
                    return self.barrier(environment);
                };
                self.member(object, &key, environment)
            }
            Expression::SequenceExpression(sequence) => {
                let mut result = Evaluation::unknown_inert();
                for item in &sequence.expressions {
                    let mut next = self.expression(item, environment);
                    next.inert &= result.inert;
                    result = next;
                }
                result
            }
            Expression::UnaryExpression(unary) => self.unary_expression(unary, environment),
            Expression::BinaryExpression(binary) => self.binary_expression(binary, environment),
            Expression::LogicalExpression(logical) => self.logical_expression(logical, environment),
            Expression::ConditionalExpression(conditional) => {
                self.conditional_expression(conditional, environment)
            }
            Expression::ArrayExpression(array) => self.array_expression(array, environment),
            Expression::ObjectExpression(object) => self.object_expression(object, environment),
            Expression::CallExpression(call) => self.local_call(call, environment),
            Expression::NewExpression(call) => {
                self.expression(&call.callee, environment);
                self.arguments(&call.arguments, environment);
                self.barrier(environment)
            }
            Expression::AssignmentExpression(assignment) => {
                self.assignment(assignment, environment)
            }
            Expression::UpdateExpression(update) => self.update_expression(update, environment),
            Expression::FunctionExpression(function) => {
                self.allocate_callable(function.scope_id.get(), environment)
            }
            Expression::ArrowFunctionExpression(function) => {
                self.allocate_callable(function.scope_id.get(), environment)
            }
            _ => eval(expression).map_or_else(
                || {
                    self.unobserved(expression.span());
                    self.barrier(environment)
                },
                |value| Evaluation::primitive(value, true),
            ),
        }
    }

    fn allocate_callable(
        &mut self,
        scope: Option<ScopeId>,
        environment: &mut Environment,
    ) -> Evaluation {
        let origin = scope.and_then(|scope| {
            self.heap_result(
                self.scope_instances
                    .capture(scope, self.scoping, self.budget),
            )
            .flatten()
        });
        self.allocate(environment, OwnData::callable(origin), true)
    }

    fn arguments(&mut self, arguments: &[Argument<'_>], environment: &mut Environment) {
        for argument in arguments {
            if let Argument::SpreadElement(spread) = argument {
                self.expression(&spread.argument, environment);
                self.invalidate(environment);
            } else if let Some(expression) = argument.as_expression() {
                self.expression(expression, environment);
            }
        }
    }

    fn declaration_symbol(
        &self,
        declarator: &VariableDeclarator<'_>,
        kind: VariableDeclarationKind,
    ) -> Option<CellId> {
        let symbol = match kind {
            VariableDeclarationKind::Var => self
                .bindings
                .var_initializer_target(self.scoping, declarator)?,
            VariableDeclarationKind::Let | VariableDeclarationKind::Const => {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    return None;
                };
                identifier.symbol_id.get()?
            }
            _ => return None,
        };
        self.cell_id(symbol)
    }

    fn declaration(
        &mut self,
        declaration: &VariableDeclaration<'_>,
        environment: &mut Environment,
    ) {
        for declarator in &declaration.declarations {
            let kind = declaration.kind;
            if kind == VariableDeclarationKind::Var && declarator.init.is_none() {
                // Instantiation hoists the binding. Executing a bare var
                // declaration never writes undefined to an existing cell.
                continue;
            }
            if !matches!(declarator.id, BindingPattern::BindingIdentifier(_))
                && matches!(
                    kind,
                    VariableDeclarationKind::Let
                        | VariableDeclarationKind::Const
                        | VariableDeclarationKind::Var
                )
            {
                if !self.destructuring_declaration(declarator, kind, environment) {
                    break;
                }
                continue;
            }
            let symbol = self.declaration_symbol(declarator, kind);
            if kind == VariableDeclarationKind::Var && symbol.is_none() {
                // ResolveBinding for var initialization precedes its RHS.
                // An unproved lookup may be observable even before GetValue.
                self.invalidate(environment);
            }
            let value = declarator.init.as_ref().map_or_else(
                || Evaluation::primitive(Value::Undefined, true),
                |init| self.expression(init, environment),
            );
            let Some(symbol) = symbol else {
                if !matches!(declarator.id, BindingPattern::BindingIdentifier(_)) {
                    self.unobserved(declarator.id.span());
                }
                self.invalidate(environment);
                continue;
            };
            if let Some(fact) = value.fact {
                if self
                    .heap_result(environment.insert(symbol, fact, self.budget))
                    .is_none()
                {
                    break;
                }
            } else if self
                .heap_result(environment.remove(symbol, self.budget))
                .is_none()
            {
                break;
            }
        }
    }

    /// A completed statement has no pending expression references. A
    /// completed lexical block additionally retires exactly its own cells;
    /// object identities can still be live through outer aliases.
    fn collect_heap(&mut self, environment: &mut Environment) -> bool {
        if let Err(failure) =
            environment.collect_if_needed(self.scope_instances.roots(), self.budget)
        {
            self.failure = Some(failure);
            self.invalidate(environment);
            return false;
        }
        true
    }

    fn statements(&mut self, statements: &[Statement<'_>], environment: &mut Environment) -> bool {
        if let (Some(first), Some(last)) = (statements.first(), statements.last()) {
            self.visited_lists
                .insert((first.span().start, last.span().end));
        }
        for statement in statements {
            if !self.statement(statement, environment) || !self.collect_heap(environment) {
                // An abrupt path has no normal successor, not an opaque effect.
                environment.clear();
                return false;
            }
        }
        true
    }

    /// Implicit disposal runs on leaving a resource-owning scope. Even if
    /// the returned value was already captured, a disposer can mutate its
    /// object graph or any other reachable binding.
    fn enter_resource_scope(&mut self, scope: Option<oxc_syntax::scope::ScopeId>) -> bool {
        let active = scope.is_some_and(|scope| self.bindings.scope_may_dispose(scope));
        self.pending_disposals += usize::from(active);
        active
    }

    fn leave_resource_scope(&mut self, active: bool, environment: &mut Environment) {
        if active {
            self.pending_disposals -= 1;
            self.invalidate(environment);
        }
    }

    fn refresh_iteration_scope(
        &mut self,
        statement: &ForStatement<'_>,
        environment: &mut Environment,
    ) -> Option<()> {
        if matches!(&statement.init,
            Some(ForStatementInit::VariableDeclaration(declaration))
                if declaration.kind == VariableDeclarationKind::Let)
        {
            let scope = statement.scope_id.get()?;
            let id = self.fresh_identity();
            let old = self.scope_instances.refresh(scope, id)?;
            self.heap_result(environment.copy_instance(old, id, self.budget))?;
        }
        Some(())
    }

    fn for_initializer(
        &mut self,
        statement: &ForStatement<'_>,
        environment: &mut Environment,
    ) -> Option<()> {
        if let Some(initializer) = &statement.init {
            match initializer {
                ForStatementInit::VariableDeclaration(declaration) => {
                    self.declaration(declaration, environment);
                }
                expression => {
                    self.expression(expression.as_expression()?, environment);
                }
            }
        }
        Some(())
    }

    fn consume_iteration(&mut self) -> Option<()> {
        let fuel = self.loop_fuel.as_mut()?;
        *fuel = fuel.checked_sub(1)?;
        self.heap_result(self.budget.consume(1))
    }

    fn simulate_for(
        &mut self,
        statement: &ForStatement<'_>,
        environment: &mut Environment,
    ) -> Option<bool> {
        let test = statement.test.as_ref()?;
        // A literal true test cannot reach a normal exit without a transfer.
        // Avoid spending the entire speculative execution budget on it.
        if eval(test).is_some_and(|value| value.truthy()) {
            return None;
        }
        if crate::control_flow::statement_has_loop_control(&statement.body) {
            return None;
        }
        self.for_initializer(statement, environment)?;
        self.refresh_iteration_scope(statement, environment)?;
        loop {
            self.consume_iteration()?;
            let condition = self.expression(test, environment);
            if !condition.fact.as_ref()?.truthy() {
                return Some(true);
            }
            let normal = self.statement(&statement.body, environment);
            if self.loop_failed {
                return None;
            }
            if !normal {
                // Direct transfers to the loop are excluded by the shape
                // proof; return/throw exits the enclosing activation.
                return Some(false);
            }
            self.refresh_iteration_scope(statement, environment)?;
            if let Some(update) = &statement.update {
                self.expression(update, environment);
            }
            if !self.collect_heap(environment) {
                return None;
            }
        }
    }

    /// Prove a bounded normal execution transaction, including nested loops.
    /// If any test or transfer is unproved, discard speculative observations
    /// as well as the speculative heap. A partial path is not a rewrite proof.
    fn bounded_for(&mut self, statement: &ForStatement<'_>, environment: &mut Environment) -> bool {
        let outermost = self.loop_fuel.is_none();
        if outermost {
            self.loop_fuel = Some(4096);
        }
        let mut candidate = environment.clone();
        let previous_reads = std::mem::take(&mut self.reads);
        let previous_lists = std::mem::take(&mut self.visited_lists);
        let previous_returns = self.return_frame.take();
        self.return_frame = previous_returns
            .as_ref()
            .map(activation::ReturnFrame::empty_like);
        let ticket = self.enter_instance(statement.scope_id.get(), &mut candidate);
        let disposes = self.enter_resource_scope(statement.scope_id.get());
        let result = if self.has_dispatch_shape(statement) {
            self.simulate_dispatch(statement, &mut candidate)
                .map(|()| true)
        } else {
            self.simulate_for(statement, &mut candidate)
        }
        .filter(|_| !self.loop_failed);
        self.leave_resource_scope(disposes, &mut candidate);
        let scope_exit = self.leave_instance(ticket, &mut candidate);
        let result = result.filter(|_| scope_exit);
        let loop_returns = std::mem::replace(&mut self.return_frame, previous_returns);
        let proven = result.is_some();
        let mut observations = std::mem::replace(&mut self.reads, previous_reads);
        let mut visited = std::mem::replace(&mut self.visited_lists, previous_lists);
        if outermost {
            self.loop_fuel = None;
            self.loop_failed = false;
        } else if !proven {
            // A successful inner iteration cannot publish observations if
            // another execution of the same inner loop was not proved.
            self.loop_failed = true;
        }
        if proven {
            if outermost
                && self
                    .heap_result(observations.discard_unobserved(&mut visited, self.budget))
                    .is_none()
            {
                return false;
            }
            self.reads.merge(observations);
            self.visited_lists.extend(visited);
            *environment = candidate;
            self.merge_loop_returns(loop_returns);
            result.unwrap_or(true)
        } else {
            self.invalidate(environment);
            self.unproved_loop_returns(statement);
            true
        }
    }

    fn block_statement(
        &mut self,
        block: &oxc_ast::ast::BlockStatement<'_>,
        environment: &mut Environment,
    ) -> bool {
        let ticket = self.enter_instance(block.scope_id.get(), environment);
        let disposes = self.enter_resource_scope(block.scope_id.get());
        let normal = self.statements(&block.body, environment);
        self.leave_resource_scope(disposes, environment);
        let scope_exit = self.leave_instance(ticket, environment);
        normal && scope_exit && self.collect_heap(environment)
    }

    fn statement(&mut self, statement: &Statement<'_>, environment: &mut Environment) -> bool {
        if !self.checkpoint() {
            return false;
        }
        match statement {
            Statement::VariableDeclaration(declaration) => {
                self.declaration(declaration, environment);
            }
            Statement::ExportDeclaration(export) => {
                if let Declaration::VariableDeclaration(declaration) = &export.declaration {
                    self.declaration(declaration, environment);
                } else {
                    self.unobserved(statement.span());
                    self.invalidate(environment);
                }
            }
            Statement::ExpressionStatement(statement) => {
                self.expression(&statement.expression, environment);
            }
            Statement::BlockStatement(block) => {
                return self.block_statement(block, environment);
            }
            Statement::ForStatement(statement) => {
                return self.bounded_for(statement, environment);
            }
            Statement::IfStatement(branch) => {
                let test = self.expression(&branch.test, environment);
                if let Some(value) = &test.fact {
                    return if value.truthy() {
                        self.statement(&branch.consequent, environment)
                    } else {
                        branch
                            .alternate
                            .as_ref()
                            .is_none_or(|alternate| self.statement(alternate, environment))
                    };
                }
                let mut other = environment.clone();
                let first_new = self.next_identity;
                let previous_floor = environment.protect_before(first_new);
                other.protect_before(first_new);
                let left = self.statement(&branch.consequent, environment);
                let right = branch
                    .alternate
                    .as_ref()
                    .is_none_or(|alternate| self.statement(alternate, &mut other));
                environment.protect_before(previous_floor);
                other.protect_before(previous_floor);
                match (left, right) {
                    (true, true) => {
                        if !self.join_heap(environment, &other, first_new) {
                            return false;
                        }
                    }
                    (false, true) => *environment = other,
                    (true, false) => {}
                    (false, false) => return false,
                }
            }
            Statement::ReturnStatement(ret) => {
                let value = ret
                    .argument
                    .as_ref()
                    .map_or(Some(Fact::Primitive(Value::Undefined)), |argument| {
                        self.expression(argument, environment).fact
                    });
                self.record_return(value, environment);
                return false;
            }
            Statement::ThrowStatement(throw) => {
                self.expression(&throw.argument, environment);
                return false;
            }
            Statement::BreakStatement(_) | Statement::ContinueStatement(_) => return false,
            Statement::FunctionDeclaration(function)
                if self
                    .bindings
                    .inert_function_declaration(self.scoping, function) => {}
            Statement::EmptyStatement(_) => {}
            _ => {
                self.unobserved(statement.span());
                self.unproved_statement_returns(statement);
                self.invalidate(environment);
            }
        }
        true
    }
}

impl<'a> Visit<'a> for Analyzer<'_, 'a> {
    fn enter_scope(&mut self, _: ScopeFlags, scope: &std::cell::Cell<Option<ScopeId>>) {
        let ticket = scope.get().map(|scope| {
            let id = self.fresh_identity();
            self.scope_instances.enter(scope, id)
        });
        self.lexical_scopes.push(ticket);
    }

    fn leave_scope(&mut self) {
        if let Some(Some(ticket)) = self.lexical_scopes.pop() {
            let _ = self.scope_instances.leave(&ticket);
        }
    }

    fn visit_statements(&mut self, statements: &oxc_allocator::Vec<'a, Statement<'a>>) {
        self.independent_statements(statements, true);
        walk::walk_statements(self, statements);
    }

    fn visit_switch_case(&mut self, case: &oxc_ast::ast::SwitchCase<'a>) {
        if let Some(test) = &case.test {
            self.visit_expression(test);
        }
        // The case test and previous cases may already have modified the
        // shared switch environment. This is not an instantiation boundary.
        self.independent_statements(&case.consequent, false);
        walk::walk_statements(self, &case.consequent);
    }
}

impl Analyzer<'_, '_> {
    fn independent_statements(&mut self, statements: &[Statement<'_>], at_entry: bool) {
        if !self.checkpoint() {
            return;
        }
        let (Some(first), Some(last)) = (statements.first(), statements.last()) else {
            return;
        };
        if self
            .visited_lists
            .contains(&(first.span().start, last.span().end))
        {
            return;
        }
        let mut environment = Environment::new();
        if at_entry {
            if let Some(scope) = self
                .lexical_scopes
                .last()
                .and_then(Option::as_ref)
                .map(scope_instances::ScopeTicket::scope)
            {
                if self
                    .initialize_hoisted_callables(scope, &mut environment)
                    .is_none()
                {
                    return;
                }
            }
        }
        self.statements(statements, &mut environment);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;

    fn reads(source: &str) -> Result<Vec<(String, String)>, BudgetExceeded> {
        observed(source, false)
    }

    fn observed(source: &str, comparisons: bool) -> Result<Vec<(String, String)>, BudgetExceeded> {
        let allocator = Allocator::default();
        let program = crate::parse_as(&allocator, source, SourceType::cjs())
            .unwrap_or_else(|| unreachable!("{source}"));
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        assert!(semantic.diagnostics.is_empty(), "{source}");
        let scoping = semantic.semantic.scoping();
        let bindings = BindingFacts::analyze(&program, scoping);
        let pure_functions = crate::collect_pure_functions(&program, scoping, &bindings);
        let analysis = FreshDataReads::analyze(
            &program,
            scoping,
            &bindings,
            &pure_functions,
            &WorkBudget::unlimited("fresh-data-tests"),
        )?;
        let observations = if comparisons {
            analysis.comparisons
        } else {
            analysis.members
        };
        let mut facts = observations.values.into_iter().collect::<Vec<_>>();
        facts.sort_by_key(|(span, _)| *span);
        Ok(facts
            .into_iter()
            .filter_map(|((start, end), observation)| {
                let Observation::Exact(value) = observation else {
                    return None;
                };
                Some((
                    source.get(start as usize..end as usize)?.to_owned(),
                    value.render()?,
                ))
            })
            .collect())
    }

    #[test]
    fn declarative_var_initializers_preserve_reaching_heap_facts() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            (
                "function f(){var a=[7];var b=a;b[0]=9;return a[0];}",
                vec![("a[0]", "9")],
            ),
            (
                "function f(){var a=[7];var a;return a[0];}",
                vec![("a[0]", "7")],
            ),
            (
                "function f(){var a=[7];{var b=a;}b[0]++;return a[0];}",
                vec![("a[0]", "8")],
            ),
            (
                "function f(){var a=[1];for(var i=0;i<2;i++){a[0]++;}return a[0];}",
                vec![("a[0]", "3")],
            ),
            (
                "function f(p){'use strict';var p=[7];return p[0];}",
                vec![("p[0]", "7")],
            ),
            ("function f(p){var p=[7];return p[0];}", vec![("p[0]", "7")]),
            (
                "function f(p){var p=[7];arguments[0]=[9];return p[0];}",
                vec![],
            ),
            ("function f(p){p=[7];return p[0];}", vec![("p[0]", "7")]),
            ("function f(p){p=[7];arguments[0]=[9];return p[0];}", vec![]),
            (
                "function f(){var a=[7];with(o){var a=[9];a[0];}return a[0];}",
                vec![],
            ),
            (
                "function f(){var a=[9];try{throw [];}catch(a){var a=[7];a[0];}return a[0];}",
                vec![("a[0]", "7")],
            ),
            ("var a=[7];a[0];", vec![]),
        ] {
            let expected = expected
                .into_iter()
                .map(|(s, v)| (s.to_owned(), v.to_owned()))
                .collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn immediate_activations_preserve_reaching_allocations() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let a=(()=>[7])();a[0];", vec![("a[0]", "7")]),
            ("let a=(()=>{let x=[7];return x;})();a[0];", vec![("a[0]", "7")]),
            ("let a=(function(){var a=[1,2];for(var i=0;i<2;i++)a[i]+=2;return a;})();a[0];a[1];", vec![("a[0]", "3"),("a[1]", "4")]),
            ("let a=[1];let b=(x=>{x[0]=7;return x;})(a);a[0];b[0];", vec![("a[0]", "7"),("b[0]", "7")]),
            ("let a=(()=>{let a=[7];for(let i=0;i<2;i++){if(i===1)return a;}return [9];})();a[0];", vec![("a[0]", "7")]),
            ("function f(flag){let a=[7];let b=(()=>{if(flag)return a;return a;})();return b[0];}", vec![("b[0]", "7")]),
            ("function f(flag){let a=[7];let b=(()=>{if(flag)throw 0;return a;})();return b[0];}", vec![("b[0]", "7")]),
            ("let a=(()=>{effect();return [7];})();a[0];", vec![("a[0]", "7")]),
            ("let a=(function(){effect();return [7];})();a[0];", vec![]),
            ("let a=(()=>{try{return [7];}finally{}return [9];})();a[0];", vec![]),
            ("let a=[7];let old=a;a[(()=>{a=[9];return 0;})()]=11;old[0];a[0];", vec![("old[0]", "11"),("a[0]", "9")]),
            ("let a=[[7],(()=>{let b=[8];return b;})()];a[0][0];a[1][0];", vec![("a[0][0]", "7"),("a[1][0]", "8")]),
            ("let result=[0,0];for(let i=0;i<2;i++){result[i]=(x=>{let a=[x];return a[0];})(i);}result[0];result[1];", vec![("result[0]", "0"),("result[1]", "1")]),
            // Do not erase the invocation in the receiver of a member read.
            ("let outer=[7];let escaped=(function(){var arguments;return [arguments,outer[0]];})();outer[0]=9;escaped[0].callee()[1];", vec![]),
            ("let outer=[7];let escaped=(function(){var arguments;return [arguments,outer[0]];})();outer[0]=9;let result=escaped[0].callee();result[1];", vec![("result[1]", "9")]),
        ] {
            let expected = expected.into_iter().map(|(source, value)| (source.to_owned(), value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        let aliases = "let a=[1];let b=(x=>x)(a);a===b;";
        assert_eq!(
            observed(aliases, true)?,
            vec![("a===b".into(), "true".into())]
        );
        Ok(())
    }

    #[test]
    fn named_activations_preserve_heap_at_each_call_without_specializing_bodies(
    ) -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("function outer(){function build(v){let a=[v];return a;}let r=build(7);return r[0];}", vec![("r[0]", "7")]),
            ("function outer(){let a=[7];function mutate(x){x[0]=9;return x;}let b=mutate(a);return a[0]+b[0];}", vec![("a[0]", "9"), ("b[0]", "9")]),
            ("function outer(){let a=[7];function mutate(){a[0]=9;}mutate();return a[0];}", vec![("a[0]", "9")]),
            ("function outer(){let a=[0,0];function write(i){a[i]=i+7;}for(let i=0;i<2;i++){write(i);}return a[0]+a[1];}", vec![("a[0]", "7"), ("a[1]", "8")]),
            ("function outer(){function pick(v){let a=[v];return a[0];}let b=[pick(7),pick(9)];return b[0]+b[1];}", vec![("b[0]", "7"), ("b[1]", "9")]),
            ("function outer(){function pick(v){let a=[v];return a[0];}let b=[pick(7)];let c=b[0];let alias=pick;return alias(9)+c;}", vec![("b[0]", "7")]),
            ("function outer(flag){function build(){if(flag)return [7];return [7];}let b=build();return b[0];}", vec![("b[0]", "7")]),
            ("function outer(flag){function build(){if(flag)return [7];return [9];}let b=build();return b[0];}", vec![]),
            ("function outer(){let a=[7];function g(){a[0]=9;return a;}function f(){return g();}let b=f();return b[0]+a[0];}", vec![("b[0]", "9"), ("a[0]", "9")]),
            ("function outer(){let a=build(7);function build(x){return [x];}return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){function f(a,n){if(n)f(a,n-1);a[0]++;return a;}let a=[0];f(a,2);return a[0];}", vec![("a[0]", "3")]),
            ("function outer(){function build(){effect();return [7];}let a=build();return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){function f(x,x){return [x];}let a=f(1,7);return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){function f(x){arguments[0]=9;return [x];}let a=f(7);return a[0];}", vec![("a[0]", "9")]),
            ("function outer(){function f(p){function p(){return 9}return [p];}let a=f(7);return a[0];}", vec![]),
            ("function outer(){function f(){let x=[7];using r={[Symbol.dispose](){x[0]=9;}};return x;}let a=f();return a[0];}", vec![]),
            ("function outer(){'use strict';{let a=build(7);function build(x){return [x];}return a[0];}}", vec![("a[0]", "7")]),
            ("function outer(flag){function build(){if(flag)throw 0;return [7];}let a=build();return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){function f(){return [7];}eval('f=()=>[9]');let a=f();return a[0];}", vec![]),
            ("function f(){return [7];}globalThis.f=()=>[9];let a=f();a[0];", vec![]),
            // An unknown first property read may execute a getter and invalidate b.
            ("function outer(){let a=[7];function f(){effect();return [9];}let b=f();return a[0]+b[0];}", vec![]),
            ("function outer(){let a=[7];function f(){effect();return [9];}let b=f();return b[0]+a[0];}", vec![("b[0]", "9")]),
            ("function outer(){function f(v){if(v)return [7];return [9];}let a=f(1);let b=f(0);return a[0]+b[0];}", vec![("a[0]", "7"), ("b[0]", "9")]),
        ] {
            let expected = expected.into_iter().map(|(source, value)| (source.to_owned(), value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        let alias = "function outer(){function f(x){return x;}let a=[7];let b=f(a);return a===b;}";
        assert_eq!(
            observed(alias, true)?,
            vec![("a===b".into(), "true".into())]
        );
        Ok(())
    }

    #[test]
    fn callable_values_keep_identity_and_live_lexical_captures() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let f=x=>[x];let a=f(7);a[0];", vec![("a[0]", "7")]),
            (
                "let f=function(x){return [x];};let alias=f;let a=alias(7);a[0];",
                vec![("a[0]", "7")],
            ),
            (
                "let f=function inner(x){return [x];};let a=f(7);a[0];",
                vec![("a[0]", "7")],
            ),
            (
                "let a=[7];let f=()=>{a[0]=9;return a;};let b=f();a[0];b[0];",
                vec![("a[0]", "9"), ("b[0]", "9")],
            ),
            (
                "let a=[7];let f=()=>a;a=[9];let b=f();b[0];",
                vec![("b[0]", "9")],
            ),
            ("let fs=[x=>[x]];let a=fs[0](7);a[0];", vec![("a[0]", "7")]),
            (
                "let f=x=>[x];let a=f((f=x=>[9],7));a[0];",
                vec![("a[0]", "7")],
            ),
            (
                "let f=x=>[x];let a=f(7);let b=f(9);a[0];b[0];",
                vec![("a[0]", "7"), ("b[0]", "9")],
            ),
            (
                "let a=[7];let f=()=>[a[0]];let b=f();a[0]=9;let c=f();b[0];c[0];",
                vec![("b[0]", "7"), ("c[0]", "9")],
            ),
            (
                "let f;{let x=7;f=()=>[x];}let a=f();a[0];",
                vec![("a[0]", "7")],
            ),
            (
                "let f;for(let i=0;i<2;i++){if(i===0)f=()=>[i];else{let a=f();a[0];}}",
                vec![("a[0]", "0")],
            ),
            (
                "let a;for(let i=0;i<2;i++){let f=()=>[i];a=f();}a[0];",
                vec![("a[0]", "1")],
            ),
            (
                "let f;for(let i=0;i<2;i++)if(i===0)f=()=>[i];else{let a=f();a[0];}",
                vec![("a[0]", "0")],
            ),
            (
                "let a;for(let i=0,f=()=>[i];i<1;i++){a=f();}a[0];",
                vec![("a[0]", "0")],
            ),
            (
                "let f;let a;for(let i=0;i<2;f=()=>[i],i++){if(i===1)a=f();}a[0];",
                vec![("a[0]", "1")],
            ),
            (
                "let a;for(let i=0;i<2;i++){let x=i;let f=()=>[x];a=f();}a[0];",
                vec![("a[0]", "1")],
            ),
            (
                "let f=(()=>{let x=7;return ()=>[x];})();let a=f();a[0];",
                vec![("a[0]", "7")],
            ),
            (
                "let a=[7];let f=()=>{unknown();return [9];};let b=f();b[0];a[0];",
                vec![("b[0]", "9")],
            ),
            (
                "let f=()=>[7];let a=f;f=()=>[9];let b=a();b[0];",
                vec![("b[0]", "7")],
            ),
            (
                "let f=()=>[7];let a=[typeof f];a[0];",
                vec![("a[0]", "\"function\"")],
            ),
            (
                "let f=()=>[7];let a=[typeof {}];a[0];",
                vec![("a[0]", "\"object\"")],
            ),
            (
                "let f=function(){};let a=[7];delete f.prototype;a[0];",
                vec![],
            ),
            ("let f=()=>[7];let a={...f,x:7};a.x;", vec![("a.x", "7")]),
            (
                "let f=()=>[7];let a={f};let b=a.f();b[0];",
                vec![("b[0]", "7")],
            ),
            (
                "let a=[7];let f=()=>[a[0]];let b=f((a[0]=9,0));b[0];",
                vec![("b[0]", "9")],
            ),
        ] {
            let expected = expected
                .into_iter()
                .map(|(source, value)| (source.to_owned(), value.to_owned()))
                .collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn callable_comparisons_use_allocation_identity() -> Result<(), BudgetExceeded> {
        let source = "let f=()=>7;let g=f;let h=()=>7;f===g;f===h;[f][0]===f;";
        assert_eq!(
            observed(source, true)?,
            vec![
                ("f===g".into(), "true".into()),
                ("f===h".into(), "false".into()),
                ("[f][0]===f".into(), "true".into()),
            ]
        );
        Ok(())
    }

    #[test]
    fn arguments_objects_retain_formal_cell_identity() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let f=function(a){arguments[0]=9;return [a]};let r=f(7);r[0];", vec![("r[0]", "9")]),
            ("let f=function(a){a=9;return [arguments[0]]};let r=f(7);r[0];", vec![("r[0]", "9")]),
            ("let f=function(a,a){a=9;return arguments};let r=f(7,8);r[0];r[1];", vec![("r[0]", "7"),("r[1]", "9")]),
            ("let f=function(a,a){a=9;return arguments};let r=f(7);r[0];", vec![("r[0]", "7")]),
            ("let f=function(a){delete arguments[0];a=9;return [a]};let r=f(7);r[0];", vec![("r[0]", "9")]),
            ("let f=function(a){'use strict';arguments[0]=9;return [a,arguments[0]]};let r=f(7);r[0];r[1];", vec![("r[0]", "7"),("r[1]", "9")]),
            ("let f=function(a=1){a=9;return arguments};let r=f(7);r[0];", vec![("r[0]", "7")]),
            ("let f=function(a,...rest){a=9;return arguments};let r=f(7,8);r[0];r[1];r.length;", vec![("r[0]", "7"),("r[1]", "8"),("r.length", "2")]),
            ("let f=function(a){return [arguments,()=>[a]]};let p=f(7);p[0][0]=9;let r=p[1]();r[0];", vec![("r[0]", "9")]),
            ("let f=function(a){return [arguments,()=>[a]]};let p=f(7);for(let i=0;i<256;i++){let x=[i];}p[0][0]=9;let r=p[1]();r[0];", vec![("r[0]", "9")]),
            ("let f=function(a){let b={__proto__: arguments};b[0]=9;return [a,b[0]]};let r=f(7);r[0];r[1];", vec![("r[0]", "7"),("r[1]", "9")]),
            ("let f=function(a){a=9;return {__proto__:null,...arguments}};let r=f(7);r[0];r.length;r.callee;", vec![("r[0]", "9"),("r.length", "void 0"),("r.callee", "void 0")]),
            ("let f=function(a){let b={...arguments};a=9;return b};let r=f(7);r[0];", vec![("r[0]", "7")]),
            ("let f=function(a){let {0:x,...r}=arguments;return {__proto__:null,...r}};let r=f(7,8);r[0];r[1];r.length;", vec![("r[0]", "void 0"),("r[1]", "8"),("r.length", "void 0")]),
            ("let f=function(a){var arguments;return arguments};let r=f(7);r[0];", vec![("r[0]", "7")]),
            ("let f=function(a){let b=arguments;arguments=[9];b[0]=8;return [a,arguments[0]]};let r=f(7);r[0];r[1];", vec![("r[0]", "8"),("r[1]", "9")]),
            ("let f=function(a){return ()=>arguments};let g=f(7);let r=g();r[0];", vec![("r[0]", "7")]),
            ("let f=function(a,g=()=>arguments){var arguments=[9];return g};let g=f(7);let r=g();r[0];", vec![("r[0]", "7")]),
            ("let f=function(arguments){return arguments};let r=f([7]);r[0];", vec![("r[0]", "7")]),
            ("let f=function(a){return arguments.callee};let g=f(7);let r=[g===f];r[0];", vec![("r[0]", "true")]),
        ] {
            let expected = expected.into_iter().map(|(source,value)| (source.to_owned(),value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn ordered_parameter_initialization_and_rest_arrays() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            (
                "let f=(a=7,b=a+2)=>[a,b];let r=f();r[0];r[1];",
                vec![("r[0]", "7"), ("r[1]", "9")],
            ),
            (
                "let f=(a=7)=>[a];let r=f(void 0);r[0];",
                vec![("r[0]", "7")],
            ),
            (
                "let f=(a=7)=>[a];let r=f(null);r[0];",
                vec![("r[0]", "null")],
            ),
            (
                "let n=0;let f=(a=(n+=1),b=(n+=2))=>[a,b,n];let r=f();r[0];r[1];r[2];",
                vec![("r[0]", "1"), ("r[1]", "3"), ("r[2]", "3")],
            ),
            (
                "let n=0;let f=(a=(n+=1),b=(n+=2))=>[a,b,n];let r=f(7,9);r[0];r[1];r[2];",
                vec![("r[0]", "7"), ("r[1]", "9"), ("r[2]", "0")],
            ),
            (
                "function outer(x){let a=[7];let f=(v=(a[0]=9))=>[v];f(x);return a[0];}",
                vec![],
            ),
            (
                "function outer(x){let a=[7];let f=(v=(a[0]=7))=>[v];f(x);return a[0];}",
                vec![("a[0]", "7")],
            ),
            (
                "let f=(...a)=>a;let b=f(7,9);b[0];b[1];b.length;",
                vec![("b[0]", "7"), ("b[1]", "9"), ("b.length", "2")],
            ),
            (
                "let f=(a,...rest)=>[a,rest.length,rest[0]];let r=f(7,9);r[0];r[1];r[2];",
                vec![("r[0]", "7"), ("r[1]", "1"), ("r[2]", "9")],
            ),
            (
                "let f=(...a)=>a;let b=f();b.length;",
                vec![("b.length", "0")],
            ),
            (
                "let f=(a=7,...rest)=>[a,rest.length];let r=f(void 0,9);r[0];r[1];",
                vec![("r[0]", "7"), ("r[1]", "1")],
            ),
            (
                "let o={x:7,f:function(a=this.x){return [a]}};let r=o.f();r[0];",
                vec![("r[0]", "7")],
            ),
            (
                "let f=(a=7)=>{var x;return [x,a]};let r=f();r[0];r[1];",
                vec![("r[0]", "void 0"), ("r[1]", "7")],
            ),
        ] {
            let expected = expected
                .into_iter()
                .map(|(source, value)| (source.to_owned(), value.to_owned()))
                .collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn defaults_capture_parameter_cells_before_body_instantiation() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let f=(a=7,g=()=>[a])=>{var a=9;return g};let r=f()();r[0];", vec![("r[0]", "7")]),
            ("let f=(a=7,g=()=>[a])=>{a=9;return g};let r=f()();r[0];", vec![("r[0]", "9")]),
            ("let f=(g=()=>[a],a=7)=>{var a=9;return g};let r=f()();r[0];", vec![("r[0]", "7")]),
            ("let f=(a=7,g=()=>[a])=>{var a;return [a,g]};let p=f();let r=p[1]();p[0];r[0];", vec![("p[0]", "7"),("r[0]", "7")]),
            ("let f=(a=7,g=()=>[a])=>{var a;let h=()=>[a];a=9;return [g,h]};let p=f();let r=p[0](),s=p[1]();r[0];s[0];", vec![("r[0]", "7"),("s[0]", "9")]),
            ("let f=(a=7,g=()=>[a])=>{if(false){try{}catch(a){var a=11}}a=9;return g;};let r=f()();r[0];", vec![("r[0]", "7")]),
            ("let f=function(a=7,g=()=>[a]){function a(){return 9}return g;};let r=f()();r[0];", vec![("r[0]", "7")]),
            ("let f=function(a=7,g=()=>[a]){function a(){return [9]}let p=a();return [g,p];};let p=f();let r=p[0](),s=p[1];r[0];s[0];", vec![("r[0]", "7"),("s[0]", "9")]),
            ("let a=7;let f=(g=()=>[a])=>{var a=9;return g};let r=f()();r[0];", vec![("r[0]", "7")]),
            ("let f=(a=7,g=()=>[a])=>{var a=9;return g};let g=f(),h=f(11);let r=g(),s=h();r[0];s[0];", vec![("r[0]", "7"),("s[0]", "11")]),
            ("let f=(a=7,g=()=>[a])=>{var a=9;return g};let g=f();for(let i=0;i<256;i++){let a=[i];}let r=g();r[0];", vec![("r[0]", "7")]),
            ("let o={x:7,f:function(g=()=>[this.x]){return g}};let r=o.f()();r[0];", vec![("r[0]", "7")]),
        ] {
            let expected = expected.into_iter().map(|(source,value)| (source.to_owned(),value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn object_binding_patterns_share_heap_lookup_and_copy_semantics() -> Result<(), BudgetExceeded>
    {
        for (source, expected) in [
            (
                "let f=({x,y:z=9})=>[x,z];let r=f({x:7,y:void 0});r[0];r[1];",
                vec![("r[0]", "7"), ("r[1]", "9")],
            ),
            (
                "let f=({x:{y=7}})=>[y];let r=f({x:{y:void 0}});r[0];",
                vec![("r[0]", "7")],
            ),
            (
                "let f=({x,...rest})=>[x,rest.y];let r=f({x:7,y:9});r[0];r[1];",
                vec![("r[0]", "7"), ("r[1]", "9")],
            ),
            (
                "let f=({x,...rest})=>rest;let r=f({x:7,y:9});r.y;",
                vec![("r.y", "9")],
            ),
            (
                "let f=({x})=>{var x;return [x]};let r=f({x:7});r[0];",
                vec![("r[0]", "7")],
            ),
            (
                "let f=({['x']:a,b=a})=>[a,b];let r=f({x:7,b:void 0});r[0];r[1];",
                vec![("r[0]", "7"), ("r[1]", "7")],
            ),
            (
                "let a=[7];let f=({x})=>[x];f({get x(){a[0]=9;return 7}});a[0];",
                vec![],
            ),
            ("let f=([x])=>[x];let r=f([7]);r[0];", vec![]),
            (
                "let {x,y:z=9}={x:7,y:void 0};let a=[x,z];a[0];a[1];",
                vec![("a[0]", "7"), ("a[1]", "9")],
            ),
            ("const {x,...r}={x:7,y:9};r.y;", vec![("r.y", "9")]),
            (
                "function outer(){var {x,...r}={x:7,y:9};return r.y;}",
                vec![("r.y", "9")],
            ),
            ("var {x}={x: 7};let r=[x];r[0];", vec![]),
            (
                "let a={x:7,y:9};let {x:v,...r}=a;let b=[v,r.y];b[0];b[1];",
                vec![("r.y", "9"), ("b[0]", "7"), ("b[1]", "9")],
            ),
        ] {
            let expected = expected
                .into_iter()
                .map(|(source, value)| (source.to_owned(), value.to_owned()))
                .collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn last_hoisted_declaration_instantiates_once() -> Result<(), BudgetExceeded> {
        let source = "function outer(){let g=f;function f(){return [7]}function f(){return [9]}let r=g();return r[0];}";
        assert_eq!(reads(source)?, vec![("r[0]".into(), "9".into())]);
        Ok(())
    }

    #[test]
    fn alternative_call_targets_join_return_values_and_effects() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("function outer(flag){let f=flag?()=>[7]:()=>[7];let a=f();return a[0];}", vec![("a[0]", "7")]),
            ("function outer(flag){let f=flag?()=>[7]:()=>[9];let a=f();return a[0];}", vec![]),
            ("function outer(flag){let a=[0];let f=flag?()=>{a[0]=7}:()=>{a[0]=7};f();return a[0];}", vec![("a[0]", "7")]),
            ("function outer(flag){let a=[0];let f=flag?()=>{a[0]=7}:()=>{a[0]=9};f();return a[0];}", vec![]),
            ("function outer(flag){let a=[0];let f=flag?()=>{a[0]=7}:()=>{};f();return a[0];}", vec![]),
            ("function outer(flag){let f=flag?x=>[x]:x=>[x];let n=0;let a=f(++n);let b=[n];return a[0]+b[0];}", vec![("a[0]", "1"),("b[0]", "1")]),
            ("function outer(flag){let a=[7];let f=flag?()=>a:()=>a;let b=f();b[0]=9;return a[0];}", vec![("a[0]", "9")]),
            ("function outer(flag){let make=x=>()=>[x];let f=flag?make(7):make(7);let a=f();return a[0];}", vec![("a[0]", "7")]),
            ("function outer(flag){let make=x=>()=>[x];let f=flag?make(7):make(9);let a=f();return a[0];}", vec![]),
            ("function outer(flag){let f=flag?()=>[7]:()=>{unknown();return [7]};let a=f();return a[0];}", vec![("a[0]", "7")]),
            ("function outer(flag){let a=[7];let f=flag?()=>{}:()=>{unknown()};f();return a[0];}", vec![]),
            ("function outer(flag){let a=[7];let f=flag?()=>a:{};let b=f();return b[0];}", vec![]),
            ("function outer(flag){let o={x:7,f:flag?function(){return [this.x]}:function(){return [this.x]}};let a=o.f();return a[0];}", vec![("a[0]", "7")]),
            ("function outer(flag){let f=flag?()=>[7]:()=>[7];let a=f((f=()=>[9],0));return a[0];}", vec![("a[0]", "7")]),
            ("function outer(flag){let make=()=>{let a=[7];return ()=>a;};let f=flag?make():make();let a=f();return a[0];}", vec![("a[0]", "7")]),
            ("function outer(flag){let a=[7];let f=flag?()=>{a[0]=9;return a}:()=>{a[0]=9;return a};let b=f();return a[0]+b[0];}", vec![("a[0]", "9"),("b[0]", "9")]),
        ] {
            let expected = expected.into_iter().map(|(source,value)| (source.to_owned(),value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn alternative_call_targets_preserve_allocation_identity() -> Result<(), BudgetExceeded> {
        let source =
            "function outer(flag){let a=[7];let f=flag?()=>a:()=>a;let b=f();return a===b;}";
        assert_eq!(
            observed(source, true)?,
            vec![("a===b".into(), "true".into())]
        );
        let source =
            "function outer(flag){let f=flag?()=>[7]:()=>[7];let a=f(),b=f();return a===b;}";
        assert_eq!(
            observed(source, true)?,
            vec![("a===b".into(), "false".into())]
        );
        Ok(())
    }

    #[test]
    fn receiver_bindings_follow_ordered_call_references() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let o={x:7,f:function(){return [this.x]}};let a=o.f();a[0];", vec![("a[0]", "7")]),
            ("let o={x:7,f(){return [this.x]}};let a=o.f();a[0];", vec![("a[0]", "7")]),
            ("let o={x:7,f(){this.x++;return this;}};let a=o.f();a.x;o.x;", vec![("a.x", "8"),("o.x", "8")]),
            ("let o={x:7,f(){return [this.x]}};let a=o.f((o={x: 9},0));a[0];", vec![("a[0]", "7")]),
            ("let o={x:7,f(){return [this.x]}};let a=o[(o={x: 9},'f')]();a[0];", vec![("a[0]", "7")]),
            ("let o={x:7,f(){return [this.x]}};let a=(o.f)();a[0];", vec![("a[0]", "7")]),
            ("let f=function(){'use strict';return [this===void 0]};let a=f();a[0];", vec![("a[0]", "true")]),
            ("let o={x:7,f(){'use strict';return [this===void 0]}};let a=(0,o.f)();a[0];", vec![("a[0]", "true")]),
            ("let o={x:7,f(){return [this.x]}};let a=(0,o.f)();a[0];", vec![]),
            ("let o={x:7,f(){return [this.x]}};let p={x:9,f:o.f};let a=o.f(),b=p.f();a[0];b[0];", vec![("a[0]", "7"),("b[0]", "9")]),
            ("let o={x:7,f(){return [this.x]}};let a=o.f((o.x=9,0));a[0];", vec![("a[0]", "9")]),
            ("let o={x:7,f(){return [this.x]}};let a=o.f(unknown());a[0];", vec![]),
            ("let o={x:7,f(){'use strict';let g=function(){return [this===void 0]};return g();}};let a=o.f();a[0];", vec![("a[0]", "true")]),
        ] {
            let expected = expected.into_iter().map(|(source, value)| (source.to_owned(),value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn escaped_arrows_keep_lexical_receivers_not_call_receivers() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let o={x:7,f(){return ()=>[this.x]}};let g=o.f();o.x=9;let a=g();a[0];", vec![("a[0]", "9")]),
            ("let o={x:7,f(){return {x:9,g:()=>[this.x]}}};let p=o.f();let a=p.g();a[0];", vec![("a[0]", "7")]),
            ("let o={x:7,f(){return ()=>[this.x]}};let p={x:9,f:o.f};let g=o.f(),h=p.f();let a=g(),b=h();a[0];b[0];", vec![("a[0]", "7"),("b[0]", "9")]),
            ("let o={x:7,f(){return ()=>[this.x]}};let g=o.f();o={x: 9};for(let i=0;i<256;i++){let a=[i];}let a=g();a[0];", vec![("a[0]", "7")]),
            ("let o={x:7,f(){return [()=>this.x,()=>{this.x=9}]}};let p=o.f();p[1]();let a=[p[0]()];a[0];", vec![("a[0]", "9")]),
            ("let o={x:7,f(){return ()=>[this.x]}};let g=o.f();unknown(g);let a=g();a[0];", vec![]),
            ("let o={x:7,f:()=>[this.x]};let a=o.f();a[0];", vec![]),
        ] {
            let expected = expected.into_iter().map(|(source,value)| (source.to_owned(), value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn hoisted_callable_cells_follow_aliases_and_declaration_instances(
    ) -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("function outer(){let f=make;function make(x){return [x];}let a=f(7);return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){function make(){let x=7;function f(){return [x++];}return f;}let f=make();let a=f(),b=f();return a[0]+b[0];}", vec![("a[0]", "7"), ("b[0]", "8")]),
            ("function outer(){function f(){return [7]}let old=f;f=()=>[9];let a=old(),b=f();return a[0]+b[0];}", vec![("a[0]", "7"), ("b[0]", "9")]),
            ("function outer(){let a=f();function f(){return [7];}return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){let a=[null];{ 'use strict'; }function f(){return [7];}a[0]=f;let b=a[0]();return b[0];}", vec![("b[0]", "7")]),
            ("function outer(){'use strict';let f;{let x=7;f=inner;function inner(){return [x];}}let a=f();return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){'use strict';let fs=[null,null];for(let i=0;i<2;i++){fs[i]=f;function f(){return [i];}}let a=fs[0](),b=fs[1]();return a[0]+b[0];}", vec![("a[0]", "0"),("b[0]", "1")]),
            ("function outer(){function f(){return [7];}let g=f;let a=g((f=()=>[9],0));return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){function f(){return [7];}let g=f;unknown();let a=g();return a[0];}", vec![]),
            ("function outer(n){'use strict';switch(n){case 0:f=()=>[9];case 1:let a=f();return a[0];function f(){return [7];}}}", vec![]),
            ("function outer(){function f(){return [7];}f=()=>[9];function g(){return f();}let a=g();return a[0];}", vec![("a[0]", "9")]),
            ("function outer(){function f(){return [7];}let a=f((f=()=>[9],0));let b=f();return a[0]+b[0];}", vec![("a[0]", "7"),("b[0]", "9")]),
        ] {
            let expected = expected.into_iter().map(|(source, value)| (source.to_owned(), value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn hoisted_function_identity_is_not_recreated_after_effects() -> Result<(), BudgetExceeded> {
        let source = "function outer(){function f(){}let g=f;f===g;f===(unknown(),f);}";
        assert_eq!(
            observed(source, true)?,
            vec![("f===g".into(), "true".into())]
        );
        let source = "function outer(){function make(){function f(){}return f;}let a=make(),b=make();a===b;}";
        assert_eq!(
            observed(source, true)?,
            vec![("a===b".into(), "false".into())]
        );
        Ok(())
    }

    #[test]
    fn escaped_closures_retain_distinct_and_shared_cells() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let make=x=>()=>[x];let f=make(7),g=make(9);let a=f(),b=g();a[0];b[0];", vec![("a[0]", "7"), ("b[0]", "9")]),
            ("let make=()=>{let x=0;return [()=>[x++],()=>[x]]};let pair=make();let a=pair[0](),b=pair[1]();a[0];b[0];", vec![("a[0]", "0"), ("b[0]", "1")]),
            ("let fs=[null,null,null];for(let i=0;i<3;i++)fs[i]=()=>[i];let a=fs[0](),b=fs[1](),c=fs[2]();a[0];b[0];c[0];", vec![("a[0]", "0"), ("b[0]", "1"), ("c[0]", "2")]),
            ("function outer(){let fs=[null,null,null];for(var i=0;i<3;i++)fs[i]=()=>[i];let a=fs[0](),b=fs[1](),c=fs[2]();return a[0]+b[0]+c[0];}", vec![("a[0]", "3"), ("b[0]", "3"), ("c[0]", "3")]),
            ("let make=()=>{let a=[7];return ()=>[a[0]++];};let f=make();let g=make();let a=f(),b=g(),c=f();a[0];b[0];c[0];", vec![("a[0]", "7"),("b[0]", "7"),("c[0]", "8")]),
            ("let f=()=>{let x=[7];return ()=>x;};let g=f();for(let i=0;i<256;i++){let garbage=[i];}let a=g();a[0];", vec![("a[0]", "7")]),
            ("let f=()=>{let x=[7];return [()=>x,()=>{x[0]=9}];};let pair=f();let a=pair[0]();pair[1]();a[0];", vec![("a[0]", "9")]),
            ("let f=()=>{let x=[7];return ()=>x;};let g=f();unknown(g);let a=g();a[0];", vec![]),
            ("let f=()=>{let x=7;return ()=>[x];};let g=f();let a=g();let b=f()();a[0];b[0];", vec![("a[0]", "7"), ("b[0]", "7")]),
        ] {
            let expected = expected.into_iter().map(|(source, value)| (source.to_owned(), value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn recursion_uses_fresh_cells_and_preserves_caller_bindings() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("function outer(){function f(n){let a=[n];if(n){let b=f(n-1);return [a[0]+b[0]];}return a;}let r=f(3);return r[0];}", vec![("r[0]", "6")]),
            ("let f=function self(n){return n?self(n-1):[7];};let a=f(2);a[0];", vec![("a[0]", "7")]),
            ("let f=n=>n?f(n-1):[7];let a=f(2);a[0];", vec![("a[0]", "7")]),
            ("function outer(){let a=[0];function f(n){if(n)g(n-1);a[0]++;}function g(n){if(n)f(n-1);a[0]++;}f(4);return a[0];}", vec![("a[0]", "5")]),
            ("let make=x=>{let f=()=>[x];return [f,()=>{let a=make(x+1);return a[0]();}]};let a=make(7);let b=a[1]();let c=a[0]();b[0];c[0];", vec![("b[0]", "8"),("c[0]", "7")]),
            ("let f=n=>{let x=[n];if(n)f(n-1);return x;};let a=f(3);a[0];", vec![("a[0]", "3")]),
        ] {
            let expected = expected.into_iter().map(|(source, value)| (source.to_owned(), value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn unknown_recursive_call_tree_remains_bounded() -> Result<(), BudgetExceeded> {
        let source =
            "function outer(n){function f(n){if(n){f(n-1);f(n-1);}return [7];}let a=f(n);a[0];}";
        assert_eq!(reads(source)?, vec![("a[0]".into(), "7".into())]);
        Ok(())
    }

    #[test]
    fn return_paths_preserve_disjoint_allocation_graphs() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("function f(flag){let a=(()=>{if(flag)return [7];return [7];})();return a[0];}", vec![("a[0]", "7")]),
            ("function f(flag){let a=(()=>{if(flag)return [[7]];return [[7]];})();return a[0][0];}", vec![("a[0][0]", "7")]),
            ("function f(flag){let a=(()=>{if(flag)return [7];return [9];})();return a[0];}", vec![]),
            ("function f(flag){let a=(()=>{if(flag)return (()=>[7])();return [7];})();return a[0];}", vec![("a[0]", "7")]),
            ("function f(flag){let a=(()=>{if(flag)return {__proto__:{'x':7}};return {'x':7};})();return a.x;}", vec![("a.x", "7")]),
            ("function f(flag){let a=(()=>{if(flag)return [7];for(let i=0;i<2;i++){if(i===1)return [7];}return [9];})();return a[0];}", vec![("a[0]", "7")]),
            ("function f(flag){let a=(()=>{let x=[7];if(flag){using r={[Symbol.dispose](){x[0]=9;}};x=[7];return x;}return x;})();return a[0];}", vec![]),
            ("function f(flag){let a=(()=>{let x=[7];if(flag)return x;return [7];})();a[0]=8;return a[0];}", vec![]),
            ("function f(flag){let a=(()=>{if(flag)return [7];return [7];})();a[0]=7;return a[0];}", vec![("a[0]", "7")]),
        ] {
            let expected = expected.into_iter().map(|(source, value)| (source.to_owned(), value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        let source = "function f(flag){let a=[7];let b=(()=>{if(flag)return [7];return [7];})();return a===b;}";
        assert_eq!(
            observed(source, true)?,
            vec![("a===b".into(), "false".into())]
        );
        Ok(())
    }

    #[test]
    fn disposal_effects_follow_scope_exit_and_return_value_capture() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let a;{using r={[Symbol.dispose](){a[0]=9;}};a=[7];a[0];}a[0];", vec![("a[0]", "7")]),
            ("let a=(()=>{let x;using r={[Symbol.dispose](){x[0]=9;}};x=[7];return x;})();a[0];", vec![]),
            ("let a=(()=>{let x;{using r={[Symbol.dispose](){x[0]=9;}};x=[7];return x;}})();a[0];", vec![]),
            ("let a=(()=>{let x;using r={[Symbol.dispose](){x[0]=9;}};x=[7];return x[0];})();let b=[a];b[0];", vec![("x[0]", "7"), ("b[0]", "7")]),
            ("let a;{using r={[Symbol.dispose](){a[0]=9;}};a=[7];let v=(()=>a[0])();let b=[v];b[0];}a[0];", vec![("a[0]", "7"), ("b[0]", "7")]),
            ("let a;(()=>{using r={[Symbol.dispose](){a[0]=9;}};a=[7];})();a[0];", vec![]),
            ("let a=(()=>{let x;using r={[Symbol.dispose](){x[0]=9;}};x=[7];for(let i=0;i<1;i++){return x;}})();a[0];", vec![]),
        ] {
            let expected = expected.into_iter().map(|(source, value)| (source.to_owned(), value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn repeated_reads_require_agreement() -> Result<(), BudgetExceeded> {
        let stable = "let a=[7];let x=0;for(let i=0;i<3;i++){x=a[0];}x;";
        assert_eq!(reads(stable)?, vec![("a[0]".into(), "7".into())]);

        let changing = "let a=[1];let x=0;for(let i=0;i<2;i++){x=a[0];a[0]++;}a[0];";
        assert_eq!(reads(changing)?, vec![("a[0]".into(), "3".into())]);

        let unknown = "let a=[7];let x=0;for(let i=0;i<3;i++){x=a[0];if(flag)a[0]=8;}x;";
        assert_eq!(reads(unknown)?, [] as [(String, String); 0]);

        let nested =
            "let a=[7];let x=0;for(let i=0;i<2;i++){for(let j=0;j<(i===0?1:flag);j++){x=a[0];}}x;";
        assert_eq!(reads(nested)?, [] as [(String, String); 0]);
        Ok(())
    }

    #[test]
    fn unobserved_executions_invalidate_only_covered_facts() -> Result<(), BudgetExceeded> {
        let source = "function f(target){let last;for(let i=0;i<2;){let a=i===0?[0]:target;let b=[i];let c=[7];c[0];i=i+(a[0]=b[0],1);last=[i];}return last[0];}";
        // The post-loop read witnesses successful normal-exit simulation;
        // rejecting the entire transaction would also lose this proof.
        assert_eq!(
            reads(source)?,
            vec![("c[0]".into(), "7".into()), ("last[0]".into(), "2".into())]
        );

        // An unknown compound GetValue can similarly hide the RHS.
        let compound = "function f(target){for(let i=0;i<2;){let a=i===0?[0]:{get x(){return target;}};let b=[i];i=i+(a[i===0?'0':'x']+=b[0],1);}}";
        assert_eq!(reads(compound)?, [] as [(String, String); 0]);
        Ok(())
    }

    #[test]
    fn scalar_helpers_preserve_heap_and_argument_order() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("function outer(){function index(x){let y=x;return (x=9,y);}let a=[0,0];for(let i=0;i<2;i++){a[index(i)]=7;}return a[0]+a[1];}", vec![("a[0]", "7"), ("a[1]", "7")]),
            ("function outer(){function index(x,y){return x+y;}let a=[0,7];let i=0;index(i++,i++);return a[i-1];}", vec![("a[i-1]", "7")]),
            ("function outer(){function index(x){return x;}let a=[7];index(a[0]=9);return a[0];}", vec![("a[0]", "9")]),
            ("function outer(){function index(x,y){return x;}let a=[7];index(0,a);return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){function index(x){return (x=0,x);}let a=[7];index(a);return a[0];}", vec![("a[0]", "7")]),
            ("function outer(){function index(x){return x;}let a=[7];index(a[0]=9,a);return a[0];}", vec![("a[0]", "9")]),
            ("function outer(){function index(x){return x;}let a=[7];index(a);return a[0];}", vec![("a[0]", "7")]),
            ("function index(x){return x;}let a=[7];index(0);a[0];", vec![]),
            ("function outer(flag){if(flag){function index(x){return x;}}let a=[7];index(0);return a[0];}", vec![]),
        ] {
            let expected = expected.into_iter().map(|(span, value)| (span.to_owned(), value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        let source = "function outer(){function index(x){return x%2;}let a=[[],[]];for(let i=0;i<2;i++){a[index(i)]=a[0];}return a[0]===a[1];}";
        assert_eq!(
            observed(source, true)?,
            vec![("a[0]===a[1]".into(), "true".into())]
        );
        Ok(())
    }

    #[test]
    fn finite_heap_construction_proves_real_object_identity() -> Result<(), BudgetExceeded> {
        let source = "let a=[[],[]];for(let i=0;i<2;i++)a[i]=a[0];a[0]===a[1];a[0]!=a[1];";
        assert_eq!(
            observed(source, true)?,
            vec![
                ("a[0]===a[1]".into(), "true".into()),
                ("a[0]!=a[1]".into(), "false".into()),
            ]
        );

        let changing = "let a=[[],[]];for(let i=0;i<2;i++){a[0]===a[1];a[1]=a[0];}";
        assert_eq!(observed(changing, true)?, [] as [(String, String); 0]);

        let distinct = "let a=[[],[]];a[0]===a[1];a[0]!==a[1];";
        assert_eq!(
            observed(distinct, true)?,
            vec![
                ("a[0]===a[1]".into(), "false".into()),
                ("a[0]!==a[1]".into(), "true".into()),
            ]
        );
        Ok(())
    }

    #[test]
    fn exhausted_heap_budget_does_not_publish_partial_reaching_facts() -> Result<(), BudgetExceeded>
    {
        let mut source = "let p0={ x:7 };".to_owned();
        for index in 1..128 {
            use std::fmt::Write;
            let _ = write!(source, "let p{index}={{__proto__:p{}}};", index - 1);
        }
        source.push_str("p0.x;p127.x;");
        let allocator = Allocator::default();
        let program = crate::parse_as(&allocator, &source, SourceType::cjs())
            .unwrap_or_else(|| unreachable!());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let bindings = BindingFacts::analyze(&program, scoping);
        let budget = WorkBudget::new("bounded-heap-analysis", work_budget::BudgetLimits::work(16));
        let pure_functions = crate::collect_pure_functions(&program, scoping, &bindings);
        assert!(
            FreshDataReads::analyze(&program, scoping, &bindings, &pure_functions, &budget)
                .is_err()
        );
        assert_eq!(
            reads(&source)?,
            vec![("p0.x".into(), "7".into()), ("p127.x".into(), "7".into())]
        );
        Ok(())
    }

    #[test]
    fn heap_collection_keeps_outer_aliases_prototypes_and_expression_temporaries(
    ) -> Result<(), BudgetExceeded> {
        let churn = "{let waste={ x:1 };}".repeat(256);
        let source = format!(
            "let holder;{{let p={{x:7}};let a={{__proto__:p}};holder={{a}};}}{churn}holder.a.x;"
        );
        assert_eq!(reads(&source)?, vec![("holder.a.x".into(), "7".into())]);
        let source = format!(
            "let holder={{x:{{y:7}},self:null}};holder.self=holder;{churn}holder.self.x.y;"
        );
        assert_eq!(
            reads(&source)?,
            vec![("holder.self.x.y".into(), "7".into())]
        );
        let source = format!(
            "function f(flag){{let holder; if(flag){{let a={{x:7}};holder=a;{churn}}}else{{let b={{x:7}};holder=b;{churn}}}holder.x;}}"
        );
        assert_eq!(reads(&source)?, vec![("holder.x".into(), "7".into())]);
        let source = format!(
            "function f(flag){{let holder={{x:7}};if(flag){{holder={{x:7}};{churn}}}holder.x;}}"
        );
        assert_eq!(reads(&source)?, vec![("holder.x".into(), "7".into())]);
        let temporaries = "({ x:1 }),".repeat(256);
        let source = format!("let a={{x:7}};let b=a; b.x=({temporaries}a={{x: 9}},8);b.x;a.x;");
        assert_eq!(
            reads(&source)?,
            vec![("b.x".into(), "8".into()), ("a.x".into(), "9".into())]
        );
        let source = format!("let a={{child:{{x:7}},extra:({temporaries}0)}};a.child.x;");
        assert_eq!(reads(&source)?, vec![("a.child.x".into(), "7".into())]);
        Ok(())
    }

    #[test]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "JavaScript fixture braces are source syntax, not Rust format placeholders"
    )]
    fn reaching_facts_follow_real_expression_order_and_joins() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("const a=[7]; a[0]; mutate(a); a[0];", vec![("a[0]", "7")]),
            (
                "const a=[7]; const b=a; b[0]; a[0];",
                vec![("b[0]", "7"), ("a[0]", "7")],
            ),
            (
                "function f(fn){const a=[7];fn(a[0],mutate(a),a[0]);}",
                vec![("a[0]", "7")],
            ),
            (
                "function f(flag){let a={x:7};let b=a;if(flag){b={x:8}}a.x;b.x;}",
                vec![("a.x", "7")],
            ),
            (
                "function f(flag){let a=[7];if(flag){mutate(a);return;}return a[0];}",
                vec![("a[0]", "7")],
            ),
            (
                "function f(flag){let a=[7];if(flag){mutate(a);}return a[0];}",
                vec![],
            ),
            (
                "let a=[7];let i=0;a[i];a=[9];a[i];",
                vec![("a[i]", "7"), ("a[i]", "9")],
            ),
            ("let a={x:7,...side(),x:9};a.x;", vec![("a.x", "9")]),
            ("let a={x:7,...side()};a.x;", vec![]),
            (
                "function f(flag){let a={x:7,y:8};if(flag)a={x:7,z:9};return a.x;}",
                vec![("a.x", "7")],
            ),
            (
                "function f(flag){let a=flag?{x:7,y:8}:{x:7,y:9};a.y;return a.x;}",
                vec![("a.x", "7")],
            ),
            (
                "function f(flag){let a=flag?[-0]:[0];a[0];a.length;}",
                vec![("a.length", "1")],
            ),
            (
                "function f(flag){let a=flag?{x:7}:{get x(){return 7}};return a.x;}",
                vec![],
            ),
            ("let a={'1e+21':7,1e21:9};a[1e21];", vec![("a[1e21]", "9")]),
            (
                "let a={'0.0000001':7,1e-7:9};a['0.0000001'];a[1e-7];",
                vec![("a['0.0000001']", "7"), ("a[1e-7]", "9")],
            ),
            ("const a=[7,...iter];a[0];", vec![("a[0]", "7")]),
            ("const a=[...iter,7];a.length;", vec![]),
            (
                "const a=[,9];a.length;a[1];",
                vec![("a.length", "2"), ("a[1]", "9")],
            ),
            ("({x:7}).x;", vec![("({x:7}).x", "7")]),
            ("({x:7,y:side()}).x;", vec![]),
            ("const a={x:7,y:side()};a.x;", vec![("a.x", "7")]),
            (
                "function f(flag){const a=[7];{if(flag){7;}else{8;}}return a[0];}",
                vec![("a[0]", "7")],
            ),
            (
                "function f(flag){const a=[7];return flag ? a[0] : a.length;}",
                vec![("a[0]", "7"), ("a.length", "1")],
            ),
            ("const a=[7];(true||side());a[0];", vec![("a[0]", "7")]),
            ("const a=[7];false&&side();a[0];", vec![("a[0]", "7")]),
            ("const a=[7];const b={unknown:missing};a[0];", vec![]),
        ] {
            let expected = expected
                .into_iter()
                .map(|(text, value)| (text.to_owned(), value.to_owned()))
                .collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "JavaScript fixture braces are source syntax, not Rust format placeholders"
    )]
    fn heap_facts_follow_alias_writes_and_nested_references() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("const a=[7];a[0]=9;a[0];", vec![("a[0]","9")]),
            ("let a={x:7,y:8};let b=a;b.x=9;a.x;a.y;",vec![("a.x","9"),("a.y","8")]),
            ("let a={x:{y:7}};let b=a.x;b.y=9;a.x.y;",vec![("a.x.y","9")]),
            ("let a={x:7};let b={a};a.x=9;b.a.x;",vec![("b.a.x","9")]),
            ("let a={x:7};let b={a};b.a.x+=2;a.x;",vec![("a.x","9")]),
            ("let a={x:7};let b={a};const p=b.a.x++;const q=++b.a.x;a.x;({p,q}).p;({p,q}).q;",vec![("a.x","9"),("({p,q}).p","7"),("({p,q}).q","9")]),
            ("let a={x:0,y:8};a.x ||= 9;a.x &&= 7;a.x ??= side();a.x;a.y;",vec![("a.x","7"),("a.y","8")]),
            ("let a={x:null};a.x ??= {y:7};a.x.y;",vec![("a.x.y","7")]),
            ("let a={x:7};let b=a;a.x=(a={x:8},9);a.x;b.x;",vec![("a.x","8"),("b.x","9")]),
            ("let a={x:7};let b=a;a[(a={x:8},'x')]=9;a.x;b.x;",vec![("a.x","8"),("b.x","9")]),
            ("let a=[7,8,9];let b=a;b.length=2;a.length;a[1];",vec![("a.length","2"),("a[1]","8")]),
            ("let a=[7,8,9];a.length='1';a[0];a.length;",vec![("a[0]","7"),("a.length","1")]),
            ("let a=[7,8,9];delete a[1];a[0];a[2];a.length;",vec![("a[0]","7"),("a[2]","9"),("a.length","3")]),
            ("let a={x:null};a.x=a;a.x.x.x===a;a.x.x.x.x.x.x.x.x;",vec![]),
            ("let a={x:7};let b={x: 9};let c=true?a:b;c.x=8;a.x;b.x;",vec![("a.x","8"),("b.x","9")]),
            ("function f(flag){let a={x:7};let b={x:8};let c=flag?a:b;c.x=9;a.x;b.x;}",vec![]),
            ("function f(flag){let a={x:7,y:8};let b={x:7,y:9};let c=flag?a:b;c.x=9;c.y;a.y;b.y;}",vec![("a.y","8"),("b.y","9")]),
            ("function f(flag){let a={x:7};if(flag)a.x=9;else a.x=9;return a.x;}",vec![("a.x","9")]),
            ("function f(flag){let a={x:7};if(flag)a.x=9;return a.x;}",vec![]),
            ("function f(flag,v){let a={x:v,y:7};a.x ||= 9;return a.y;}",vec![("a.y","7")]),
            ("function f(v){let a={x:7,y:8};a.x=v;return a.y;}",vec![("a.y","8")]),
            ("let a={x:7};let b={p:a};let c={q:b};c.q.p.x=9;c.q.p.x;",vec![("c.q.p.x","9")]),
            ("let a={x:7};let b={p:a,y:side()};b.p.x;",vec![]),
            ("let a={x:7};let b={p:a,y:(a.x=9)};b.p.x;",vec![("b.p.x","9")]),
            ("let a={x:7};a[(a.x=9,'x')];a.x;",vec![("a.x","9")]),
            ("let a={x:7};let b={p:a};unknown();b.p.x;",vec![]),
            ("function f(flag){let a={x:7};let b=flag?{p:a}:{p:a};b.p.x;}",vec![("b.p.x","7")]),
            ("const a=[7,...iter];a.length=1;a[0];a.length;",vec![("a[0]","7"),("a.length","1")]),
            ("let a={x:7};a[0n]=8;a.x;",vec![]),
            ("const a={16:7};a[0x10n]=9;a[16n];",vec![("a[16n]","9")]),
            ("let a={x:7};let b=a;if(a===b)a.x=9;a.x;", vec![("a.x","9")]),
            ("let a={x:7};let b={x:8};if(a!==b)a.x=9;a.x;", vec![("a.x","9")]),
            ("let a={x:7};if(typeof a==='object')a.x=9;a.x;", vec![("a.x","9")]),
            ("function f(flag){let a={x:7};let b={x:8};let c=flag?a:b;if(c===a)a.x=9;a.x;}",vec![]),
        ] {
            let expected = expected.into_iter().map(|(text,value)|(text.to_owned(),value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "JavaScript fixture braces are source syntax, not Rust format placeholders"
    )]
    fn prototype_and_descriptor_facts_support_inheritance_and_new_properties(
    ) -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let a={__proto__:null};a.missing;a.x=7;a.x;delete a.x;a.x;",vec![("a.missing","void 0"),("a.x","7"),("a.x","void 0")]),
            ("let p={x:7};let a={__proto__:p};a.x;p.x=9;a.x;",vec![("a.x","7"),("a.x","9")]),
            ("let p={x:7};let a={__proto__:p};a.x=9;a.x;p.x;delete a.x;a.x;",vec![("a.x","9"),("p.x","7"),("a.x","7")]),
            ("let p={__proto__:null,x:7};let a={__proto__:p};a.y=9;a.y;p.y;delete a.y;a.y;",vec![("a.y","9"),("p.y","void 0"),("a.y","void 0")]),
            ("let p={__proto__:null,x:{y:7}};let a={__proto__:p};a.x.y=9;p.x.y;a.x.y;",vec![("p.x.y","9"),("a.x.y","9")]),
            ("let p={x:7};let a={__proto__:{__proto__:p}};a.x;p.x=9;a.x;",vec![("a.x","7"),("a.x","9")]),
            ("let a={__proto__:{x:7},x:8};delete a.x;a.x;",vec![("a.x","7")]),
            ("let a={__proto__:null};a.__proto__=9;a.__proto__;",vec![("a.__proto__","9")]),
            ("let a={['__proto__']:7};a.__proto__;",vec![("a.__proto__","7")]),
            ("let a={__proto__:null};a.x??=7;a.x;",vec![("a.x","7")]),
            ("let p={x:7};let a={__proto__:p};a.x+=2;a.x;p.x;",vec![("a.x","9"),("p.x","7")]),
            ("let p={x:7};let a={__proto__:p};let y=a.x++;a.x;p.x;({y}).y;",vec![("a.x","8"),("p.x","7"),("({y}).y","7")]),
            ("function f(flag){let a={__proto__:null};if(flag)a.x=7;a.x=9;a.x;}",vec![("a.x","9")]),
            ("function f(flag){let a={__proto__:null,x:7};if(flag)delete a.x;a.x=9;a.x;}",vec![("a.x","9")]),
            ("function f(flag){let p={x:7};let a={__proto__:p};if(flag)a.x=7;a.x;}",vec![("a.x","7")]),
            ("function f(flag){let p={x:7};let a={__proto__:p,x:7};if(flag)delete a.x;a.x;}",vec![("a.x","7")]),
            ("function f(flag){let p=flag?{x:7}:{x:7};let a={__proto__:p};a.x;}",vec![("a.x","7")]),
            ("function f(flag){let p=flag?{x:7}:{x: 9};let a={__proto__:p};a.x;}",vec![]),
            ("function f(flag){let a={__proto__:null};let b={__proto__:null};let c=flag?a:b;c.x=7;c.x=9;}",vec![]),
            ("function f(k){let a={x:7,[k]:9};a.x=8;a.x;}",vec![("a.x","8")]),
            ("function f(k){let a={__proto__:null,[k]:9};a.x=8;a.x;}",vec![("a.x","8")]),
            ("let a={__proto__:null,x:7,...thing};a.x=9;a.x;",vec![("a.x","9")]),
            ("let a={__proto__:null,...thing};a.x=9;a.x;",vec![("a.x","9")]),
            ("let a={x:7,...thing};a.x=9;a.x;",vec![("a.x","9")]),
            ("let a={__proto__:null,get x(){return 7;}};delete a.x;a.x=9;a.x;",vec![("a.x","9")]),
            ("let p=[7,8];let a={__proto__:p};a.length;a[0];p.length=1;a.length;",vec![("a.length","2"),("a[0]","7"),("a.length","1")]),
            ("let p=[7];let a={__proto__:p};a.length=9;a.length;p.length;",vec![("a.length","9"),("p.length","1")]),
            // Unproven prototypes/accessors remain effect barriers, even
            // when the receiver itself is definitely an ordinary object.
            ("let a={__proto__:3};a.missing;",vec![]),
            ("let a={};a.missing;",vec![]),
            ("let a={};a.x=9;a.x;",vec![]),
            ("let p={get x(){return 7;}};let a={__proto__:p};a.x;",vec![]),
            ("let p={set x(v){side(v)}};let a={__proto__:p};a.x=9;a.x;",vec![]),
            ("let a={__proto__:null,get x(){return 7;}};a.x;",vec![]),
            ("function f(k){let a={__proto__:null,x:7,get [k](){return 9;}};a.x;}",vec![]),
            ("function f(k){let a={__proto__:null,x:7,get [k](){return 9;}};a.x=8;a.x;}",vec![]),
            ("let p={x:7};let a={__proto__:p};unknown();a.x;",vec![]),
            ("let p={x:7};let a={__proto__:p,y:unknown()};a.x;",vec![]),
            ("let a={__proto__:null};Object.setPrototypeOf(a,p);a.x;",vec![]),
            ("let a={__proto__:null};Object.defineProperty(a,'x',{value:7});a.x=9;a.x;",vec![]),
        ] {
            let expected = expected.into_iter().map(|(text,value)|(text.to_owned(),value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "JavaScript fixture braces are source syntax, not Rust format placeholders"
    )]
    fn copy_data_properties_preserves_exact_enumerability_aliases_and_effects(
    ) -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let a={x:7};let b={...a};b.x;",vec![("b.x","7")]),
            ("let a={x:7};let b={...a};a.x=9;b.x;",vec![("b.x","7")]),
            ("let a={x:{y:7}};let b={...a};b.x.y=9;a.x.y;b.x.y;",vec![("a.x.y","9"),("b.x.y","9")]),
            ("let a={__proto__:{x:7}};let b={__proto__:null,...a};b.x;",vec![("b.x","void 0")]),
            ("let a=[7,,9];let b={__proto__:null,...a};b[0];b[1];b[2];b.length;",vec![("b[0]","7"),("b[1]","void 0"),("b[2]","9"),("b.length","void 0")]),
            ("let a=[7,8];a.length=1;let b={__proto__:null,...a};b[0];b[1];b.length;",vec![("b[0]","7"),("b[1]","void 0"),("b.length","void 0")]),
            ("let b={x:2,...{x:7},x:9};b.x;",vec![("b.x","9")]),
            ("let b={x:2,...{x:7}};b.x;",vec![("b.x","7")]),
            ("let a={__proto__:null,x:7};let b={__proto__:null,...a};b.x;b.y;",vec![("b.x","7"),("b.y","void 0")]),
            ("let a={__proto__:null,...null,...void 0,...7,...true};a.x;",vec![("a.x","void 0")]),
            ("let a={__proto__:null,...'ab'};a[0];a[1];a[2];a.length;",vec![("a[0]",r#""a""#),("a[1]",r#""b""#),("a[2]","void 0"),("a.length","void 0")]),
            ("let a={__proto__:null,...'é中'};a[0];a[1];a[2];",vec![("a[0]",r#""é""#),("a[1]",r#""中""#),("a[2]","void 0")]),
            ("let a={__proto__:null,...'😀z'};a[0];a[1];a[2];a[3];",vec![("a[2]",r#""z""#),("a[3]","void 0")]),
            ("let a={['__proto__']:7};let b={__proto__:null,...a};b.__proto__;b.x;",vec![("b.__proto__","7"),("b.x","void 0")]),
            ("let a={x:7};let b={get x(){return 9},...a};b.x;",vec![("b.x","7")]),
            ("function f(flag){let a=flag?{x:7}:{y:8};let b={__proto__:null,x:7,...a};b.x;}",vec![("b.x","7")]),
            ("function f(flag){let a=flag?{x:7}:{y:8};let b={__proto__:null,...a};b.x;b.z;}",vec![("b.z","void 0")]),
            ("function f(k){const a={__proto__:null,[k]:7};const b={__proto__:null,x:7,...a};b.x;}",vec![("b.x","7")]),
            ("let a={x:7,...thing};let b={...a};b.x=9;b.x;",vec![("b.x","9")]),
            ("let p={x:7};let b={...{get x(){p.x=9;return 7}}};p.x;",vec![]),
            ("let a={get x(){return 7}};let b={...a};b.x;",vec![]),
            ("function f(k){let a={get [k](){return 7}};let b={__proto__:null,...a};b.x;}",vec![]),
            ("let a={x:7};let b={...a,y:side()};b.x;a.x;",vec![("b.x","7")]),
            ("let a={x:7};let b={...a,y:side()};a.x;b.x;",vec![]),
            ("let a={x:7};let b={...a,y:(a.x=9)};a.x;b.x;",vec![("a.x","9"),("b.x","7")]),
            ("let a={x:7};let b={...a,...(a.x=9,a)};a.x;b.x;",vec![("a.x","9"),("b.x","9")]),
            ("let a={x:7};let b={...a,...(unknown(),a)};b.x;",vec![]),
        ] {
            let expected = expected.into_iter().map(|(text,value)|(text.to_owned(),value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn no_facts_cross_unknown_effects_or_deferred_execution() -> Result<(), BudgetExceeded> {
        for source in [
            "const a=[7];unknown(a[0]);",
        "function f(){const a=[7];with(new Proxy({},{has(t,k){if(k==='b')a[0]=9;return false;}})){var b=a[0];}return b;}f();",
            "const a=[7];(eval)('a[0]=9');a[0];",
            "const a=[7];a[(mutate(a),0)];",
            "const a=[7];a[8];a[0];",
            "const a=[7];delete a[0];a[0];",
            "const a=[7];function f(){return a[0];}",
            "const a=[7];while(flag){a[0];mutate(a);}",
            "let a=[7];try{mutate(a);}catch(e){}a[0];",
            "const a={get x(){return 1},y:2};a.x;a.y;",
            "let a;{a=[7];}eval('a[0]=9');a[0];",
            "function f(flag){const a=[7];flag&&mutate(a);return a[0];}",
            "function f(flag){const a=[7];flag?mutate(a):0;return a[0];}",
        ] {
            assert!(reads(source)?.is_empty(), "{source}");
        }
        Ok(())
    }
}
