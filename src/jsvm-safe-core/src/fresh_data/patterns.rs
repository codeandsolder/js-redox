//! Object binding and assignment share property extraction and rest copies.
//! Assignment references are prepared before the source property is read,
//! unlike binding initialization.
use super::{
    heap::charge, AllocationKind, Analyzer, Environment, Evaluation, Fact, OwnData, Reference,
    Value,
};
use crate::value_eval::literal_property_key;
use oxc_ast::ast::{
    AssignmentExpression, AssignmentTarget, AssignmentTargetMaybeDefault, AssignmentTargetProperty,
    Expression, ObjectAssignmentTarget, PropertyKey,
};
use oxc_span::GetSpan;
use std::collections::HashSet;

pub(super) struct ObjectPatternSource<'a> {
    value: Option<&'a Fact>,
    excluded: Option<HashSet<String>>,
}

impl<'a> ObjectPatternSource<'a> {
    pub(super) fn new(
        analyzer: &mut Analyzer<'_, '_>,
        value: Option<&'a Fact>,
        has_rest: bool,
    ) -> Self {
        // Even an empty object pattern performs RequireObjectCoercible.
        if value.is_none_or(|fact| matches!(fact.primitive(), Some(Value::Null | Value::Undefined)))
        {
            analyzer.note_exception();
        }
        Self {
            value,
            excluded: has_rest.then(HashSet::new),
        }
    }

    pub(super) fn record_key(
        &mut self,
        analyzer: &mut Analyzer<'_, '_>,
        key: &Evaluation,
    ) -> Option<()> {
        if let Some(excluded) = &mut self.excluded {
            if let Some(key) = key.primitive_value().map(Value::js_string) {
                analyzer.heap_result(charge(analyzer.budget, key.len()))?;
                excluded.insert(key);
            } else {
                self.excluded = None;
            }
        }
        Some(())
    }

    pub(super) fn read(
        &self,
        analyzer: &mut Analyzer<'_, '_>,
        key: &Evaluation,
        environment: &mut Environment,
    ) -> Option<Evaluation> {
        let receiver = self
            .value
            .map(|value| value.copy(analyzer.budget))
            .transpose();
        let receiver = analyzer.heap_result(receiver)?;
        Some(analyzer.member(
            Evaluation {
                fact: receiver,
                inert: true,
            },
            key,
            environment,
        ))
    }

    pub(super) fn rest(
        &self,
        analyzer: &mut Analyzer<'_, '_>,
        environment: &mut Environment,
    ) -> Option<Evaluation> {
        let mut data = OwnData::new(AllocationKind::Ordinary);
        let copied = if let (Some(source), Some(excluded)) = (self.value, &self.excluded) {
            analyzer.heap_result(data.spread_excluding(
                environment,
                source,
                excluded,
                analyzer.budget,
            ))?
        } else {
            false
        };
        if !copied {
            analyzer.invalidate(environment);
            analyzer.heap_result(data.define_unknown_key(true, None, analyzer.budget))?;
        }
        Some(analyzer.allocate(environment, data, copied))
    }
}

enum Destination<'a, 'ast> {
    Reference(Reference),
    Pattern(&'a AssignmentTarget<'ast>),
}

impl Analyzer<'_, '_> {
    pub(super) fn pattern_key(
        &mut self,
        key: &PropertyKey<'_>,
        computed: bool,
        environment: &mut Environment,
    ) -> Evaluation {
        if computed {
            let key = key
                .as_expression()
                .map_or_default(|key| self.key(key, environment));
            // ToPropertyKey precedes target-reference evaluation. If a
            // conversion can invoke user code, invalidate before resolving
            // any target (not merely when reading the source property).
            if key.primitive_value().is_none() {
                return self.barrier(environment);
            }
            key
        } else {
            literal_property_key(key)
                .map_or_default(|key| Evaluation::primitive(Value::String(key), true))
        }
    }

    pub(super) fn destructuring_assignment(
        &mut self,
        assignment: &AssignmentExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        // A destructuring assignment obtains its RHS before evaluating
        // any target reference, and the expression returns that RHS.
        let value = self.expression(&assignment.right, environment).fact;
        if self
            .assign_pattern(&assignment.left, value.as_ref(), environment)
            .is_none()
        {
            self.unobserved(assignment.span);
            return self.barrier(environment);
        }
        Evaluation {
            fact: value,
            inert: false,
        }
    }

    fn assign_pattern(
        &mut self,
        pattern: &AssignmentTarget<'_>,
        source: Option<&Fact>,
        environment: &mut Environment,
    ) -> Option<()> {
        self.heap_result(self.budget.consume(1))?;
        match pattern {
            AssignmentTarget::ObjectAssignmentTarget(pattern) => {
                self.assign_object(pattern, source, environment)
            }
            AssignmentTarget::ArrayAssignmentTarget(_) => {
                self.unobserved(pattern.span());
                self.invalidate(environment);
                Some(())
            }
            _ => None,
        }
    }

    fn destination<'a, 'ast>(
        &mut self,
        target: &'a AssignmentTarget<'ast>,
        environment: &mut Environment,
    ) -> Option<Destination<'a, 'ast>> {
        if let Some(simple) = target.as_simple_assignment_target() {
            Some(Destination::Reference(self.reference(simple, environment)?))
        } else {
            Some(Destination::Pattern(target))
        }
    }

    fn write_destination(
        &mut self,
        destination: Destination<'_, '_>,
        value: Option<&Fact>,
        environment: &mut Environment,
    ) -> Option<()> {
        match destination {
            Destination::Reference(reference) => {
                if !self.heap_result(reference.write(environment, value, self.budget))? {
                    self.invalidate(environment);
                }
                Some(())
            }
            Destination::Pattern(pattern) => self.assign_pattern(pattern, value, environment),
        }
    }

    fn assignment_property<'a, 'ast>(
        &mut self,
        property: &'a AssignmentTargetProperty<'ast>,
        environment: &mut Environment,
    ) -> Option<(
        Evaluation,
        Destination<'a, 'ast>,
        Option<&'a Expression<'ast>>,
    )> {
        match property {
            AssignmentTargetProperty::AssignmentTargetPropertyIdentifier(property) => {
                let key =
                    Evaluation::primitive(Value::String(property.binding.name.to_string()), true);
                let destination = Destination::Reference(
                    self.identifier_reference(&property.binding, environment)?,
                );
                Some((key, destination, property.init.as_ref()))
            }
            AssignmentTargetProperty::AssignmentTargetPropertyProperty(property) => {
                let key = self.pattern_key(&property.name, property.computed, environment);
                let (target, default) = match &property.binding {
                    AssignmentTargetMaybeDefault::AssignmentTargetWithDefault(value) => {
                        (&value.binding, Some(&value.init))
                    }
                    binding => (binding.as_assignment_target()?, None),
                };
                let destination = self.destination(target, environment)?;
                Some((key, destination, default))
            }
        }
    }

    fn assign_object(
        &mut self,
        pattern: &ObjectAssignmentTarget<'_>,
        source: Option<&Fact>,
        environment: &mut Environment,
    ) -> Option<()> {
        let mut source = ObjectPatternSource::new(self, source, pattern.rest.is_some());
        for property in &pattern.properties {
            let (key, destination, default) = self.assignment_property(property, environment)?;
            source.record_key(self, &key)?;
            let mut value = source.read(self, &key, environment)?.fact;
            if let Some(default) = default {
                value = self.apply_default(value, default, environment);
            }
            self.write_destination(destination, value.as_ref(), environment)?;
        }
        if let Some(rest) = &pattern.rest {
            let destination = self.destination(&rest.target, environment)?;
            let value = source.rest(self, environment)?.fact;
            self.write_destination(destination, value.as_ref(), environment)?;
        }
        Some(())
    }
}
