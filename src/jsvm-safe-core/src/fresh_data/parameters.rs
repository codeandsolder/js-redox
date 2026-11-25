//! Function declaration instantiation and ordered binding initialization.
//!
//! Default initializers run before body var/function instantiation, and
//! may create closures that retain the original formal cells. Object
//! patterns use the ordinary heap lookup and enumerable-copy machinery.
//! Array patterns require iterator proofs, not assumptions about intrinsics.
use super::{
    cells::CellId, heap::charge, AllocationKind, Analyzer, Environment, Evaluation, Fact, OwnData,
    Value,
};
use crate::value_eval::literal_property_key;
use oxc_ast::ast::{
    BindingPattern, Expression, FormalParameters, ObjectPattern, VariableDeclarationKind,
    VariableDeclarator,
};
use oxc_span::GetSpan;
use oxc_syntax::{
    scope::ScopeId,
    symbol::{SymbolFlags, SymbolId},
};
use std::collections::HashSet;

fn pattern_has_expression(pattern: &BindingPattern<'_>) -> bool {
    match pattern {
        BindingPattern::BindingIdentifier(_) => false,
        BindingPattern::AssignmentPattern(_) => true,
        BindingPattern::ObjectPattern(pattern) => {
            pattern
                .properties
                .iter()
                .any(|property| property.computed || pattern_has_expression(&property.value))
                || pattern
                    .rest
                    .as_ref()
                    .is_some_and(|rest| pattern_has_expression(&rest.argument))
        }
        BindingPattern::ArrayPattern(pattern) => {
            pattern
                .elements
                .iter()
                .flatten()
                .any(pattern_has_expression)
                || pattern
                    .rest
                    .as_ref()
                    .is_some_and(|rest| pattern_has_expression(&rest.argument))
        }
    }
}

pub(super) fn has_parameter_expressions(params: &FormalParameters<'_>) -> bool {
    params.items.iter().any(|parameter| {
        parameter.initializer.is_some() || pattern_has_expression(&parameter.pattern)
    }) || params
        .rest
        .as_ref()
        .is_some_and(|rest| pattern_has_expression(&rest.rest.argument))
}

impl Analyzer<'_, '_> {
    fn write_initialized(
        &mut self,
        cell: CellId,
        value: Option<Fact>,
        environment: &mut Environment,
    ) -> Option<()> {
        let result = if let Some(value) = value {
            environment.insert(cell, value, self.budget)
        } else {
            environment.remove(cell, self.budget)
        };
        self.heap_result(result)
    }

    /// Unknown input may be undefined. Evaluate the initializer only on
    /// that alternative, then join its effects with the supplied-value path.
    fn apply_default(
        &mut self,
        value: Option<Fact>,
        initializer: &Expression<'_>,
        environment: &mut Environment,
    ) -> Option<Fact> {
        match value {
            Some(Fact::Primitive(Value::Undefined)) => {
                self.expression(initializer, environment).fact
            }
            Some(value) => Some(value),
            None => {
                let skip = environment.clone();
                let first_new = self.next_identity;
                self.expression(initializer, environment);
                if !self.join_heap(environment, &skip, first_new) {
                    self.invalidate(environment);
                }
                None
            }
        }
    }

    fn bind_pattern(
        &mut self,
        pattern: &BindingPattern<'_>,
        value: Option<Fact>,
        environment: &mut Environment,
    ) -> Option<()> {
        self.heap_result(self.budget.consume(1))?;
        match pattern {
            BindingPattern::BindingIdentifier(identifier) => {
                let symbol = identifier.symbol_id.get()?;
                self.write_initialized(self.cell_id(symbol)?, value, environment)
            }
            BindingPattern::AssignmentPattern(pattern) => {
                let value = self.apply_default(value, &pattern.right, environment);
                self.bind_pattern(&pattern.left, value, environment)
            }
            BindingPattern::ObjectPattern(pattern) => {
                self.bind_object(pattern, value.as_ref(), environment)
            }
            BindingPattern::ArrayPattern(_) => {
                // Iterator acquisition, next, value and close can invoke
                // arbitrary code, even for an array literal input.
                self.unobserved(pattern.span());
                self.invalidate(environment);
                Some(())
            }
        }
    }

    fn bind_object(
        &mut self,
        pattern: &ObjectPattern<'_>,
        source: Option<&Fact>,
        environment: &mut Environment,
    ) -> Option<()> {
        let mut excluded = HashSet::new();
        let mut known_exclusions = true;
        for property in &pattern.properties {
            let key = if property.computed {
                property
                    .key
                    .as_expression()
                    .map_or_default(|key| self.key(key, environment))
            } else {
                literal_property_key(&property.key)
                    .map_or_default(|key| Evaluation::primitive(Value::String(key), true))
            };
            if pattern.rest.is_some() {
                if let Some(key) = key.primitive_value().map(Value::js_string) {
                    self.heap_result(charge(self.budget, key.len()))?;
                    excluded.insert(key);
                } else {
                    known_exclusions = false;
                }
            }
            let receiver = source.map(|value| value.copy(self.budget)).transpose();
            let receiver = self.heap_result(receiver)?;
            let value = self
                .member(
                    Evaluation {
                        fact: receiver,
                        inert: true,
                    },
                    &key,
                    environment,
                )
                .fact;
            self.bind_pattern(&property.value, value, environment)?;
        }
        if let Some(rest) = &pattern.rest {
            let mut data = OwnData::new(AllocationKind::Ordinary);
            let copied = if let Some(source) = source.filter(|_| known_exclusions) {
                self.heap_result(data.spread_excluding(
                    environment,
                    source,
                    &excluded,
                    self.budget,
                ))?
            } else {
                false
            };
            if !copied {
                self.invalidate(environment);
                self.heap_result(data.define_unknown_key(true, None, self.budget))?;
            }
            let rest_value = self.allocate(environment, data, copied).fact;
            self.bind_pattern(&rest.argument, rest_value, environment)?;
        }
        Some(())
    }

    /// Variable patterns share binding initialization with parameters.
    /// Var patterns may resolve through dynamic environments, so prove
    /// every target before interpreting any property or default operation.
    pub(super) fn destructuring_declaration(
        &mut self,
        declarator: &VariableDeclarator<'_>,
        kind: VariableDeclarationKind,
        environment: &mut Environment,
    ) -> bool {
        let Some(initializer) = &declarator.init else {
            self.unobserved(declarator.id.span());
            self.invalidate(environment);
            return true;
        };
        let value = self.expression(initializer, environment).fact;
        if kind == VariableDeclarationKind::Var
            && !declarator
                .id
                .get_binding_identifiers()
                .iter()
                .all(|identifier| {
                    self.bindings
                        .var_initializer_binding_target(self.scoping, declarator, identifier)
                        .is_some()
                })
        {
            self.unobserved(declarator.id.span());
            self.invalidate(environment);
            return true;
        }
        self.bind_pattern(&declarator.id, value, environment)
            .is_some()
    }

    pub(super) fn initialize_parameters(
        &mut self,
        params: &FormalParameters<'_>,
        arguments: Vec<Option<Fact>>,
        environment: &mut Environment,
    ) -> Option<()> {
        let mut arguments = arguments.into_iter();
        for parameter in &params.items {
            let mut value = arguments
                .next()
                .unwrap_or(Some(Fact::Primitive(Value::Undefined)));
            if let Some(initializer) = &parameter.initializer {
                value = self.apply_default(value, initializer, environment);
            }
            self.bind_pattern(&parameter.pattern, value, environment)?;
        }
        if let Some(rest) = &params.rest {
            // Rest parameters construct an ordinary fresh array directly;
            // unlike array destructuring they do not invoke an iterator.
            self.heap_result(charge(self.budget, arguments.len()))?;
            let mut data = OwnData::new(AllocationKind::Array);
            let length = u32::try_from(arguments.len()).ok()?;
            for (index, value) in arguments.enumerate() {
                data.define_data(index.to_string(), value);
            }
            data.define_data(
                "length".into(),
                Some(Fact::Primitive(Value::Number(f64::from(length)))),
            );
            let rest_value = self.allocate(environment, data, true).fact;
            self.bind_pattern(&rest.rest.argument, rest_value, environment)?;
        }
        Some(())
    }

    pub(super) fn initialize_body_environment(
        &mut self,
        scope: ScopeId,
        params: &FormalParameters<'_>,
        environment: &mut Environment,
    ) -> Option<()> {
        let parameter_instance = if has_parameter_expressions(params) {
            let body = self.fresh_identity();
            self.heap_result(environment.record_birth(body, self.budget))?;
            Some(self.scope_instances.split_parameters(scope, body)?)
        } else {
            None
        };

        for &symbol in self.scoping.get_bindings(scope).values() {
            self.heap_result(self.budget.consume(1))?;
            let flags = self.scoping.symbol_flags(symbol);
            if flags.contains(SymbolFlags::FunctionExpression) {
                continue;
            }
            if self
                .bindings
                .implicit_arguments_symbol(self.scoping, symbol)
            {
                if let Some(instance) = parameter_instance {
                    let value = self.heap_result(
                        environment.read_binding(CellId::arguments(instance), self.budget),
                    )?;
                    self.write_initialized(self.cell_id(symbol)?, value, environment)?;
                }
                continue;
            }
            if flags.is_function() {
                // Body function declarations override formals; unsupported
                // redeclarations must not accidentally retain a formal value.
                self.write_initialized(self.cell_id(symbol)?, None, environment)?;
                continue;
            }
            if !flags.is_function_scoped_declaration() {
                continue;
            }
            self.initialize_body_var(symbol, parameter_instance, environment)?;
        }
        Some(())
    }

    fn initialize_body_var(
        &mut self,
        symbol: SymbolId,
        parameter_instance: Option<super::cells::InstanceId>,
        environment: &mut Environment,
    ) -> Option<()> {
        let value = if self.bindings.is_parameter(symbol) {
            if !self.bindings.is_hoisted_var(symbol) {
                return Some(());
            }
            let Some(parameter_instance) = parameter_instance else {
                // With no parameter expressions, var shares the formal cell.
                return Some(());
            };
            self.heap_result(
                environment.read_binding(CellId::symbol(parameter_instance, symbol), self.budget),
            )?
        } else {
            Some(Fact::Primitive(Value::Undefined))
        };
        self.write_initialized(self.cell_id(symbol)?, value, environment)
    }
}
