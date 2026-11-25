//! Function-local arguments objects share the activation's formal cells.
//! Mapped indices are descriptor edges, not copies of formal values.
use super::{
    cells::CellId, heap::charge, parameters::has_parameter_expressions, AllocationKind, Analyzer,
    Environment, Fact, OwnData, Value,
};
use oxc_ast::ast::{BindingPattern, FormalParameters};
use oxc_ecmascript::IsSimpleParameterList;
use oxc_syntax::{scope::ScopeId, symbol::SymbolFlags};
use std::collections::HashSet;

pub(super) struct ArgumentsSpec<'a, 'ast> {
    pub(super) scope: ScopeId,
    pub(super) params: &'a FormalParameters<'ast>,
    pub(super) strict: bool,
    pub(super) callee: Option<&'a Fact>,
}

impl Analyzer<'_, '_> {
    pub(super) fn initialize_arguments_object(
        &mut self,
        spec: ArgumentsSpec<'_, '_>,
        values: &[Option<Fact>],
        environment: &mut Environment,
    ) -> Option<()> {
        let ArgumentsSpec {
            scope,
            params,
            strict,
            callee,
        } = spec;
        if !self.bindings.implicit_arguments_used(scope) {
            return Some(());
        }
        if self
            .scoping
            .get_binding(scope, "arguments".into())
            .is_some_and(|symbol| {
                let flags = self.scoping.symbol_flags(symbol);
                self.bindings.is_parameter(symbol)
                    || (!has_parameter_expressions(params)
                        && !flags.contains(SymbolFlags::FunctionExpression)
                        && !self
                            .bindings
                            .implicit_arguments_symbol(self.scoping, symbol))
            })
        {
            return Some(());
        }
        self.heap_result(charge(self.budget, values.len()))?;
        let length = u32::try_from(values.len()).ok()?;
        let mut data = OwnData::new(AllocationKind::Ordinary);
        for (index, value) in values.iter().enumerate() {
            let value = self.heap_result(
                value
                    .as_ref()
                    .map(|fact| fact.copy(self.budget))
                    .transpose(),
            )?;
            data.define_data(index.to_string(), value);
        }
        data.define_hidden_data(
            "length".into(),
            Some(Fact::Primitive(Value::Number(f64::from(length)))),
        );
        if !strict && params.is_simple_parameter_list() {
            let callee = self.heap_result(callee.map(|fact| fact.copy(self.budget)).transpose())?;
            data.define_hidden_data("callee".into(), callee);
            let mut mapped = HashSet::new();
            // The last occurrence of a duplicate formal wins, even if
            // there is no actual argument at that position.
            for (index, parameter) in params.items.iter().enumerate().rev() {
                self.heap_result(self.budget.consume(1))?;
                let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                    return None;
                };
                let symbol = identifier.symbol_id.get()?;
                if mapped.insert(symbol) && index < values.len() {
                    data.define_mapped(index.to_string(), self.cell_id(symbol)?);
                }
            }
        } else {
            data.define_restricted("callee".into());
        }
        let instance = self.scope_instances.get(scope, || true)?;
        let value = self.allocate(environment, data, true).fact?;
        self.heap_result(environment.insert(CellId::arguments(instance), value, self.budget))
    }
}
