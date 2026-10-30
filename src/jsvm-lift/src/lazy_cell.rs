use crate::{
    receiver_identity::{proven_origin_direct_call_event_unreachable, ProvenOriginDirectCall},
    symbolic_integer::{normalize_integer_polynomial, IntegerPolynomial},
};
use oxc_ast::{
    ast::{
        ArrayExpressionElement, AssignmentTarget, BindingPattern, Expression, FormalParameter,
        Function, Program, Statement,
    },
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, Semantic};
use oxc_span::{GetSpan, Span};
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SlowLazyCellFactoryShape {
    pub function_start: u32,
    pub function_end: u32,
    pub guard_start: u32,
    pub guard_end: u32,
    pub slow_sequence_start: u32,
    pub slow_sequence_end: u32,
    pub state_parameter_index: usize,
    pub handler_parameter_index: usize,
    pub handler_slot: usize,
    pub handler_capture_start: u32,
    pub handler_capture_end: u32,
    pub prototype_field: String,
    pub method_key_field: String,
    pub phase_binding_symbol: SymbolId,
    pub phase_capture_start: u32,
    pub phase_capture_end: u32,
    pub cell_construction_start: u32,
    pub cell_construction_end: u32,
    pub update_function_start: u32,
    pub update_function_end: u32,
    pub resolver_property: String,
    pub resolver_function_start: u32,
    pub resolver_function_end: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellFactoryCall {
    pub shape: SlowLazyCellFactoryShape,
    pub call: ProvenOriginDirectCall,
}

fn strip_parentheses<'a>(expression: &'a Expression<'a>) -> &'a Expression<'a> {
    match expression {
        Expression::ParenthesizedExpression(parenthesized) => {
            strip_parentheses(&parenthesized.expression)
        }
        _ => expression,
    }
}

fn last_sequence_expression<'a>(expression: &'a Expression<'a>) -> &'a Expression<'a> {
    match expression {
        Expression::ParenthesizedExpression(parenthesized) => {
            last_sequence_expression(&parenthesized.expression)
        }
        Expression::SequenceExpression(sequence) => sequence
            .expressions
            .last()
            .map_or(expression, last_sequence_expression),
        _ => expression,
    }
}

fn reference_symbol(scoping: &Scoping, expression: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = last_sequence_expression(expression) else {
        return None;
    };
    scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()
}

fn assignment_symbol(scoping: &Scoping, target: &AssignmentTarget<'_>) -> Option<SymbolId> {
    let AssignmentTarget::AssignmentTargetIdentifier(identifier) = target else {
        return None;
    };
    scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()
}

fn parameter_symbol(parameter: &FormalParameter<'_>) -> Option<SymbolId> {
    let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
        return None;
    };
    identifier.symbol_id.get()
}

fn parameter_symbols(function: &Function<'_>) -> Option<Vec<SymbolId>> {
    if function.params.rest.is_some() {
        return None;
    }
    function.params.items.iter().map(parameter_symbol).collect()
}

fn direct_identifier_array_slot(
    scoping: &Scoping,
    array: &oxc_ast::ast::ArrayExpression<'_>,
    symbol: SymbolId,
) -> Option<usize> {
    let mut matches = Vec::new();
    for (index, element) in array.elements.iter().enumerate() {
        let expression = match element {
            ArrayExpressionElement::SpreadElement(_) | ArrayExpressionElement::Elision(_) => {
                continue;
            }
            element => element.as_expression()?,
        };
        if reference_symbol(scoping, expression) == Some(symbol) {
            matches.push(index);
        }
    }
    let [slot] = matches.as_slice() else {
        return None;
    };
    Some(*slot)
}

fn parameter_member(
    scoping: &Scoping,
    expression: &Expression<'_>,
    parameters: &[SymbolId],
) -> Option<(usize, String)> {
    let Expression::StaticMemberExpression(member) = last_sequence_expression(expression) else {
        return None;
    };
    if member.optional {
        return None;
    }
    let object = reference_symbol(scoping, &member.object)?;
    let index = parameters
        .iter()
        .position(|candidate| *candidate == object)?;
    Some((index, member.property.name.to_string()))
}

fn assignment_expression<'a>(
    expression: &'a Expression<'a>,
) -> Option<&'a oxc_ast::ast::AssignmentExpression<'a>> {
    let Expression::AssignmentExpression(assignment) = expression else {
        return None;
    };
    assignment.operator.is_assign().then_some(assignment)
}

fn shape_for_function(
    function: &Function<'_>,
    scoping: &Scoping,
) -> Option<SlowLazyCellFactoryShape> {
    if function.r#async || function.generator {
        return None;
    }
    let parameters = parameter_symbols(function)?;
    let body = function.body.as_ref()?;
    let mut returns = body
        .statements
        .iter()
        .filter_map(|statement| match statement {
            Statement::ReturnStatement(ret) => Some(ret),
            _ => None,
        });
    let ret = returns.next()?;
    if returns.next().is_some() {
        return None;
    }
    let Expression::SequenceExpression(return_sequence) = ret.argument.as_ref()? else {
        return None;
    };
    let [guarded, returned] = return_sequence.expressions.as_slice() else {
        return None;
    };
    let returned_symbol = reference_symbol(scoping, returned)?;
    let Expression::LogicalExpression(logical) = last_sequence_expression(guarded) else {
        return None;
    };
    if logical.operator.as_str() != "&&" {
        return None;
    }
    let Expression::SequenceExpression(slow_sequence) = strip_parentheses(&logical.right) else {
        return None;
    };

    let mut handler = None;
    let mut phase = None;
    let mut cell = None;
    let mut update = None;
    let mut resolver = None;
    let mut returned_alias = false;

    for expression in &slow_sequence.expressions {
        let Some(assignment) = assignment_expression(expression) else {
            continue;
        };
        if let Some(target_symbol) = assignment_symbol(scoping, &assignment.left) {
            if let Expression::ArrayExpression(array) = last_sequence_expression(&assignment.right)
            {
                if let Some(parameter_index) = parameters
                    .iter()
                    .position(|parameter| *parameter == target_symbol)
                {
                    if let Some(slot) = direct_identifier_array_slot(scoping, array, target_symbol)
                    {
                        if handler
                            .replace((target_symbol, parameter_index, slot, assignment.span))
                            .is_some()
                        {
                            return None;
                        }
                        continue;
                    }
                }
            }

            if let Some(rhs_symbol) = reference_symbol(scoping, &assignment.right) {
                let rhs_declaration = scoping.symbol_span(rhs_symbol);
                if !(function.span.start <= rhs_declaration.start
                    && rhs_declaration.end <= function.span.end)
                {
                    if phase
                        .replace((target_symbol, rhs_symbol, assignment.span))
                        .is_some()
                    {
                        return None;
                    }
                    continue;
                }
            }

            if let Expression::CallExpression(call) = last_sequence_expression(&assignment.right) {
                if !call.optional && call.arguments.len() == 1 {
                    let argument = call.arguments[0].as_expression()?;
                    let (state_parameter_index, prototype_field) =
                        parameter_member(scoping, argument, &parameters)?;
                    let Expression::ComputedMemberExpression(callee) =
                        last_sequence_expression(&call.callee)
                    else {
                        continue;
                    };
                    if callee.optional {
                        continue;
                    }
                    let (method_state_index, method_key_field) =
                        parameter_member(scoping, &callee.expression, &parameters)?;
                    if state_parameter_index != method_state_index {
                        return None;
                    }
                    if cell
                        .replace((
                            target_symbol,
                            state_parameter_index,
                            prototype_field,
                            method_key_field,
                            assignment.span,
                        ))
                        .is_some()
                    {
                        return None;
                    }
                    continue;
                }
            }

            if returned_symbol == target_symbol {
                if let Some((cell_symbol, ..)) = cell.as_ref() {
                    if reference_symbol(scoping, &assignment.right) == Some(*cell_symbol) {
                        returned_alias = true;
                    }
                }
            }
            continue;
        }

        match &assignment.left {
            AssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
                let Some((cell_symbol, state_parameter_index, _, method_key_field, _)) =
                    cell.as_ref()
                else {
                    continue;
                };
                if reference_symbol(scoping, &member.object) != Some(*cell_symbol) {
                    continue;
                }
                let Some((key_state_index, key_field)) =
                    parameter_member(scoping, &member.expression, &parameters)
                else {
                    continue;
                };
                if key_state_index != *state_parameter_index || key_field != *method_key_field {
                    continue;
                }
                let Expression::FunctionExpression(function) =
                    last_sequence_expression(&assignment.right)
                else {
                    continue;
                };
                if update.replace(function.span).is_some() {
                    return None;
                }
            }
            AssignmentTarget::StaticMemberExpression(member) if !member.optional => {
                let Some((cell_symbol, ..)) = cell.as_ref() else {
                    continue;
                };
                if reference_symbol(scoping, &member.object) != Some(*cell_symbol) {
                    continue;
                }
                let Expression::FunctionExpression(function) =
                    last_sequence_expression(&assignment.right)
                else {
                    continue;
                };
                if resolver
                    .replace((member.property.name.to_string(), function.span))
                    .is_some()
                {
                    return None;
                }
            }
            _ => {}
        }
    }

    let (_, handler_parameter_index, handler_slot, handler_capture) = handler?;
    let (_, phase_binding_symbol, phase_capture) = phase?;
    let (cell_symbol, state_parameter_index, prototype_field, method_key_field, cell_construction) =
        cell?;
    let update_function = update?;
    let (resolver_property, resolver_function) = resolver?;
    if returned_symbol == cell_symbol {
        returned_alias = true;
    }
    if !returned_alias {
        return None;
    }

    Some(SlowLazyCellFactoryShape {
        function_start: function.span.start,
        function_end: function.span.end,
        guard_start: logical.left.span().start,
        guard_end: logical.left.span().end,
        slow_sequence_start: logical.right.span().start,
        slow_sequence_end: logical.right.span().end,
        state_parameter_index,
        handler_parameter_index,
        handler_slot,
        handler_capture_start: handler_capture.start,
        handler_capture_end: handler_capture.end,
        prototype_field,
        method_key_field,
        phase_binding_symbol,
        phase_capture_start: phase_capture.start,
        phase_capture_end: phase_capture.end,
        cell_construction_start: cell_construction.start,
        cell_construction_end: cell_construction.end,
        update_function_start: update_function.start,
        update_function_end: update_function.end,
        resolver_property,
        resolver_function_start: resolver_function.start,
        resolver_function_end: resolver_function.end,
    })
}

fn pure_integer_expression(expression: &Expression<'_>) -> bool {
    match strip_parentheses(expression) {
        Expression::NumericLiteral(_) | Expression::Identifier(_) => true,
        Expression::UnaryExpression(unary) => {
            matches!(unary.operator.as_str(), "+" | "-" | "~")
                && pure_integer_expression(&unary.argument)
        }
        Expression::BinaryExpression(binary) => {
            matches!(
                binary.operator.as_str(),
                "+" | "-" | "*" | "%" | "&" | "|" | "^" | "<<" | ">>" | ">>>"
            ) && pure_integer_expression(&binary.left)
                && pure_integer_expression(&binary.right)
        }
        _ => false,
    }
}

fn exact_guard_value(
    guard: &Expression<'_>,
    scoping: &Scoping,
    parameters: &[SymbolId],
    call: &ProvenOriginDirectCall,
) -> Option<bool> {
    let Expression::BinaryExpression(binary) = strip_parentheses(guard) else {
        return None;
    };
    if !matches!(binary.operator.as_str(), "==" | "===" | "!=" | "!==")
        || !pure_integer_expression(&binary.left)
        || !pure_integer_expression(&binary.right)
    {
        return None;
    }
    let bindings = parameters
        .iter()
        .enumerate()
        .filter_map(|(index, symbol)| {
            call.exact_integer_arguments
                .get(index)
                .copied()
                .flatten()
                .map(|value| (*symbol, IntegerPolynomial::constant(i128::from(value))))
        })
        .collect::<HashMap<_, _>>();
    let left = normalize_integer_polynomial(
        &binary.left,
        scoping,
        &bindings,
        &HashMap::new(),
        &HashSet::new(),
    )?
    .constant_value()?;
    let right = normalize_integer_polynomial(
        &binary.right,
        scoping,
        &bindings,
        &HashMap::new(),
        &HashSet::new(),
    )?
    .constant_value()?;
    Some(match binary.operator.as_str() {
        "==" | "===" => left == right,
        "!=" | "!==" => left != right,
        _ => return None,
    })
}

fn function_body_uses_arguments(body: &oxc_ast::ast::FunctionBody<'_>) -> bool {
    #[derive(Default)]
    struct Probe {
        uses_arguments: bool,
    }
    impl<'a> Visit<'a> for Probe {
        fn visit_identifier_reference(
            &mut self,
            identifier: &oxc_ast::ast::IdentifierReference<'a>,
        ) {
            if identifier.name.as_str() == "arguments" {
                self.uses_arguments = true;
            }
        }
        fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
        fn visit_arrow_function_expression(
            &mut self,
            _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
        ) {
        }
    }
    let mut probe = Probe::default();
    probe.visit_function_body(body);
    probe.uses_arguments
}

fn function_subtree_has_dynamic_scope(function: &Function<'_>) -> bool {
    #[derive(Default)]
    struct Probe {
        dynamic: bool,
    }
    impl<'a> Visit<'a> for Probe {
        fn visit_with_statement(&mut self, _statement: &oxc_ast::ast::WithStatement<'a>) {
            self.dynamic = true;
        }
        fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
            if matches!(
                strip_parentheses(&call.callee),
                Expression::Identifier(identifier) if identifier.name.as_str() == "eval"
            ) {
                self.dynamic = true;
            }
            walk::walk_call_expression(self, call);
        }
    }
    let Some(body) = function.body.as_deref() else {
        return true;
    };
    let mut probe = Probe::default();
    probe.visit_function_body(body);
    probe.dynamic
}

fn enclosing_function_span(semantic: &Semantic<'_>, node_id: oxc_semantic::NodeId) -> Option<Span> {
    semantic
        .nodes()
        .ancestors(node_id)
        .find_map(|node| match node.kind() {
            AstKind::Function(function) => Some(function.span),
            AstKind::ArrowFunctionExpression(function) => Some(function.span),
            _ => None,
        })
}

fn enclosing_write_event_span(
    semantic: &Semantic<'_>,
    node_id: oxc_semantic::NodeId,
) -> Option<Span> {
    semantic
        .nodes()
        .ancestors(node_id)
        .find_map(|node| match node.kind() {
            AstKind::AssignmentExpression(assignment) => Some(assignment.span),
            AstKind::UpdateExpression(update) => Some(update.span),
            _ => None,
        })
}

fn parameter_binding_preserved_before_event(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    call: &ProvenOriginDirectCall,
    function_span: Span,
    symbol: SymbolId,
    event: Span,
) -> bool {
    for reference_id in semantic.scoping().get_resolved_reference_ids(symbol) {
        let reference = semantic.scoping().get_reference(*reference_id);
        if !reference.is_write() {
            continue;
        }
        let Some(span) = enclosing_write_event_span(semantic, reference.node_id()) else {
            return false;
        };
        let Some(enclosing) = enclosing_function_span(semantic, reference.node_id()) else {
            return false;
        };
        if enclosing != function_span {
            return false;
        }
        if span.start < event.start
            && !proven_origin_direct_call_event_unreachable(
                source,
                program,
                semantic.scoping(),
                call,
                span,
            )
        {
            return false;
        }
    }
    true
}

fn guard_expression<'a>(function: &'a Function<'a>) -> Option<&'a Expression<'a>> {
    let body = function.body.as_ref()?;
    let mut returns = body
        .statements
        .iter()
        .filter_map(|statement| match statement {
            Statement::ReturnStatement(ret) => Some(ret),
            _ => None,
        });
    let ret = returns.next()?;
    if returns.next().is_some() {
        return None;
    }
    let Expression::SequenceExpression(sequence) = ret.argument.as_ref()? else {
        return None;
    };
    let [guarded, _] = sequence.expressions.as_slice() else {
        return None;
    };
    let Expression::LogicalExpression(logical) = strip_parentheses(guarded) else {
        return None;
    };
    (logical.operator.as_str() == "&&").then_some(&logical.left)
}

fn specialize_shape_for_call(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    function: &Function<'_>,
    shape: &SlowLazyCellFactoryShape,
    call: &ProvenOriginDirectCall,
) -> Option<ProvenSlowLazyCellFactoryCall> {
    if function_subtree_has_dynamic_scope(function)
        || function
            .body
            .as_deref()
            .is_none_or(function_body_uses_arguments)
    {
        return None;
    }
    let parameters = parameter_symbols(function)?;
    if !call
        .callee
        .parameter_indices
        .contains(&shape.state_parameter_index)
    {
        return None;
    }
    let guard = guard_expression(function)?;
    if guard.span().start != shape.guard_start
        || guard.span().end != shape.guard_end
        || !exact_guard_value(guard, semantic.scoping(), &parameters, call)?
    {
        return None;
    }
    let function_span = function.span;
    let state = *parameters.get(shape.state_parameter_index)?;
    let handler = *parameters.get(shape.handler_parameter_index)?;
    if !parameter_binding_preserved_before_event(
        source,
        program,
        semantic,
        call,
        function_span,
        state,
        Span::new(shape.cell_construction_start, shape.cell_construction_end),
    ) || !parameter_binding_preserved_before_event(
        source,
        program,
        semantic,
        call,
        function_span,
        handler,
        Span::new(shape.handler_capture_start, shape.handler_capture_end),
    ) {
        return None;
    }
    Some(ProvenSlowLazyCellFactoryCall {
        shape: shape.clone(),
        call: call.clone(),
    })
}

/// Promote one structural slow-cell factory shape to an exact call proof.
///
/// The call must select the guarded slow branch from exact integer arguments;
/// its exact-origin parameter must be the shape's state parameter; and neither
/// the state binding nor the incoming handler binding may have a reachable
/// write before their respective capture events. Property contents and cell
/// resolver semantics remain separate obligations.
#[must_use]
pub fn proven_slow_lazy_cell_factory_call(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    call: &ProvenOriginDirectCall,
) -> Option<ProvenSlowLazyCellFactoryCall> {
    let mut shapes = structurally_proven_slow_lazy_cell_factory_shapes(program, semantic.scoping())
        .into_iter()
        .filter(|shape| {
            shape.function_start == call.callee.function_start
                && shape.function_end == call.callee.function_end
        });
    let shape = shapes.next()?;
    if shapes.next().is_some() {
        return None;
    }

    struct Harness<'s, 'p, 'm, 'c> {
        source: &'s str,
        program: &'p Program<'p>,
        semantic: &'m Semantic<'m>,
        shape: &'c SlowLazyCellFactoryShape,
        call: &'c ProvenOriginDirectCall,
        result: Option<Option<ProvenSlowLazyCellFactoryCall>>,
    }
    impl<'a> Visit<'a> for Harness<'_, 'a, '_, '_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if self.result.is_some() {
                return;
            }
            if function.span.start == self.shape.function_start
                && function.span.end == self.shape.function_end
            {
                self.result = Some(specialize_shape_for_call(
                    self.source,
                    self.program,
                    self.semantic,
                    function,
                    self.shape,
                    self.call,
                ));
                return;
            }
            walk::walk_function(self, function, flags);
        }
    }
    let mut harness = Harness {
        source,
        program,
        semantic,
        shape: &shape,
        call,
        result: None,
    };
    harness.visit_program(program);
    harness.result.flatten()
}

#[must_use]
pub fn structurally_proven_slow_lazy_cell_factory_shapes(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<SlowLazyCellFactoryShape> {
    struct Collector<'c> {
        scoping: &'c Scoping,
        proven: Vec<SlowLazyCellFactoryShape>,
    }
    impl<'a> Visit<'a> for Collector<'_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if let Some(shape) = shape_for_function(function, self.scoping) {
                self.proven.push(shape);
            }
            walk::walk_function(self, function, flags);
        }
    }
    let mut collector = Collector {
        scoping,
        proven: Vec::new(),
    };
    collector.visit_program(program);
    collector
        .proven
        .sort_by_key(|shape| (shape.function_start, shape.function_end));
    collector.proven.dedup();
    collector.proven
}

#[cfg(test)]
mod tests {
    use super::{
        proven_slow_lazy_cell_factory_call, structurally_proven_slow_lazy_cell_factory_shapes,
    };
    use crate::receiver_identity::structurally_proven_origin_flow;
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    fn shapes(source: &str) -> Vec<super::SlowLazyCellFactoryShape> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        structurally_proven_slow_lazy_cell_factory_shapes(
            &parsed.program,
            semantic.semantic.scoping(),
        )
    }

    #[test]
    fn proves_structural_slow_cell_factory_shape() {
        let source = r#"
            let phase;
            function make(mode, state, handler, s, q, cell, out) {
                return (mode | 48) == mode && (
                    handler = [11, -39, handler, 87],
                    s = 1,
                    q = phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) { s = value; },
                    cell.resolve = function() { return handler[s]; },
                    out = cell
                ), out;
            }
        "#;
        let proven = shapes(source);
        assert_eq!(proven.len(), 1);
        let shape = &proven[0];
        assert_eq!(shape.state_parameter_index, 1);
        assert_eq!(shape.handler_parameter_index, 2);
        assert_eq!(shape.handler_slot, 2);
        assert_eq!(shape.prototype_field, "base");
        assert_eq!(shape.method_key_field, "method");
        assert_eq!(shape.resolver_property, "resolve");
    }

    #[test]
    fn rejects_factory_when_handler_is_not_captured_directly() {
        assert!(shapes(
            r#"
            let phase;
            function make(mode, state, handler, q, cell, out) {
                return (mode | 48) == mode && (
                    handler = [11, wrap(handler), 87],
                    q = phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) {},
                    cell.resolve = function() {},
                    out = cell
                ), out;
            }
            "#,
        )
        .is_empty());
    }

    fn specialized_call(source: &str, needle: &str) -> bool {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let start = source.find(needle).expect("call") as u32;
        let Some(call) = flow
            .direct_calls
            .iter()
            .find(|call| call.call_start == start)
        else {
            return false;
        };
        proven_slow_lazy_cell_factory_call(source, &parsed.program, &semantic.semantic, call)
            .is_some()
    }

    #[test]
    fn specializes_slow_cell_call_with_unreachable_handler_write() {
        let source = r#"
            let phase;
            const C = function() { enter(this); };
            function enter(state) {
                return make(48, state, function handler() {}, 0, 0, 0, 0);
            }
            function make(mode, state, handler, s, q, cell, out) {
                if (mode === 99) handler = other;
                return (mode | 48) == mode && (
                    handler = [11, -39, handler, 87],
                    s = 1,
                    q = phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) { s = value; },
                    cell.resolve = function() { return handler[s]; },
                    out = cell
                ), out;
            }
            new C();
        "#;
        assert!(specialized_call(source, "make(48"));
    }

    #[test]
    fn specialization_rejects_reachable_handler_write() {
        let source = r#"
            let phase;
            const C = function() { enter(this); };
            function enter(state) {
                return make(48, state, function handler() {}, 0, 0, 0, 0);
            }
            function make(mode, state, handler, s, q, cell, out) {
                handler = other;
                return (mode | 48) == mode && (
                    handler = [11, -39, handler, 87],
                    s = 1,
                    q = phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) { s = value; },
                    cell.resolve = function() { return handler[s]; },
                    out = cell
                ), out;
            }
            new C();
        "#;
        assert!(!specialized_call(source, "make(48"));
    }

    #[test]
    fn specialization_rejects_outer_arguments_parameter_alias() {
        let source = r#"
            let phase;
            const C = function() { enter(this); };
            function enter(state) {
                return make(48, state, function handler() {}, 0, 0, 0, 0);
            }
            function make(mode, state, handler, s, q, cell, out) {
                arguments[2] = other;
                return (mode | 48) == mode && (
                    handler = [11, -39, handler, 87],
                    s = 1,
                    q = phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) { s = value; },
                    cell.resolve = function() { return handler[s]; },
                    out = cell
                ), out;
            }
            new C();
        "#;
        assert!(!specialized_call(source, "make(48"));
    }

    #[test]
    fn specialization_rejects_false_slow_guard() {
        let source = r#"
            let phase;
            const C = function() { enter(this); };
            function enter(state) {
                return make(7, state, function handler() {}, 0, 0, 0, 0);
            }
            function make(mode, state, handler, s, q, cell, out) {
                return (mode | 48) == mode && (
                    handler = [11, -39, handler, 87],
                    s = 1,
                    q = phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) { s = value; },
                    cell.resolve = function() { return handler[s]; },
                    out = cell
                ), out;
            }
            new C();
        "#;
        assert!(!specialized_call(source, "make(7"));
    }

    #[test]
    fn rejects_factory_when_phase_value_is_local() {
        assert!(shapes(
            r#"
            function make(mode, state, handler, phase, q, cell, out) {
                return (mode | 48) == mode && (
                    handler = [11, handler, 87],
                    q = phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) {},
                    cell.resolve = function() {},
                    out = cell
                ), out;
            }
            "#,
        )
        .is_empty());
    }
}
