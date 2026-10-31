use crate::{
    cfg_order::prove_event_before_barriers,
    forwarding_semantics::ProvenLazyRegistryReadCall,
    numeric::{eval_js_bitwise_i64, exact_i64},
    receiver_identity::{
        proven_exact_own_data_field_at_direct_call, proven_origin_direct_call_event_unreachable,
        proven_origin_direct_call_prefix_preserves_exact_property_before_direct_call,
        proven_origin_direct_call_preserves_exact_property, proven_prototype_string_at_allocation,
        proven_prototype_string_at_direct_calls, ProvenExactOwnDataFieldAtDirectCall,
        ProvenOriginDirectCall, ProvenPrototypeStringAtDirectCall,
    },
    state_flatten::{
        prove_function_if_ladder_event_before_barriers,
        prove_function_if_ladder_event_unreachable_with_integer_parameters,
        prove_function_if_ladder_states_before_event_with_integer_parameters,
        prove_function_protected_if_ladder_event_unreachable_with_call_arguments,
        prove_function_structured_branch_event_unreachable_with_integer_parameters,
        prove_function_switch_event_unreachable_with_integer_parameters,
    },
    symbolic_integer::{normalize_integer_polynomial, IntegerPolynomial},
};
use oxc_ast::{
    ast::{
        ArrayExpressionElement, AssignmentTarget, BindingPattern, Expression, FormalParameter,
        Function, ObjectPropertyKind, Program, PropertyKind, Statement,
    },
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, Semantic};
use oxc_span::{GetSpan, Span};
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::{BTreeMap, HashMap, HashSet};

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
    pub index_state_symbol: SymbolId,
    pub index_state_initialization_start: u32,
    pub index_state_initialization_end: u32,
    pub prototype_field: String,
    pub method_key_field: String,
    pub phase_local_symbol: SymbolId,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellStateFields {
    pub factory_call: ProvenSlowLazyCellFactoryCall,
    pub prototype_field: ProvenExactOwnDataFieldAtDirectCall,
    pub method_key: ProvenPrototypeStringAtDirectCall,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellExactStateFields {
    pub exact_assignment: ProvenSlowLazyCellExactRegistryAssignment,
    pub fields: ProvenSlowLazyCellStateFields,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellPrototypeCarrier {
    pub state_fields: ProvenSlowLazyCellExactStateFields,
    pub accessor: ProvenLazyRegistryReadCall,
    pub helper_function_start: u32,
    pub helper_function_end: u32,
    pub helper_call_start: u32,
    pub helper_call_end: u32,
    pub helper_create_start: u32,
    pub helper_create_end: u32,
    pub getter_function_start: u32,
    pub getter_function_end: u32,
    pub object_constructor_symbol: SymbolId,
    pub method_name: String,
    pub projection_property: String,
    pub resolver_property: String,
    /// Resolving `({}).constructor` to the intrinsic `Object`, interpreting
    /// `Object.create`, inherited accessors, and getter `this` use ordinary,
    /// untampered ECMAScript built-in/prototype semantics.
    pub standard_object_prototype_semantics_required: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellUpdateState {
    pub factory_call: ProvenSlowLazyCellFactoryCall,
    pub initial_state_value: i64,
    pub post_update_state_value: i64,
    pub selector_capture_symbol: SymbolId,
    pub update_parameter_symbol: SymbolId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellRegistryAssignment {
    pub factory_call: ProvenSlowLazyCellFactoryCall,
    pub registry_path: Vec<String>,
    pub receiver_start: u32,
    pub receiver_end: u32,
    pub key_start: u32,
    pub key_end: u32,
    pub registry_key_symbol: SymbolId,
    pub factory_key_parameter_index: usize,
    pub factory_key_symbol: SymbolId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellExactRegistryAssignment {
    pub assignment: ProvenSlowLazyCellRegistryAssignment,
    /// Final direct call into the M-containing installer context.
    pub caller: ProvenOriginDirectCall,
    /// Exact direct-call chain from the concrete-key root call through any
    /// forwarding/delegating helpers to `caller`.
    pub provenance_calls: Vec<ProvenOriginDirectCall>,
    pub exact_key_value: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellResolverIndex {
    pub update_state: ProvenSlowLazyCellUpdateState,
    pub exact_assignment: ProvenSlowLazyCellExactRegistryAssignment,
    pub selector_key_symbol: SymbolId,
    pub selector_start: u32,
    pub selector_end: u32,
    pub factory_key_symbol: SymbolId,
    pub exact_key_value: i64,
    pub phase_value: i64,
    pub handler_slot: usize,
    pub index_assignment_start: u32,
    pub index_assignment_end: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellCapturedValueInstall {
    pub exact_assignment: ProvenSlowLazyCellExactRegistryAssignment,
    pub install: crate::registry_identity::ProvenOriginRegistryValueInstall,
    pub caller_value_parameter_index: usize,
    pub caller_value_symbol: SymbolId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellCapturedHandlerInstall {
    pub exact_assignment: ProvenSlowLazyCellExactRegistryAssignment,
    pub install: crate::registry_identity::ProvenOriginRegistryHandlerInstall,
    pub caller_handler_parameter_index: usize,
    pub caller_handler_symbol: SymbolId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellResolvedHandler {
    pub resolver: ProvenSlowLazyCellResolverIndex,
    pub captured_handler: ProvenSlowLazyCellCapturedHandlerInstall,
}

/// End-to-end proof that one exact slow-cell registry assignment is observed by
/// the structural lazy accessor as the original logical handler.
///
/// The proof joins the same exact wrapper assignment across update-before-
/// projection accessor semantics, inherited prototype getter delegation,
/// resolver slot selection, and captured-handler provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellReadResult {
    pub resolved_handler: ProvenSlowLazyCellResolvedHandler,
    pub carrier: ProvenSlowLazyCellPrototypeCarrier,
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

fn same_direct_receiver(scoping: &Scoping, left: &Expression<'_>, right: &Expression<'_>) -> bool {
    let left = last_sequence_expression(left);
    let right = last_sequence_expression(right);
    matches!(
        (left, right),
        (Expression::ThisExpression(_), Expression::ThisExpression(_))
    ) || reference_symbol(scoping, left)
        .zip(reference_symbol(scoping, right))
        .is_some_and(|(left, right)| left == right)
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
    let mut index_state = None;
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

            if !matches!(
                last_sequence_expression(&assignment.right),
                Expression::Identifier(_)
            ) && pure_integer_expression(&assignment.right)
            {
                if index_state
                    .replace((target_symbol, assignment.span))
                    .is_some()
                {
                    return None;
                }
                continue;
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
    let (index_state_symbol, index_state_initialization) = index_state?;
    let (phase_local_symbol, phase_binding_symbol, phase_capture) = phase?;
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
        index_state_symbol,
        index_state_initialization_start: index_state_initialization.start,
        index_state_initialization_end: index_state_initialization.end,
        prototype_field,
        method_key_field,
        phase_local_symbol,
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

fn exact_integer_bindings(
    parameters: &[SymbolId],
    call: &ProvenOriginDirectCall,
) -> HashMap<SymbolId, IntegerPolynomial> {
    parameters
        .iter()
        .enumerate()
        .filter_map(|(index, symbol)| {
            call.exact_integer_arguments
                .get(index)
                .copied()
                .flatten()
                .map(|value| (*symbol, IntegerPolynomial::constant(i128::from(value))))
        })
        .collect()
}

fn exact_integer_scalar_bindings(
    parameters: &[SymbolId],
    call: &ProvenOriginDirectCall,
) -> HashMap<SymbolId, i64> {
    parameters
        .iter()
        .enumerate()
        .filter_map(|(index, symbol)| {
            call.exact_integer_arguments
                .get(index)
                .copied()
                .flatten()
                .map(|value| (*symbol, value))
        })
        .collect()
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
    let bindings = exact_integer_bindings(parameters, call);
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

fn slow_sequence<'a>(
    function: &'a Function<'a>,
) -> Option<&'a oxc_ast::ast::SequenceExpression<'a>> {
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
    let [guarded, _] = return_sequence.expressions.as_slice() else {
        return None;
    };
    let Expression::LogicalExpression(logical) = last_sequence_expression(guarded) else {
        return None;
    };
    if logical.operator.as_str() != "&&" {
        return None;
    }
    let Expression::SequenceExpression(sequence) = strip_parentheses(&logical.right) else {
        return None;
    };
    Some(sequence)
}

fn flatten_top_level_sequence<'a>(
    expression: &'a Expression<'a>,
    out: &mut Vec<&'a Expression<'a>>,
) {
    match strip_parentheses(expression) {
        Expression::SequenceExpression(sequence) => {
            for expression in &sequence.expressions {
                flatten_top_level_sequence(expression, out);
            }
        }
        expression => out.push(expression),
    }
}

fn exact_integer_value(
    expression: &Expression<'_>,
    scoping: &Scoping,
    bindings: &HashMap<SymbolId, IntegerPolynomial>,
) -> Option<i64> {
    let value = normalize_integer_polynomial(
        expression,
        scoping,
        bindings,
        &HashMap::new(),
        &HashSet::new(),
    )?
    .constant_value()?;
    i64::try_from(value).ok()
}

fn exact_js_integer_add(left: i64, right: i64) -> Option<i64> {
    const MAX_SAFE_INTEGER: i128 = 9_007_199_254_740_991;
    let value = i128::from(left).checked_add(i128::from(right))?;
    (value.abs() <= MAX_SAFE_INTEGER)
        .then(|| i64::try_from(value).ok())
        .flatten()
}

fn update_selector_capture_symbol(
    expression: &Expression<'_>,
    scoping: &Scoping,
    update_parameter: SymbolId,
) -> Option<SymbolId> {
    struct Probe<'s> {
        scoping: &'s Scoping,
        update_parameter: SymbolId,
        targets: Vec<SymbolId>,
    }
    impl<'a> Visit<'a> for Probe<'_> {
        fn visit_assignment_expression(
            &mut self,
            assignment: &oxc_ast::ast::AssignmentExpression<'a>,
        ) {
            if assignment.operator.is_assign()
                && reference_symbol(self.scoping, &assignment.right) == Some(self.update_parameter)
            {
                if let Some(target) = assignment_symbol(self.scoping, &assignment.left) {
                    self.targets.push(target);
                }
            }
            walk::walk_assignment_expression(self, assignment);
        }
        fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
        fn visit_arrow_function_expression(
            &mut self,
            _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
        ) {
        }
    }
    let mut probe = Probe {
        scoping,
        update_parameter,
        targets: Vec::new(),
    };
    probe.visit_expression(expression);
    probe.targets.sort_unstable();
    probe.targets.dedup();
    let [target] = probe.targets.as_slice() else {
        return None;
    };
    Some(*target)
}

fn analyze_slow_lazy_cell_update_state(
    function: &Function<'_>,
    semantic: &Semantic<'_>,
    factory_call: &ProvenSlowLazyCellFactoryCall,
) -> Option<ProvenSlowLazyCellUpdateState> {
    let shape = &factory_call.shape;
    let parameters = parameter_symbols(function)?;
    let sequence = slow_sequence(function)?;
    let initialization = sequence.expressions.iter().find_map(|expression| {
        let assignment = assignment_expression(expression)?;
        (assignment.span.start == shape.index_state_initialization_start
            && assignment.span.end == shape.index_state_initialization_end)
            .then_some(assignment)
    })?;
    if assignment_symbol(semantic.scoping(), &initialization.left) != Some(shape.index_state_symbol)
    {
        return None;
    }

    let mut bindings = exact_integer_bindings(&parameters, &factory_call.call);
    let initial_state_value =
        exact_integer_value(&initialization.right, semantic.scoping(), &bindings)?;
    bindings.insert(
        shape.index_state_symbol,
        IntegerPolynomial::constant(i128::from(initial_state_value)),
    );

    let mut updates = sequence.expressions.iter().filter_map(|expression| {
        let assignment = assignment_expression(expression)?;
        let Expression::FunctionExpression(update) = last_sequence_expression(&assignment.right)
        else {
            return None;
        };
        (update.span.start == shape.update_function_start
            && update.span.end == shape.update_function_end)
            .then_some(update)
    });
    let update = updates.next()?;
    if updates.next().is_some()
        || update.r#async
        || update.generator
        || function_subtree_has_dynamic_scope(update)
        || update
            .body
            .as_deref()
            .is_none_or(function_body_uses_arguments)
    {
        return None;
    }
    let update_parameters = parameter_symbols(update)?;
    let [update_parameter] = update_parameters.as_slice() else {
        return None;
    };
    let body = update.body.as_ref()?;
    let [Statement::ExpressionStatement(statement)] = body.statements.as_slice() else {
        return None;
    };
    let mut items = Vec::new();
    flatten_top_level_sequence(&statement.expression, &mut items);
    let [first_expression, second_expression] = items.as_slice() else {
        return None;
    };
    let Expression::AssignmentExpression(first) = strip_parentheses(first_expression) else {
        return None;
    };
    let Expression::AssignmentExpression(second) = strip_parentheses(second_expression) else {
        return None;
    };
    if first.operator.as_str() != "+="
        || second.operator.as_str() != "&="
        || assignment_symbol(semantic.scoping(), &first.left) != Some(shape.index_state_symbol)
        || assignment_symbol(semantic.scoping(), &second.left) != Some(shape.index_state_symbol)
    {
        return None;
    }

    let expected_writes = HashSet::from([
        (first.span.start, first.span.end),
        (second.span.start, second.span.end),
    ]);
    let mut actual_writes = HashSet::new();
    for reference_id in semantic
        .scoping()
        .get_resolved_reference_ids(shape.index_state_symbol)
    {
        let reference = semantic.scoping().get_reference(*reference_id);
        if !reference.is_write()
            || enclosing_function_span(semantic, reference.node_id()) != Some(update.span)
        {
            continue;
        }
        let span = enclosing_write_event_span(semantic, reference.node_id())?;
        actual_writes.insert((span.start, span.end));
    }
    if actual_writes != expected_writes {
        return None;
    }

    let selector_capture_symbol =
        update_selector_capture_symbol(&first.right, semantic.scoping(), *update_parameter)?;
    let declaration = semantic.scoping().symbol_span(selector_capture_symbol);
    if !(function.span.start <= declaration.start
        && declaration.end <= function.span.end
        && !(update.span.start <= declaration.start && declaration.end <= update.span.end))
    {
        return None;
    }

    let delta = exact_integer_value(&first.right, semantic.scoping(), &bindings)?;
    let after_add = exact_js_integer_add(initial_state_value, delta)?;
    bindings.insert(
        shape.index_state_symbol,
        IntegerPolynomial::constant(i128::from(after_add)),
    );
    let mask = exact_integer_value(&second.right, semantic.scoping(), &bindings)?;
    let post_update_state_value = eval_js_bitwise_i64("&", after_add, mask)?;

    Some(ProvenSlowLazyCellUpdateState {
        factory_call: factory_call.clone(),
        initial_state_value,
        post_update_state_value,
        selector_capture_symbol,
        update_parameter_symbol: *update_parameter,
    })
}

/// Prove the exact scalar state established by the installed one-argument
/// slow-cell update and identify the closure binding that receives its selector.
///
/// The supported update is deliberately narrow: two top-level writes to the
/// factory's captured index state, first `+=` and then `&=`, with an exact
/// integer result under the call's exact arguments. A direct assignment from
/// the update parameter must occur inside the `+=` RHS, and no additional
/// writes to the index-state binding are allowed in the update body.
#[must_use]
pub fn proven_slow_lazy_cell_update_state(
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    factory_call: &ProvenSlowLazyCellFactoryCall,
) -> Option<ProvenSlowLazyCellUpdateState> {
    struct Harness<'m, 'c> {
        semantic: &'m Semantic<'m>,
        factory_call: &'c ProvenSlowLazyCellFactoryCall,
        result: Option<Option<ProvenSlowLazyCellUpdateState>>,
    }
    impl<'a> Visit<'a> for Harness<'_, '_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if self.result.is_some() {
                return;
            }
            let shape = &self.factory_call.shape;
            if function.span.start == shape.function_start
                && function.span.end == shape.function_end
            {
                self.result = Some(analyze_slow_lazy_cell_update_state(
                    function,
                    self.semantic,
                    self.factory_call,
                ));
                return;
            }
            walk::walk_function(self, function, flags);
        }
    }
    let mut harness = Harness {
        semantic,
        factory_call,
        result: None,
    };
    harness.visit_program(program);
    harness.result.flatten()
}

fn registry_receiver_and_path<'a>(
    expression: &'a Expression<'a>,
) -> Option<(&'a Expression<'a>, Vec<String>)> {
    match strip_parentheses(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => {
            let (receiver, mut path) = registry_receiver_and_path(&member.object)?;
            path.push(member.property.name.to_string());
            Some((receiver, path))
        }
        expression => Some((expression, Vec::new())),
    }
}

/// Prove that a specialized slow-cell factory call is directly stored into a
/// computed registry slot whose key is passed through one factory parameter.
///
/// The registry receiver must be the same symbol as the factory's proven
/// exact-origin state argument. The computed key must be the unique
/// symbol-resolved call argument matching the assignment key. This establishes
/// the structural key bridge only; it does not prove later reads see this write.
#[must_use]
pub fn proven_slow_lazy_cell_registry_assignment(
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    factory_call: &ProvenSlowLazyCellFactoryCall,
) -> Option<ProvenSlowLazyCellRegistryAssignment> {
    let shape = &factory_call.shape;
    let state_argument = factory_call
        .call
        .argument_spans
        .get(shape.state_parameter_index)
        .copied()?;

    let mut factory_parameters = None;
    struct Parameters<'o> {
        start: u32,
        end: u32,
        output: &'o mut Option<Vec<SymbolId>>,
    }
    impl<'a> Visit<'a> for Parameters<'_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if function.span.start == self.start && function.span.end == self.end {
                *self.output = parameter_symbols(function);
                return;
            }
            walk::walk_function(self, function, flags);
        }
    }
    Parameters {
        start: shape.function_start,
        end: shape.function_end,
        output: &mut factory_parameters,
    }
    .visit_program(program);
    let factory_parameters = factory_parameters?;

    struct Collector<'s, 'c, 'p> {
        scoping: &'s Scoping,
        call: &'c ProvenOriginDirectCall,
        state_argument: (u32, u32),
        factory_parameters: &'p [SymbolId],
        proven: Vec<ProvenSlowLazyCellRegistryAssignment>,
        factory_call: &'c ProvenSlowLazyCellFactoryCall,
    }
    impl<'a> Visit<'a> for Collector<'_, '_, '_> {
        fn visit_assignment_expression(
            &mut self,
            assignment: &oxc_ast::ast::AssignmentExpression<'a>,
        ) {
            if !assignment.operator.is_assign() {
                walk::walk_assignment_expression(self, assignment);
                return;
            }
            let Expression::CallExpression(call) = last_sequence_expression(&assignment.right)
            else {
                walk::walk_assignment_expression(self, assignment);
                return;
            };
            if call.span.start != self.call.call_start || call.span.end != self.call.call_end {
                walk::walk_assignment_expression(self, assignment);
                return;
            }
            let AssignmentTarget::ComputedMemberExpression(member) = &assignment.left else {
                walk::walk_assignment_expression(self, assignment);
                return;
            };
            if member.optional {
                walk::walk_assignment_expression(self, assignment);
                return;
            }
            let Some((receiver, registry_path)) = registry_receiver_and_path(&member.object) else {
                walk::walk_assignment_expression(self, assignment);
                return;
            };
            if registry_path.is_empty() {
                walk::walk_assignment_expression(self, assignment);
                return;
            }
            let Some(receiver_symbol) = reference_symbol(self.scoping, receiver) else {
                walk::walk_assignment_expression(self, assignment);
                return;
            };
            let state_symbol = call.arguments.iter().find_map(|argument| {
                let expression = argument.as_expression()?;
                let span = expression.span();
                ((span.start, span.end) == self.state_argument)
                    .then(|| reference_symbol(self.scoping, expression))
                    .flatten()
            });
            if state_symbol != Some(receiver_symbol) {
                walk::walk_assignment_expression(self, assignment);
                return;
            }
            let Some(key_symbol) = reference_symbol(self.scoping, &member.expression) else {
                walk::walk_assignment_expression(self, assignment);
                return;
            };
            let matching_arguments = call
                .arguments
                .iter()
                .enumerate()
                .filter_map(|(index, argument)| {
                    let expression = argument.as_expression()?;
                    (reference_symbol(self.scoping, expression) == Some(key_symbol))
                        .then_some(index)
                })
                .collect::<Vec<_>>();
            let [key_parameter_index] = matching_arguments.as_slice() else {
                walk::walk_assignment_expression(self, assignment);
                return;
            };
            let Some(factory_key_symbol) = self.factory_parameters.get(*key_parameter_index) else {
                walk::walk_assignment_expression(self, assignment);
                return;
            };
            self.proven.push(ProvenSlowLazyCellRegistryAssignment {
                factory_call: self.factory_call.clone(),
                registry_path,
                receiver_start: receiver.span().start,
                receiver_end: receiver.span().end,
                key_start: member.expression.span().start,
                key_end: member.expression.span().end,
                registry_key_symbol: key_symbol,
                factory_key_parameter_index: *key_parameter_index,
                factory_key_symbol: *factory_key_symbol,
            });
            walk::walk_assignment_expression(self, assignment);
        }
    }

    let mut collector = Collector {
        scoping: semantic.scoping(),
        call: &factory_call.call,
        state_argument,
        factory_parameters: &factory_parameters,
        proven: Vec::new(),
        factory_call,
    };
    collector.visit_program(program);
    let [proven] = collector.proven.as_slice() else {
        return None;
    };
    Some(proven.clone())
}

fn function_parameter_symbols_at(
    program: &Program<'_>,
    start: u32,
    end: u32,
) -> Option<Vec<SymbolId>> {
    struct Probe<'o> {
        start: u32,
        end: u32,
        output: &'o mut Option<Vec<SymbolId>>,
    }
    impl<'a> Visit<'a> for Probe<'_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if function.span.start == self.start && function.span.end == self.end {
                *self.output = parameter_symbols(function);
                return;
            }
            walk::walk_function(self, function, flags);
        }
    }

    let mut output = None;
    Probe {
        start,
        end,
        output: &mut output,
    }
    .visit_program(program);
    output
}

fn call_argument_symbol_at(
    program: &Program<'_>,
    scoping: &Scoping,
    call_start: u32,
    call_end: u32,
    argument_index: usize,
) -> Option<SymbolId> {
    struct Probe<'c, 'o> {
        scoping: &'c Scoping,
        call_start: u32,
        call_end: u32,
        argument_index: usize,
        output: &'o mut Option<Option<SymbolId>>,
    }
    impl<'a> Visit<'a> for Probe<'_, '_> {
        fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
            if self.output.is_some() {
                return;
            }
            if call.span.start == self.call_start && call.span.end == self.call_end {
                *self.output = Some(
                    call.arguments
                        .get(self.argument_index)
                        .and_then(|argument| argument.as_expression())
                        .and_then(|expression| reference_symbol(self.scoping, expression)),
                );
                return;
            }
            walk::walk_call_expression(self, call);
        }
    }

    let mut output = None;
    Probe {
        scoping,
        call_start,
        call_end,
        argument_index,
        output: &mut output,
    }
    .visit_program(program);
    output.flatten()
}

fn symbol_only_forwarded_at_direct_call(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    symbol: SymbolId,
    function_span: Span,
    incoming: &ProvenOriginDirectCall,
    exact_integer_parameter: (usize, i64),
    call: &ProvenOriginDirectCall,
    argument_index: usize,
) -> bool {
    let Some((argument_start, argument_end)) = call.argument_spans.get(argument_index).copied()
    else {
        return false;
    };
    let argument = Span::new(argument_start, argument_end);
    let call_span = Span::new(call.call_start, call.call_end);
    let mut specialized_incoming = incoming.clone();
    let Some(argument_value) = specialized_incoming
        .exact_integer_arguments
        .get_mut(exact_integer_parameter.0)
    else {
        return false;
    };
    match *argument_value {
        Some(existing) if existing != exact_integer_parameter.1 => return false,
        _ => *argument_value = Some(exact_integer_parameter.1),
    }
    let mut allowed_references = 0usize;
    let mut barriers = Vec::new();

    for reference_id in semantic.scoping().get_resolved_reference_ids(symbol) {
        let reference = semantic.scoping().get_reference(*reference_id);
        let node = semantic.nodes().get_node(reference.node_id());
        let span = node.kind().span();
        if enclosing_function_span(semantic, reference.node_id()) != Some(function_span) {
            return false;
        }
        if argument.start <= span.start && span.end <= argument.end {
            if reference.is_write() {
                return false;
            }
            allowed_references += 1;
            continue;
        }
        if call_span.start <= span.start && span.end <= call_span.end {
            return false;
        }
        if !proven_origin_direct_call_event_unreachable(
            source,
            program,
            semantic.scoping(),
            &specialized_incoming,
            span,
        ) {
            barriers.push(span);
        }
    }

    allowed_references == 1
        && (prove_event_before_barriers(semantic, call_span, &barriers)
            || prove_function_if_ladder_event_before_barriers(
                source,
                program,
                function_span.start,
                function_span.end,
                call_span,
                &barriers,
            ))
}

fn event_unreachable_with_integer_parameter(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    function_start: u32,
    function_end: u32,
    event: Span,
    parameter_index: usize,
    value: i64,
    provided_argument_count: usize,
) -> bool {
    let bindings = BTreeMap::from([(parameter_index, value)]);
    prove_function_if_ladder_event_unreachable_with_integer_parameters(
        source,
        program,
        scoping,
        function_start,
        function_end,
        event,
        &bindings,
    ) || prove_function_switch_event_unreachable_with_integer_parameters(
        program,
        scoping,
        function_start,
        function_end,
        event,
        &bindings,
    ) || prove_function_structured_branch_event_unreachable_with_integer_parameters(
        program,
        scoping,
        function_start,
        function_end,
        event,
        &bindings,
    ) || prove_function_protected_if_ladder_event_unreachable_with_call_arguments(
        source,
        program,
        scoping,
        function_start,
        function_end,
        event,
        provided_argument_count,
        &bindings,
    )
}

fn exact_integer_parameter_provenance(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    flow: &crate::receiver_identity::ProvenOriginFlow,
    context: &crate::receiver_identity::ProvenOriginContext,
    symbol: SymbolId,
    event: Span,
    visiting: &mut HashSet<(crate::receiver_identity::ProvenOriginContext, SymbolId)>,
) -> Vec<(i64, Vec<ProvenOriginDirectCall>)> {
    if !visiting.insert((context.clone(), symbol)) {
        return Vec::new();
    }
    let Some(parameters) =
        function_parameter_symbols_at(program, context.function_start, context.function_end)
    else {
        visiting.remove(&(context.clone(), symbol));
        return Vec::new();
    };
    let indices = parameters
        .iter()
        .enumerate()
        .filter_map(|(index, candidate)| (*candidate == symbol).then_some(index))
        .collect::<Vec<_>>();
    let [parameter_index] = indices.as_slice() else {
        visiting.remove(&(context.clone(), symbol));
        return Vec::new();
    };
    let function_span = Span::new(context.function_start, context.function_end);
    let mut proven = Vec::new();

    for incoming in flow
        .direct_calls
        .iter()
        .filter(|call| call.callee == *context)
    {
        if proven_origin_direct_call_event_unreachable(
            source,
            program,
            semantic.scoping(),
            incoming,
            event,
        ) || !parameter_binding_preserved_before_event(
            source,
            program,
            semantic,
            incoming,
            function_span,
            symbol,
            event,
        ) {
            continue;
        }
        if let Some(value) = incoming
            .exact_integer_arguments
            .get(*parameter_index)
            .copied()
            .flatten()
        {
            proven.push((value, vec![incoming.clone()]));
            continue;
        }
        let Some(parent_symbol) = call_argument_symbol_at(
            program,
            semantic.scoping(),
            incoming.call_start,
            incoming.call_end,
            *parameter_index,
        ) else {
            continue;
        };
        let parent_event = Span::new(incoming.call_start, incoming.call_end);
        for (value, mut chain) in exact_integer_parameter_provenance(
            source,
            program,
            semantic,
            flow,
            &incoming.caller,
            parent_symbol,
            parent_event,
            visiting,
        ) {
            if event_unreachable_with_integer_parameter(
                source,
                program,
                semantic.scoping(),
                context.function_start,
                context.function_end,
                event,
                *parameter_index,
                value,
                incoming.argument_spans.len(),
            ) {
                continue;
            }
            chain.push(incoming.clone());
            proven.push((value, chain));
        }
    }

    visiting.remove(&(context.clone(), symbol));
    proven
}

/// Specialize one structural M-style registry assignment to exact registry keys
/// carried through a proven direct-call parameter chain.
///
/// This supports both direct installers and forwarding/delegating helpers. Each
/// proof records the exact chain that carries the unchanged key into the
/// enclosing M-style installer, so downstream handler provenance can use the
/// same path rather than joining unrelated calls that happen to share a helper.
#[must_use]
pub fn proven_slow_lazy_cell_exact_registry_assignments(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    flow: &crate::receiver_identity::ProvenOriginFlow,
    assignment: &ProvenSlowLazyCellRegistryAssignment,
) -> Vec<ProvenSlowLazyCellExactRegistryAssignment> {
    let caller_context = &assignment.factory_call.call.caller;
    let Some(caller_parameters) = function_parameter_symbols_at(
        program,
        caller_context.function_start,
        caller_context.function_end,
    ) else {
        return Vec::new();
    };
    let key_indices = caller_parameters
        .iter()
        .enumerate()
        .filter_map(|(index, symbol)| (*symbol == assignment.registry_key_symbol).then_some(index))
        .collect::<Vec<_>>();
    let [key_parameter_index] = key_indices.as_slice() else {
        return Vec::new();
    };
    let event = Span::new(
        assignment.factory_call.call.call_start,
        assignment.factory_call.call.call_end,
    );
    let mut visiting = HashSet::new();
    let mut proven = exact_integer_parameter_provenance(
        source,
        program,
        semantic,
        flow,
        caller_context,
        assignment.registry_key_symbol,
        event,
        &mut visiting,
    )
    .into_iter()
    .filter_map(|(exact_key_value, provenance_calls)| {
        let caller = provenance_calls.last()?.clone();
        if event_unreachable_with_integer_parameter(
            source,
            program,
            semantic.scoping(),
            caller_context.function_start,
            caller_context.function_end,
            event,
            *key_parameter_index,
            exact_key_value,
            caller.argument_spans.len(),
        ) {
            return None;
        }
        Some(ProvenSlowLazyCellExactRegistryAssignment {
            assignment: assignment.clone(),
            caller,
            provenance_calls,
            exact_key_value,
        })
    })
    .collect::<Vec<_>>();
    proven.sort_by_key(|proof| {
        (
            proof
                .provenance_calls
                .first()
                .map_or(u32::MAX, |call| call.call_start),
            proof.caller.call_start,
            proof.exact_key_value,
        )
    });
    proven.dedup();
    proven
}

fn unique_argument_containing(
    argument_spans: &[(u32, u32)],
    start: u32,
    end: u32,
) -> Option<usize> {
    let mut matches = argument_spans
        .iter()
        .enumerate()
        .filter(|(_, (argument_start, argument_end))| {
            *argument_start <= start && end <= *argument_end
        })
        .map(|(index, _)| index);
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn proven_slow_lazy_cell_captured_value_path(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    exact_assignment: &ProvenSlowLazyCellExactRegistryAssignment,
    install_call_start: u32,
    install_call_end: u32,
    install_key_start: u32,
    install_key_end: u32,
    install_value_start: u32,
    install_value_end: u32,
    install_registry_path: &[String],
    install_origin: &crate::registry_identity::ProvenRegistryObjectOrigin,
    install_exact_key: i64,
) -> Option<(usize, SymbolId)> {
    let chain = &exact_assignment.provenance_calls;
    let root = chain.first()?;
    let final_call = chain.last()?;
    if final_call != &exact_assignment.caller
        || (root.call_start, root.call_end) != (install_call_start, install_call_end)
        || exact_assignment.exact_key_value != install_exact_key
        || exact_assignment.assignment.registry_path != install_registry_path
        || crate::registry_identity::ProvenRegistryObjectOrigin::from(&root.callee)
            != *install_origin
    {
        return None;
    }

    let root_value_parameter_index =
        unique_argument_containing(&root.argument_spans, install_value_start, install_value_end)?;
    let root_key_parameter_index =
        unique_argument_containing(&root.argument_spans, install_key_start, install_key_end)?;
    let root_parameters = function_parameter_symbols_at(
        program,
        root.callee.function_start,
        root.callee.function_end,
    )?;
    let mut current_symbol = *root_parameters.get(root_value_parameter_index)?;
    let mut current_key_parameter_index = root_key_parameter_index;
    let mut current_key_symbol = *root_parameters.get(root_key_parameter_index)?;
    let mut current_context = root.callee.clone();
    let mut incoming = root.clone();

    for next in chain.iter().skip(1) {
        if next.caller != current_context {
            return None;
        }
        let event = Span::new(next.call_start, next.call_end);
        if !parameter_binding_preserved_before_event(
            source,
            program,
            semantic,
            &incoming,
            Span::new(current_context.function_start, current_context.function_end),
            current_symbol,
            event,
        ) {
            return None;
        }
        let matching_arguments = (0..next.argument_spans.len())
            .filter(|index| {
                call_argument_symbol_at(
                    program,
                    semantic.scoping(),
                    next.call_start,
                    next.call_end,
                    *index,
                ) == Some(current_symbol)
            })
            .collect::<Vec<_>>();
        let [next_parameter_index] = matching_arguments.as_slice() else {
            return None;
        };
        if !symbol_only_forwarded_at_direct_call(
            source,
            program,
            semantic,
            current_symbol,
            Span::new(current_context.function_start, current_context.function_end),
            &incoming,
            (
                current_key_parameter_index,
                exact_assignment.exact_key_value,
            ),
            next,
            *next_parameter_index,
        ) {
            return None;
        }
        let matching_key_arguments = (0..next.argument_spans.len())
            .filter(|index| {
                call_argument_symbol_at(
                    program,
                    semantic.scoping(),
                    next.call_start,
                    next.call_end,
                    *index,
                ) == Some(current_key_symbol)
            })
            .collect::<Vec<_>>();
        let [next_key_parameter_index] = matching_key_arguments.as_slice() else {
            return None;
        };
        let next_parameters = function_parameter_symbols_at(
            program,
            next.callee.function_start,
            next.callee.function_end,
        )?;
        current_symbol = *next_parameters.get(*next_parameter_index)?;
        current_key_symbol = *next_parameters.get(*next_key_parameter_index)?;
        current_key_parameter_index = *next_key_parameter_index;
        current_context = next.callee.clone();
        incoming = next.clone();
    }

    let factory_caller = &exact_assignment.assignment.factory_call.call.caller;
    if current_context != *factory_caller {
        return None;
    }

    let mut nested_value_symbol = None;
    struct Probe<'o> {
        nested_call_start: u32,
        nested_call_end: u32,
        nested_value_index: usize,
        scoping: &'o Scoping,
        nested_value_symbol: &'o mut Option<SymbolId>,
    }
    impl<'a> Visit<'a> for Probe<'_> {
        fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
            if call.span.start == self.nested_call_start && call.span.end == self.nested_call_end {
                *self.nested_value_symbol = call
                    .arguments
                    .get(self.nested_value_index)
                    .and_then(|argument| argument.as_expression())
                    .and_then(|expression| reference_symbol(self.scoping, expression));
                return;
            }
            walk::walk_call_expression(self, call);
        }
    }
    Probe {
        nested_call_start: exact_assignment.assignment.factory_call.call.call_start,
        nested_call_end: exact_assignment.assignment.factory_call.call.call_end,
        nested_value_index: exact_assignment
            .assignment
            .factory_call
            .shape
            .handler_parameter_index,
        scoping: semantic.scoping(),
        nested_value_symbol: &mut nested_value_symbol,
    }
    .visit_program(program);
    if nested_value_symbol != Some(current_symbol)
        || !symbol_only_forwarded_at_direct_call(
            source,
            program,
            semantic,
            current_symbol,
            Span::new(factory_caller.function_start, factory_caller.function_end),
            &incoming,
            (
                current_key_parameter_index,
                exact_assignment.exact_key_value,
            ),
            &exact_assignment.assignment.factory_call.call,
            exact_assignment
                .assignment
                .factory_call
                .shape
                .handler_parameter_index,
        )
    {
        return None;
    }

    let event = Span::new(
        exact_assignment.assignment.factory_call.call.call_start,
        exact_assignment.assignment.factory_call.call.call_end,
    );
    if !parameter_binding_preserved_before_event(
        source,
        program,
        semantic,
        &incoming,
        Span::new(factory_caller.function_start, factory_caller.function_end),
        current_symbol,
        event,
    ) {
        return None;
    }

    Some((root_value_parameter_index, current_symbol))
}

/// Join one exact slow-cell registry assignment to any logical forwarding
/// install whose original value feeds the wrapper. The same exact object-origin,
/// key-provenance, binding-preservation, and no-use-before-forwarding barriers
/// used for logical function handlers are required for arbitrary values.
#[must_use]
pub fn proven_slow_lazy_cell_captured_value_install(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    exact_assignment: &ProvenSlowLazyCellExactRegistryAssignment,
    install: &crate::registry_identity::ProvenOriginRegistryValueInstall,
) -> Option<ProvenSlowLazyCellCapturedValueInstall> {
    let (caller_value_parameter_index, caller_value_symbol) =
        proven_slow_lazy_cell_captured_value_path(
            source,
            program,
            semantic,
            exact_assignment,
            install.install.call_start,
            install.install.call_end,
            install.install.key_start,
            install.install.key_end,
            install.install.value_start,
            install.install.value_end,
            &install.install.registry_path,
            &install.origin,
            install.exact_key,
        )?;
    Some(ProvenSlowLazyCellCapturedValueInstall {
        exact_assignment: exact_assignment.clone(),
        install: install.clone(),
        caller_value_parameter_index,
        caller_value_symbol,
    })
}

/// Specialize an already-proven arbitrary captured value to the function-valued
/// handler view without replaying the provenance proof.
///
/// The handler install must be the exact same structural install already joined
/// by `captured_value`: same call, receiver, key, value span, registry path,
/// object origin, and exact key. This is therefore only a lossless view change;
/// it adds independently proven function-literal metadata and no new flow
/// assumption.
#[must_use]
pub fn proven_slow_lazy_cell_captured_handler_from_value(
    captured_value: &ProvenSlowLazyCellCapturedValueInstall,
    install: &crate::registry_identity::ProvenOriginRegistryHandlerInstall,
) -> Option<ProvenSlowLazyCellCapturedHandlerInstall> {
    let value = &captured_value.install;
    let value_call = &value.install;
    let handler_call = &install.install;
    if value.origin != install.origin
        || value.exact_key != install.exact_key
        || value_call.call_start != handler_call.call_start
        || value_call.call_end != handler_call.call_end
        || value_call.receiver_start != handler_call.receiver_start
        || value_call.receiver_end != handler_call.receiver_end
        || value_call.key_start != handler_call.key_start
        || value_call.key_end != handler_call.key_end
        || value_call.value_start != handler_call.handler_start
        || value_call.value_end != handler_call.handler_end
        || value_call.registry_path != handler_call.registry_path
    {
        return None;
    }
    Some(ProvenSlowLazyCellCapturedHandlerInstall {
        exact_assignment: captured_value.exact_assignment.clone(),
        install: install.clone(),
        caller_handler_parameter_index: captured_value.caller_value_parameter_index,
        caller_handler_symbol: captured_value.caller_value_symbol,
    })
}

/// Join one exact slow-cell registry assignment to the logical forwarding
/// install whose original handler feeds the wrapper.
///
/// This is the function-valued specialization of the generic captured-value
/// theorem above; it intentionally preserves the old handler-only API.
#[must_use]
pub fn proven_slow_lazy_cell_captured_handler_install(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    exact_assignment: &ProvenSlowLazyCellExactRegistryAssignment,
    install: &crate::registry_identity::ProvenOriginRegistryHandlerInstall,
) -> Option<ProvenSlowLazyCellCapturedHandlerInstall> {
    let (caller_handler_parameter_index, caller_handler_symbol) =
        proven_slow_lazy_cell_captured_value_path(
            source,
            program,
            semantic,
            exact_assignment,
            install.install.call_start,
            install.install.call_end,
            install.install.key_start,
            install.install.key_end,
            install.install.handler_start,
            install.install.handler_end,
            &install.install.registry_path,
            &install.origin,
            install.exact_key,
        )?;
    Some(ProvenSlowLazyCellCapturedHandlerInstall {
        exact_assignment: exact_assignment.clone(),
        install: install.clone(),
        caller_handler_parameter_index,
        caller_handler_symbol,
    })
}

/// Join the independently proven resolver index and captured logical handler.
/// Slot equality is already discharged by the resolver theorem; this step only
/// requires both proofs to refer to the same exact wrapper assignment.
#[must_use]
pub fn proven_slow_lazy_cell_resolved_handler(
    resolver: &ProvenSlowLazyCellResolverIndex,
    captured_handler: &ProvenSlowLazyCellCapturedHandlerInstall,
) -> Option<ProvenSlowLazyCellResolvedHandler> {
    (resolver.exact_assignment == captured_handler.exact_assignment).then(|| {
        ProvenSlowLazyCellResolvedHandler {
            resolver: resolver.clone(),
            captured_handler: captured_handler.clone(),
        }
    })
}

/// Join all independently proven slow-cell obligations for one exact wrapper.
#[must_use]
pub fn proven_slow_lazy_cell_read_result(
    resolved_handler: &ProvenSlowLazyCellResolvedHandler,
    carrier: &ProvenSlowLazyCellPrototypeCarrier,
) -> Option<ProvenSlowLazyCellReadResult> {
    let resolver = &resolved_handler.resolver;
    let exact_assignment = &resolver.exact_assignment;
    let factory_call = &resolver.update_state.factory_call;
    let accessor = &carrier.accessor;
    if resolved_handler.captured_handler.exact_assignment != *exact_assignment
        || carrier.state_fields.exact_assignment != *exact_assignment
        || carrier.state_fields.fields.factory_call != *factory_call
        || exact_assignment.assignment.factory_call != *factory_call
        || accessor.read.registry_path != exact_assignment.assignment.registry_path
        || accessor.selector_start != resolver.selector_start
        || accessor.selector_end != resolver.selector_end
        || accessor.selector_key_symbol != resolver.selector_key_symbol
        || carrier.method_name != accessor.update_property
        || carrier.projection_property != accessor.projection_property
        || carrier.resolver_property != factory_call.shape.resolver_property
    {
        return None;
    }
    Some(ProvenSlowLazyCellReadResult {
        resolved_handler: resolved_handler.clone(),
        carrier: carrier.clone(),
    })
}

fn assignment_at_span<'a>(
    sequence: &'a oxc_ast::ast::SequenceExpression<'a>,
    start: u32,
    end: u32,
) -> Option<&'a oxc_ast::ast::AssignmentExpression<'a>> {
    sequence.expressions.iter().find_map(|expression| {
        let assignment = assignment_expression(expression)?;
        (assignment.span.start == start && assignment.span.end == end).then_some(assignment)
    })
}

fn binding_stable_after_capture(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    factory_call: &ProvenSlowLazyCellFactoryCall,
    symbol: SymbolId,
    capture: Span,
) -> bool {
    let factory_span = Span::new(
        factory_call.shape.function_start,
        factory_call.shape.function_end,
    );
    for reference_id in semantic.scoping().get_resolved_reference_ids(symbol) {
        let reference = semantic.scoping().get_reference(*reference_id);
        if !reference.is_write() {
            continue;
        }
        let Some(write) = enclosing_write_event_span(semantic, reference.node_id()) else {
            return false;
        };
        if write == capture {
            continue;
        }
        let Some(enclosing) = enclosing_function_span(semantic, reference.node_id()) else {
            return false;
        };
        if enclosing != factory_span {
            return false;
        }
        if write.start > capture.start
            && !proven_origin_direct_call_event_unreachable(
                source,
                program,
                semantic.scoping(),
                &factory_call.call,
                write,
            )
        {
            return false;
        }
    }
    true
}

fn binding_stable_from_factory_entry(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    factory_call: &ProvenSlowLazyCellFactoryCall,
    symbol: SymbolId,
) -> bool {
    let factory_span = Span::new(
        factory_call.shape.function_start,
        factory_call.shape.function_end,
    );
    semantic
        .scoping()
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| {
            let reference = semantic.scoping().get_reference(*reference_id);
            if !reference.is_write() {
                return true;
            }
            let Some(write) = enclosing_write_event_span(semantic, reference.node_id()) else {
                return false;
            };
            let Some(enclosing) = enclosing_function_span(semantic, reference.node_id()) else {
                return false;
            };
            enclosing == factory_span
                && proven_origin_direct_call_event_unreachable(
                    source,
                    program,
                    semantic.scoping(),
                    &factory_call.call,
                    write,
                )
        })
}

const MAX_SAFE_INTEGER: i128 = 9_007_199_254_740_991;

fn exact_js_safe_integer(value: i128) -> Option<i64> {
    (value.abs() <= MAX_SAFE_INTEGER)
        .then(|| i64::try_from(value).ok())
        .flatten()
}

fn exact_js_integer_unary(op: &str, value: i64) -> Option<i64> {
    match op {
        "+" => Some(value),
        "-" => exact_js_safe_integer(i128::from(value).checked_neg()?),
        "~" => eval_js_bitwise_i64("^", value, -1),
        _ => None,
    }
}

fn exact_js_integer_binary(op: &str, left: i64, right: i64) -> Option<i64> {
    let left128 = i128::from(left);
    let right128 = i128::from(right);
    match op {
        "+" => exact_js_safe_integer(left128.checked_add(right128)?),
        "-" => exact_js_safe_integer(left128.checked_sub(right128)?),
        "*" => exact_js_safe_integer(left128.checked_mul(right128)?),
        "%" if right != 0 => exact_js_safe_integer(left128.checked_rem(right128)?),
        "&" | "|" | "^" | "<<" | ">>" | ">>>" => eval_js_bitwise_i64(op, left, right),
        _ => None,
    }
}

fn exact_static_safe_integer(expression: &Expression<'_>) -> Option<i64> {
    match strip_parentheses(expression) {
        Expression::NumericLiteral(number) => {
            exact_js_safe_integer(i128::from(exact_i64(number.value)?))
        }
        Expression::UnaryExpression(unary) => exact_js_integer_unary(
            unary.operator.as_str(),
            exact_static_safe_integer(&unary.argument)?,
        ),
        Expression::BinaryExpression(binary) => exact_js_integer_binary(
            binary.operator.as_str(),
            exact_static_safe_integer(&binary.left)?,
            exact_static_safe_integer(&binary.right)?,
        ),
        _ => None,
    }
}

struct ExactSafeIntegerEvaluator<'s, 'h> {
    scoping: &'s Scoping,
    bindings: HashMap<SymbolId, i64>,
    local_assignment_span: Option<Span>,
    handler_symbol: Option<SymbolId>,
    handler_array: Option<&'h oxc_ast::ast::ArrayExpression<'h>>,
    phase_symbol: Option<SymbolId>,
    phase_value: Option<i64>,
    phase_calls: usize,
}

impl ExactSafeIntegerEvaluator<'_, '_> {
    fn eval(&mut self, expression: &Expression<'_>) -> Option<i64> {
        match strip_parentheses(expression) {
            Expression::NumericLiteral(number) => {
                exact_js_safe_integer(i128::from(exact_i64(number.value)?))
            }
            Expression::Identifier(_) => {
                let symbol = reference_symbol(self.scoping, expression)?;
                self.bindings.get(&symbol).copied()
            }
            Expression::UnaryExpression(unary) => {
                let value = self.eval(&unary.argument)?;
                exact_js_integer_unary(unary.operator.as_str(), value)
            }
            Expression::BinaryExpression(binary) => {
                let left = self.eval(&binary.left)?;
                let right = self.eval(&binary.right)?;
                exact_js_integer_binary(binary.operator.as_str(), left, right)
            }
            Expression::SequenceExpression(sequence) => {
                let mut value = None;
                for expression in &sequence.expressions {
                    value = Some(self.eval(expression)?);
                }
                value
            }
            Expression::AssignmentExpression(assignment) if assignment.operator.is_assign() => {
                let symbol = assignment_symbol(self.scoping, &assignment.left)?;
                let declaration = self.scoping.symbol_span(symbol);
                let local = self.local_assignment_span?;
                if !(local.start <= declaration.start && declaration.end <= local.end) {
                    return None;
                }
                let value = self.eval(&assignment.right)?;
                self.bindings.insert(symbol, value);
                Some(value)
            }
            Expression::CallExpression(call)
                if !call.optional
                    && call.arguments.is_empty()
                    && reference_symbol(self.scoping, &call.callee) == self.phase_symbol =>
            {
                self.phase_calls += 1;
                self.phase_value
            }
            Expression::ComputedMemberExpression(member)
                if !member.optional
                    && reference_symbol(self.scoping, &member.object) == self.handler_symbol =>
            {
                let index = usize::try_from(self.eval(&member.expression)?).ok()?;
                let array = self.handler_array?;
                let element = array.elements.get(index)?;
                let expression = match element {
                    ArrayExpressionElement::SpreadElement(_)
                    | ArrayExpressionElement::Elision(_) => {
                        return None;
                    }
                    element => element.as_expression()?,
                };
                exact_static_safe_integer(expression)
            }
            _ => None,
        }
    }
}

fn exact_selector_value(
    program: &Program<'_>,
    scoping: &Scoping,
    selector_start: u32,
    selector_end: u32,
    selector_key_symbol: SymbolId,
    exact_key_value: i64,
) -> Option<i64> {
    exact_js_safe_integer(i128::from(exact_key_value))?;

    struct Probe<'s> {
        scoping: &'s Scoping,
        selector_start: u32,
        selector_end: u32,
        selector_key_symbol: SymbolId,
        exact_key_value: i64,
        matches: Vec<Option<i64>>,
    }
    impl<'a> Visit<'a> for Probe<'_> {
        fn visit_expression(&mut self, expression: &Expression<'a>) {
            let span = expression.span();
            if span.start == self.selector_start && span.end == self.selector_end {
                let mut evaluator = ExactSafeIntegerEvaluator {
                    scoping: self.scoping,
                    bindings: HashMap::from([(self.selector_key_symbol, self.exact_key_value)]),
                    local_assignment_span: None,
                    handler_symbol: None,
                    handler_array: None,
                    phase_symbol: None,
                    phase_value: None,
                    phase_calls: 0,
                };
                self.matches.push(evaluator.eval(expression));
                return;
            }
            walk::walk_expression(self, expression);
        }
    }

    let mut probe = Probe {
        scoping,
        selector_start,
        selector_end,
        selector_key_symbol,
        exact_key_value,
        matches: Vec::new(),
    };
    probe.visit_program(program);
    let [value] = probe.matches.as_slice() else {
        return None;
    };
    *value
}

fn resolver_index_value(
    resolver: &Function<'_>,
    semantic: &Semantic<'_>,
    handler_symbol: SymbolId,
    handler_array: &oxc_ast::ast::ArrayExpression<'_>,
    phase_symbol: SymbolId,
    phase_value: i64,
    bindings: &HashMap<SymbolId, i64>,
) -> Option<(Span, i64)> {
    let body = resolver.body.as_ref()?;
    let Statement::ExpressionStatement(first) = body.statements.first()? else {
        return None;
    };

    struct Probe<'s, 'r, 'h, 'b> {
        semantic: &'s Semantic<'s>,
        resolver: &'r Function<'r>,
        handler_symbol: SymbolId,
        handler_array: &'h oxc_ast::ast::ArrayExpression<'h>,
        phase_symbol: SymbolId,
        phase_value: i64,
        bindings: &'b HashMap<SymbolId, i64>,
        matches: Vec<(Span, i64)>,
    }
    impl<'a> Visit<'a> for Probe<'_, 'a, 'a, '_> {
        fn visit_computed_member_expression(
            &mut self,
            member: &oxc_ast::ast::ComputedMemberExpression<'a>,
        ) {
            if reference_symbol(self.semantic.scoping(), &member.object)
                == Some(self.handler_symbol)
            {
                if let Some(index_symbol) =
                    reference_symbol(self.semantic.scoping(), &member.expression)
                {
                    let mut object_items = Vec::new();
                    flatten_top_level_sequence(&member.object, &mut object_items);
                    let mut assignments = object_items.into_iter().filter_map(|expression| {
                        let assignment = assignment_expression(expression)?;
                        (assignment_symbol(self.semantic.scoping(), &assignment.left)
                            == Some(index_symbol))
                        .then_some(assignment)
                    });
                    if let Some(assignment) = assignments.next() {
                        if assignments.next().is_none() {
                            let mut evaluator = ExactSafeIntegerEvaluator {
                                scoping: self.semantic.scoping(),
                                bindings: self.bindings.clone(),
                                local_assignment_span: Some(self.resolver.span),
                                handler_symbol: Some(self.handler_symbol),
                                handler_array: Some(self.handler_array),
                                phase_symbol: Some(self.phase_symbol),
                                phase_value: Some(self.phase_value),
                                phase_calls: 0,
                            };
                            if let Some(value) = evaluator.eval(&assignment.right) {
                                if evaluator.phase_calls == 1 {
                                    self.matches.push((assignment.span, value));
                                }
                            }
                        }
                    }
                }
            }
            walk::walk_computed_member_expression(self, member);
        }

        fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
        fn visit_arrow_function_expression(
            &mut self,
            _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
        ) {
        }
    }

    let mut probe = Probe {
        semantic,
        resolver,
        handler_symbol,
        handler_array,
        phase_symbol,
        phase_value,
        bindings,
        matches: Vec::new(),
    };
    probe.visit_expression(&first.expression);
    let [(span, value)] = probe.matches.as_slice() else {
        return None;
    };
    Some((*span, *value))
}

fn analyze_slow_lazy_cell_resolver_index(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    function: &Function<'_>,
    update_state: &ProvenSlowLazyCellUpdateState,
    selector_start: u32,
    selector_end: u32,
    selector_key_symbol: SymbolId,
    exact_assignment: &ProvenSlowLazyCellExactRegistryAssignment,
    phase_value: i64,
) -> Option<ProvenSlowLazyCellResolverIndex> {
    let factory_call = &update_state.factory_call;
    if exact_assignment.assignment.factory_call != *factory_call {
        return None;
    }
    let exact_key_value = exact_assignment.exact_key_value;
    let factory_key_symbol = exact_assignment.assignment.factory_key_symbol;
    let shape = &factory_call.shape;
    let parameters = parameter_symbols(function)?;
    let handler_symbol = *parameters.get(shape.handler_parameter_index)?;
    let sequence = slow_sequence(function)?;

    let handler_capture = assignment_at_span(
        sequence,
        shape.handler_capture_start,
        shape.handler_capture_end,
    )?;
    if assignment_symbol(semantic.scoping(), &handler_capture.left) != Some(handler_symbol) {
        return None;
    }
    let Expression::ArrayExpression(handler_array) =
        last_sequence_expression(&handler_capture.right)
    else {
        return None;
    };
    if !binding_stable_after_capture(
        source,
        program,
        semantic,
        factory_call,
        handler_symbol,
        handler_capture.span,
    ) || !binding_stable_after_capture(
        source,
        program,
        semantic,
        factory_call,
        shape.phase_local_symbol,
        Span::new(shape.phase_capture_start, shape.phase_capture_end),
    ) {
        return None;
    }

    let key_declaration = semantic.scoping().symbol_span(factory_key_symbol);
    if !(function.span.start <= key_declaration.start && key_declaration.end <= function.span.end)
        || !binding_stable_from_factory_entry(
            source,
            program,
            semantic,
            factory_call,
            factory_key_symbol,
        )
    {
        return None;
    }

    let selector_value = exact_selector_value(
        program,
        semantic.scoping(),
        selector_start,
        selector_end,
        selector_key_symbol,
        exact_key_value,
    )?;

    let mut resolvers = sequence.expressions.iter().filter_map(|expression| {
        let assignment = assignment_expression(expression)?;
        let Expression::FunctionExpression(resolver) = last_sequence_expression(&assignment.right)
        else {
            return None;
        };
        (resolver.span.start == shape.resolver_function_start
            && resolver.span.end == shape.resolver_function_end)
            .then_some(resolver)
    });
    let resolver = resolvers.next()?;
    if resolvers.next().is_some()
        || resolver.r#async
        || resolver.generator
        || function_subtree_has_dynamic_scope(resolver)
        || resolver
            .body
            .as_deref()
            .is_none_or(function_body_uses_arguments)
    {
        return None;
    }

    let mut bindings = exact_integer_scalar_bindings(&parameters, &factory_call.call);
    bindings.insert(
        shape.index_state_symbol,
        update_state.post_update_state_value,
    );
    bindings.insert(update_state.selector_capture_symbol, selector_value);
    bindings.insert(factory_key_symbol, exact_key_value);

    let (index_assignment_span, index) = resolver_index_value(
        resolver,
        semantic,
        handler_symbol,
        handler_array,
        shape.phase_local_symbol,
        phase_value,
        &bindings,
    )?;
    let handler_slot = i64::try_from(shape.handler_slot).ok()?;
    if index != handler_slot {
        return None;
    }

    Some(ProvenSlowLazyCellResolverIndex {
        update_state: update_state.clone(),
        exact_assignment: exact_assignment.clone(),
        selector_key_symbol,
        selector_start,
        selector_end,
        factory_key_symbol,
        exact_key_value,
        phase_value,
        handler_slot: shape.handler_slot,
        index_assignment_start: index_assignment_span.start,
        index_assignment_end: index_assignment_span.end,
    })
}

/// Prove that one slow-cell resolver's computed handler-array index collapses
/// to the factory's captured handler slot under independently supplied facts.
///
/// This theorem is intentionally conditional. The selector span identifies the
/// selector installed by a lazy accessor; `exact_assignment` proves the concrete
/// installer key survives unchanged to this nested factory assignment; and
/// `phase_value` is supplied by a separate phase proof. Selector and resolver
/// arithmetic are evaluated in JavaScript order and accepted only while every
/// ordinary arithmetic intermediate remains an exact safe integer. This function
/// does not claim that a particular accessor reaches this cell, that the update
/// occurs exactly once before the resolver, or that the resulting handler survives
/// in the registry; those remain separate provenance/temporal obligations.
#[must_use]
pub fn proven_slow_lazy_cell_resolver_index(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    update_state: &ProvenSlowLazyCellUpdateState,
    selector_start: u32,
    selector_end: u32,
    selector_key_symbol: SymbolId,
    exact_assignment: &ProvenSlowLazyCellExactRegistryAssignment,
    phase_value: i64,
) -> Option<ProvenSlowLazyCellResolverIndex> {
    struct Harness<'s, 'p, 'm, 'u> {
        source: &'s str,
        program: &'p Program<'p>,
        semantic: &'m Semantic<'m>,
        update_state: &'u ProvenSlowLazyCellUpdateState,
        selector_start: u32,
        selector_end: u32,
        selector_key_symbol: SymbolId,
        exact_assignment: &'u ProvenSlowLazyCellExactRegistryAssignment,
        phase_value: i64,
        result: Option<Option<ProvenSlowLazyCellResolverIndex>>,
    }
    impl<'a> Visit<'a> for Harness<'_, 'a, '_, '_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if self.result.is_some() {
                return;
            }
            let shape = &self.update_state.factory_call.shape;
            if function.span.start == shape.function_start
                && function.span.end == shape.function_end
            {
                self.result = Some(analyze_slow_lazy_cell_resolver_index(
                    self.source,
                    self.program,
                    self.semantic,
                    function,
                    self.update_state,
                    self.selector_start,
                    self.selector_end,
                    self.selector_key_symbol,
                    self.exact_assignment,
                    self.phase_value,
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
        update_state,
        selector_start,
        selector_end,
        selector_key_symbol,
        exact_assignment,
        phase_value,
        result: None,
    };
    harness.visit_program(program);
    harness.result.flatten()
}

/// Prove the two state-object facts consumed by slow-cell construction:
/// the exact prototype-carrier own field is unchanged at this factory call,
/// and the computed method-key field still has its exact inherited string value.
///
/// This theorem deliberately does not interpret the carrier object itself. A
/// separate object-model proof must establish what the exact carrier value does
/// when used as the prototype of the newly created cell.
#[must_use]
pub fn proven_slow_lazy_cell_state_fields(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    factory_call: &ProvenSlowLazyCellFactoryCall,
) -> Option<ProvenSlowLazyCellStateFields> {
    let call = &factory_call.call;
    let shape = &factory_call.shape;
    let allocation = Span::new(call.callee.allocation_start, call.callee.allocation_end);

    let string_at_allocation = proven_prototype_string_at_allocation(
        program,
        semantic,
        call.callee.constructor_start,
        call.callee.constructor_end,
        allocation,
        &shape.method_key_field,
    )?;
    let mut method_keys =
        proven_prototype_string_at_direct_calls(source, program, semantic, &string_at_allocation)
            .into_iter()
            .filter(|proof| proof.call == *call);
    let method_key = method_keys.next()?;
    if method_keys.next().is_some() {
        return None;
    }

    let mut prototype_fields = proven_exact_own_data_field_at_direct_call(
        source,
        program,
        semantic,
        &shape.prototype_field,
        call,
    )
    .into_iter()
    .filter(|proof| {
        proof.direct_call == *call
            && proof.initialization.allocation_start == call.callee.allocation_start
            && proof.initialization.allocation_end == call.callee.allocation_end
            && proof.initialization.constructor_start == call.callee.constructor_start
            && proof.initialization.constructor_end == call.callee.constructor_end
    });
    let prototype_field = prototype_fields.next()?;
    if prototype_fields.next().is_some() {
        return None;
    }

    Some(ProvenSlowLazyCellStateFields {
        factory_call: factory_call.clone(),
        prototype_field,
        method_key,
    })
}

/// Prove the same slow-cell state facts along one concrete exact-assignment
/// provenance chain instead of requiring a merged installer context to be
/// valid for every incoming edge.
///
/// The exact `ST` value and inherited method-key string are established at the
/// concrete root call, then every direct-call edge that carries the same exact
/// allocation is required to preserve both properties. This is intentionally a
/// path theorem: unrelated incoming edges to a shared installer do not weaken a
/// proof for this concrete constructor path.
#[must_use]
pub fn proven_slow_lazy_cell_state_fields_for_exact_assignment(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    exact_assignment: &ProvenSlowLazyCellExactRegistryAssignment,
) -> Option<ProvenSlowLazyCellExactStateFields> {
    let factory_call = &exact_assignment.assignment.factory_call;
    let shape = &factory_call.shape;
    let chain = &exact_assignment.provenance_calls;
    let root = chain.first()?;
    if chain.last()? != &exact_assignment.caller
        || exact_assignment.caller.callee != factory_call.call.caller
        || crate::registry_identity::ProvenRegistryObjectOrigin::from(&root.callee)
            != crate::registry_identity::ProvenRegistryObjectOrigin::from(&factory_call.call.callee)
    {
        return None;
    }

    let allocation = Span::new(root.callee.allocation_start, root.callee.allocation_end);
    let string_at_allocation = proven_prototype_string_at_allocation(
        program,
        semantic,
        root.callee.constructor_start,
        root.callee.constructor_end,
        allocation,
        &shape.method_key_field,
    )?;
    let mut method_keys =
        proven_prototype_string_at_direct_calls(source, program, semantic, &string_at_allocation)
            .into_iter()
            .filter(|proof| proof.call == *root);
    let method_key = method_keys.next()?;
    if method_keys.next().is_some() {
        return None;
    }

    let mut prototype_fields = proven_exact_own_data_field_at_direct_call(
        source,
        program,
        semantic,
        &shape.prototype_field,
        root,
    )
    .into_iter()
    .filter(|proof| {
        proof.direct_call == *root
            && proof.initialization.allocation_start == root.callee.allocation_start
            && proof.initialization.allocation_end == root.callee.allocation_end
            && proof.initialization.constructor_start == root.callee.constructor_start
            && proof.initialization.constructor_end == root.callee.constructor_end
    });
    let prototype_field = prototype_fields.next()?;
    if prototype_fields.next().is_some() {
        return None;
    }

    let preserves_until = |entry: &ProvenOriginDirectCall, before: &ProvenOriginDirectCall| {
        proven_origin_direct_call_prefix_preserves_exact_property_before_direct_call(
            source,
            program,
            semantic.scoping(),
            entry,
            before,
            &shape.prototype_field,
        ) && proven_origin_direct_call_prefix_preserves_exact_property_before_direct_call(
            source,
            program,
            semantic.scoping(),
            entry,
            before,
            &shape.method_key_field,
        )
    };
    for pair in chain.windows(2) {
        let [entry, before] = pair else {
            return None;
        };
        if !preserves_until(entry, before) {
            return None;
        }
    }
    if !preserves_until(chain.last()?, &factory_call.call) {
        return None;
    }

    Some(ProvenSlowLazyCellExactStateFields {
        exact_assignment: exact_assignment.clone(),
        fields: ProvenSlowLazyCellStateFields {
            factory_call: factory_call.clone(),
            prototype_field,
            method_key,
        },
    })
}
#[derive(Debug, Clone)]
struct CarrierInitializerShape {
    helper_symbol: SymbolId,
    helper_call: Span,
    exact_integer_arguments: BTreeMap<usize, i64>,
    method_key_argument_index: usize,
    getter_argument_index: usize,
    getter_function: Span,
}

#[derive(Debug, Clone)]
struct CarrierHelperShape {
    function: Span,
    create_assignment: Span,
    return_event: Span,
    create_state: u64,
    object_constructor_symbol: SymbolId,
    method_key_parameter_index: usize,
    descriptor_parameter_index: usize,
}

fn symbol_binding_has_no_writes(scoping: &Scoping, symbol: SymbolId) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| !scoping.get_reference(*reference_id).is_write())
}

fn expression_is_empty_ordinary_object(expression: &Expression<'_>) -> bool {
    matches!(last_sequence_expression(expression), Expression::ObjectExpression(object) if object.properties.is_empty())
}

fn variable_initializer_is_empty_ordinary_object(
    program: &Program<'_>,
    scoping: &Scoping,
    symbol: SymbolId,
) -> bool {
    if !symbol_binding_has_no_writes(scoping, symbol) {
        return false;
    }
    struct Probe {
        symbol: SymbolId,
        matches: usize,
        ordinary: bool,
    }
    impl<'a> Visit<'a> for Probe {
        fn visit_variable_declaration(
            &mut self,
            declaration: &oxc_ast::ast::VariableDeclaration<'a>,
        ) {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    continue;
                };
                if identifier.symbol_id.get() != Some(self.symbol) {
                    continue;
                }
                self.matches += 1;
                self.ordinary = declarator
                    .init
                    .as_ref()
                    .is_some_and(expression_is_empty_ordinary_object);
            }
            walk::walk_variable_declaration(self, declaration);
        }
    }
    let mut probe = Probe {
        symbol,
        matches: 0,
        ordinary: false,
    };
    probe.visit_program(program);
    probe.matches == 1 && probe.ordinary
}

fn symbol_is_ordinary_object_constructor_alias(
    program: &Program<'_>,
    scoping: &Scoping,
    symbol: SymbolId,
) -> bool {
    if !symbol_binding_has_no_writes(scoping, symbol) {
        return false;
    }
    struct Probe<'c> {
        scoping: &'c Scoping,
        symbol: SymbolId,
        matches: usize,
        object_symbol: Option<SymbolId>,
        direct_object: bool,
    }
    impl<'a> Visit<'a> for Probe<'_> {
        fn visit_variable_declaration(
            &mut self,
            declaration: &oxc_ast::ast::VariableDeclaration<'a>,
        ) {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    continue;
                };
                if identifier.symbol_id.get() != Some(self.symbol) {
                    continue;
                }
                self.matches += 1;
                let Some(Expression::StaticMemberExpression(member)) =
                    declarator.init.as_ref().map(last_sequence_expression)
                else {
                    continue;
                };
                if member.optional || member.property.name.as_str() != "constructor" {
                    continue;
                }
                let object = last_sequence_expression(&member.object);
                if expression_is_empty_ordinary_object(object) {
                    self.direct_object = true;
                } else {
                    self.object_symbol = reference_symbol(self.scoping, object);
                }
            }
            walk::walk_variable_declaration(self, declaration);
        }
    }
    let mut probe = Probe {
        scoping,
        symbol,
        matches: 0,
        object_symbol: None,
        direct_object: false,
    };
    probe.visit_program(program);
    probe.matches == 1
        && (probe.direct_object
            || probe.object_symbol.is_some_and(|object_symbol| {
                variable_initializer_is_empty_ordinary_object(program, scoping, object_symbol)
            }))
}

fn getter_descriptor_delegate(
    object: &oxc_ast::ast::ObjectExpression<'_>,
    resolver_property: &str,
) -> Option<Span> {
    let mut getter = None;
    for item in &object.properties {
        let ObjectPropertyKind::ObjectProperty(property) = item else {
            return None;
        };
        let name = property.key.static_name()?;
        if property.computed && property.key.static_name().is_none() {
            return None;
        }
        if name != "get" {
            continue;
        }
        if property.kind != PropertyKind::Init || property.method || property.shorthand {
            return None;
        }
        let Expression::FunctionExpression(function) = last_sequence_expression(&property.value)
        else {
            return None;
        };
        if function.r#async || function.generator || !function.params.items.is_empty() {
            return None;
        }
        let body = function.body.as_ref()?;
        let [Statement::ReturnStatement(ret)] = body.statements.as_slice() else {
            return None;
        };
        let Expression::CallExpression(call) =
            ret.argument.as_ref().map(last_sequence_expression)?
        else {
            return None;
        };
        if call.optional || !call.arguments.is_empty() {
            return None;
        }
        let Expression::StaticMemberExpression(member) = last_sequence_expression(&call.callee)
        else {
            return None;
        };
        if member.optional
            || member.property.name.as_str() != resolver_property
            || !matches!(
                last_sequence_expression(&member.object),
                Expression::ThisExpression(_)
            )
        {
            return None;
        }
        if getter.replace(function.span).is_some() {
            return None;
        }
    }
    getter
}

fn carrier_initializer_shape(
    program: &Program<'_>,
    scoping: &Scoping,
    initialization: &crate::receiver_identity::ProvenOwnDataFieldInitialization,
    method_key_field: &str,
    resolver_property: &str,
) -> Option<CarrierInitializerShape> {
    struct Probe<'c, 'o> {
        scoping: &'c Scoping,
        span: Span,
        property: &'o str,
        method_key_field: &'o str,
        resolver_property: &'o str,
        matches: Vec<CarrierInitializerShape>,
    }
    impl<'a> Visit<'a> for Probe<'_, '_> {
        fn visit_assignment_expression(
            &mut self,
            assignment: &oxc_ast::ast::AssignmentExpression<'a>,
        ) {
            if assignment.span != self.span || !assignment.operator.is_assign() {
                walk::walk_assignment_expression(self, assignment);
                return;
            }
            let AssignmentTarget::StaticMemberExpression(left) = &assignment.left else {
                return;
            };
            if left.optional || left.property.name.as_str() != self.property {
                return;
            }
            let receiver = &left.object;
            if !matches!(
                last_sequence_expression(receiver),
                Expression::Identifier(_) | Expression::ThisExpression(_)
            ) {
                return;
            }
            let Expression::CallExpression(call) = last_sequence_expression(&assignment.right)
            else {
                return;
            };
            if call.optional {
                return;
            }
            let Some(helper_symbol) = reference_symbol(self.scoping, &call.callee) else {
                return;
            };
            let mut exact_integer_arguments = BTreeMap::new();
            let mut method_keys = Vec::new();
            let mut getters = Vec::new();
            for (index, argument) in call.arguments.iter().enumerate() {
                let Some(expression) = argument.as_expression() else {
                    continue;
                };
                if let Some(value) = exact_static_safe_integer(last_sequence_expression(expression))
                {
                    exact_integer_arguments.insert(index, value);
                }
                if let Expression::StaticMemberExpression(member) =
                    last_sequence_expression(expression)
                {
                    if !member.optional
                        && member.property.name.as_str() == self.method_key_field
                        && same_direct_receiver(self.scoping, receiver, &member.object)
                    {
                        method_keys.push(index);
                    }
                }
                if let Expression::ObjectExpression(object) = last_sequence_expression(expression) {
                    if let Some(getter) = getter_descriptor_delegate(object, self.resolver_property)
                    {
                        getters.push((index, getter));
                    }
                }
            }
            let [method_key_argument_index] = method_keys.as_slice() else {
                return;
            };
            let [(getter_argument_index, getter_function)] = getters.as_slice() else {
                return;
            };
            self.matches.push(CarrierInitializerShape {
                helper_symbol,
                helper_call: call.span,
                exact_integer_arguments,
                method_key_argument_index: *method_key_argument_index,
                getter_argument_index: *getter_argument_index,
                getter_function: *getter_function,
            });
        }
    }
    let mut probe = Probe {
        scoping,
        span: Span::new(initialization.write_start, initialization.write_end),
        property: &initialization.property,
        method_key_field,
        resolver_property,
        matches: Vec::new(),
    };
    probe.visit_program(program);
    let [shape] = probe.matches.as_slice() else {
        return None;
    };
    Some(shape.clone())
}

fn descriptor_parameter_for_projection(
    object: &oxc_ast::ast::ObjectExpression<'_>,
    scoping: &Scoping,
    parameters: &[SymbolId],
    projection_property: &str,
) -> Option<usize> {
    let mut matched = None;
    for item in &object.properties {
        let ObjectPropertyKind::ObjectProperty(property) = item else {
            return None;
        };
        let Some(name) = property.key.static_name() else {
            return None;
        };
        if property.computed && property.key.static_name().is_none() {
            return None;
        }
        if name != projection_property {
            continue;
        }
        if property.kind != PropertyKind::Init || property.method || property.shorthand {
            return None;
        }
        let symbol = reference_symbol(scoping, &property.value)?;
        let index = parameters
            .iter()
            .position(|parameter| *parameter == symbol)?;
        if matched.replace(index).is_some() {
            return None;
        }
    }
    matched
}

fn helper_state_for_create_event(
    source: &str,
    function: &Function<'_>,
    create: Span,
    ret: Span,
) -> Option<u64> {
    fn equality_state(expression: &Expression<'_>, state_var: &str) -> Option<u64> {
        let Expression::BinaryExpression(binary) = strip_parentheses(expression) else {
            return None;
        };
        if !matches!(binary.operator.as_str(), "==" | "===") {
            return None;
        }
        let parse = |id: &Expression<'_>, value: &Expression<'_>| {
            let Expression::Identifier(identifier) = strip_parentheses(id) else {
                return None;
            };
            if identifier.name.as_str() != state_var {
                return None;
            }
            let Expression::NumericLiteral(number) = strip_parentheses(value) else {
                return None;
            };
            u64::try_from(exact_i64(number.value)?).ok()
        };
        parse(&binary.left, &binary.right).or_else(|| parse(&binary.right, &binary.left))
    }

    struct MachineProbe<'s> {
        source: &'s str,
        create: Span,
        ret: Span,
        states: Vec<u64>,
    }
    impl MachineProbe<'_> {
        fn inspect<'a>(&mut self, statements: &[Statement<'a>]) {
            for pair in statements.windows(2) {
                let [init, Statement::WhileStatement(while_statement)] = pair else {
                    continue;
                };
                let Some(machine) = crate::state_flatten::detect_while_state_machine(
                    self.source,
                    "lazy-cell-carrier",
                    init,
                    while_statement,
                ) else {
                    continue;
                };
                if !(machine.start <= self.create.start
                    && self.create.end <= machine.end
                    && machine.start <= self.ret.start
                    && self.ret.end <= machine.end)
                {
                    continue;
                }
                struct GuardProbe<'g> {
                    state_var: &'g str,
                    event: Span,
                    states: Vec<u64>,
                }
                impl<'a> Visit<'a> for GuardProbe<'_> {
                    fn visit_logical_expression(
                        &mut self,
                        expression: &oxc_ast::ast::LogicalExpression<'a>,
                    ) {
                        if expression.operator.as_str() == "&&"
                            && expression.right.span().start <= self.event.start
                            && self.event.end <= expression.right.span().end
                        {
                            if let Some(state) = equality_state(&expression.left, self.state_var) {
                                self.states.push(state);
                            }
                        }
                        walk::walk_logical_expression(self, expression);
                    }
                    fn visit_if_statement(&mut self, statement: &oxc_ast::ast::IfStatement<'a>) {
                        if statement.consequent.span().start <= self.event.start
                            && self.event.end <= statement.consequent.span().end
                        {
                            if let Some(state) = equality_state(&statement.test, self.state_var) {
                                self.states.push(state);
                            }
                        }
                        walk::walk_if_statement(self, statement);
                    }
                    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
                    fn visit_arrow_function_expression(
                        &mut self,
                        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                    ) {
                    }
                }
                let mut guard = GuardProbe {
                    state_var: &machine.state_var,
                    event: self.create,
                    states: Vec::new(),
                };
                guard.visit_statement(&while_statement.body);
                if let [state] = guard.states.as_slice() {
                    self.states.push(*state);
                }
            }
        }
    }
    impl<'a> Visit<'a> for MachineProbe<'_> {
        fn visit_function_body(&mut self, body: &oxc_ast::ast::FunctionBody<'a>) {
            self.inspect(&body.statements);
            walk::walk_function_body(self, body);
        }
        fn visit_block_statement(&mut self, block: &oxc_ast::ast::BlockStatement<'a>) {
            self.inspect(&block.body);
            walk::walk_block_statement(self, block);
        }
        fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
        fn visit_arrow_function_expression(
            &mut self,
            _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
        ) {
        }
    }
    let mut probe = MachineProbe {
        source,
        create,
        ret,
        states: Vec::new(),
    };
    if let Some(body) = function.body.as_ref() {
        probe.visit_function_body(body);
    }
    let [state] = probe.states.as_slice() else {
        return None;
    };
    Some(*state)
}

fn carrier_helper_shape(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    helper_symbol: SymbolId,
    projection_property: &str,
) -> Option<CarrierHelperShape> {
    if !symbol_binding_has_no_writes(scoping, helper_symbol) {
        return None;
    }
    struct Probe<'s, 'c, 'o> {
        source: &'s str,
        scoping: &'c Scoping,
        helper_symbol: SymbolId,
        projection_property: &'o str,
        shapes: Vec<CarrierHelperShape>,
    }
    impl Probe<'_, '_, '_> {
        fn analyze(&mut self, function: &Function<'_>) {
            if function.r#async || function.generator {
                return;
            }
            let Some(parameters) = parameter_symbols(function) else {
                return;
            };
            let Some(body) = function.body.as_ref() else {
                return;
            };
            let mut creates = Vec::new();
            let mut returns = Vec::new();
            struct BodyProbe<'c, 'p, 'o> {
                scoping: &'c Scoping,
                parameters: &'p [SymbolId],
                projection_property: &'o str,
                creates: Vec<(Span, SymbolId, SymbolId, usize, usize)>,
                returns: Vec<(Span, SymbolId)>,
            }
            impl<'a> Visit<'a> for BodyProbe<'_, '_, '_> {
                fn visit_assignment_expression(
                    &mut self,
                    assignment: &oxc_ast::ast::AssignmentExpression<'a>,
                ) {
                    if assignment.operator.is_assign() {
                        if let Some(target) = assignment_symbol(self.scoping, &assignment.left) {
                            if let Expression::CallExpression(call) =
                                last_sequence_expression(&assignment.right)
                            {
                                if !call.optional && call.arguments.len() == 2 {
                                    if let Expression::ComputedMemberExpression(callee) =
                                        last_sequence_expression(&call.callee)
                                    {
                                        if !callee.optional {
                                            if let (Some(constructor), Some(key_symbol)) = (
                                                reference_symbol(self.scoping, &callee.object),
                                                reference_symbol(self.scoping, &callee.expression),
                                            ) {
                                                if let Some(key_index) = self
                                                    .parameters
                                                    .iter()
                                                    .position(|symbol| *symbol == key_symbol)
                                                {
                                                    let base_ok = call
                                                        .arguments
                                                        .first()
                                                        .and_then(|argument| argument.as_expression())
                                                        .is_some_and(|argument| {
                                                            matches!(
                                                                last_sequence_expression(argument),
                                                                Expression::StaticMemberExpression(member)
                                                                    if !member.optional
                                                                        && member.property.name.as_str() == "prototype"
                                                                        && reference_symbol(self.scoping, &member.object) == Some(constructor)
                                                            )
                                                        });
                                                    let descriptor_index = call
                                                        .arguments
                                                        .get(1)
                                                        .and_then(|argument| argument.as_expression())
                                                        .and_then(|argument| match last_sequence_expression(argument) {
                                                            Expression::ObjectExpression(object) => descriptor_parameter_for_projection(
                                                                object,
                                                                self.scoping,
                                                                self.parameters,
                                                                self.projection_property,
                                                            ),
                                                            _ => None,
                                                        });
                                                    if base_ok {
                                                        if let Some(descriptor_index) =
                                                            descriptor_index
                                                        {
                                                            self.creates.push((
                                                                assignment.span,
                                                                target,
                                                                constructor,
                                                                key_index,
                                                                descriptor_index,
                                                            ));
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    walk::walk_assignment_expression(self, assignment);
                }
                fn visit_return_statement(&mut self, ret: &oxc_ast::ast::ReturnStatement<'a>) {
                    if let Some(symbol) = ret
                        .argument
                        .as_ref()
                        .and_then(|argument| reference_symbol(self.scoping, argument))
                    {
                        self.returns.push((ret.span, symbol));
                    }
                    walk::walk_return_statement(self, ret);
                }
                fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
                fn visit_arrow_function_expression(
                    &mut self,
                    _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                ) {
                }
            }
            let mut probe = BodyProbe {
                scoping: self.scoping,
                parameters: &parameters,
                projection_property: self.projection_property,
                creates: Vec::new(),
                returns: Vec::new(),
            };
            probe.visit_function_body(body);
            creates.append(&mut probe.creates);
            returns.append(&mut probe.returns);
            let [(create, result_symbol, constructor, key_index, descriptor_index)] =
                creates.as_slice()
            else {
                return;
            };
            let return_events = returns
                .iter()
                .filter_map(|(span, symbol)| (*symbol == *result_symbol).then_some(*span))
                .collect::<Vec<_>>();
            let [return_event] = return_events.as_slice() else {
                return;
            };
            let Some(create_state) =
                helper_state_for_create_event(self.source, function, *create, *return_event)
            else {
                return;
            };
            self.shapes.push(CarrierHelperShape {
                function: function.span,
                create_assignment: *create,
                return_event: *return_event,
                create_state,
                object_constructor_symbol: *constructor,
                method_key_parameter_index: *key_index,
                descriptor_parameter_index: *descriptor_index,
            });
        }
    }
    impl<'a> Visit<'a> for Probe<'_, '_, '_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if function
                .id
                .as_ref()
                .and_then(|identifier| identifier.symbol_id.get())
                == Some(self.helper_symbol)
            {
                self.analyze(function);
            }
            walk::walk_function(self, function, flags);
        }
        fn visit_variable_declaration(
            &mut self,
            declaration: &oxc_ast::ast::VariableDeclaration<'a>,
        ) {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    continue;
                };
                if identifier.symbol_id.get() != Some(self.helper_symbol) {
                    continue;
                }
                if let Some(Expression::FunctionExpression(function)) = &declarator.init {
                    self.analyze(function);
                }
            }
            walk::walk_variable_declaration(self, declaration);
        }
    }
    let mut probe = Probe {
        source,
        scoping,
        helper_symbol,
        projection_property,
        shapes: Vec::new(),
    };
    probe.visit_program(program);
    let [shape] = probe.shapes.as_slice() else {
        return None;
    };
    Some(shape.clone())
}

fn slow_cell_object_constructor_symbol(
    program: &Program<'_>,
    scoping: &Scoping,
    factory_call: &ProvenSlowLazyCellFactoryCall,
) -> Option<SymbolId> {
    let span = Span::new(
        factory_call.shape.cell_construction_start,
        factory_call.shape.cell_construction_end,
    );
    let mut matches = Vec::new();
    struct Probe<'c, 'o> {
        scoping: &'c Scoping,
        span: Span,
        matches: &'o mut Vec<SymbolId>,
    }
    impl<'a> Visit<'a> for Probe<'_, '_> {
        fn visit_assignment_expression(
            &mut self,
            assignment: &oxc_ast::ast::AssignmentExpression<'a>,
        ) {
            if assignment.span == self.span && assignment.operator.is_assign() {
                if let Expression::CallExpression(call) =
                    last_sequence_expression(&assignment.right)
                {
                    if let Expression::ComputedMemberExpression(callee) =
                        last_sequence_expression(&call.callee)
                    {
                        if let Some(symbol) = reference_symbol(self.scoping, &callee.object) {
                            self.matches.push(symbol);
                        }
                    }
                }
            }
            walk::walk_assignment_expression(self, assignment);
        }
    }
    Probe {
        scoping,
        span,
        matches: &mut matches,
    }
    .visit_program(program);
    let [symbol] = matches.as_slice() else {
        return None;
    };
    Some(*symbol)
}

/// Prove that the exact slow-cell prototype carrier routes the lazy accessor's
/// projected property through an inherited getter to the cell's resolver.
///
/// The theorem joins the constructor-time exact `ST` value and method-key
/// string to the helper that creates `ST`, specializes that helper's flattened
/// control flow with the exact integer arguments from the initializer, and
/// requires the M-style factory to use the same Object-constructor alias when it
/// creates the cell from `ST`. It deliberately records, rather than hides, the
/// ordinary/untampered built-in Object + prototype + accessor semantics premise.
#[must_use]
pub fn proven_slow_lazy_cell_prototype_carrier(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    state_fields: &ProvenSlowLazyCellExactStateFields,
    accessor: &ProvenLazyRegistryReadCall,
) -> Option<ProvenSlowLazyCellPrototypeCarrier> {
    let scoping = semantic.scoping();
    let fields = &state_fields.fields;
    let factory_call = &fields.factory_call;
    if state_fields.exact_assignment.assignment.factory_call != *factory_call {
        return None;
    }
    let shape = &factory_call.shape;
    let method_name = fields.method_key.string.assignment.value.clone();
    if method_name != accessor.update_property
        || fields.prototype_field.initialization.property != shape.prototype_field
        || fields.method_key.string.assignment.property != shape.method_key_field
    {
        return None;
    }
    if !proven_origin_direct_call_preserves_exact_property(
        source,
        program,
        scoping,
        &factory_call.call,
        &shape.prototype_field,
    ) || !proven_origin_direct_call_preserves_exact_property(
        source,
        program,
        scoping,
        &factory_call.call,
        &shape.method_key_field,
    ) {
        return None;
    }

    let initializer = carrier_initializer_shape(
        program,
        scoping,
        &fields.prototype_field.initialization,
        &shape.method_key_field,
        &shape.resolver_property,
    )?;
    let helper = carrier_helper_shape(
        source,
        program,
        scoping,
        initializer.helper_symbol,
        &accessor.projection_property,
    )?;
    if initializer.method_key_argument_index != helper.method_key_parameter_index
        || initializer.getter_argument_index != helper.descriptor_parameter_index
        || !symbol_binding_has_no_writes(
            scoping,
            parameter_symbols_for_span(program, helper.function)?
                .get(helper.method_key_parameter_index)
                .copied()?,
        )
        || !symbol_binding_has_no_writes(
            scoping,
            parameter_symbols_for_span(program, helper.function)?
                .get(helper.descriptor_parameter_index)
                .copied()?,
        )
        || !prove_function_if_ladder_states_before_event_with_integer_parameters(
            source,
            program,
            scoping,
            helper.function.start,
            helper.function.end,
            &[helper.create_state],
            helper.return_event,
            &initializer.exact_integer_arguments,
        )
    {
        return None;
    }

    let cell_constructor = slow_cell_object_constructor_symbol(program, scoping, factory_call)?;
    if cell_constructor != helper.object_constructor_symbol
        || !symbol_is_ordinary_object_constructor_alias(program, scoping, cell_constructor)
    {
        return None;
    }

    Some(ProvenSlowLazyCellPrototypeCarrier {
        state_fields: state_fields.clone(),
        accessor: accessor.clone(),
        helper_function_start: helper.function.start,
        helper_function_end: helper.function.end,
        helper_call_start: initializer.helper_call.start,
        helper_call_end: initializer.helper_call.end,
        helper_create_start: helper.create_assignment.start,
        helper_create_end: helper.create_assignment.end,
        getter_function_start: initializer.getter_function.start,
        getter_function_end: initializer.getter_function.end,
        object_constructor_symbol: cell_constructor,
        method_name,
        projection_property: accessor.projection_property.clone(),
        resolver_property: shape.resolver_property.clone(),
        standard_object_prototype_semantics_required: true,
    })
}

fn parameter_symbols_for_span(program: &Program<'_>, span: Span) -> Option<Vec<SymbolId>> {
    let mut output = None;
    struct Probe<'o> {
        span: Span,
        output: &'o mut Option<Vec<SymbolId>>,
    }
    impl<'a> Visit<'a> for Probe<'_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if function.span == self.span {
                *self.output = parameter_symbols(function);
                return;
            }
            walk::walk_function(self, function, flags);
        }
    }
    Probe {
        span,
        output: &mut output,
    }
    .visit_program(program);
    output
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
        proven_slow_lazy_cell_captured_handler_from_value,
        proven_slow_lazy_cell_captured_handler_install,
        proven_slow_lazy_cell_captured_value_install,
        proven_slow_lazy_cell_exact_registry_assignments, proven_slow_lazy_cell_factory_call,
        proven_slow_lazy_cell_prototype_carrier, proven_slow_lazy_cell_read_result,
        proven_slow_lazy_cell_registry_assignment, proven_slow_lazy_cell_resolved_handler,
        proven_slow_lazy_cell_resolver_index, proven_slow_lazy_cell_state_fields,
        proven_slow_lazy_cell_state_fields_for_exact_assignment,
        proven_slow_lazy_cell_update_state, structurally_proven_slow_lazy_cell_factory_shapes,
    };
    use crate::{
        forwarding_semantics::structurally_proven_lazy_registry_read_calls,
        receiver_identity::structurally_proven_origin_flow,
        registry_identity::{
            proven_origin_registry_handler_installs, proven_origin_registry_value_installs,
        },
    };
    use oxc_allocator::Allocator;
    use oxc_ast::ast::{BindingPattern, Statement};
    use oxc_semantic::SemanticBuilder;
    use oxc_span::{GetSpan, SourceType};
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
    fn proves_exact_state_fields_at_slow_cell_factory_call() {
        let source = r#"
            let outer_phase;
            const C = function() {
                this.base = {};
                enter(this);
            };
            C.prototype.method = "create";
            function enter(state) {
                return make(48, 19, 49, state, 7, function handler() {}, 0, 0, 0, 0, 0);
            }
            function make(mode, q, y, state, key, handler, capture, s, phase, cell, out) {
                return (mode | 48) == mode && (
                    handler = [11, -39, 3, 4, 5, 6, handler, 87],
                    s = 1,
                    phase = outer_phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) { s = value; },
                    cell.resolve = function() { return handler[s]; },
                    out = cell
                ), out;
            }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let start = source.find("make(48").expect("factory call") as u32;
        let call = flow
            .direct_calls
            .iter()
            .find(|call| call.call_start == start)
            .expect("origin factory call");
        let factory =
            proven_slow_lazy_cell_factory_call(source, &parsed.program, &semantic.semantic, call)
                .expect("slow-cell factory");
        let fields = proven_slow_lazy_cell_state_fields(
            source,
            &parsed.program,
            &semantic.semantic,
            &factory,
        )
        .expect("state fields");
        assert_eq!(fields.method_key.string.assignment.value, "create");
        assert_eq!(fields.prototype_field.initialization.property, "base");
    }

    #[test]
    fn proves_state_fields_along_concrete_forwarding_chain() {
        let source = r#"
            let outer_phase;
            const C = function() {
                this.base = {};
                install(this, 7, "payload");
            };
            C.prototype.method = "create";
            function install(state, key, handler) {
                return write(state, key, handler);
            }
            function write(state, key, handler) {
                return state.T[key] = make(
                    48, 19, 49, state, key, handler, 0, 0, 0, 0, 0
                );
            }
            function make(mode, q, y, state, key, handler, capture, s, phase, cell, out) {
                return (mode | 48) == mode && (
                    handler = [11, -39, 3, 4, 5, 6, handler, 87],
                    s = 1,
                    phase = outer_phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) { s = value; },
                    cell.resolve = function() { return handler[s]; },
                    out = cell
                ), out;
            }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let start = source
            .find("make(\n                    48")
            .expect("factory call") as u32;
        let call = flow
            .direct_calls
            .iter()
            .find(|call| call.call_start == start)
            .expect("origin factory call");
        let factory =
            proven_slow_lazy_cell_factory_call(source, &parsed.program, &semantic.semantic, call)
                .expect("slow-cell factory");
        let registry = proven_slow_lazy_cell_registry_assignment(
            &parsed.program,
            &semantic.semantic,
            &factory,
        )
        .expect("registry assignment");
        let exact = proven_slow_lazy_cell_exact_registry_assignments(
            source,
            &parsed.program,
            &semantic.semantic,
            &flow,
            &registry,
        )
        .into_iter()
        .find(|proof| proof.exact_key_value == 7)
        .expect("exact assignment");
        assert_eq!(exact.provenance_calls.len(), 2);
        let fields = proven_slow_lazy_cell_state_fields_for_exact_assignment(
            source,
            &parsed.program,
            &semantic.semantic,
            &exact,
        )
        .expect("path state fields");
        assert_eq!(fields.fields.method_key.string.assignment.value, "create");
        assert_eq!(
            fields.fields.prototype_field.initialization.property,
            "base"
        );
        let values = proven_origin_registry_value_installs(
            &parsed.program,
            semantic.semantic.scoping(),
            &flow,
        );
        let value = values
            .iter()
            .find(|proof| {
                proof.exact_key == 7
                    && &source[proof.install.value_start as usize..proof.install.value_end as usize]
                        == "\"payload\""
            })
            .expect("logical value install");
        let captured = proven_slow_lazy_cell_captured_value_install(
            source,
            &parsed.program,
            &semantic.semantic,
            &exact,
            value,
        )
        .expect("captured non-function value");
        assert_eq!(captured.exact_assignment.exact_key_value, 7);
    }

    #[test]
    fn proves_object_create_carrier_getter_delegation() {
        let source = r#"
            let outer_phase;
            const Seed = {};
            const Maker = Seed.constructor;
            const C = function() {
                this.T = [];
                this.base = carrier(0, 17, this.method, {
                    get: function() { return this.resolve(); }
                });
                install(this, 7, function handler() {});
                run(this);
            };
            C.prototype.method = "create";
            function carrier(j, q, key, descriptor, out, state) {
                state = 88;
                while (state != 78) {
                    if (state == 63) return out;
                    else if (state == 88) state = j;
                    else if (state == 0) state = q << 2 & 6 ? 80 : 59;
                    else if (state == 59) state = 80;
                    else if (state == 80) state = (q | 3) >> 3 >= 2 && (q | 2) >> 5 < 5 ? 48 : 63;
                    else if (state == 48) {
                        out = Maker[key](Maker.prototype, {
                            stack: descriptor,
                            prototype: descriptor
                        });
                        state = 63;
                    }
                }
            }
            function install(state, key, handler) {
                return write(state, key, handler);
            }
            function write(state, key, handler) {
                return state.T[key] = make(
                    48, 19, 49, state, key, handler, 0, 0, 0, 0, 0
                );
            }
            function make(mode, q, y, state, key, handler, capture, s, phase, cell, out) {
                return (mode | 48) == mode && (
                    handler = [51, -39, -92, 71, -35, 4, handler, 87, -37, -29],
                    s = -2 * ~(y & 7) + -8 + (y ^ 7) + (~y | 7),
                    phase = outer_phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) {
                        s += 6 + 7 * (capture = value, y), s &= 7;
                    },
                    cell.resolve = function(r, n, m, d, T, B) {
                        capture = (n = (B = (
                            T = key % 16 + 1,
                            +s + (phase() | 0) * T - T * capture
                                + 61 * capture * capture
                                - 305 * key * key * capture
                                + handler[
                                    r = s + q,
                                    -~(r & 7) + (r ^ 7) + (~r ^ 7)
                                ] * key * T
                                + 5 * key * key * T
                                + 2379 * key * capture
                                - 1403 * capture
                        ), handler)[B], void 0);
                        return n;
                    },
                    out = cell
                ), out;
            }
            function access(state, key) {
                let cell;
                cell = state.T[key];
                if (cell.value) return cell.create();
                return (cell.create(key * 5 * key + -39 * key + 23), cell).prototype;
            }
            function run(state) { return access(state, 7); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let flow = structurally_proven_origin_flow(&parsed.program, scoping);
        let start = source
            .find("make(\n                    48")
            .expect("factory call") as u32;
        let call = flow
            .direct_calls
            .iter()
            .find(|call| call.call_start == start)
            .expect("origin factory call");
        let factory =
            proven_slow_lazy_cell_factory_call(source, &parsed.program, &semantic.semantic, call)
                .expect("slow-cell factory");
        let registry = proven_slow_lazy_cell_registry_assignment(
            &parsed.program,
            &semantic.semantic,
            &factory,
        )
        .expect("registry assignment");
        let exact = proven_slow_lazy_cell_exact_registry_assignments(
            source,
            &parsed.program,
            &semantic.semantic,
            &flow,
            &registry,
        )
        .into_iter()
        .find(|proof| proof.exact_key_value == 7)
        .expect("exact assignment");
        let fields = proven_slow_lazy_cell_state_fields_for_exact_assignment(
            source,
            &parsed.program,
            &semantic.semantic,
            &exact,
        )
        .expect("path state fields");
        let reads = structurally_proven_lazy_registry_read_calls(&parsed.program, scoping);
        let accessor = reads.first().expect("lazy accessor");
        let carrier = proven_slow_lazy_cell_prototype_carrier(
            source,
            &parsed.program,
            &semantic.semantic,
            &fields,
            accessor,
        )
        .expect("prototype carrier");
        assert_eq!(carrier.method_name, "create");
        assert_eq!(carrier.projection_property, "prototype");
        assert_eq!(carrier.resolver_property, "resolve");
        assert!(carrier.standard_object_prototype_semantics_required);

        let update =
            proven_slow_lazy_cell_update_state(&parsed.program, &semantic.semantic, &factory)
                .expect("update state");
        let installs = proven_origin_registry_handler_installs(&parsed.program, scoping, &flow);
        let install = installs
            .iter()
            .find(|install| install.exact_key == 7)
            .expect("logical handler install");
        let captured = proven_slow_lazy_cell_captured_handler_install(
            source,
            &parsed.program,
            &semantic.semantic,
            &exact,
            install,
        )
        .expect("captured handler");
        let values = proven_origin_registry_value_installs(&parsed.program, scoping, &flow);
        let value = values
            .iter()
            .find(|value| {
                value.exact_key == install.exact_key
                    && value.install.call_start == install.install.call_start
                    && value.install.call_end == install.install.call_end
                    && value.install.value_start == install.install.handler_start
                    && value.install.value_end == install.install.handler_end
            })
            .expect("same generic value install");
        let captured_value = proven_slow_lazy_cell_captured_value_install(
            source,
            &parsed.program,
            &semantic.semantic,
            &exact,
            value,
        )
        .expect("captured generic handler value");
        let specialized =
            proven_slow_lazy_cell_captured_handler_from_value(&captured_value, install)
                .expect("handler specialization");
        assert_eq!(specialized, captured);
        let resolver = proven_slow_lazy_cell_resolver_index(
            source,
            &parsed.program,
            &semantic.semantic,
            &update,
            accessor.selector_start,
            accessor.selector_end,
            accessor.selector_key_symbol,
            &exact,
            23,
        )
        .expect("resolver slot");
        let resolved =
            proven_slow_lazy_cell_resolved_handler(&resolver, &captured).expect("resolved handler");
        let read =
            proven_slow_lazy_cell_read_result(&resolved, &carrier).expect("end-to-end lazy read");
        assert_eq!(read.resolved_handler.resolver.exact_key_value, 7);
        assert_eq!(read.resolved_handler.resolver.handler_slot, 6);
    }

    #[test]
    fn proves_exact_slow_cell_update_state_and_selector_capture() {
        let source = r#"
            let outer_phase;
            const C = function() { enter(this); };
            function enter(state) {
                return make(48, 19, 49, state, 7, function handler() {}, 0, 0, 0, 0, 0);
            }
            function make(mode, q, y, state, key, handler, capture, s, phase, cell, out) {
                return (mode | 48) == mode && (
                    handler = [11, -39, 3, 4, 5, 6, handler, 87],
                    s = -2 * ~(y & 7) + -8 + (y ^ 7) + (~y | 7),
                    phase = outer_phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) {
                        s += 6 + 7 * (capture = value, y), s &= 7;
                    },
                    cell.resolve = function() { return handler[0]; },
                    out = cell
                ), out;
            }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let start = source.find("make(48").expect("call") as u32;
        let call = flow
            .direct_calls
            .iter()
            .find(|call| call.call_start == start)
            .expect("origin call");
        let factory =
            proven_slow_lazy_cell_factory_call(source, &parsed.program, &semantic.semantic, call)
                .expect("factory proof");
        let update =
            proven_slow_lazy_cell_update_state(&parsed.program, &semantic.semantic, &factory)
                .expect("update proof");
        assert_eq!(update.initial_state_value, 1);
        assert_eq!(update.post_update_state_value, 6);
        assert_eq!(
            semantic
                .semantic
                .scoping()
                .symbol_name(update.selector_capture_symbol),
            "capture"
        );
        assert_eq!(
            semantic
                .semantic
                .scoping()
                .symbol_name(update.update_parameter_symbol),
            "value"
        );
    }

    #[test]
    fn proves_real_style_resolver_index_cancellation() {
        let source = r#"
            let outer_phase;
            const C = function() { enter(this); };
            function enter(state) {
                install(state, 7, function handler() {});
                return install(state, 1000000, function largeHandler() {});
            }
            function install(state, incoming_key, incoming_handler) {
                return write(state, incoming_key, incoming_handler);
            }
            function write(state, incoming_key, incoming_handler) {
                return state.T[incoming_key] = make(
                    48, 19, 49, state, incoming_key,
                    incoming_handler, 0, 0, 0, 0, 0, 0
                );
            }
            function make(mode, q, y, state, key, handler, capture, s, phase, cell, out, tmp) {
                return (mode | 48) == mode && (
                    handler = [51, -39, -92, 71, -35, 4, handler, 87, -37, -29],
                    s = -2 * ~(y & 7) + -8 + (y ^ 7) + (~y | 7),
                    phase = outer_phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) {
                        s += 6 + 7 * (capture = value, y), s &= 7;
                    },
                    cell.resolve = function(r, n, m, d, T, B) {
                        capture = (n = (B = (
                            T = key % 16 + 1,
                            +s + (phase() | 0) * T - T * capture
                                + 61 * capture * capture
                                - 305 * key * key * capture
                                + handler[
                                    r = s + q,
                                    -~(r & 7) + (r ^ 7) + (~r ^ 7)
                                ] * key * T
                                + 5 * key * key * T
                                + 2379 * key * capture
                                - 1403 * capture
                        ), handler)[B], void 0);
                        return n;
                    },
                    out = cell
                ), out;
            }
            function selector(key) {
                return key * 5 * key + -39 * key + 23;
            }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let flow = structurally_proven_origin_flow(&parsed.program, scoping);
        let start = source.find("make(\n                    48").expect("call") as u32;
        let call = flow
            .direct_calls
            .iter()
            .find(|call| call.call_start == start)
            .expect("origin call");
        let factory =
            proven_slow_lazy_cell_factory_call(source, &parsed.program, &semantic.semantic, call)
                .expect("factory proof");
        let update =
            proven_slow_lazy_cell_update_state(&parsed.program, &semantic.semantic, &factory)
                .expect("update proof");

        let registry = proven_slow_lazy_cell_registry_assignment(
            &parsed.program,
            &semantic.semantic,
            &factory,
        )
        .expect("registry assignment");
        assert_eq!(registry.registry_path, vec!["T"]);
        assert_eq!(registry.factory_key_parameter_index, 4);
        let exact_assignments = proven_slow_lazy_cell_exact_registry_assignments(
            source,
            &parsed.program,
            &semantic.semantic,
            &flow,
            &registry,
        );
        assert_eq!(
            exact_assignments
                .iter()
                .map(|proof| proof.exact_key_value)
                .collect::<Vec<_>>(),
            vec![7, 1_000_000]
        );
        let exact_seven = exact_assignments
            .iter()
            .find(|proof| proof.exact_key_value == 7)
            .expect("small exact key");
        let exact_large = exact_assignments
            .iter()
            .find(|proof| proof.exact_key_value == 1_000_000)
            .expect("large exact key");
        let origin_installs =
            proven_origin_registry_handler_installs(&parsed.program, scoping, &flow);
        let install_seven = origin_installs
            .iter()
            .find(|install| install.exact_key == 7)
            .expect("logical install");
        let captured_handler = proven_slow_lazy_cell_captured_handler_install(
            source,
            &parsed.program,
            &semantic.semantic,
            exact_seven,
            install_seven,
        )
        .expect("captured logical handler");

        let selector = parsed
            .program
            .body
            .iter()
            .find_map(|statement| match statement {
                Statement::FunctionDeclaration(function)
                    if function
                        .id
                        .as_ref()
                        .is_some_and(|id| id.name.as_str() == "selector") =>
                {
                    Some(function)
                }
                _ => None,
            })
            .expect("selector function");
        let BindingPattern::BindingIdentifier(selector_key) = &selector.params.items[0].pattern
        else {
            panic!("selector key binding");
        };
        let selector_key_symbol = selector_key.symbol_id.get().expect("selector key symbol");
        let body = selector.body.as_ref().expect("selector body");
        let [Statement::ReturnStatement(ret)] = body.statements.as_slice() else {
            panic!("selector return");
        };
        let selector_expression = ret.argument.as_ref().expect("selector expression");
        let selector_span = selector_expression.span();

        let proof = proven_slow_lazy_cell_resolver_index(
            source,
            &parsed.program,
            &semantic.semantic,
            &update,
            selector_span.start,
            selector_span.end,
            selector_key_symbol,
            exact_seven,
            23,
        )
        .expect("resolver cancellation");
        assert_eq!(proof.handler_slot, 6);
        let resolved = proven_slow_lazy_cell_resolved_handler(&proof, &captured_handler)
            .expect("resolved original handler");
        assert_eq!(resolved.captured_handler.install.exact_key, 7);
        assert!(proven_slow_lazy_cell_resolver_index(
            source,
            &parsed.program,
            &semantic.semantic,
            &update,
            selector_span.start,
            selector_span.end,
            selector_key_symbol,
            exact_seven,
            50,
        )
        .is_none());
        assert!(proven_slow_lazy_cell_resolver_index(
            source,
            &parsed.program,
            &semantic.semantic,
            &update,
            selector_span.start,
            selector_span.end,
            selector_key_symbol,
            exact_large,
            23,
        )
        .is_none());
    }

    #[test]
    fn forwarding_order_allows_flattened_use_after_forward() {
        let source = r#"
            const C = function() { install(this, 7, function handler() {}); };
            function install(state, key, handler, pc) {
                pc = 0;
                while (pc != 99) {
                    if (pc == 0) pc = 1;
                    else if (pc == 1) { write(state, key, handler); pc = 2; }
                    else if (pc == 2) { handler.tag = 1; pc = 99; }
                    else if (pc == 3) { pc = 99; }
                }
            }
            function write(state, key, handler) { state.T[key] = handler; }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let call_start = source
            .find("write(state, key, handler)")
            .expect("write call") as u32;
        let call = flow
            .direct_calls
            .iter()
            .find(|call| call.call_start == call_start)
            .expect("exact forwarding call");
        let parameters = super::function_parameter_symbols_at(
            &parsed.program,
            call.caller.function_start,
            call.caller.function_end,
        )
        .expect("installer parameters");
        let handler = parameters[2];
        let incoming = flow
            .direct_calls
            .iter()
            .find(|edge| edge.callee == call.caller)
            .expect("exact installer entry");
        assert!(super::symbol_only_forwarded_at_direct_call(
            source,
            &parsed.program,
            &semantic.semantic,
            handler,
            oxc_span::Span::new(call.caller.function_start, call.caller.function_end),
            incoming,
            (1, 7),
            call,
            2,
        ));
    }

    #[test]
    fn forwarding_order_uses_recovered_key_across_delegate_edge() {
        let source = r#"
            const C = function() { install(this, 7, function handler() {}); };
            function install(state, key, handler) {
                return write(state, key, handler);
            }
            function write(state, key, handler) {
                if (key === 7) {
                    return sink(state, key, handler);
                } else {
                    handler();
                }
            }
            function sink(state, key, handler) { state.T[key] = handler; }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let call_start = source.find("sink(state, key, handler)").expect("sink call") as u32;
        let call = flow
            .direct_calls
            .iter()
            .find(|call| call.call_start == call_start)
            .expect("inner forwarding call");
        let incoming = flow
            .direct_calls
            .iter()
            .find(|edge| edge.callee == call.caller)
            .expect("delegate entry");
        assert_eq!(incoming.exact_integer_arguments, vec![None, None, None]);
        let parameters = super::function_parameter_symbols_at(
            &parsed.program,
            call.caller.function_start,
            call.caller.function_end,
        )
        .expect("write parameters");
        assert!(super::symbol_only_forwarded_at_direct_call(
            source,
            &parsed.program,
            &semantic.semantic,
            parameters[2],
            oxc_span::Span::new(call.caller.function_start, call.caller.function_end),
            incoming,
            (1, 7),
            call,
            2,
        ));
    }

    #[test]
    fn forwarding_order_rejects_handler_invocation_before_forward() {
        let source = r#"
            const C = function() { install(this, 7, function handler() {}); };
            function install(state, key, handler) {
                handler();
                return write(state, key, handler);
            }
            function write(state, key, handler) { state.T[key] = handler; }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let call_start = source
            .find("write(state, key, handler)")
            .expect("write call") as u32;
        let call = flow
            .direct_calls
            .iter()
            .find(|call| call.call_start == call_start)
            .expect("exact forwarding call");
        let parameters = super::function_parameter_symbols_at(
            &parsed.program,
            call.caller.function_start,
            call.caller.function_end,
        )
        .expect("installer parameters");
        let handler = parameters[2];
        let incoming = flow
            .direct_calls
            .iter()
            .find(|edge| edge.callee == call.caller)
            .expect("exact installer entry");
        assert!(!super::symbol_only_forwarded_at_direct_call(
            source,
            &parsed.program,
            &semantic.semantic,
            handler,
            oxc_span::Span::new(call.caller.function_start, call.caller.function_end),
            incoming,
            (1, 7),
            call,
            2,
        ));
    }

    #[test]
    fn exact_registry_assignment_rejects_call_specialized_unreachable_branch() {
        let source = r#"
            let phase;
            const C = function() { enter(this); };
            function enter(state) {
                install(state, 7, function seven() {});
                return install(state, 8, function eight() {});
            }
            function install(state, key, handler) {
                return key == 7
                    ? state.T[key] = make(48, 19, 49, state, key, handler, 0, 0, 0, 0, 0)
                    : state.T[key] = make(48, 19, 49, state, key, handler, 0, 0, 0, 0, 0);
            }
            function make(mode, q, y, state, key, handler, capture, s, phase_local, cell, out) {
                return (mode | 48) == mode && (
                    handler = [51, -39, -92, 71, -35, 4, handler, 87],
                    s = -2 * ~(y & 7) + -8 + (y ^ 7) + (~y | 7),
                    phase_local = phase,
                    cell = Maker[state.method](state.base),
                    cell[state.method] = function(value) {
                        s += 6 + 7 * (capture = value, y), s &= 7;
                    },
                    cell.resolve = function() { return handler[s]; },
                    out = cell
                ), out;
            }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let flow = structurally_proven_origin_flow(&parsed.program, scoping);
        let starts = [
            source.find("make(48, 19, 49").expect("first make") as u32,
            source.rfind("make(48, 19, 49").expect("second make") as u32,
        ];
        let mut keys_by_site = Vec::new();
        for start in starts {
            let call = flow
                .direct_calls
                .iter()
                .find(|call| call.call_start == start)
                .expect("origin call");
            let factory = proven_slow_lazy_cell_factory_call(
                source,
                &parsed.program,
                &semantic.semantic,
                call,
            )
            .expect("factory proof");
            let registry = proven_slow_lazy_cell_registry_assignment(
                &parsed.program,
                &semantic.semantic,
                &factory,
            )
            .expect("registry assignment");
            keys_by_site.push(
                proven_slow_lazy_cell_exact_registry_assignments(
                    source,
                    &parsed.program,
                    &semantic.semantic,
                    &flow,
                    &registry,
                )
                .into_iter()
                .map(|proof| proof.exact_key_value)
                .collect::<Vec<_>>(),
            );
        }
        assert_eq!(keys_by_site, vec![vec![7], vec![8]]);
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
