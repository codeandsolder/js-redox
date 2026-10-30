use crate::{
    numeric::eval_js_bitwise_i64,
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
    pub factory_key_parameter_index: usize,
    pub factory_key_symbol: SymbolId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenSlowLazyCellResolverIndex {
    pub update_state: ProvenSlowLazyCellUpdateState,
    pub selector_key_symbol: SymbolId,
    pub factory_key_symbol: SymbolId,
    pub phase_value: i64,
    pub handler_slot: usize,
    pub index_assignment_start: u32,
    pub index_assignment_end: u32,
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

fn handler_array_constant_at(
    array: &oxc_ast::ast::ArrayExpression<'_>,
    index: i64,
    scoping: &Scoping,
) -> Option<i128> {
    let index = usize::try_from(index).ok()?;
    let element = array.elements.get(index)?;
    let expression = match element {
        ArrayExpressionElement::SpreadElement(_) | ArrayExpressionElement::Elision(_) => {
            return None;
        }
        element => element.as_expression()?,
    };
    normalize_integer_polynomial(
        expression,
        scoping,
        &HashMap::new(),
        &HashMap::new(),
        &HashSet::new(),
    )?
    .constant_value()
}

fn normalize_resolver_index_rhs(
    rhs: &Expression<'_>,
    resolver: &Function<'_>,
    semantic: &Semantic<'_>,
    handler_symbol: SymbolId,
    handler_array: &oxc_ast::ast::ArrayExpression<'_>,
    phase_symbol: SymbolId,
    phase_value: i64,
    bindings: &HashMap<SymbolId, IntegerPolynomial>,
) -> Option<IntegerPolynomial> {
    struct Facts<'s, 'h, 'b> {
        scoping: &'s Scoping,
        handler_symbol: SymbolId,
        handler_array: &'h oxc_ast::ast::ArrayExpression<'h>,
        phase_symbol: SymbolId,
        bindings: &'b HashMap<SymbolId, IntegerPolynomial>,
        resolver_span: Span,
        phase_calls: Vec<(u32, u32)>,
        opaque_constants: HashMap<(u32, u32), i128>,
        write_counts: HashMap<SymbolId, usize>,
        arbitrary_assignments: HashSet<SymbolId>,
        failed: bool,
    }
    impl<'a> Visit<'a> for Facts<'_, 'a, '_> {
        fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
            if !call.optional
                && call.arguments.is_empty()
                && reference_symbol(self.scoping, &call.callee) == Some(self.phase_symbol)
            {
                self.phase_calls.push((call.span.start, call.span.end));
            }
            walk::walk_call_expression(self, call);
        }

        fn visit_computed_member_expression(
            &mut self,
            member: &oxc_ast::ast::ComputedMemberExpression<'a>,
        ) {
            if reference_symbol(self.scoping, &member.object) == Some(self.handler_symbol) {
                let value = normalize_integer_polynomial(
                    &member.expression,
                    self.scoping,
                    self.bindings,
                    &HashMap::new(),
                    &HashSet::new(),
                )
                .and_then(|index| index.constant_value())
                .and_then(|index| i64::try_from(index).ok())
                .and_then(|index| {
                    handler_array_constant_at(self.handler_array, index, self.scoping)
                });
                let Some(value) = value else {
                    self.failed = true;
                    return;
                };
                self.opaque_constants
                    .insert((member.span.start, member.span.end), value);
            }
            walk::walk_computed_member_expression(self, member);
        }

        fn visit_assignment_expression(
            &mut self,
            assignment: &oxc_ast::ast::AssignmentExpression<'a>,
        ) {
            if assignment.operator.is_assign() && pure_integer_expression(&assignment.right) {
                if let Some(symbol) = assignment_symbol(self.scoping, &assignment.left) {
                    let declaration = self.scoping.symbol_span(symbol);
                    if self.resolver_span.start <= declaration.start
                        && declaration.end <= self.resolver_span.end
                    {
                        *self.write_counts.entry(symbol).or_default() += 1;
                        self.arbitrary_assignments.insert(symbol);
                    }
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

    let mut facts = Facts {
        scoping: semantic.scoping(),
        handler_symbol,
        handler_array,
        phase_symbol,
        bindings,
        resolver_span: resolver.span,
        phase_calls: Vec::new(),
        opaque_constants: HashMap::new(),
        write_counts: HashMap::new(),
        arbitrary_assignments: HashSet::new(),
        failed: false,
    };
    facts.visit_expression(rhs);
    if facts.failed || facts.write_counts.values().any(|count| *count != 1) {
        return None;
    }
    let [phase_call] = facts.phase_calls.as_slice() else {
        return None;
    };
    facts
        .opaque_constants
        .insert(*phase_call, i128::from(phase_value));

    normalize_integer_polynomial(
        rhs,
        semantic.scoping(),
        bindings,
        &facts.opaque_constants,
        &facts.arbitrary_assignments,
    )
}

fn resolver_index_polynomial(
    resolver: &Function<'_>,
    semantic: &Semantic<'_>,
    handler_symbol: SymbolId,
    handler_array: &oxc_ast::ast::ArrayExpression<'_>,
    phase_symbol: SymbolId,
    phase_value: i64,
    bindings: &HashMap<SymbolId, IntegerPolynomial>,
) -> Option<(Span, IntegerPolynomial)> {
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
        bindings: &'b HashMap<SymbolId, IntegerPolynomial>,
        matches: Vec<(Span, IntegerPolynomial)>,
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
                            if let Some(polynomial) = normalize_resolver_index_rhs(
                                &assignment.right,
                                self.resolver,
                                self.semantic,
                                self.handler_symbol,
                                self.handler_array,
                                self.phase_symbol,
                                self.phase_value,
                                self.bindings,
                            ) {
                                self.matches.push((assignment.span, polynomial));
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
    let [(span, polynomial)] = probe.matches.as_slice() else {
        return None;
    };
    Some((*span, polynomial.clone()))
}

fn analyze_slow_lazy_cell_resolver_index(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    function: &Function<'_>,
    update_state: &ProvenSlowLazyCellUpdateState,
    selector_key_symbol: SymbolId,
    selector_polynomial: &IntegerPolynomial,
    factory_key_symbol: SymbolId,
    phase_value: i64,
) -> Option<ProvenSlowLazyCellResolverIndex> {
    let factory_call = &update_state.factory_call;
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

    let selector_variables = selector_polynomial.variables();
    if selector_variables.as_slice() != [selector_key_symbol] {
        return None;
    }
    let selector = selector_polynomial.substitute_variable(
        selector_key_symbol,
        &IntegerPolynomial::variable(factory_key_symbol),
    )?;
    if selector.variables().as_slice() != [factory_key_symbol] {
        return None;
    }

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

    let mut bindings = exact_integer_bindings(&parameters, &factory_call.call);
    bindings.insert(
        shape.index_state_symbol,
        IntegerPolynomial::constant(i128::from(update_state.post_update_state_value)),
    );
    bindings.insert(update_state.selector_capture_symbol, selector);

    let (index_assignment_span, polynomial) = resolver_index_polynomial(
        resolver,
        semantic,
        handler_symbol,
        handler_array,
        shape.phase_local_symbol,
        phase_value,
        &bindings,
    )?;
    let index = polynomial.constant_value()?;
    let handler_slot = i128::try_from(shape.handler_slot).ok()?;
    if index != handler_slot {
        return None;
    }

    Some(ProvenSlowLazyCellResolverIndex {
        update_state: update_state.clone(),
        selector_key_symbol,
        factory_key_symbol,
        phase_value,
        handler_slot: shape.handler_slot,
        index_assignment_start: index_assignment_span.start,
        index_assignment_end: index_assignment_span.end,
    })
}

/// Prove that one slow-cell resolver's computed handler-array index collapses
/// to the factory's captured handler slot under independently supplied facts.
///
/// This theorem is intentionally conditional. `selector_polynomial` describes
/// the selector installed by a lazy accessor; `factory_key_symbol` is the
/// caller-proven factory binding denoting that same registry key; and
/// `phase_value` is supplied by a separate phase proof. This function proves
/// only the resolver algebra and structural capture stability. It does not
/// claim that a particular accessor reaches this cell, that the update occurs
/// exactly once before the resolver, or that the resulting handler survives in
/// the registry; those remain separate provenance/temporal obligations.
#[must_use]
pub fn proven_slow_lazy_cell_resolver_index(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    update_state: &ProvenSlowLazyCellUpdateState,
    selector_key_symbol: SymbolId,
    selector_polynomial: &IntegerPolynomial,
    factory_key_symbol: SymbolId,
    phase_value: i64,
) -> Option<ProvenSlowLazyCellResolverIndex> {
    struct Harness<'s, 'p, 'm, 'u, 'q> {
        source: &'s str,
        program: &'p Program<'p>,
        semantic: &'m Semantic<'m>,
        update_state: &'u ProvenSlowLazyCellUpdateState,
        selector_key_symbol: SymbolId,
        selector_polynomial: &'q IntegerPolynomial,
        factory_key_symbol: SymbolId,
        phase_value: i64,
        result: Option<Option<ProvenSlowLazyCellResolverIndex>>,
    }
    impl<'a> Visit<'a> for Harness<'_, 'a, '_, '_, '_> {
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
                    self.selector_key_symbol,
                    self.selector_polynomial,
                    self.factory_key_symbol,
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
        selector_key_symbol,
        selector_polynomial,
        factory_key_symbol,
        phase_value,
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
        proven_slow_lazy_cell_factory_call, proven_slow_lazy_cell_registry_assignment,
        proven_slow_lazy_cell_resolver_index, proven_slow_lazy_cell_update_state,
        structurally_proven_slow_lazy_cell_factory_shapes,
    };
    use crate::{
        receiver_identity::structurally_proven_origin_flow,
        symbolic_integer::normalize_integer_polynomial,
    };
    use oxc_allocator::Allocator;
    use oxc_ast::ast::{BindingPattern, Statement};
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;
    use std::collections::{HashMap, HashSet};

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
            let incoming_key;
            const C = function() { enter(this); };
            function enter(state) {
                return state.T[incoming_key] = make(
                    48, 19, 49, state, incoming_key,
                    function handler() {}, 0, 0, 0, 0, 0, 0
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
        let factory_key_symbol = registry.factory_key_symbol;

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
        let selector_polynomial = normalize_integer_polynomial(
            ret.argument.as_ref().expect("selector expression"),
            scoping,
            &HashMap::new(),
            &HashMap::new(),
            &HashSet::new(),
        )
        .expect("selector polynomial");

        let proof = proven_slow_lazy_cell_resolver_index(
            source,
            &parsed.program,
            &semantic.semantic,
            &update,
            selector_key_symbol,
            &selector_polynomial,
            factory_key_symbol,
            23,
        )
        .expect("resolver cancellation");
        assert_eq!(proof.handler_slot, 6);
        assert!(proven_slow_lazy_cell_resolver_index(
            source,
            &parsed.program,
            &semantic.semantic,
            &update,
            selector_key_symbol,
            &selector_polynomial,
            factory_key_symbol,
            50,
        )
        .is_none());
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
