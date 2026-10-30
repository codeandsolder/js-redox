use crate::symbolic_integer::{normalize_integer_polynomial, IntegerPolynomial};
use jsvm_safe_core::{exact_u32, string_literal_value};
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, AssignmentTarget, BindingPattern, CallExpression, Expression,
    Function, FunctionBody, IfStatement, Program, Statement, VariableDeclaration,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::GetSpan;
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ExprKey {
    Symbol(SymbolId),
    Index(Box<ExprKey>, u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenRegistryForwardingCall {
    pub call_start: u32,
    pub call_end: u32,
    pub receiver_start: u32,
    pub receiver_end: u32,
    pub key_start: u32,
    pub key_end: u32,
    pub registry_path: Vec<String>,
    pub handler_start: u32,
    pub handler_end: u32,
    pub handler_params: usize,
    pub handler_async: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenRegistryReadCall {
    pub call_start: u32,
    pub call_end: u32,
    pub receiver_start: u32,
    pub receiver_end: u32,
    pub key_start: u32,
    pub key_end: u32,
    pub registry_path: Vec<String>,
}

/// Structural proof that a registry accessor routes the loaded cell through a
/// truthiness probe, an update method, and a projected property on the same
/// symbol. This intentionally does not assign semantics to those properties; a
/// lazy-cell theorem must separately prove what the cell object does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenLazyRegistryReadCall {
    pub read: ProvenRegistryReadCall,
    pub accessor_function_start: u32,
    pub accessor_function_end: u32,
    pub cell_assignment_start: u32,
    pub cell_assignment_end: u32,
    pub probe_property: String,
    pub update_property: String,
    pub projection_property: String,
    pub selector_start: u32,
    pub selector_end: u32,
    /// Key-parameter symbol in the accessor function's semantic scope.
    pub selector_key_symbol: SymbolId,
    /// Canonical selector polynomial. It is guaranteed to reference no symbol
    /// other than `selector_key_symbol` (or none for a constant selector).
    pub selector_polynomial: IntegerPolynomial,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RegistryForwarderProof {
    receiver_argument: u32,
    key_argument: u32,
    value_argument: u32,
    registry_path: Vec<String>,
}

fn reference_symbol(scoping: &Scoping, expression: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = expression else {
        return None;
    };
    scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()
}

fn symbol_binding_is_stable(scoping: &Scoping, symbol: SymbolId) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| !scoping.get_reference(*reference_id).is_write())
}

fn expr_key(scoping: &Scoping, expression: &Expression<'_>) -> Option<ExprKey> {
    match expression {
        Expression::Identifier(identifier) => scoping
            .get_reference(identifier.reference_id.get()?)
            .symbol_id()
            .map(ExprKey::Symbol),
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::NumericLiteral(index) = &member.expression else {
                return None;
            };
            Some(ExprKey::Index(
                Box::new(expr_key(scoping, &member.object)?),
                exact_u32(index.value)?,
            ))
        }
        _ => None,
    }
}

fn argument_key(scoping: &Scoping, argument: &Argument<'_>) -> Option<ExprKey> {
    match argument {
        Argument::Identifier(identifier) => scoping
            .get_reference(identifier.reference_id.get()?)
            .symbol_id()
            .map(ExprKey::Symbol),
        Argument::ComputedMemberExpression(member) if !member.optional => {
            let Expression::NumericLiteral(index) = &member.expression else {
                return None;
            };
            Some(ExprKey::Index(
                Box::new(expr_key(scoping, &member.object)?),
                exact_u32(index.value)?,
            ))
        }
        _ => None,
    }
}

fn assignment_target_key(scoping: &Scoping, target: &AssignmentTarget<'_>) -> Option<ExprKey> {
    match target {
        AssignmentTarget::AssignmentTargetIdentifier(identifier) => scoping
            .get_reference(identifier.reference_id.get()?)
            .symbol_id()
            .map(ExprKey::Symbol),
        AssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
            let Expression::NumericLiteral(index) = &member.expression else {
                return None;
            };
            Some(ExprKey::Index(
                Box::new(expr_key(scoping, &member.object)?),
                exact_u32(index.value)?,
            ))
        }
        _ => None,
    }
}

fn parameter_symbols(function: &Function<'_>) -> Option<Vec<SymbolId>> {
    if function.params.rest.is_some() {
        return None;
    }
    function
        .params
        .items
        .iter()
        .map(|parameter| match &parameter.pattern {
            BindingPattern::BindingIdentifier(identifier) => identifier.symbol_id.get(),
            _ => None,
        })
        .collect()
}

#[derive(Default)]
struct ArgumentsBoxCollector {
    boxes: HashMap<SymbolId, u32>,
}

impl<'a> Visit<'a> for ArgumentsBoxCollector {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(Expression::ArrayExpression(array)) = &declarator.init else {
                continue;
            };
            if array.elements.len() != 1 {
                continue;
            }
            let ArrayExpressionElement::Identifier(value) = &array.elements[0] else {
                continue;
            };
            if value.name.as_str() == "arguments" {
                if let Some(symbol) = identifier.symbol_id.get() {
                    self.boxes.insert(symbol, declarator.span.start);
                }
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }
}

fn argument_box_declarations(body: &FunctionBody<'_>) -> HashMap<SymbolId, u32> {
    let mut collector = ArgumentsBoxCollector::default();
    collector.visit_function_body(body);
    collector.boxes
}

fn argument_boxes(body: &FunctionBody<'_>) -> HashSet<SymbolId> {
    argument_box_declarations(body).into_keys().collect()
}

fn expression_access_path(
    scoping: &Scoping,
    expression: &Expression<'_>,
) -> Option<(SymbolId, Vec<Option<u32>>)> {
    match expression {
        Expression::Identifier(identifier) => Some((
            scoping
                .get_reference(identifier.reference_id.get()?)
                .symbol_id()?,
            Vec::new(),
        )),
        Expression::ParenthesizedExpression(parenthesized) => {
            expression_access_path(scoping, &parenthesized.expression)
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let (root, mut path) = expression_access_path(scoping, &member.object)?;
            let index = match &member.expression {
                Expression::NumericLiteral(value) => exact_u32(value.value),
                _ => None,
            };
            path.push(index);
            Some((root, path))
        }
        Expression::StaticMemberExpression(member) if !member.optional => {
            let (root, mut path) = expression_access_path(scoping, &member.object)?;
            path.push(None);
            Some((root, path))
        }
        _ => None,
    }
}

fn assignment_access_path(
    scoping: &Scoping,
    target: &AssignmentTarget<'_>,
) -> Option<(SymbolId, Vec<Option<u32>>)> {
    match target {
        AssignmentTarget::AssignmentTargetIdentifier(identifier) => Some((
            scoping
                .get_reference(identifier.reference_id.get()?)
                .symbol_id()?,
            Vec::new(),
        )),
        AssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
            let (root, mut path) = expression_access_path(scoping, &member.object)?;
            let index = match &member.expression {
                Expression::NumericLiteral(value) => exact_u32(value.value),
                _ => None,
            };
            path.push(index);
            Some((root, path))
        }
        AssignmentTarget::StaticMemberExpression(member) if !member.optional => {
            let (root, mut path) = expression_access_path(scoping, &member.object)?;
            path.push(None);
            Some((root, path))
        }
        _ => None,
    }
}

fn simple_assignment_access_path(
    scoping: &Scoping,
    target: &oxc_ast::ast::SimpleAssignmentTarget<'_>,
) -> Option<(SymbolId, Vec<Option<u32>>)> {
    match target {
        oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) => Some((
            scoping
                .get_reference(identifier.reference_id.get()?)
                .symbol_id()?,
            Vec::new(),
        )),
        oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member)
            if !member.optional =>
        {
            let (root, mut path) = expression_access_path(scoping, &member.object)?;
            let index = match &member.expression {
                Expression::NumericLiteral(value) => exact_u32(value.value),
                _ => None,
            };
            path.push(index);
            Some((root, path))
        }
        oxc_ast::ast::SimpleAssignmentTarget::StaticMemberExpression(member)
            if !member.optional =>
        {
            let (root, mut path) = expression_access_path(scoping, &member.object)?;
            path.push(None);
            Some((root, path))
        }
        _ => None,
    }
}

fn mutates_argument_role(
    root: SymbolId,
    path: &[Option<u32>],
    parameters: &HashSet<SymbolId>,
    boxes: &HashSet<SymbolId>,
) -> bool {
    if parameters.contains(&root) && path.is_empty() {
        return true;
    }
    boxes.contains(&root)
        && (path.is_empty() || !matches!(path.first(), Some(Some(index)) if *index > 0))
}

struct ArgumentRoleSafety<'c, 'r> {
    scoping: &'c Scoping,
    parameters: HashSet<SymbolId>,
    boxes: &'r HashSet<SymbolId>,
    declarations: HashMap<SymbolId, u32>,
    valid: bool,
}

impl<'a> Visit<'a> for ArgumentRoleSafety<'_, '_> {
    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        let Some(symbol) = identifier
            .reference_id
            .get()
            .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
        else {
            return;
        };
        if let Some(declaration_start) = self.declarations.get(&symbol) {
            if identifier.span.start < *declaration_start {
                self.valid = false;
            }
        }
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment_access_path(self.scoping, &assignment.left).is_some_and(|(root, path)| {
            mutates_argument_role(root, &path, &self.parameters, self.boxes)
        }) {
            self.valid = false;
        }
        if let Some((root, path)) = expression_access_path(self.scoping, &assignment.right) {
            if self.boxes.contains(&root) && path.is_empty() {
                self.valid = false;
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_update_expression(&mut self, update: &oxc_ast::ast::UpdateExpression<'a>) {
        if simple_assignment_access_path(self.scoping, &update.argument).is_some_and(
            |(root, path)| mutates_argument_role(root, &path, &self.parameters, self.boxes),
        ) {
            self.valid = false;
        }
        walk::walk_update_expression(self, update);
    }

    fn visit_unary_expression(&mut self, unary: &oxc_ast::ast::UnaryExpression<'a>) {
        if unary.operator.as_str() == "delete"
            && expression_access_path(self.scoping, &unary.argument).is_some_and(|(root, path)| {
                mutates_argument_role(root, &path, &self.parameters, self.boxes)
            })
        {
            self.valid = false;
        }
        walk::walk_unary_expression(self, unary);
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        for argument in &call.arguments {
            if let Argument::Identifier(identifier) = argument {
                let Some(symbol) = identifier
                    .reference_id
                    .get()
                    .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
                else {
                    continue;
                };
                if self.boxes.contains(&symbol) {
                    self.valid = false;
                }
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_return_statement(&mut self, statement: &oxc_ast::ast::ReturnStatement<'a>) {
        if let Some(expression) = &statement.argument {
            if expression_access_path(self.scoping, expression)
                .is_some_and(|(root, path)| self.boxes.contains(&root) && path.is_empty())
            {
                self.valid = false;
            }
        }
        walk::walk_return_statement(self, statement);
    }
}

fn argument_roles_are_stable(
    scoping: &Scoping,
    body: &FunctionBody<'_>,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
) -> bool {
    let declarations = argument_box_declarations(body);
    let mut safety = ArgumentRoleSafety {
        scoping,
        parameters: parameters.iter().copied().collect(),
        boxes,
        declarations,
        valid: true,
    };
    safety.visit_function_body(body);
    safety.valid
}

fn selected_argument_roles_are_stable(
    scoping: &Scoping,
    body: &FunctionBody<'_>,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
    indices: &[u32],
) -> bool {
    let selected = indices
        .iter()
        .filter_map(|index| usize::try_from(*index).ok())
        .filter_map(|index| parameters.get(index).copied())
        .collect::<HashSet<_>>();
    if selected.len() != indices.len() {
        return false;
    }
    let declarations = argument_box_declarations(body);
    let mut safety = ArgumentRoleSafety {
        scoping,
        parameters: selected,
        boxes,
        declarations,
        valid: true,
    };
    safety.visit_function_body(body);
    safety.valid
}

fn argument_index_expr(
    scoping: &Scoping,
    expression: &Expression<'_>,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
) -> Option<u32> {
    if let Some(symbol) = reference_symbol(scoping, expression) {
        return parameters
            .iter()
            .position(|parameter| *parameter == symbol)
            .and_then(|index| u32::try_from(index).ok());
    }

    let Expression::ComputedMemberExpression(outer) = expression else {
        return None;
    };
    if outer.optional {
        return None;
    }
    let Expression::NumericLiteral(outer_index) = &outer.expression else {
        return None;
    };
    let outer_index = exact_u32(outer_index.value)?;
    let Expression::ComputedMemberExpression(inner) = &outer.object else {
        return None;
    };
    if inner.optional {
        return None;
    }
    let Expression::NumericLiteral(inner_index) = &inner.expression else {
        return None;
    };
    if exact_u32(inner_index.value)? != 0 {
        return None;
    }
    let box_symbol = reference_symbol(scoping, &inner.object)?;
    boxes.contains(&box_symbol).then_some(outer_index)
}

fn argument_index_arg(
    scoping: &Scoping,
    argument: &Argument<'_>,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
) -> Option<u32> {
    match argument {
        Argument::Identifier(identifier) => {
            let symbol = scoping
                .get_reference(identifier.reference_id.get()?)
                .symbol_id()?;
            parameters
                .iter()
                .position(|parameter| *parameter == symbol)
                .and_then(|index| u32::try_from(index).ok())
        }
        Argument::ComputedMemberExpression(member) if !member.optional => {
            let Expression::NumericLiteral(outer_index) = &member.expression else {
                return None;
            };
            let outer_index = exact_u32(outer_index.value)?;
            let Expression::ComputedMemberExpression(inner) = &member.object else {
                return None;
            };
            if inner.optional {
                return None;
            }
            let Expression::NumericLiteral(inner_index) = &inner.expression else {
                return None;
            };
            if exact_u32(inner_index.value)? != 0 {
                return None;
            }
            let box_symbol = reference_symbol(scoping, &inner.object)?;
            boxes.contains(&box_symbol).then_some(outer_index)
        }
        _ => None,
    }
}

fn last_sequence_expression<'a>(expression: &'a Expression<'a>) -> &'a Expression<'a> {
    if let Expression::ParenthesizedExpression(parenthesized) = expression {
        return last_sequence_expression(&parenthesized.expression);
    }
    if let Expression::SequenceExpression(sequence) = expression {
        sequence
            .expressions
            .last()
            .map_or(expression, last_sequence_expression)
    } else {
        expression
    }
}

fn stable_receiver_expression<'a>(
    scoping: &Scoping,
    expression: &'a Expression<'a>,
) -> Option<&'a Expression<'a>> {
    match expression {
        Expression::ParenthesizedExpression(parenthesized) => {
            stable_receiver_expression(scoping, &parenthesized.expression)
        }
        Expression::SequenceExpression(sequence) => {
            let receiver = stable_receiver_expression(scoping, sequence.expressions.last()?)?;
            match receiver {
                Expression::Identifier(_) => reference_symbol(scoping, receiver)
                    .filter(|symbol| symbol_binding_is_stable(scoping, *symbol))
                    .map(|_| receiver),
                Expression::ThisExpression(_) => Some(receiver),
                _ => None,
            }
        }
        _ => Some(expression),
    }
}

fn array_element_key(scoping: &Scoping, element: &ArrayExpressionElement<'_>) -> Option<ExprKey> {
    match element {
        ArrayExpressionElement::Identifier(identifier) => scoping
            .get_reference(identifier.reference_id.get()?)
            .symbol_id()
            .map(ExprKey::Symbol),
        ArrayExpressionElement::ComputedMemberExpression(member) if !member.optional => {
            let Expression::NumericLiteral(index) = &member.expression else {
                return None;
            };
            Some(ExprKey::Index(
                Box::new(expr_key(scoping, &member.object)?),
                exact_u32(index.value)?,
            ))
        }
        _ => None,
    }
}

fn is_resolver_call(
    scoping: &Scoping,
    call: &CallExpression<'_>,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
) -> bool {
    if call.optional || call.arguments.len() != 1 {
        return false;
    }
    argument_index_expr(
        scoping,
        last_sequence_expression(&call.callee),
        parameters,
        boxes,
    ) == Some(1)
        && argument_index_arg(scoping, &call.arguments[0], parameters, boxes) == Some(0)
}

fn selected_target_rhs(
    scoping: &Scoping,
    expression: &Expression<'_>,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
    owner_keys: &HashSet<ExprKey>,
) -> bool {
    let Expression::ComputedMemberExpression(selection) = expression else {
        return false;
    };
    if selection.optional
        || argument_index_expr(scoping, &selection.expression, parameters, boxes) != Some(3)
    {
        return false;
    }
    let Expression::ArrayExpression(array) = &selection.object else {
        return false;
    };
    if array.elements.len() != 2 {
        return false;
    }
    let Some(owner) = array_element_key(scoping, &array.elements[0]) else {
        return false;
    };
    if !owner_keys.contains(&owner) {
        return false;
    }
    let ArrayExpressionElement::StaticMemberExpression(prototype) = &array.elements[1] else {
        return false;
    };
    !prototype.optional
        && prototype.property.name.as_str() == "prototype"
        && expr_key(scoping, &prototype.object).as_ref() == Some(&owner)
}

fn forwarded_member(
    scoping: &Scoping,
    expression: &Expression<'_>,
    target: &ExprKey,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
    property_argument: u32,
) -> bool {
    let Expression::ComputedMemberExpression(member) = expression else {
        return false;
    };
    !member.optional
        && expr_key(scoping, &member.object).as_ref() == Some(target)
        && argument_index_expr(scoping, &member.expression, parameters, boxes)
            == Some(property_argument)
}

fn assignment_member_parts<'a>(
    target: &'a AssignmentTarget<'a>,
) -> Option<(&'a Expression<'a>, &'a Expression<'a>)> {
    let AssignmentTarget::ComputedMemberExpression(member) = target else {
        return None;
    };
    (!member.optional).then_some((&member.object, &member.expression))
}

fn assignment_is_forwarded_member(
    scoping: &Scoping,
    target: &AssignmentTarget<'_>,
    object: &ExprKey,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
    property_argument: u32,
) -> bool {
    let Some((member_object, member_property)) = assignment_member_parts(target) else {
        return false;
    };
    expr_key(scoping, member_object).as_ref() == Some(object)
        && argument_index_expr(scoping, member_property, parameters, boxes)
            == Some(property_argument)
}

fn undefined_identifier(expression: &Expression<'_>) -> bool {
    matches!(expression, Expression::Identifier(identifier) if identifier.name.as_str() == "undefined")
}

fn getter_return_forwards(
    scoping: &Scoping,
    expression: &Expression<'_>,
    target: &ExprKey,
    outer_parameters: &[SymbolId],
    outer_boxes: &HashSet<SymbolId>,
) -> bool {
    if forwarded_member(
        scoping,
        expression,
        target,
        outer_parameters,
        outer_boxes,
        2,
    ) {
        return true;
    }

    let Expression::ConditionalExpression(conditional) = expression else {
        return false;
    };
    if !undefined_identifier(&conditional.consequent)
        || !forwarded_member(
            scoping,
            &conditional.alternate,
            target,
            outer_parameters,
            outer_boxes,
            2,
        )
    {
        return false;
    }
    let Expression::BinaryExpression(test) = &conditional.test else {
        return false;
    };
    if !matches!(test.operator.as_str(), "==" | "===") {
        return false;
    }
    let Expression::UnaryExpression(unary) = &test.left else {
        return false;
    };
    if unary.operator.as_str() != "typeof"
        || !forwarded_member(
            scoping,
            &unary.argument,
            target,
            outer_parameters,
            outer_boxes,
            2,
        )
    {
        return false;
    }
    matches!(&test.right, Expression::StringLiteral(value) if value.value.as_str() == Some("undefined"))
}

struct SetterProbe<'c, 'o, 'b> {
    scoping: &'c Scoping,
    target: &'o ExprKey,
    outer_parameters: &'o [SymbolId],
    outer_boxes: &'b HashSet<SymbolId>,
    inner_parameters: Vec<SymbolId>,
    inner_boxes: HashSet<SymbolId>,
    good_writes: usize,
    bad_writes: usize,
}

impl<'a> Visit<'a> for SetterProbe<'_, '_, '_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment_is_forwarded_member(
            self.scoping,
            &assignment.left,
            self.target,
            self.outer_parameters,
            self.outer_boxes,
            2,
        ) {
            if assignment.operator.as_str() == "="
                && argument_index_expr(
                    self.scoping,
                    &assignment.right,
                    &self.inner_parameters,
                    &self.inner_boxes,
                ) == Some(0)
            {
                self.good_writes += 1;
            } else {
                self.bad_writes += 1;
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

fn setter_forwards(
    scoping: &Scoping,
    function: &Function<'_>,
    target: &ExprKey,
    outer_parameters: &[SymbolId],
    outer_boxes: &HashSet<SymbolId>,
) -> bool {
    if function.r#async || function.generator {
        return false;
    }
    let Some(parameters) = parameter_symbols(function) else {
        return false;
    };
    if parameters.len() != 1 {
        return false;
    }
    let Some(body) = &function.body else {
        return false;
    };
    let boxes = argument_boxes(body);
    if !argument_roles_are_stable(scoping, body, &parameters, &boxes) {
        return false;
    }
    let mut probe = SetterProbe {
        scoping,
        target,
        outer_parameters,
        outer_boxes,
        inner_parameters: parameters,
        inner_boxes: boxes,
        good_writes: 0,
        bad_writes: 0,
    };
    probe.visit_function_body(body);
    probe.good_writes == 1 && probe.bad_writes == 0
}

struct GetterProbe<'c, 'o, 'b> {
    scoping: &'c Scoping,
    target: &'o ExprKey,
    outer_parameters: &'o [SymbolId],
    outer_boxes: &'b HashSet<SymbolId>,
    returns: usize,
    invalid: bool,
}

impl<'a> Visit<'a> for GetterProbe<'_, '_, '_> {
    fn visit_return_statement(&mut self, statement: &oxc_ast::ast::ReturnStatement<'a>) {
        self.returns += 1;
        let Some(expression) = &statement.argument else {
            self.invalid = true;
            return;
        };
        if !getter_return_forwards(
            self.scoping,
            expression,
            self.target,
            self.outer_parameters,
            self.outer_boxes,
        ) {
            self.invalid = true;
        }
    }

    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }
}

fn getter_forwards(
    scoping: &Scoping,
    function: &Function<'_>,
    target: &ExprKey,
    outer_parameters: &[SymbolId],
    outer_boxes: &HashSet<SymbolId>,
) -> bool {
    if function.r#async || function.generator || !function.params.items.is_empty() {
        return false;
    }
    let Some(body) = &function.body else {
        return false;
    };
    let mut probe = GetterProbe {
        scoping,
        target,
        outer_parameters,
        outer_boxes,
        returns: 0,
        invalid: false,
    };
    probe.visit_function_body(body);
    probe.returns == 1 && !probe.invalid
}

fn is_object_constructor(
    scoping: &Scoping,
    expression: &Expression<'_>,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
) -> bool {
    if let Expression::Identifier(identifier) = expression {
        let Some(reference_id) = identifier.reference_id.get() else {
            return false;
        };
        return identifier.name.as_str() == "Object"
            && scoping.get_reference(reference_id).symbol_id().is_none();
    }
    let Expression::StaticMemberExpression(member) = expression else {
        return false;
    };
    !member.optional
        && member.property.name.as_str() == "Object"
        && argument_index_expr(scoping, &member.object, parameters, boxes) == Some(0)
}

type BranchPath = Vec<(u32, bool)>;

#[derive(Debug, Clone)]
struct KeyEvidence {
    key: ExprKey,
    path: BranchPath,
    start: u32,
}

#[derive(Debug, Clone)]
struct PairEvidence {
    left: ExprKey,
    right: ExprKey,
    path: BranchPath,
    start: u32,
}

fn evidence_precedes_on_path(evidence: &BranchPath, define: &BranchPath) -> bool {
    evidence
        .iter()
        .all(|constraint| define.contains(constraint))
}

fn merge_strings(
    left: &HashMap<ExprKey, String>,
    right: &HashMap<ExprKey, String>,
) -> HashMap<ExprKey, String> {
    left.iter()
        .filter_map(|(key, value)| {
            right
                .get(key)
                .filter(|other| *other == value)
                .map(|_| (key.clone(), value.clone()))
        })
        .collect()
}

struct HelperProbe<'c> {
    scoping: &'c Scoping,
    parameters: Vec<SymbolId>,
    boxes: HashSet<SymbolId>,
    owner_keys: HashSet<ExprKey>,
    target_keys: HashMap<ExprKey, u32>,
    initialized_targets: Vec<KeyEvidence>,
    setter_pairs: Vec<PairEvidence>,
    getter_pairs: Vec<PairEvidence>,
    define_pairs: Vec<PairEvidence>,
    strings: HashMap<ExprKey, String>,
    branch_path: BranchPath,
}

impl HelperProbe<'_> {
    fn string_value(&self, expression: &Expression<'_>) -> Option<String> {
        match expression {
            Expression::StringLiteral(value) => string_literal_value(value),
            _ => self
                .strings
                .get(&expr_key(self.scoping, expression)?)
                .cloned(),
        }
    }

    fn record_string_assignment(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'_>) {
        let Some(key) = assignment_target_key(self.scoping, &assignment.left) else {
            return;
        };
        match assignment.operator.as_str() {
            "=" => {
                if let Some(value) = self.string_value(&assignment.right) {
                    self.strings.insert(key, value);
                } else {
                    self.strings.remove(&key);
                }
            }
            "+=" => {
                let Some(suffix) = self.string_value(&assignment.right) else {
                    self.strings.remove(&key);
                    return;
                };
                if let Some(current) = self.strings.get_mut(&key) {
                    current.push_str(&suffix);
                } else {
                    self.strings.remove(&key);
                }
            }
            _ => {
                self.strings.remove(&key);
            }
        }
    }

    fn callee_is_define_property(&self, callee: &Expression<'_>) -> bool {
        match callee {
            Expression::StaticMemberExpression(member) => {
                !member.optional
                    && member.property.name.as_str() == "defineProperty"
                    && is_object_constructor(
                        self.scoping,
                        &member.object,
                        &self.parameters,
                        &self.boxes,
                    )
            }
            Expression::ComputedMemberExpression(member) => {
                !member.optional
                    && self.string_value(&member.expression).as_deref() == Some("defineProperty")
                    && is_object_constructor(
                        self.scoping,
                        &member.object,
                        &self.parameters,
                        &self.boxes,
                    )
            }
            _ => false,
        }
    }

    fn proven(&self) -> bool {
        self.define_pairs.iter().any(|define| {
            let Some(target_start) = self.target_keys.get(&define.left) else {
                return false;
            };
            if *target_start >= define.start {
                return false;
            }
            let evidence_ok = |path: &BranchPath, start: u32| {
                start < define.start && evidence_precedes_on_path(path, &define.path)
            };
            self.initialized_targets.iter().any(|evidence| {
                evidence.key == define.left && evidence_ok(&evidence.path, evidence.start)
            }) && self.setter_pairs.iter().any(|evidence| {
                evidence.left == define.right
                    && evidence.right == define.left
                    && evidence_ok(&evidence.path, evidence.start)
            }) && self.getter_pairs.iter().any(|evidence| {
                evidence.left == define.right
                    && evidence.right == define.left
                    && evidence_ok(&evidence.path, evidence.start)
            })
        })
    }
}

impl<'a> Visit<'a> for HelperProbe<'_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        self.record_string_assignment(assignment);

        if assignment.operator.as_str() == "=" {
            if self.branch_path.is_empty() {
                if let Some(left_key) = assignment_target_key(self.scoping, &assignment.left) {
                    if let Expression::CallExpression(call) = &assignment.right {
                        if is_resolver_call(self.scoping, call, &self.parameters, &self.boxes) {
                            self.owner_keys.insert(left_key.clone());
                        }
                    }
                    if selected_target_rhs(
                        self.scoping,
                        &assignment.right,
                        &self.parameters,
                        &self.boxes,
                        &self.owner_keys,
                    ) {
                        self.target_keys
                            .entry(left_key)
                            .or_insert(assignment.span.start);
                    }
                }
            }

            if let Some((object, property)) = assignment_member_parts(&assignment.left) {
                if argument_index_expr(self.scoping, property, &self.parameters, &self.boxes)
                    == Some(4)
                {
                    if let Some(target) = expr_key(self.scoping, object) {
                        if forwarded_member(
                            self.scoping,
                            &assignment.right,
                            &target,
                            &self.parameters,
                            &self.boxes,
                            2,
                        ) {
                            self.initialized_targets.push(KeyEvidence {
                                key: target,
                                path: self.branch_path.clone(),
                                start: assignment.span.start,
                            });
                        }
                    }
                }
            }

            if let AssignmentTarget::StaticMemberExpression(member) = &assignment.left {
                if !member.optional {
                    if let (Some(descriptor), Expression::FunctionExpression(function)) =
                        (expr_key(self.scoping, &member.object), &assignment.right)
                    {
                        for target in self.target_keys.keys() {
                            let evidence = PairEvidence {
                                left: descriptor.clone(),
                                right: (*target).clone(),
                                path: self.branch_path.clone(),
                                start: assignment.span.start,
                            };
                            match member.property.name.as_str() {
                                "set"
                                    if setter_forwards(
                                        self.scoping,
                                        function,
                                        target,
                                        &self.parameters,
                                        &self.boxes,
                                    ) =>
                                {
                                    self.setter_pairs.push(evidence);
                                }
                                "get"
                                    if getter_forwards(
                                        self.scoping,
                                        function,
                                        target,
                                        &self.parameters,
                                        &self.boxes,
                                    ) =>
                                {
                                    self.getter_pairs.push(evidence);
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }

        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional
            && call.arguments.len() == 3
            && self.callee_is_define_property(&call.callee)
            && argument_index_arg(
                self.scoping,
                &call.arguments[1],
                &self.parameters,
                &self.boxes,
            ) == Some(4)
        {
            if let (Some(target), Some(descriptor)) = (
                argument_key(self.scoping, &call.arguments[0]),
                argument_key(self.scoping, &call.arguments[2]),
            ) {
                self.define_pairs.push(PairEvidence {
                    left: target,
                    right: descriptor,
                    path: self.branch_path.clone(),
                    start: call.span.start,
                });
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_if_statement(&mut self, statement: &IfStatement<'a>) {
        walk::walk_expression(self, &statement.test);
        let base_strings = self.strings.clone();
        let marker = statement.span.start;

        self.branch_path.push((marker, true));
        walk::walk_statement(self, &statement.consequent);
        self.branch_path.pop();
        let consequent_strings = self.strings.clone();

        self.strings = base_strings.clone();
        let alternate_strings = if let Some(alternate) = &statement.alternate {
            self.branch_path.push((marker, false));
            walk::walk_statement(self, alternate);
            self.branch_path.pop();
            self.strings.clone()
        } else {
            base_strings
        };

        self.strings = merge_strings(&consequent_strings, &alternate_strings);
    }

    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }
}

struct HelperCollector<'c> {
    scoping: &'c Scoping,
    helpers: HashSet<SymbolId>,
}

impl<'a> Visit<'a> for HelperCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if !function.r#async && !function.generator {
            if let (Some(identifier), Some(body), Some(parameters)) =
                (&function.id, &function.body, parameter_symbols(function))
            {
                if parameters.len() == 5 {
                    if let Some(symbol) = identifier.symbol_id.get() {
                        let boxes = argument_boxes(body);
                        if !argument_roles_are_stable(self.scoping, body, &parameters, &boxes) {
                            walk::walk_function(self, function, flags);
                            return;
                        }
                        let mut probe = HelperProbe {
                            scoping: self.scoping,
                            parameters,
                            boxes,
                            owner_keys: HashSet::new(),
                            target_keys: HashMap::new(),
                            initialized_targets: Vec::new(),
                            setter_pairs: Vec::new(),
                            getter_pairs: Vec::new(),
                            define_pairs: Vec::new(),
                            strings: HashMap::new(),
                            branch_path: Vec::new(),
                        };
                        probe.visit_function_body(body);
                        if probe.proven() {
                            self.helpers.insert(symbol);
                        }
                    }
                }
            }
        }
        walk::walk_function(self, function, flags);
    }
}

fn only_unconditional_statements(statements: &[Statement<'_>]) -> bool {
    statements.iter().all(|statement| match statement {
        Statement::BlockStatement(block) => only_unconditional_statements(&block.body),
        Statement::VariableDeclaration(_)
        | Statement::ExpressionStatement(_)
        | Statement::ReturnStatement(_)
        | Statement::EmptyStatement(_)
        | Statement::DebuggerStatement(_) => true,
        _ => false,
    })
}

struct DelegateProbe<'c, 'h> {
    scoping: &'c Scoping,
    helpers: &'h HashSet<SymbolId>,
    parameters: Vec<SymbolId>,
    boxes: HashSet<SymbolId>,
    matches: usize,
}

impl<'a> Visit<'a> for DelegateProbe<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        let Expression::Identifier(callee) = last_sequence_expression(&call.callee) else {
            walk::walk_call_expression(self, call);
            return;
        };
        let Some(symbol) = callee
            .reference_id
            .get()
            .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
            .filter(|symbol| symbol_binding_is_stable(self.scoping, *symbol))
        else {
            walk::walk_call_expression(self, call);
            return;
        };
        if self.helpers.contains(&symbol)
            && call.arguments.len() == 5
            && (1..=4).all(|argument| {
                argument_index_arg(
                    self.scoping,
                    &call.arguments[argument],
                    &self.parameters,
                    &self.boxes,
                ) == u32::try_from(argument - 1).ok()
            })
        {
            self.matches += 1;
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }
}

struct InstallerCollector<'c, 'h> {
    scoping: &'c Scoping,
    helpers: &'h HashSet<SymbolId>,
    installers: HashSet<SymbolId>,
}

impl InstallerCollector<'_, '_> {
    fn analyze_function(&mut self, symbol: SymbolId, function: &Function<'_>) {
        if function.r#async || function.generator {
            return;
        }
        let (Some(body), Some(parameters)) = (&function.body, parameter_symbols(function)) else {
            return;
        };
        if parameters.len() != 4 || !only_unconditional_statements(&body.statements) {
            return;
        }
        let boxes = argument_boxes(body);
        if !argument_roles_are_stable(self.scoping, body, &parameters, &boxes) {
            return;
        }
        let mut probe = DelegateProbe {
            scoping: self.scoping,
            helpers: self.helpers,
            parameters,
            boxes,
            matches: 0,
        };
        probe.visit_function_body(body);
        if probe.matches == 1 {
            self.installers.insert(symbol);
        }
    }
}

impl<'a> Visit<'a> for InstallerCollector<'_, '_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(symbol) = function
            .id
            .as_ref()
            .and_then(|identifier| identifier.symbol_id.get())
        {
            self.analyze_function(symbol, function);
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(Expression::FunctionExpression(function)) = &declarator.init else {
                continue;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                continue;
            };
            self.analyze_function(symbol, function);
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

fn parameter_member_path(
    scoping: &Scoping,
    expression: &Expression<'_>,
    parameters: &[SymbolId],
    boxes: &HashSet<SymbolId>,
) -> Option<(u32, Vec<String>)> {
    if let Some(argument) = argument_index_expr(scoping, expression, parameters, boxes) {
        return Some((argument, Vec::new()));
    }
    match expression {
        Expression::ParenthesizedExpression(parenthesized) => {
            parameter_member_path(scoping, &parenthesized.expression, parameters, boxes)
        }
        Expression::StaticMemberExpression(member) if !member.optional => {
            let (argument, mut path) =
                parameter_member_path(scoping, &member.object, parameters, boxes)?;
            path.push(member.property.name.to_string());
            Some((argument, path))
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = &member.expression else {
                return None;
            };
            let (argument, mut path) =
                parameter_member_path(scoping, &member.object, parameters, boxes)?;
            path.push(string_literal_value(property)?);
            Some((argument, path))
        }
        _ => None,
    }
}

struct ParameterReferenceCollector<'c, 'p> {
    scoping: &'c Scoping,
    parameters: &'p [SymbolId],
    arguments: HashSet<u32>,
}

impl<'a> Visit<'a> for ParameterReferenceCollector<'_, '_> {
    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        let Some(symbol) = identifier
            .reference_id
            .get()
            .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
        else {
            return;
        };
        if let Some(index) = self
            .parameters
            .iter()
            .position(|parameter| *parameter == symbol)
        {
            if let Ok(index) = u32::try_from(index) {
                self.arguments.insert(index);
            }
        }
    }
    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }
}

fn parameter_references(
    scoping: &Scoping,
    expression: &Expression<'_>,
    parameters: &[SymbolId],
) -> HashSet<u32> {
    let mut collector = ParameterReferenceCollector {
        scoping,
        parameters,
        arguments: HashSet::new(),
    };
    collector.visit_expression(expression);
    collector.arguments
}

struct RegistryWriteCollector<'c, 'p> {
    scoping: &'c Scoping,
    parameters: &'p [SymbolId],
    boxes: &'p HashSet<SymbolId>,
    proofs: Vec<RegistryForwarderProof>,
}

impl<'a> Visit<'a> for RegistryWriteCollector<'_, '_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment.operator.is_assign() {
            if let AssignmentTarget::ComputedMemberExpression(member) = &assignment.left {
                if !member.optional {
                    if let (Some((receiver_argument, registry_path)), Some(key_argument)) = (
                        parameter_member_path(
                            self.scoping,
                            &member.object,
                            self.parameters,
                            self.boxes,
                        ),
                        argument_index_expr(
                            self.scoping,
                            &member.expression,
                            self.parameters,
                            self.boxes,
                        ),
                    ) {
                        let mut references =
                            parameter_references(self.scoping, &assignment.right, self.parameters);
                        references.remove(&receiver_argument);
                        references.remove(&key_argument);
                        if references.len() == 1 {
                            if let Some(value_argument) = references.iter().next().copied() {
                                if value_argument != receiver_argument
                                    && value_argument != key_argument
                                {
                                    self.proofs.push(RegistryForwarderProof {
                                        receiver_argument,
                                        key_argument,
                                        value_argument,
                                        registry_path,
                                    });
                                }
                            }
                        }
                    }
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

fn registry_forwarder_proof(
    scoping: &Scoping,
    function: &Function<'_>,
) -> Option<RegistryForwarderProof> {
    if function.r#async || function.generator {
        return None;
    }
    let (Some(body), Some(parameters)) = (&function.body, parameter_symbols(function)) else {
        return None;
    };
    if parameters.len() < 3 {
        return None;
    }
    let boxes = argument_boxes(body);
    let mut collector = RegistryWriteCollector {
        scoping,
        parameters: &parameters,
        boxes: &boxes,
        proofs: Vec::new(),
    };
    collector.visit_function_body(body);
    let first = collector.proofs.first()?.clone();
    if !collector.proofs.iter().all(|proof| proof == &first) {
        return None;
    }
    selected_argument_roles_are_stable(
        scoping,
        body,
        &parameters,
        &boxes,
        &[
            first.receiver_argument,
            first.key_argument,
            first.value_argument,
        ],
    )
    .then_some(first)
}

struct RegistryForwarderCollector<'c> {
    scoping: &'c Scoping,
    proofs: HashMap<SymbolId, RegistryForwarderProof>,
}
impl RegistryForwarderCollector<'_> {
    fn record(&mut self, symbol: SymbolId, function: &Function<'_>) {
        if let Some(proof) = registry_forwarder_proof(self.scoping, function) {
            self.proofs.insert(symbol, proof);
        }
    }
}
impl<'a> Visit<'a> for RegistryForwarderCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(symbol) = function
            .id
            .as_ref()
            .and_then(|identifier| identifier.symbol_id.get())
        {
            self.record(symbol, function);
        }
        walk::walk_function(self, function, flags);
    }
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(Expression::FunctionExpression(function)) = &declarator.init else {
                continue;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                continue;
            };
            self.record(symbol, function);
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

struct RegistryDelegateProbe<'c, 'p, 'k> {
    scoping: &'c Scoping,
    parameters: &'p [SymbolId],
    boxes: &'p HashSet<SymbolId>,
    known: &'k HashMap<SymbolId, RegistryForwarderProof>,
    proofs: Vec<RegistryForwarderProof>,
}

impl<'a> Visit<'a> for RegistryDelegateProbe<'_, '_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Expression::Identifier(callee) = last_sequence_expression(&call.callee) {
                if let Some(symbol) = callee
                    .reference_id
                    .get()
                    .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
                    .filter(|symbol| symbol_binding_is_stable(self.scoping, *symbol))
                {
                    if let Some(delegate) = self.known.get(&symbol) {
                        let mapped = [
                            delegate.receiver_argument,
                            delegate.key_argument,
                            delegate.value_argument,
                        ]
                        .map(|role| {
                            usize::try_from(role)
                                .ok()
                                .and_then(|index| call.arguments.get(index))
                                .and_then(|argument| {
                                    argument_index_arg(
                                        self.scoping,
                                        argument,
                                        self.parameters,
                                        self.boxes,
                                    )
                                })
                        });
                        if let [Some(receiver_argument), Some(key_argument), Some(value_argument)] =
                            mapped
                        {
                            if receiver_argument != key_argument
                                && receiver_argument != value_argument
                                && key_argument != value_argument
                            {
                                self.proofs.push(RegistryForwarderProof {
                                    receiver_argument,
                                    key_argument,
                                    value_argument,
                                    registry_path: delegate.registry_path.clone(),
                                });
                            }
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }
}

fn registry_delegate_proof(
    scoping: &Scoping,
    function: &Function<'_>,
    known: &HashMap<SymbolId, RegistryForwarderProof>,
) -> Option<RegistryForwarderProof> {
    if function.r#async || function.generator {
        return None;
    }
    let (Some(body), Some(parameters)) = (&function.body, parameter_symbols(function)) else {
        return None;
    };
    if parameters.len() < 3 {
        return None;
    }
    let boxes = argument_boxes(body);
    let mut probe = RegistryDelegateProbe {
        scoping,
        parameters: &parameters,
        boxes: &boxes,
        known,
        proofs: Vec::new(),
    };
    probe.visit_function_body(body);
    let first = probe.proofs.first()?.clone();
    if !probe.proofs.iter().all(|proof| proof == &first) {
        return None;
    }
    selected_argument_roles_are_stable(
        scoping,
        body,
        &parameters,
        &boxes,
        &[
            first.receiver_argument,
            first.key_argument,
            first.value_argument,
        ],
    )
    .then_some(first)
}

struct RegistryDelegateCollector<'c, 'k> {
    scoping: &'c Scoping,
    known: &'k HashMap<SymbolId, RegistryForwarderProof>,
    proofs: HashMap<SymbolId, RegistryForwarderProof>,
}

impl RegistryDelegateCollector<'_, '_> {
    fn record(&mut self, symbol: SymbolId, function: &Function<'_>) {
        if self.known.contains_key(&symbol) {
            return;
        }
        if let Some(proof) = registry_delegate_proof(self.scoping, function, self.known) {
            self.proofs.insert(symbol, proof);
        }
    }
}

impl<'a> Visit<'a> for RegistryDelegateCollector<'_, '_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(symbol) = function
            .id
            .as_ref()
            .and_then(|identifier| identifier.symbol_id.get())
        {
            self.record(symbol, function);
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(Expression::FunctionExpression(function)) = &declarator.init else {
                continue;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                continue;
            };
            self.record(symbol, function);
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RegistryAccessorProof {
    receiver_argument: u32,
    key_argument: u32,
    registry_path: Vec<String>,
}

struct RegistryReadProbe<'c, 'p> {
    scoping: &'c Scoping,
    parameters: &'p [SymbolId],
    boxes: &'p HashSet<SymbolId>,
    proofs: Vec<RegistryAccessorProof>,
}

impl<'a> Visit<'a> for RegistryReadProbe<'_, '_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment.operator.is_assign() {
            if let Expression::ComputedMemberExpression(member) = &assignment.right {
                if !member.optional {
                    if let (Some((receiver_argument, registry_path)), Some(key_argument)) = (
                        parameter_member_path(
                            self.scoping,
                            &member.object,
                            self.parameters,
                            self.boxes,
                        ),
                        argument_index_expr(
                            self.scoping,
                            &member.expression,
                            self.parameters,
                            self.boxes,
                        ),
                    ) {
                        if receiver_argument != key_argument {
                            self.proofs.push(RegistryAccessorProof {
                                receiver_argument,
                                key_argument,
                                registry_path,
                            });
                        }
                    }
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

fn registry_accessor_proof(
    scoping: &Scoping,
    function: &Function<'_>,
) -> Option<RegistryAccessorProof> {
    if function.r#async || function.generator {
        return None;
    }
    let (Some(body), Some(parameters)) = (&function.body, parameter_symbols(function)) else {
        return None;
    };
    if parameters.len() < 2 {
        return None;
    }
    let boxes = argument_boxes(body);
    let mut probe = RegistryReadProbe {
        scoping,
        parameters: &parameters,
        boxes: &boxes,
        proofs: Vec::new(),
    };
    probe.visit_function_body(body);
    let first = probe.proofs.first()?.clone();
    if !probe.proofs.iter().all(|proof| proof == &first) {
        return None;
    }
    selected_argument_roles_are_stable(
        scoping,
        body,
        &parameters,
        &boxes,
        &[first.receiver_argument, first.key_argument],
    )
    .then_some(first)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LazyRegistryAccessorProof {
    accessor: RegistryAccessorProof,
    function_start: u32,
    function_end: u32,
    cell_assignment_start: u32,
    cell_assignment_end: u32,
    probe_property: String,
    update_property: String,
    projection_property: String,
    selector_start: u32,
    selector_end: u32,
    selector_key_symbol: SymbolId,
    selector_polynomial: IntegerPolynomial,
}

struct RegistryCellAssignmentProbe<'c, 'p> {
    scoping: &'c Scoping,
    parameters: &'p [SymbolId],
    boxes: &'p HashSet<SymbolId>,
    accessor: &'p RegistryAccessorProof,
    matches: Vec<(SymbolId, u32, u32)>,
}

impl<'a> Visit<'a> for RegistryCellAssignmentProbe<'_, '_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment.operator.is_assign() {
            if let (
                AssignmentTarget::AssignmentTargetIdentifier(target),
                Expression::ComputedMemberExpression(member),
            ) = (&assignment.left, &assignment.right)
            {
                if !member.optional {
                    let receiver = parameter_member_path(
                        self.scoping,
                        &member.object,
                        self.parameters,
                        self.boxes,
                    );
                    let key = argument_index_expr(
                        self.scoping,
                        &member.expression,
                        self.parameters,
                        self.boxes,
                    );
                    if receiver.as_ref().is_some_and(|(argument, path)| {
                        *argument == self.accessor.receiver_argument
                            && *path == self.accessor.registry_path
                    }) && key == Some(self.accessor.key_argument)
                    {
                        if let Some(symbol) = target.reference_id.get().and_then(|reference_id| {
                            self.scoping.get_reference(reference_id).symbol_id()
                        }) {
                            self.matches
                                .push((symbol, assignment.span.start, assignment.span.end));
                        }
                    }
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

fn static_member_on_symbol(
    scoping: &Scoping,
    expression: &Expression<'_>,
    symbol: SymbolId,
) -> Option<String> {
    let Expression::StaticMemberExpression(member) = last_sequence_expression(expression) else {
        return None;
    };
    if member.optional
        || reference_symbol(scoping, last_sequence_expression(&member.object)) != Some(symbol)
    {
        return None;
    }
    Some(member.property.name.to_string())
}

fn static_method_call_on_symbol<'a>(
    scoping: &Scoping,
    expression: &'a Expression<'a>,
    symbol: SymbolId,
) -> Option<(String, &'a CallExpression<'a>)> {
    let Expression::CallExpression(call) = last_sequence_expression(expression) else {
        return None;
    };
    if call.optional {
        return None;
    }
    let Expression::StaticMemberExpression(member) = last_sequence_expression(&call.callee) else {
        return None;
    };
    if member.optional
        || reference_symbol(scoping, last_sequence_expression(&member.object)) != Some(symbol)
    {
        return None;
    }
    Some((member.property.name.to_string(), call))
}

fn first_return_expression<'a>(statement: &'a Statement<'a>) -> Option<&'a Expression<'a>> {
    match statement {
        Statement::ReturnStatement(ret) => ret.argument.as_ref(),
        Statement::BlockStatement(block) => {
            let Statement::ReturnStatement(ret) = block.body.first()? else {
                return None;
            };
            ret.argument.as_ref()
        }
        _ => None,
    }
}

fn fast_cell_branch_parts(
    scoping: &Scoping,
    test: &Expression<'_>,
    consequent: &Statement<'_>,
    cell: SymbolId,
) -> Option<(String, String)> {
    let probe_property = static_member_on_symbol(scoping, test, cell)?;
    let return_expression = first_return_expression(consequent)?;
    let (update_property, call) = static_method_call_on_symbol(scoping, return_expression, cell)?;
    call.arguments
        .is_empty()
        .then_some((probe_property, update_property))
}

fn one_effect_then_symbol<'a>(
    scoping: &Scoping,
    expression: &'a Expression<'a>,
    symbol: SymbolId,
) -> Option<&'a Expression<'a>> {
    let expression = match expression {
        Expression::ParenthesizedExpression(parenthesized) => &parenthesized.expression,
        expression => expression,
    };
    let Expression::SequenceExpression(sequence) = expression else {
        return None;
    };
    let [effect, value] = sequence.expressions.as_slice() else {
        return None;
    };
    if reference_symbol(scoping, last_sequence_expression(value)) != Some(symbol) {
        return None;
    }
    Some(effect)
}

fn slow_cell_projection<'a>(
    scoping: &Scoping,
    expression: &'a Expression<'a>,
    cell: SymbolId,
) -> Option<(String, String, &'a Expression<'a>)> {
    let expression = match expression {
        Expression::ParenthesizedExpression(parenthesized) => &parenthesized.expression,
        expression => expression,
    };
    let Expression::StaticMemberExpression(projection) = expression else {
        return None;
    };
    if projection.optional {
        return None;
    }
    let effect = one_effect_then_symbol(scoping, &projection.object, cell)?;
    let (update_property, call) = static_method_call_on_symbol(scoping, effect, cell)?;
    let [argument] = call.arguments.as_slice() else {
        return None;
    };
    let selector = argument.as_expression().map(last_sequence_expression)?;
    Some((
        update_property,
        projection.property.name.to_string(),
        selector,
    ))
}

fn function_body_has_dynamic_scope(body: &FunctionBody<'_>) -> bool {
    #[derive(Default)]
    struct Probe {
        dynamic: bool,
    }
    impl<'a> Visit<'a> for Probe {
        fn visit_with_statement(&mut self, _statement: &oxc_ast::ast::WithStatement<'a>) {
            self.dynamic = true;
        }

        fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
            if matches!(
                last_sequence_expression(&call.callee),
                Expression::Identifier(identifier) if identifier.name.as_str() == "eval"
            ) {
                self.dynamic = true;
            }
            walk::walk_call_expression(self, call);
        }
    }

    let mut probe = Probe::default();
    probe.visit_function_body(body);
    probe.dynamic
}

#[derive(Debug, Clone)]
struct LazyAccessorFastCandidate {
    span_start: u32,
    probe_property: String,
    update_property: String,
}

#[derive(Debug, Clone)]
struct LazyAccessorSlowCandidate {
    span_start: u32,
    update_property: String,
    projection_property: String,
    selector_start: u32,
    selector_end: u32,
    selector_polynomial: IntegerPolynomial,
}

struct LazyAccessorShapeCollector<'c> {
    scoping: &'c Scoping,
    cell: SymbolId,
    key: SymbolId,
    after: u32,
    fast: Vec<LazyAccessorFastCandidate>,
    slow: Vec<LazyAccessorSlowCandidate>,
}

impl<'a> Visit<'a> for LazyAccessorShapeCollector<'_> {
    fn visit_if_statement(&mut self, statement: &oxc_ast::ast::IfStatement<'a>) {
        if statement.span.start > self.after {
            if let Some((probe_property, update_property)) = fast_cell_branch_parts(
                self.scoping,
                &statement.test,
                &statement.consequent,
                self.cell,
            ) {
                self.fast.push(LazyAccessorFastCandidate {
                    span_start: statement.span.start,
                    probe_property,
                    update_property,
                });
            }
        }
        walk::walk_if_statement(self, statement);
    }

    fn visit_while_statement(&mut self, statement: &oxc_ast::ast::WhileStatement<'a>) {
        if statement.span.start > self.after {
            if let Some((probe_property, update_property)) =
                fast_cell_branch_parts(self.scoping, &statement.test, &statement.body, self.cell)
            {
                self.fast.push(LazyAccessorFastCandidate {
                    span_start: statement.span.start,
                    probe_property,
                    update_property,
                });
            }
        }
        walk::walk_while_statement(self, statement);
    }

    fn visit_return_statement(&mut self, statement: &oxc_ast::ast::ReturnStatement<'a>) {
        if statement.span.start > self.after {
            if let Some(argument) = statement.argument.as_ref() {
                if let Some((update_property, projection_property, selector)) =
                    slow_cell_projection(self.scoping, argument, self.cell)
                {
                    if let Some(selector_polynomial) = normalize_integer_polynomial(
                        selector,
                        self.scoping,
                        &HashMap::new(),
                        &HashMap::new(),
                        &HashSet::new(),
                    ) {
                        if selector_polynomial
                            .variables()
                            .into_iter()
                            .all(|symbol| symbol == self.key)
                        {
                            self.slow.push(LazyAccessorSlowCandidate {
                                span_start: statement.span.start,
                                update_property,
                                projection_property,
                                selector_start: selector.span().start,
                                selector_end: selector.span().end,
                                selector_polynomial,
                            });
                        }
                    }
                }
            }
        }
        walk::walk_return_statement(self, statement);
    }

    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }
}

fn lazy_registry_accessor_proof(
    scoping: &Scoping,
    function: &Function<'_>,
) -> Option<LazyRegistryAccessorProof> {
    let accessor = registry_accessor_proof(scoping, function)?;
    let (Some(body), Some(parameters)) = (&function.body, parameter_symbols(function)) else {
        return None;
    };
    if function_body_has_dynamic_scope(body) {
        return None;
    }
    let boxes = argument_boxes(body);
    let mut assignments = RegistryCellAssignmentProbe {
        scoping,
        parameters: &parameters,
        boxes: &boxes,
        accessor: &accessor,
        matches: Vec::new(),
    };
    assignments.visit_function_body(body);
    let [(cell, cell_assignment_start, cell_assignment_end)] = assignments.matches.as_slice()
    else {
        return None;
    };
    let receiver_symbol = parameters.get(usize::try_from(accessor.receiver_argument).ok()?)?;
    let key_symbol = parameters.get(usize::try_from(accessor.key_argument).ok()?)?;
    if cell == receiver_symbol || cell == key_symbol || boxes.contains(cell) {
        return None;
    }
    let write_count = scoping
        .get_resolved_reference_ids(*cell)
        .iter()
        .filter(|reference_id| scoping.get_reference(**reference_id).is_write())
        .count();
    if write_count != 1 {
        return None;
    }

    let selector_key_symbol = *key_symbol;
    let mut shapes = LazyAccessorShapeCollector {
        scoping,
        cell: *cell,
        key: selector_key_symbol,
        after: *cell_assignment_end,
        fast: Vec::new(),
        slow: Vec::new(),
    };
    shapes.visit_function_body(body);
    let [fast] = shapes.fast.as_slice() else {
        return None;
    };
    let [slow] = shapes.slow.as_slice() else {
        return None;
    };
    if fast.span_start >= slow.span_start || fast.update_property != slow.update_property {
        return None;
    }
    Some(LazyRegistryAccessorProof {
        accessor,
        function_start: function.span.start,
        function_end: function.span.end,
        cell_assignment_start: *cell_assignment_start,
        cell_assignment_end: *cell_assignment_end,
        probe_property: fast.probe_property.clone(),
        update_property: fast.update_property.clone(),
        projection_property: slow.projection_property.clone(),
        selector_start: slow.selector_start,
        selector_end: slow.selector_end,
        selector_key_symbol,
        selector_polynomial: slow.selector_polynomial.clone(),
    })
}

struct RegistryAccessorCollector<'c> {
    scoping: &'c Scoping,
    proofs: HashMap<SymbolId, RegistryAccessorProof>,
}
impl RegistryAccessorCollector<'_> {
    fn record(&mut self, symbol: SymbolId, function: &Function<'_>) {
        if let Some(proof) = registry_accessor_proof(self.scoping, function) {
            self.proofs.insert(symbol, proof);
        }
    }
}
impl<'a> Visit<'a> for RegistryAccessorCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(symbol) = function
            .id
            .as_ref()
            .and_then(|identifier| identifier.symbol_id.get())
        {
            self.record(symbol, function);
        }
        walk::walk_function(self, function, flags);
    }
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(Expression::FunctionExpression(function)) = &declarator.init else {
                continue;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                continue;
            };
            self.record(symbol, function);
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

struct RegistryReadCallCollector<'c, 'p> {
    scoping: &'c Scoping,
    proofs: &'p HashMap<SymbolId, RegistryAccessorProof>,
    calls: Vec<ProvenRegistryReadCall>,
}
impl<'a> Visit<'a> for RegistryReadCallCollector<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Expression::Identifier(callee) = last_sequence_expression(&call.callee) {
                if let Some(symbol) = callee
                    .reference_id
                    .get()
                    .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
                    .filter(|symbol| symbol_binding_is_stable(self.scoping, *symbol))
                {
                    if let Some(proof) = self.proofs.get(&symbol) {
                        let receiver = usize::try_from(proof.receiver_argument)
                            .ok()
                            .and_then(|index| call.arguments.get(index))
                            .and_then(Argument::as_expression)
                            .and_then(|expression| {
                                stable_receiver_expression(self.scoping, expression)
                            });
                        let key = usize::try_from(proof.key_argument)
                            .ok()
                            .and_then(|index| call.arguments.get(index))
                            .and_then(Argument::as_expression)
                            .map(last_sequence_expression);
                        if let (Some(receiver), Some(key)) = (receiver, key) {
                            self.calls.push(ProvenRegistryReadCall {
                                call_start: call.span.start,
                                call_end: call.span.end,
                                receiver_start: receiver.span().start,
                                receiver_end: receiver.span().end,
                                key_start: key.span().start,
                                key_end: key.span().end,
                                registry_path: proof.registry_path.clone(),
                            });
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

#[must_use]
pub fn structurally_proven_registry_read_calls(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenRegistryReadCall> {
    let mut accessors = RegistryAccessorCollector {
        scoping,
        proofs: HashMap::new(),
    };
    accessors.visit_program(program);
    let mut calls = RegistryReadCallCollector {
        scoping,
        proofs: &accessors.proofs,
        calls: Vec::new(),
    };
    calls.visit_program(program);
    calls
        .calls
        .sort_by_key(|call| (call.call_start, call.call_end));
    calls
        .calls
        .dedup_by_key(|call| (call.call_start, call.call_end));
    calls.calls
}

struct LazyRegistryAccessorCollector<'c> {
    scoping: &'c Scoping,
    proofs: HashMap<SymbolId, LazyRegistryAccessorProof>,
}

impl LazyRegistryAccessorCollector<'_> {
    fn record(&mut self, symbol: SymbolId, function: &Function<'_>) {
        if let Some(proof) = lazy_registry_accessor_proof(self.scoping, function) {
            self.proofs.insert(symbol, proof);
        }
    }
}

impl<'a> Visit<'a> for LazyRegistryAccessorCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(symbol) = function
            .id
            .as_ref()
            .and_then(|identifier| identifier.symbol_id.get())
        {
            self.record(symbol, function);
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(Expression::FunctionExpression(function)) = &declarator.init else {
                continue;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                continue;
            };
            self.record(symbol, function);
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

struct LazyRegistryReadCallCollector<'c, 'p> {
    scoping: &'c Scoping,
    proofs: &'p HashMap<SymbolId, LazyRegistryAccessorProof>,
    calls: Vec<ProvenLazyRegistryReadCall>,
}

impl<'a> Visit<'a> for LazyRegistryReadCallCollector<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Expression::Identifier(callee) = last_sequence_expression(&call.callee) {
                if let Some(symbol) = callee
                    .reference_id
                    .get()
                    .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
                    .filter(|symbol| symbol_binding_is_stable(self.scoping, *symbol))
                {
                    if let Some(proof) = self.proofs.get(&symbol) {
                        let receiver = usize::try_from(proof.accessor.receiver_argument)
                            .ok()
                            .and_then(|index| call.arguments.get(index))
                            .and_then(Argument::as_expression)
                            .and_then(|expression| {
                                stable_receiver_expression(self.scoping, expression)
                            });
                        let key = usize::try_from(proof.accessor.key_argument)
                            .ok()
                            .and_then(|index| call.arguments.get(index))
                            .and_then(Argument::as_expression)
                            .map(last_sequence_expression);
                        if let (Some(receiver), Some(key)) = (receiver, key) {
                            self.calls.push(ProvenLazyRegistryReadCall {
                                read: ProvenRegistryReadCall {
                                    call_start: call.span.start,
                                    call_end: call.span.end,
                                    receiver_start: receiver.span().start,
                                    receiver_end: receiver.span().end,
                                    key_start: key.span().start,
                                    key_end: key.span().end,
                                    registry_path: proof.accessor.registry_path.clone(),
                                },
                                accessor_function_start: proof.function_start,
                                accessor_function_end: proof.function_end,
                                cell_assignment_start: proof.cell_assignment_start,
                                cell_assignment_end: proof.cell_assignment_end,
                                probe_property: proof.probe_property.clone(),
                                update_property: proof.update_property.clone(),
                                projection_property: proof.projection_property.clone(),
                                selector_start: proof.selector_start,
                                selector_end: proof.selector_end,
                                selector_key_symbol: proof.selector_key_symbol,
                                selector_polynomial: proof.selector_polynomial.clone(),
                            });
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

/// Find call sites of registry accessors whose loaded cell follows one proven
/// lazy-accessor shape. The returned selector span belongs to the accessor
/// function body; callers may feed it into symbolic normalization separately.
#[must_use]
pub fn structurally_proven_lazy_registry_read_calls(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenLazyRegistryReadCall> {
    let mut accessors = LazyRegistryAccessorCollector {
        scoping,
        proofs: HashMap::new(),
    };
    accessors.visit_program(program);
    let mut calls = LazyRegistryReadCallCollector {
        scoping,
        proofs: &accessors.proofs,
        calls: Vec::new(),
    };
    calls.visit_program(program);
    calls
        .calls
        .sort_by_key(|call| (call.read.call_start, call.read.call_end));
    calls
        .calls
        .dedup_by_key(|call| (call.read.call_start, call.read.call_end));
    calls.calls
}

struct RegistryForwardingCallCollector<'c, 'p> {
    scoping: &'c Scoping,
    proofs: &'p HashMap<SymbolId, RegistryForwarderProof>,
    calls: Vec<ProvenRegistryForwardingCall>,
}
impl<'a> Visit<'a> for RegistryForwardingCallCollector<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Expression::Identifier(callee) = last_sequence_expression(&call.callee) {
                if let Some(symbol) = callee
                    .reference_id
                    .get()
                    .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
                    .filter(|symbol| symbol_binding_is_stable(self.scoping, *symbol))
                {
                    if let Some(proof) = self.proofs.get(&symbol) {
                        let receiver = usize::try_from(proof.receiver_argument)
                            .ok()
                            .and_then(|index| call.arguments.get(index))
                            .and_then(Argument::as_expression)
                            .and_then(|expression| {
                                stable_receiver_expression(self.scoping, expression)
                            });
                        let key = usize::try_from(proof.key_argument)
                            .ok()
                            .and_then(|index| call.arguments.get(index))
                            .and_then(Argument::as_expression)
                            .map(last_sequence_expression);
                        let value = usize::try_from(proof.value_argument)
                            .ok()
                            .and_then(|index| call.arguments.get(index))
                            .and_then(Argument::as_expression)
                            .map(last_sequence_expression);
                        if let (Some(receiver), Some(key), Some(value)) = (receiver, key, value) {
                            let handler = match value {
                                Expression::FunctionExpression(function) => Some((
                                    function.span.start,
                                    function.span.end,
                                    function.params.items.len(),
                                    function.r#async,
                                )),
                                Expression::ArrowFunctionExpression(function) => Some((
                                    function.span.start,
                                    function.span.end,
                                    function.params.items.len(),
                                    function.r#async,
                                )),
                                _ => None,
                            };
                            if let Some((
                                handler_start,
                                handler_end,
                                handler_params,
                                handler_async,
                            )) = handler
                            {
                                self.calls.push(ProvenRegistryForwardingCall {
                                    call_start: call.span.start,
                                    call_end: call.span.end,
                                    receiver_start: receiver.span().start,
                                    receiver_end: receiver.span().end,
                                    key_start: key.span().start,
                                    key_end: key.span().end,
                                    registry_path: proof.registry_path.clone(),
                                    handler_start,
                                    handler_end,
                                    handler_params,
                                    handler_async,
                                });
                            }
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

#[must_use]
pub fn structurally_proven_registry_forwarding_calls(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenRegistryForwardingCall> {
    let mut forwarders = RegistryForwarderCollector {
        scoping,
        proofs: HashMap::new(),
    };
    forwarders.visit_program(program);
    loop {
        let mut delegates = RegistryDelegateCollector {
            scoping,
            known: &forwarders.proofs,
            proofs: HashMap::new(),
        };
        delegates.visit_program(program);
        if delegates.proofs.is_empty() {
            break;
        }
        forwarders.proofs.extend(delegates.proofs);
    }
    let mut calls = RegistryForwardingCallCollector {
        scoping,
        proofs: &forwarders.proofs,
        calls: Vec::new(),
    };
    calls.visit_program(program);
    calls
        .calls
        .sort_by_key(|call| (call.call_start, call.call_end));
    calls
        .calls
        .dedup_by_key(|call| (call.call_start, call.call_end));
    calls.calls
}

#[must_use]
pub fn structurally_proven_forwarding_installers(
    program: &Program<'_>,
    scoping: &Scoping,
) -> HashSet<SymbolId> {
    let mut helpers = HelperCollector {
        scoping,
        helpers: HashSet::new(),
    };
    helpers.visit_program(program);
    let mut installers = InstallerCollector {
        scoping,
        helpers: &helpers.helpers,
        installers: HashSet::new(),
    };
    installers.visit_program(program);
    installers.installers
}

#[cfg(test)]
mod tests {
    use super::{
        structurally_proven_forwarding_installers, structurally_proven_registry_forwarding_calls,
        structurally_proven_registry_read_calls,
    };
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    fn proven_count(source: &str) -> usize {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic_ret.diagnostics.is_empty());
        structurally_proven_forwarding_installers(&parsed.program, semantic_ret.semantic.scoping())
            .len()
    }

    fn registry_calls(source: &str) -> Vec<super::ProvenRegistryForwardingCall> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic_ret.diagnostics.is_empty());
        structurally_proven_registry_forwarding_calls(
            &parsed.program,
            semantic_ret.semantic.scoping(),
        )
    }

    #[test]
    fn proves_parameter_forwarding_into_computed_registry_write() {
        let calls = registry_calls(
            r#"
            const wrap = (value) => ({ value });
            const install = function(receiver, key, value) {
                receiver.handlers[key] = wrap(receiver, key, value);
            };
            const state = { handlers: {} };
            install(state, 7, function(a) { return a + 1; });
        "#,
        );
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].registry_path, vec!["handlers"]);
        assert_eq!(calls[0].handler_params, 1);
    }

    #[test]
    fn proves_registry_forwarding_through_sequence_callee() {
        let calls = registry_calls(
            r#"
            function install(receiver, key, value) {
                receiver.handlers[key] = wrap(receiver, key, value);
            }
            (0, install)(state, 7, function(a) { return a + 1; });
        "#,
        );
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].registry_path, vec!["handlers"]);
    }

    #[test]
    fn rejects_sequence_callee_when_binding_can_be_reassigned() {
        let calls = registry_calls(
            r#"
            let install = function(receiver, key, value) {
                receiver.handlers[key] = wrap(receiver, key, value);
            };
            function replace() { install = other; }
            (replace(), install)(state, 7, function(a) { return a + 1; });
        "#,
        );
        assert!(calls.is_empty());
    }

    #[test]
    fn proves_registry_forwarding_through_sequence_arguments() {
        let calls = registry_calls(
            r#"
            function install(receiver, key, value) {
                receiver.handlers[key] = wrap(receiver, key, value);
            }
            install(state, (side(), 7), (other(), function(a) { return a + 1; }));
        "#,
        );
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].registry_path, vec!["handlers"]);
    }

    #[test]
    fn proves_registry_forwarding_through_stable_sequence_receiver() {
        let source = r#"
            function install(receiver, key, value) {
                receiver.handlers[key] = wrap(receiver, key, value);
            }
            const state = {};
            install((side(), state), 7, function(a) { return a + 1; });
        "#;
        let calls = registry_calls(source);
        assert_eq!(calls.len(), 1);
        let receiver = &source[calls[0].receiver_start as usize..calls[0].receiver_end as usize];
        assert_eq!(receiver, "state");
    }

    #[test]
    fn rejects_registry_forwarding_through_mutable_sequence_receiver() {
        let calls = registry_calls(
            r#"
            function install(receiver, key, value) {
                receiver.handlers[key] = wrap(receiver, key, value);
            }
            let state = {};
            function swap() { state = other; }
            install((swap(), state), 7, function(a) { return a + 1; });
        "#,
        );
        assert!(calls.is_empty());
    }

    #[test]
    fn rejects_registry_write_when_value_does_not_reach_rhs() {
        let calls = registry_calls(
            r#"
            function install(receiver, key, value) {
                receiver.handlers[key] = make(receiver, key);
            }
            install(state, 7, function(a) { return a; });
        "#,
        );
        assert!(calls.is_empty());
    }

    #[test]
    fn rejects_registry_write_with_ambiguous_extra_parameter_flow() {
        let calls = registry_calls(
            r#"
            function install(receiver, key, value, salt) {
                receiver.handlers[key] = make(receiver, key, value, salt);
            }
            install(state, 7, function(a) { return a; }, 12);
        "#,
        );
        assert!(calls.is_empty());
    }

    fn registry_reads(source: &str) -> Vec<super::ProvenRegistryReadCall> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic_ret.diagnostics.is_empty());
        structurally_proven_registry_read_calls(&parsed.program, semantic_ret.semantic.scoping())
    }

    #[test]
    fn proves_computed_registry_accessor_calls() {
        let reads = registry_reads(
            r#"
            function get(receiver, key, cell) {
                cell = receiver.handlers[key];
                if (cell.value) return cell.create();
                return cell.prototype;
            }
            const a = get(state, opcode);
            const b = get(other, 17);
        "#,
        );
        assert_eq!(reads.len(), 2);
        assert_eq!(reads[0].registry_path, vec!["handlers"]);
    }

    #[test]
    fn proves_lazy_registry_accessor_shape() {
        let allocator = Allocator::default();
        let source = r#"
            function get(receiver, key, cell) {
                if (cell = receiver.handlers[key], cell === undefined) throw Error();
                while (cell.value) { return cell.create(); }
                return (cell.create(key * key + 3), cell).prototype;
            }
            get(state, opcode);
        "#;
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let proven = super::structurally_proven_lazy_registry_read_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        );
        assert_eq!(proven.len(), 1);
        assert_eq!(proven[0].read.registry_path, vec!["handlers"]);
        assert_eq!(proven[0].probe_property, "value");
        assert_eq!(proven[0].update_property, "create");
        assert_eq!(proven[0].projection_property, "prototype");
        assert_eq!(
            &source[proven[0].selector_start as usize..proven[0].selector_end as usize],
            "key * key + 3"
        );
        assert_eq!(
            proven[0].selector_polynomial.variables(),
            vec![proven[0].selector_key_symbol]
        );
    }

    #[test]
    fn lazy_registry_accessor_rejects_selector_with_extra_symbol() {
        let allocator = Allocator::default();
        let source = r#"
            function get(receiver, key, cell, salt) {
                cell = receiver.handlers[key];
                if (cell.value) return cell.create();
                return (cell.create(key + salt), cell).prototype;
            }
            get(state, opcode, null, runtimeSalt);
        "#;
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(super::structurally_proven_lazy_registry_read_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .is_empty());
    }

    #[test]
    fn lazy_registry_accessor_rejects_multiple_slow_projections() {
        let allocator = Allocator::default();
        let source = r#"
            function get(receiver, key, cell) {
                cell = receiver.handlers[key];
                if (cell.value) return cell.create();
                if (flag) return (cell.create(key), cell).prototype;
                return (cell.create(key + 1), cell).prototype;
            }
            get(state, opcode);
        "#;
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(super::structurally_proven_lazy_registry_read_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .is_empty());
    }

    #[test]
    fn lazy_registry_accessor_rejects_dynamic_scope() {
        let allocator = Allocator::default();
        let source = r#"
            function get(receiver, key, cell) {
                cell = receiver.handlers[key];
                eval("cell = other");
                if (cell.value) return cell.create();
                return (cell.create(key), cell).prototype;
            }
            get(state, opcode);
        "#;
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(super::structurally_proven_lazy_registry_read_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .is_empty());
    }

    #[test]
    fn lazy_registry_accessor_rejects_mismatched_update_method() {
        let allocator = Allocator::default();
        let source = r#"
            function get(receiver, key, cell) {
                cell = receiver.handlers[key];
                if (cell.value) return cell.fast();
                return (cell.slow(key), cell).prototype;
            }
            get(state, opcode);
        "#;
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(super::structurally_proven_lazy_registry_read_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .is_empty());
    }

    #[test]
    fn lazy_registry_accessor_rejects_cell_reassignment() {
        let allocator = Allocator::default();
        let source = r#"
            function get(receiver, key, cell) {
                cell = receiver.handlers[key];
                cell = other;
                if (cell.value) return cell.create();
                return (cell.create(key), cell).prototype;
            }
            get(state, opcode);
        "#;
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(super::structurally_proven_lazy_registry_read_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .is_empty());
    }

    #[test]
    fn proves_registry_read_through_sequence_callee() {
        let reads = registry_reads(
            r#"
            function get(receiver, key, cell) {
                cell = receiver.handlers[key];
                return cell;
            }
            const result = (0, get)(state, opcode);
        "#,
        );
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].registry_path, vec!["handlers"]);
    }

    #[test]
    fn rejects_accessor_when_receiver_role_is_reassigned() {
        let reads = registry_reads(
            r#"
            function get(receiver, key, cell) {
                receiver = other;
                cell = receiver.handlers[key];
                return cell;
            }
            get(state, opcode);
        "#,
        );
        assert!(reads.is_empty());
    }

    #[test]
    fn proves_registry_forwarding_through_delegate_fixed_point() {
        let calls = registry_calls(
            r#"
            function install(receiver, key, value) {
                receiver.handlers[key] = wrap(receiver, key, value);
            }
            function delegate(selector, receiver, value, key) {
                if (selector) install(receiver, key, value);
            }
            function outer(receiver, value, key, selector) {
                delegate(selector, receiver, value, key);
            }
            outer(state, function(a) { return a; }, 9, true);
        "#,
        );
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].registry_path, vec!["handlers"]);
        assert_eq!(calls[0].handler_params, 1);
    }

    #[test]
    fn rejects_delegate_when_forwarded_value_role_is_reassigned() {
        let calls = registry_calls(
            r#"
            function install(receiver, key, value) {
                receiver.handlers[key] = wrap(receiver, key, value);
            }
            function delegate(receiver, key, value) {
                value = replacement;
                install(receiver, key, value);
            }
            delegate(state, 9, function(a) { return a; });
        "#,
        );
        assert!(calls.is_empty());
    }

    #[test]
    fn proves_live_accessor_forwarding_through_argument_boxes() {
        let source = r#"
            function helper(root, resolver, source, selector, alias) {
                var r = [arguments];
                var owner; owner = (1, r[0][1])(r[0][0]);
                var target; target = [owner, owner.prototype][r[0][3]];
                target[r[0][4]] = target[r[0][2]];
                var descriptor = {};
                descriptor.set = function(value) {
                    target[r[0][2]] = value;
                };
                descriptor.get = function() {
                    return typeof target[r[0][2]] == "undefined"
                        ? undefined
                        : target[r[0][2]];
                };
                var method; method = "define";
                method += "Property";
                r[0][0].Object[method](target, r[0][4], descriptor);
            }
            var install = function(resolver, source, selector, alias) {
                var q = [arguments];
                helper(globalThis, q[0][0], q[0][1], q[0][2], q[0][3]);
            };
        "#;
        assert_eq!(proven_count(source), 1);
    }

    #[test]
    fn rejects_non_forwarding_getter() {
        let source = r#"
            function helper(root, resolver, source, selector, alias) {
                var r = [arguments];
                var owner; owner = (1, r[0][1])(r[0][0]);
                var target; target = [owner, owner.prototype][r[0][3]];
                target[r[0][4]] = target[r[0][2]];
                var descriptor = {};
                descriptor.set = function(value) {
                    target[r[0][2]] = value;
                };
                descriptor.get = function() { return 123; };
                root.Object.defineProperty(target, r[0][4], descriptor);
            }
            function install(resolver, source, selector, alias) {
                var q = [arguments];
                helper(globalThis, q[0][0], q[0][1], q[0][2], q[0][3]);
            }
        "#;
        assert_eq!(proven_count(source), 0);
    }

    #[test]
    fn rejects_non_forwarding_setter() {
        let source = r#"
            function helper(root, resolver, source, selector, alias) {
                var r = [arguments];
                var owner; owner = (1, r[0][1])(r[0][0]);
                var target; target = [owner, owner.prototype][r[0][3]];
                target[r[0][4]] = target[r[0][2]];
                var descriptor = {};
                descriptor.set = function(value) { target[r[0][2]] = 123; };
                descriptor.get = function() { return target[r[0][2]]; };
                root.Object.defineProperty(target, r[0][4], descriptor);
            }
            var install = function(resolver, source, selector, alias) {
                var q = [arguments];
                helper(globalThis, q[0][0], q[0][1], q[0][2], q[0][3]);
            };
        "#;
        assert_eq!(proven_count(source), 0);
    }

    #[test]
    fn rejects_wrong_definition_method() {
        let source = r#"
            function helper(root, resolver, source, selector, alias) {
                var r = [arguments];
                var owner; owner = (1, r[0][1])(r[0][0]);
                var target; target = [owner, owner.prototype][r[0][3]];
                target[r[0][4]] = target[r[0][2]];
                var descriptor = {};
                descriptor.set = function(value) { target[r[0][2]] = value; };
                descriptor.get = function() { return target[r[0][2]]; };
                var method; method = "define"; method += "Properties";
                root.Object[method](target, r[0][4], descriptor);
            }
            var install = function(resolver, source, selector, alias) {
                var q = [arguments];
                helper(globalThis, q[0][0], q[0][1], q[0][2], q[0][3]);
            };
        "#;
        assert_eq!(proven_count(source), 0);
    }

    #[test]
    fn rejects_mutated_argument_role_box() {
        let source = r#"
            function helper(root, resolver, source, selector, alias) {
                var r = [arguments];
                r[0][1] = evil;
                var owner; owner = (1, r[0][1])(r[0][0]);
                var target; target = [owner, owner.prototype][r[0][3]];
                target[r[0][4]] = target[r[0][2]];
                var descriptor = {};
                descriptor.set = function(value) { target[r[0][2]] = value; };
                descriptor.get = function() { return target[r[0][2]]; };
                root.Object.defineProperty(target, r[0][4], descriptor);
            }
            var install = function(resolver, source, selector, alias) {
                var q = [arguments];
                helper(globalThis, q[0][0], q[0][1], q[0][2], q[0][3]);
            };
        "#;
        assert_eq!(proven_count(source), 0);
    }

    #[test]
    fn rejects_reassigned_role_parameter() {
        let source = r#"
            function helper(root, resolver, source, selector, alias) {
                resolver = evil;
                var r = [arguments];
                var owner; owner = (1, r[0][1])(r[0][0]);
                var target; target = [owner, owner.prototype][r[0][3]];
                target[r[0][4]] = target[r[0][2]];
                var descriptor = {};
                descriptor.set = function(value) { target[r[0][2]] = value; };
                descriptor.get = function() { return target[r[0][2]]; };
                root.Object.defineProperty(target, r[0][4], descriptor);
            }
            var install = function(resolver, source, selector, alias) {
                var q = [arguments];
                helper(globalThis, q[0][0], q[0][1], q[0][2], q[0][3]);
            };
        "#;
        assert_eq!(proven_count(source), 0);
    }

    #[test]
    fn rejects_argument_box_escape() {
        let source = r#"
            function helper(root, resolver, source, selector, alias) {
                var r = [arguments];
                unknown(r);
                var owner; owner = (1, r[0][1])(r[0][0]);
                var target; target = [owner, owner.prototype][r[0][3]];
                target[r[0][4]] = target[r[0][2]];
                var descriptor = {};
                descriptor.set = function(value) { target[r[0][2]] = value; };
                descriptor.get = function() { return target[r[0][2]]; };
                root.Object.defineProperty(target, r[0][4], descriptor);
            }
            var install = function(resolver, source, selector, alias) {
                var q = [arguments];
                helper(globalThis, q[0][0], q[0][1], q[0][2], q[0][3]);
            };
        "#;
        assert_eq!(proven_count(source), 0);
    }

    #[test]
    fn rejects_argument_box_use_before_initialization() {
        let source = r#"
            function helper(root, resolver, source, selector, alias) {
                var owner; owner = (1, r[0][1])(r[0][0]);
                var r = [arguments];
                var target; target = [owner, owner.prototype][r[0][3]];
                target[r[0][4]] = target[r[0][2]];
                var descriptor = {};
                descriptor.set = function(value) { target[r[0][2]] = value; };
                descriptor.get = function() { return target[r[0][2]]; };
                root.Object.defineProperty(target, r[0][4], descriptor);
            }
            var install = function(resolver, source, selector, alias) {
                var q = [arguments];
                helper(globalThis, q[0][0], q[0][1], q[0][2], q[0][3]);
            };
        "#;
        assert_eq!(proven_count(source), 0);
    }

    #[test]
    fn rejects_mutually_exclusive_descriptor_halves() {
        let source = r#"
            function helper(root, resolver, source, selector, alias) {
                var r = [arguments];
                var owner; owner = (1, r[0][1])(r[0][0]);
                var target; target = [owner, owner.prototype][r[0][3]];
                target[r[0][4]] = target[r[0][2]];
                var descriptor = {};
                if (flag) {
                    descriptor.set = function(value) { target[r[0][2]] = value; };
                } else {
                    descriptor.get = function() { return target[r[0][2]]; };
                }
                root.Object.defineProperty(target, r[0][4], descriptor);
            }
            var install = function(resolver, source, selector, alias) {
                var q = [arguments];
                helper(globalThis, q[0][0], q[0][1], q[0][2], q[0][3]);
            };
        "#;
        assert_eq!(proven_count(source), 0);
    }
}
