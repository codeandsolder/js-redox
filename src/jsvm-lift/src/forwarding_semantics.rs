use jsvm_safe_core::exact_u32;
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, AssignmentTarget, BindingPattern, CallExpression, Expression,
    Function, FunctionBody, IfStatement, Program, Statement, VariableDeclaration,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ExprKey {
    Symbol(SymbolId),
    Index(Box<ExprKey>, u32),
}

fn reference_symbol(scoping: &Scoping, expression: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = expression else {
        return None;
    };
    scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()
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
    matches!(&test.right, Expression::StringLiteral(value) if value.value.as_str() == "undefined")
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
            Expression::StringLiteral(value) => Some(value.value.to_string()),
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
        let Expression::Identifier(callee) = &call.callee else {
            walk::walk_call_expression(self, call);
            return;
        };
        let Some(symbol) = callee
            .reference_id
            .get()
            .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
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
    use super::structurally_proven_forwarding_installers;
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
