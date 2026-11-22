use crate::decoder_encoding::{
    decode_fixed_base64_latin1, decode_lower_alphabet_base64_rc4, decode_lower_alphabet_base64_uri,
    decode_standard_base64_latin1,
};
mod callable_observation;
mod fixed_base64_proof;
mod rotation_proof;

use crate::binding_facts::{BindingFacts, ReferenceIdentity};
use crate::numeric::exact_usize;
use crate::rewrite::Replacement;
use crate::value_eval::{
    canonical_array_index_key, eval, exact_computed_property_key, js_to_uint32,
    literal_property_key, render_value_array, same_values, Value,
};
use crate::{
    argument_integer, array_element, expression_integer, fragment, statically_resolved_symbol,
    statically_unresolved_global_reference, string_literal_value, symbol_has_only_read_references,
    symbol_of, template_element_value,
};
use fixed_base64_proof::fixed_base64_algorithm_proven;
use oxc_ast::ast::{
    Argument, BindingPattern, CallExpression, Expression, Statement, VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::{GetSpan, Span};
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use rotation_proof::{prove_checksum_rotation, prove_fixed_rotation, ChecksumExpression};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    rc::Rc,
    sync::LazyLock,
};
use work_budget::{BudgetExceeded, WorkBudget};

/// Convert an integer into the JavaScript Number domain. Precision loss above
/// 2^53 is intentional here: JavaScript itself stores the value as IEEE-754 f64.
#[expect(
    clippy::cast_precision_loss,
    reason = "JavaScript Number semantics intentionally round integers through IEEE-754 f64"
)]
const fn js_number_from_u64(value: u64) -> f64 {
    value as f64
}

/// Signed counterpart; rounding is intentional JavaScript Number semantics.
#[expect(
    clippy::cast_precision_loss,
    reason = "JavaScript Number semantics intentionally round integers through IEEE-754 f64"
)]
const fn js_number_from_i64(value: i64) -> f64 {
    value as f64
}

#[derive(Debug, Clone)]
struct StaticArrayInfo {
    symbol: SymbolId,
    values: Vec<Value>,
    span: Span,
}

#[derive(Default)]
struct StaticArrayCollector {
    candidates: Vec<StaticArrayInfo>,
}

impl<'a> Visit<'a> for StaticArrayCollector {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        for d in &it.declarations {
            let BindingPattern::BindingIdentifier(id) = &d.id else {
                continue;
            };
            let Some(symbol) = id.symbol_id.get() else {
                continue;
            };
            let Some(Expression::ArrayExpression(arr)) = &d.init else {
                continue;
            };
            let Some(values) = arr
                .elements
                .iter()
                .map(array_element)
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            if !values.is_empty() {
                self.candidates.push(StaticArrayInfo {
                    symbol,
                    values,
                    span: arr.span,
                });
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn all_static_arrays(program: &oxc_ast::ast::Program<'_>) -> Vec<StaticArrayInfo> {
    let mut collector = StaticArrayCollector::default();
    collector.visit_program(program);
    collector.candidates
}

#[derive(Debug, Clone)]
struct PartialStaticArrayInfo {
    symbol: SymbolId,
    values: Vec<Option<Value>>,
}

#[derive(Default)]
struct PartialStaticArrayCollector {
    candidates: Vec<PartialStaticArrayInfo>,
}

impl<'a> Visit<'a> for PartialStaticArrayCollector {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        for declaration in &it.declarations {
            let BindingPattern::BindingIdentifier(id) = &declaration.id else {
                continue;
            };
            let Some(symbol) = id.symbol_id.get() else {
                continue;
            };
            let Some(Expression::ArrayExpression(array)) = &declaration.init else {
                continue;
            };
            let mut values = Vec::with_capacity(array.elements.len());
            let mut valid = true;
            for element in &array.elements {
                let value = match element {
                    oxc_ast::ast::ArrayExpressionElement::SpreadElement(_) => {
                        valid = false;
                        break;
                    }
                    // A hole has no own descriptor and can inherit a value.
                    oxc_ast::ast::ArrayExpressionElement::Elision(_) => None,
                    _ => array_element(element),
                };
                values.push(value);
            }
            if valid && !values.is_empty() && values.iter().any(Option::is_some) {
                self.candidates
                    .push(PartialStaticArrayInfo { symbol, values });
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn partial_decoder_arrays(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> Vec<PartialStaticArrayInfo> {
    let mut collector = PartialStaticArrayCollector::default();
    collector.visit_program(program);
    collector
        .candidates
        .retain(|candidate| symbol_has_only_read_references(scoping, candidate.symbol));
    collector.candidates
}

fn fixed_decoder_loop_shape(statement: &Statement<'_>) -> bool {
    let Statement::ForStatement(statement) = statement else {
        return false;
    };
    match &statement.body {
        Statement::ExpressionStatement(_) => true,
        // The generic sequence splitter may already have turned the decoder's
        // six comma-separated loop operations into six expression statements.
        Statement::BlockStatement(block) => {
            block.body.len() == 6
                && block
                    .body
                    .iter()
                    .all(|statement| matches!(statement, Statement::ExpressionStatement(_)))
        }
        _ => false,
    }
}

fn fixed_decoder_control_shape(body: &oxc_ast::ast::FunctionBody<'_>) -> bool {
    if body.statements.len() != 3 {
        return false;
    }
    let first = matches!(
        &body.statements[0],
        Statement::IfStatement(statement)
            if statement.alternate.is_none()
                && matches!(&statement.consequent, Statement::ReturnStatement(_))
    );
    let second = fixed_decoder_loop_shape(&body.statements[1]);
    let third = matches!(&body.statements[2], Statement::ReturnStatement(_));
    first && second && third
}

fn fixed_decoder_iife_body_shape(body: &oxc_ast::ast::FunctionBody<'_>) -> bool {
    if !(3..=6).contains(&body.statements.len())
        || !matches!(body.statements.last(), Some(Statement::ReturnStatement(_)))
    {
        return false;
    }

    let mut loops = 0usize;
    for statement in &body.statements[..body.statements.len() - 1] {
        match statement {
            Statement::VariableDeclaration(_) | Statement::ExpressionStatement(_) => {}
            Statement::BlockStatement(block)
                if block
                    .body
                    .iter()
                    .all(|statement| matches!(statement, Statement::ExpressionStatement(_))) => {}
            Statement::ForStatement(_) if fixed_decoder_loop_shape(statement) => loops += 1,
            _ => return false,
        }
    }
    loops == 1
}

struct FixedDecoderCallProbe<'c> {
    scoping: &'c Scoping,
    aliases: &'c HashMap<SymbolId, u32>,
    function_span: Span,
    valid: bool,
}

impl<'a> Visit<'a> for FixedDecoderCallProbe<'_> {
    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        if !self.valid {
            return;
        }
        let Some(reference_id) = identifier.reference_id.get() else {
            self.valid = false;
            return;
        };
        let reference = self.scoping.get_reference(reference_id);
        match reference.symbol_id() {
            Some(symbol) => {
                let declaration = self.scoping.symbol_span(symbol);
                let local = self.function_span.start <= declaration.start
                    && declaration.end <= self.function_span.end;
                if !local && !self.aliases.contains_key(&symbol) {
                    self.valid = false;
                }
            }
            None if identifier.name.as_str() == "String" => {}
            None => self.valid = false,
        }
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !self.valid || call.optional || call.arguments.iter().any(Argument::is_spread) {
            self.valid = false;
            return;
        }
        let allowed = match &call.callee {
            Expression::Identifier(identifier) => identifier
                .reference_id
                .get()
                .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
                .is_some_and(|symbol| self.aliases.contains_key(&symbol)),
            Expression::StaticMemberExpression(member) if !member.optional => {
                let property = member.property.name.as_str();
                if matches!(property, "replace" | "indexOf" | "charAt") {
                    true
                } else {
                    property == "fromCharCode"
                        && matches!(&member.object, Expression::Identifier(object)
                        if object.name.as_str() == "String"
                            && symbol_of(self.scoping, &member.object).is_none())
                }
            }
            _ => false,
        };
        if !allowed {
            self.valid = false;
            return;
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_function(&mut self, _function: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {
        self.valid = false;
    }
}

fn fixed_decoder_iife_calls_proven(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    aliases: &HashMap<SymbolId, u32>,
) -> bool {
    let Some(body) = function.body.as_ref() else {
        return false;
    };
    let mut probe = FixedDecoderCallProbe {
        scoping,
        aliases,
        function_span: function.span,
        valid: true,
    };
    for statement in &body.statements {
        probe.visit_statement(statement);
        if !probe.valid {
            return false;
        }
    }
    true
}

fn fixed_decoder_iife_function<'a>(
    body: &'a oxc_ast::ast::FunctionBody<'a>,
) -> Option<&'a oxc_ast::ast::Function<'a>> {
    if !(1..=2).contains(&body.statements.len()) {
        return None;
    }
    let Statement::ReturnStatement(statement) = body.statements.last()? else {
        return None;
    };
    let Expression::ConditionalExpression(conditional) = statement.argument.as_ref()? else {
        return None;
    };
    let Expression::CallExpression(call) = &conditional.consequent else {
        return None;
    };
    if call.optional || call.arguments.len() != 1 || call.arguments[0].is_spread() {
        return None;
    }
    let function = rotation_iife_function(&call.callee)?;
    function
        .body
        .as_ref()
        .is_some_and(|body| fixed_decoder_iife_body_shape(body))
        .then_some(function)
}

#[derive(Debug, Clone)]
struct LocalStaticArrayInfo {
    values: Vec<Value>,
    span: Span,
}

#[derive(Debug, Clone)]
struct PlainDecoderShape {
    provider_symbol: SymbolId,
    offset: i64,
    installation: Option<ReferenceId>,
}

#[derive(Debug)]
struct FnInfo {
    name: String,
    symbol: SymbolId,
    scope: ScopeId,
    params: Vec<String>,
    span: Span,
    provider: Option<LocalStaticArrayInfo>,
    parameters_proven: bool,
    plain_decoder: Option<PlainDecoderShape>,
}

fn static_string_split(expression: &Expression<'_>) -> Option<LocalStaticArrayInfo> {
    let Expression::CallExpression(call) = unparenthesized(expression) else {
        return None;
    };
    if call.optional || call.arguments.len() != 1 || call.arguments[0].is_spread() {
        return None;
    }
    let Expression::StaticMemberExpression(member) = unparenthesized(&call.callee) else {
        return None;
    };
    if member.optional || member.property.name.as_str() != "split" {
        return None;
    }
    let Value::String(value) = eval(&member.object)? else {
        return None;
    };
    let Value::String(separator) = eval(call.arguments[0].as_expression()?)? else {
        return None;
    };
    // Empty-separator split is defined in UTF-16 code units; js-redox's static
    // string proof domain is UTF-8, so do not approximate that case.
    if separator.is_empty() {
        return None;
    }
    let values = value
        .split(&separator)
        .map(|part| Value::String(part.to_string()))
        .collect::<Vec<_>>();
    Some(LocalStaticArrayInfo {
        values,
        span: call.span,
    })
}

fn assignment_identifier<'a>(
    expression: &'a Expression<'a>,
) -> Option<(
    &'a oxc_ast::ast::IdentifierReference<'a>,
    &'a Expression<'a>,
)> {
    let Expression::AssignmentExpression(assignment) = unparenthesized(expression) else {
        return None;
    };
    if assignment.operator.as_str() != "=" {
        return None;
    }
    let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left
    else {
        return None;
    };
    Some((target, &assignment.right))
}

/// Ordinary, argument-free calls used by a self-installing provider.
fn zero_argument_call<'a>(expression: &'a Expression<'a>) -> Option<&'a Expression<'a>> {
    let Expression::CallExpression(call) = unparenthesized(expression) else {
        return None;
    };
    (!call.optional && call.arguments.is_empty()).then_some(&call.callee)
}

fn exact_identifier(
    expression: &Expression<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    facts.resolved_symbol(scoping, identifier.reference_id.get()?)
}

/// Prove the sole permitted write: installing a zero-argument function
/// that returns the exact newly created table, rather than a similarly
/// spelled or dynamically resolved name.
fn provider_installation(
    expression: &Expression<'_>,
    provider: SymbolId,
    table: SymbolId,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<ReferenceId> {
    let (target, value) = assignment_identifier(expression)?;
    let reference = target.reference_id.get()?;
    if facts.resolved_symbol(scoping, reference) != Some(provider)
        || !scoping.get_reference(reference).is_write()
    {
        return None;
    }
    let Expression::FunctionExpression(replacement) = unparenthesized(value) else {
        return None;
    };
    if replacement.r#async
        || replacement.generator
        || !replacement.params.items.is_empty()
        || replacement.params.rest.is_some()
    {
        return None;
    }
    let body = replacement.body.as_ref()?;
    let [Statement::ReturnStatement(returned)] = body.statements.as_slice() else {
        return None;
    };
    if !body.directives.is_empty()
        || exact_identifier(returned.argument.as_ref()?, scoping, facts) != Some(table)
    {
        return None;
    }
    Some(reference)
}

/// An installation and tail invocation can be separate statements, a return
/// sequence, or an immediately invoked assignment. These have the same
/// table/provider binding roles and no additional work.
fn provider_tail(
    statements: &[Statement<'_>],
    provider: SymbolId,
    table: SymbolId,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<ReferenceId> {
    let installation = match statements {
        [Statement::ExpressionStatement(install), Statement::ReturnStatement(ret)] => {
            if exact_identifier(zero_argument_call(ret.argument.as_ref()?)?, scoping, facts)
                != Some(provider)
            {
                return None;
            }
            &install.expression
        }
        [Statement::ReturnStatement(ret)] => {
            let argument = unparenthesized(ret.argument.as_ref()?);
            if let Expression::SequenceExpression(sequence) = argument {
                let [install, tail] = sequence.expressions.as_slice() else {
                    return None;
                };
                if exact_identifier(zero_argument_call(tail)?, scoping, facts) != Some(provider) {
                    return None;
                }
                install
            } else {
                zero_argument_call(argument)?
            }
        }
        _ => return None,
    };
    provider_installation(installation, provider, table, scoping, facts)
}

fn self_rewriting_provider(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<LocalStaticArrayInfo> {
    if function.r#async
        || function.generator
        || function.params.rest.is_some()
        || !function_parameters_have_no_runtime_effects(function)
    {
        return None;
    }
    let provider = function.id.as_ref()?.symbol_id.get()?;
    if facts.is_exported_binding(provider)
        || !facts.binding_unmodified_by_eval(scoping, provider)
        || !scoping.symbol_redeclarations(provider).is_empty()
    {
        return None;
    }
    let body = function.body.as_ref()?;
    if !body.directives.is_empty() {
        return None;
    }
    let (table, values, installation) = match function.params.items.as_slice() {
        [] => {
            let (first, tail) = body.statements.split_first()?;
            let Statement::VariableDeclaration(declaration) = first else {
                return None;
            };
            if !rotation_proof::ordinary_declaration(declaration) {
                return None;
            }
            let [declarator] = declaration.declarations.as_slice() else {
                return None;
            };
            let table = declarator.id.get_binding_identifier()?.symbol_id.get()?;
            let Expression::ArrayExpression(array) = unparenthesized(declarator.init.as_ref()?)
            else {
                return None;
            };
            let values = array
                .elements
                .iter()
                .map(array_element)
                .collect::<Option<Vec<_>>>()?;
            if values.is_empty() || !facts.binding_has_stable_value(scoping, table) {
                return None;
            }
            let installation = provider_tail(tail, provider, table, scoping, facts)?;
            (
                table,
                LocalStaticArrayInfo {
                    values,
                    span: array.span,
                },
                installation,
            )
        }
        [parameter] => {
            let table = parameter
                .pattern
                .get_binding_identifier()?
                .symbol_id
                .get()?;
            let [Statement::ReturnStatement(ret)] = body.statements.as_slice() else {
                return None;
            };
            let Expression::SequenceExpression(sequence) = unparenthesized(ret.argument.as_ref()?)
            else {
                return None;
            };
            let [assign, install, tail] = sequence.expressions.as_slice() else {
                return None;
            };
            let (target, value) = assignment_identifier(assign)?;
            let reference = target.reference_id.get()?;
            if facts.resolved_symbol(scoping, reference) != Some(table)
                || !scoping.get_reference(reference).is_write()
                || exact_identifier(zero_argument_call(tail)?, scoping, facts) != Some(provider)
                || !scoping
                    .get_resolved_reference_ids(table)
                    .iter()
                    .all(|&candidate| {
                        candidate == reference
                            || (scoping.get_reference(candidate).is_read()
                                && !scoping.get_reference(candidate).is_write()
                                && !scoping
                                    .get_reference(candidate)
                                    .flags()
                                    .is_member_write_target()
                                && facts.resolved_symbol(scoping, candidate) == Some(table))
                    })
            {
                return None;
            }
            let values = static_string_split(value)?;
            (
                table,
                values,
                provider_installation(install, provider, table, scoping, facts)?,
            )
        }
        _ => return None,
    };
    if table == provider
        || facts.is_eval_exposed(scoping, table)
        || !scoping.symbol_redeclarations(table).is_empty()
    {
        return None;
    }
    scoping
        .get_resolved_reference_ids(provider)
        .iter()
        .all(|&reference| {
            reference == installation
                || (facts.resolved_symbol(scoping, reference) == Some(provider)
                    && scoping.get_reference(reference).is_read()
                    && !scoping.get_reference(reference).is_write()
                    && !scoping
                        .get_reference(reference)
                        .flags()
                        .is_member_write_target())
        })
        .then_some(values)
}

/// Only the public positional parameter may be adjusted by a fixed
/// numeric subtraction before any provider-table access.
fn adjusted_index_offset(
    expression: &Expression<'_>,
    index: SymbolId,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<i64> {
    let Expression::AssignmentExpression(assignment) = unparenthesized(expression) else {
        return None;
    };
    let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left
    else {
        return None;
    };
    if facts.fixed_assignment_reference(scoping, target.reference_id.get()?) != Some(index) {
        return None;
    }
    match assignment.operator.as_str() {
        "-=" => expression_integer(&assignment.right),
        "=" => {
            let Expression::BinaryExpression(binary) = unparenthesized(&assignment.right) else {
                return None;
            };
            if binary.operator.as_str() != "-"
                || exact_identifier(&binary.left, scoping, facts) != Some(index)
            {
                return None;
            }
            expression_integer(&binary.right)
        }
        _ => None,
    }
}

fn sequence_decoder_shape(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<PlainDecoderShape> {
    if function.r#async || function.generator || function.params.rest.is_some() {
        return None;
    }
    let public_param = function.params.items.first()?;
    let BindingPattern::BindingIdentifier(public_param) = &public_param.pattern else {
        return None;
    };
    let public_param_symbol = public_param.symbol_id.get()?;
    let parameter_symbols = function
        .params
        .items
        .iter()
        .filter_map(|param| match &param.pattern {
            BindingPattern::BindingIdentifier(id) => id.symbol_id.get(),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let body = function.body.as_ref()?;
    if !body.directives.is_empty() || body.statements.len() != 1 {
        return None;
    }
    let Statement::ReturnStatement(ret) = &body.statements[0] else {
        return None;
    };
    let Expression::SequenceExpression(sequence) = unparenthesized(ret.argument.as_ref()?) else {
        return None;
    };
    let [offset_assignment, table_assignment, value_assignment, returned] =
        sequence.expressions.as_slice()
    else {
        return None;
    };

    let offset = adjusted_index_offset(offset_assignment, public_param_symbol, scoping, facts)?;

    let (table_target, table_value) = assignment_identifier(table_assignment)?;
    let table_symbol = facts.resolved_symbol(scoping, table_target.reference_id.get()?)?;
    if !parameter_symbols.contains(&table_symbol) || table_symbol == public_param_symbol {
        return None;
    }
    let Expression::CallExpression(provider_call) = unparenthesized(table_value) else {
        return None;
    };
    if provider_call.optional || !provider_call.arguments.is_empty() {
        return None;
    }
    let Expression::Identifier(provider) = unparenthesized(&provider_call.callee) else {
        return None;
    };
    let provider_symbol = facts.resolved_symbol(scoping, provider.reference_id.get()?)?;

    let (value_target, value_expression) = assignment_identifier(value_assignment)?;
    let value_symbol = facts.resolved_symbol(scoping, value_target.reference_id.get()?)?;
    if !parameter_symbols.contains(&value_symbol)
        || value_symbol == public_param_symbol
        || value_symbol == table_symbol
    {
        return None;
    }
    let Expression::ComputedMemberExpression(member) = unparenthesized(value_expression) else {
        return None;
    };
    if member.optional {
        return None;
    }
    let Expression::Identifier(table_read) = unparenthesized(&member.object) else {
        return None;
    };
    let Expression::Identifier(index_read) = unparenthesized(&member.expression) else {
        return None;
    };
    if facts.resolved_symbol(scoping, table_read.reference_id.get()?) != Some(table_symbol)
        || facts.resolved_symbol(scoping, index_read.reference_id.get()?)
            != Some(public_param_symbol)
    {
        return None;
    }
    let Expression::Identifier(returned) = unparenthesized(returned) else {
        return None;
    };
    if facts.resolved_symbol(scoping, returned.reference_id.get()?) != Some(value_symbol) {
        return None;
    }

    Some(PlainDecoderShape {
        provider_symbol,
        offset,
        installation: None,
    })
}

/// Unambiguous local declarations contain one ordinary binding and a
/// complete initializer. Do not treat resource-disposal declarations as
/// ordinary data temporaries.
fn local_initializer<'a>(
    statement: &'a Statement<'a>,
    scoping: &Scoping,
    excluded: &[SymbolId],
) -> Option<(SymbolId, &'a Expression<'a>)> {
    let Statement::VariableDeclaration(declaration) = statement else {
        return None;
    };
    if !rotation_proof::ordinary_declaration(declaration) {
        return None;
    }
    let [declarator] = declaration.declarations.as_slice() else {
        return None;
    };
    let symbol = declarator.id.get_binding_identifier()?.symbol_id.get()?;
    (!excluded.contains(&symbol) && scoping.symbol_redeclarations(symbol).is_empty())
        .then_some((symbol, declarator.init.as_ref()?))
}

fn provider_initializer(
    expression: &Expression<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<SymbolId> {
    exact_identifier(zero_argument_call(expression)?, scoping, facts)
}

/// The exact table/index reference roles are shared across the
/// return-expression and temporary-variable forms.
fn table_index<'a>(
    expression: &'a Expression<'a>,
    table: SymbolId,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<&'a Expression<'a>> {
    let Expression::ComputedMemberExpression(member) = unparenthesized(expression) else {
        return None;
    };
    (!member.optional && exact_identifier(&member.object, scoping, facts) == Some(table))
        .then_some(&member.expression)
}

fn returned_value(
    statements: &[Statement<'_>],
    table: SymbolId,
    index: SymbolId,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<()> {
    let expression = match statements {
        [Statement::ReturnStatement(result)] => result.argument.as_ref()?,
        [declaration, Statement::ReturnStatement(result)] => {
            let (value, read) = local_initializer(declaration, scoping, &[table, index])?;
            if exact_identifier(result.argument.as_ref()?, scoping, facts) != Some(value) {
                return None;
            }
            read
        }
        _ => return None,
    };
    (exact_identifier(
        table_index(expression, table, scoping, facts)?,
        scoping,
        facts,
    ) == Some(index))
    .then_some(())
}

fn statement_decoder_shape(
    function: &oxc_ast::ast::Function<'_>,
    parameters: &[SymbolId],
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<PlainDecoderShape> {
    let index = *parameters.first()?;
    let [Statement::ExpressionStatement(adjustment), declaration, remaining @ ..] =
        function.body.as_ref()?.statements.as_slice()
    else {
        return None;
    };
    let offset = adjusted_index_offset(&adjustment.expression, index, scoping, facts)?;
    let (table, initializer) = local_initializer(declaration, scoping, parameters)?;
    let provider_symbol = provider_initializer(initializer, scoping, facts)?;
    returned_value(remaining, table, index, scoping, facts)?;
    Some(PlainDecoderShape {
        provider_symbol,
        offset,
        installation: None,
    })
}

/// Validate the complete replacement function, not a fragment of its
/// return expression. Forwarded arguments must be the original positional
/// bindings; the only persistent write is the function installation.
fn replacement_decoder_shape(
    function: &oxc_ast::ast::Function<'_>,
    parameters: &[SymbolId],
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<PlainDecoderShape> {
    let symbol = function.id.as_ref()?.symbol_id.get()?;
    let (declaration, tail) = function.body.as_ref()?.statements.split_first()?;
    let (table, initializer) = local_initializer(declaration, scoping, parameters)?;
    let provider_symbol = provider_initializer(initializer, scoping, facts)?;
    let (installation, invocation, named_tail) = match tail {
        [Statement::ExpressionStatement(install), Statement::ReturnStatement(result)] => {
            (&install.expression, result.argument.as_ref()?, true)
        }
        [Statement::ReturnStatement(result)] => {
            let returned = unparenthesized(result.argument.as_ref()?);
            if let Expression::SequenceExpression(sequence) = returned {
                let [installation, invocation] = sequence.expressions.as_slice() else {
                    return None;
                };
                (installation, invocation, true)
            } else {
                let Expression::CallExpression(call) = returned else {
                    return None;
                };
                (&call.callee, returned, false)
            }
        }
        _ => return None,
    };
    let (target, value) = assignment_identifier(installation)?;
    let reference = target.reference_id.get()?;
    if facts.resolved_symbol(scoping, reference) != Some(symbol)
        || !scoping.get_reference(reference).is_write()
    {
        return None;
    }
    let Expression::FunctionExpression(replacement) = unparenthesized(value) else {
        return None;
    };
    let inner_parameters = rotation_proof::simple_parameters(replacement)?;
    let index = *inner_parameters.first()?;
    let Expression::CallExpression(call) = unparenthesized(invocation) else {
        return None;
    };
    if call.optional
        || call.arguments.len() != parameters.len()
        || inner_parameters.len() != parameters.len()
    {
        return None;
    }
    if named_tail && exact_identifier(&call.callee, scoping, facts) != Some(symbol) {
        return None;
    }
    if !call
        .arguments
        .iter()
        .zip(parameters)
        .all(|(argument, &parameter)| {
            argument
                .as_expression()
                .and_then(|expression| exact_identifier(expression, scoping, facts))
                == Some(parameter)
        })
    {
        return None;
    }
    let body = replacement.body.as_ref()?;
    let offset = match body.statements.as_slice() {
        [Statement::ReturnStatement(result)] => adjusted_index_offset(
            table_index(result.argument.as_ref()?, table, scoping, facts)?,
            index,
            scoping,
            facts,
        )?,
        [Statement::ExpressionStatement(adjustment), remaining @ ..] => {
            let offset = adjusted_index_offset(&adjustment.expression, index, scoping, facts)?;
            returned_value(remaining, table, index, scoping, facts)?;
            offset
        }
        _ => return None,
    };
    Some(PlainDecoderShape {
        provider_symbol,
        offset,
        installation: Some(reference),
    })
}

fn plain_decoder_shape(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<PlainDecoderShape> {
    let parameters = rotation_proof::simple_parameters(function)?;
    sequence_decoder_shape(function, scoping, facts)
        .or_else(|| statement_decoder_shape(function, &parameters, scoping, facts))
        .or_else(|| replacement_decoder_shape(function, &parameters, scoping, facts))
}

fn function_info(
    f: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<FnInfo> {
    if f.r#type != oxc_ast::ast::FunctionType::FunctionDeclaration {
        return None;
    }
    let id = f.id.as_ref()?;
    let symbol = id.symbol_id.get()?;
    let params: Vec<_> = f
        .params
        .items
        .iter()
        .filter_map(|parameter| {
            parameter
                .pattern
                .get_binding_identifier()
                .map(|id| id.name.to_string())
        })
        .collect();
    let parameters_proven = !f.r#async
        && !f.generator
        && f.params.rest.is_none()
        && function_parameters_have_no_runtime_effects(f)
        && params.iter().collect::<HashSet<_>>().len() == f.params.items.len();

    Some(FnInfo {
        name: id.name.to_string(),
        symbol,
        scope: scoping.symbol_scope_id(symbol),
        params,
        span: f.span,
        provider: self_rewriting_provider(f, scoping, facts),
        parameters_proven,
        plain_decoder: parameters_proven
            .then(|| plain_decoder_shape(f, scoping, facts))
            .flatten(),
    })
}

struct FunctionDeclarationCollector<'s> {
    scoping: &'s Scoping,
    facts: &'s BindingFacts,
    out: Vec<FnInfo>,
}

impl<'a> Visit<'a> for FunctionDeclarationCollector<'_> {
    fn visit_function(
        &mut self,
        it: &oxc_ast::ast::Function<'a>,
        flags: oxc_syntax::scope::ScopeFlags,
    ) {
        if let Some(info) = function_info(it, self.scoping, self.facts) {
            self.out.push(info);
        }
        walk::walk_function(self, it, flags);
    }
}

fn all_function_declarations(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Vec<FnInfo> {
    let mut collector = FunctionDeclarationCollector {
        scoping,
        facts,
        out: Vec::new(),
    };
    collector.visit_program(program);
    collector.out
}

fn is_base64_alphabet(value: &str) -> bool {
    if value.chars().count() != 65 {
        return false;
    }
    let expected = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="
        .chars()
        .collect::<HashSet<_>>();
    value.chars().collect::<HashSet<_>>() == expected
}

fn eval_from_char_code_concat(
    expression: &Expression<'_>,
    scoping: &Scoping,
    aliases: &HashMap<SymbolId, u32>,
    used_aliases: &mut HashSet<SymbolId>,
) -> Option<String> {
    match expression {
        Expression::StringLiteral(literal) => string_literal_value(literal),
        Expression::TemplateLiteral(template) if template.expressions.is_empty() => {
            template.quasis.first().and_then(template_element_value)
        }
        Expression::ParenthesizedExpression(parenthesized) => {
            eval_from_char_code_concat(&parenthesized.expression, scoping, aliases, used_aliases)
        }
        Expression::BinaryExpression(binary) if binary.operator.as_str() == "+" => {
            let left = eval_from_char_code_concat(&binary.left, scoping, aliases, used_aliases)?;
            let right = eval_from_char_code_concat(&binary.right, scoping, aliases, used_aliases)?;
            Some(format!("{left}{right}"))
        }
        Expression::CallExpression(call) if !call.optional && !call.arguments.is_empty() => {
            let Expression::Identifier(callee) = &call.callee else {
                return None;
            };
            let reference = scoping.get_reference(callee.reference_id.get()?);
            let symbol = reference.symbol_id()?;
            aliases.get(&symbol)?;
            let units = call
                .arguments
                .iter()
                .map(|argument| {
                    let expression = argument.as_expression()?;
                    let number = eval(expression)?.number();
                    Some((js_to_uint32(number) & 0xffff) as u16)
                })
                .collect::<Option<Vec<_>>>()?;
            let value = String::from_utf16(&units).ok()?;
            used_aliases.insert(symbol);
            Some(value)
        }
        _ => None,
    }
}

struct FixedAlphabetProbe<'c> {
    scoping: &'c Scoping,
    aliases: &'c HashMap<SymbolId, u32>,
    candidates: Vec<(String, HashSet<SymbolId>)>,
}

impl FixedAlphabetProbe<'_> {
    fn consider(&mut self, expression: &Expression<'_>) {
        let mut used_aliases = HashSet::new();
        let Some(value) =
            eval_from_char_code_concat(expression, self.scoping, self.aliases, &mut used_aliases)
        else {
            return;
        };
        if is_base64_alphabet(&value) {
            self.candidates.push((value, used_aliases));
        }
    }
}

impl<'a> Visit<'a> for FixedAlphabetProbe<'_> {
    fn visit_function(&mut self, _function: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        // Alphabets assigned inside deferred nested functions do not
        // exist at the point the decoder body executes.
    }

    fn visit_variable_declarator(&mut self, declarator: &oxc_ast::ast::VariableDeclarator<'a>) {
        if let Some(initializer) = &declarator.init {
            self.consider(initializer);
        }
        walk::walk_variable_declarator(self, declarator);
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        self.consider(&assignment.right);
        walk::walk_assignment_expression(self, assignment);
    }
}

fn fixed_alphabet_for_function(
    function: &oxc_ast::ast::Function<'_>,
    symbol: SymbolId,
    scoping: &Scoping,
    aliases: &HashMap<SymbolId, u32>,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Option<String> {
    let body = function.body.as_ref()?;
    let alphabet_body = fixed_decoder_iife_function(body)
        .and_then(|nested| nested.body.as_ref())
        .unwrap_or(body);
    let mut probe = FixedAlphabetProbe {
        scoping,
        aliases,
        candidates: Vec::new(),
    };
    for statement in &alphabet_body.statements {
        probe.visit_statement(statement);
    }
    probe.candidates.sort_by(|left, right| left.0.cmp(&right.0));
    probe.candidates.dedup_by(|left, right| left.0 == right.0);
    let [(alphabet, used_aliases)] = probe.candidates.as_slice() else {
        return None;
    };
    if used_aliases.is_empty() {
        return Some(alphabet.clone());
    }
    let initialized_after = used_aliases
        .iter()
        .filter_map(|alias| aliases.get(alias))
        .copied()
        .max()?;
    let all_uses_after_initialization =
        scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .all(|reference_id| {
                reference_spans
                    .get(reference_id)
                    .is_some_and(|span| span.start >= initialized_after)
            });
    all_uses_after_initialization.then(|| alphabet.clone())
}

fn unparenthesized<'a>(mut expression: &'a Expression<'a>) -> &'a Expression<'a> {
    while let Expression::ParenthesizedExpression(parenthesized) = expression {
        expression = &parenthesized.expression;
    }
    expression
}

fn function_parameters_have_no_runtime_effects(function: &oxc_ast::ast::Function<'_>) -> bool {
    formal_parameters_have_no_runtime_effects(&function.params)
}

fn formal_parameters_have_no_runtime_effects(params: &oxc_ast::ast::FormalParameters<'_>) -> bool {
    params.items.iter().all(|parameter| {
        parameter.initializer.is_none()
            && matches!(parameter.pattern, BindingPattern::BindingIdentifier(_))
    }) && params
        .rest
        .as_ref()
        .is_none_or(|rest| matches!(rest.rest.argument, BindingPattern::BindingIdentifier(_)))
}

/// Scoped IIFE guards must prove the exact table-load/alias pattern.
fn string_literal_via_aliases(
    expression: &Expression<'_>,
    scoping: &Scoping,
    aliases: &HashMap<SymbolId, u32>,
) -> bool {
    let mut used = HashSet::new();
    eval_from_char_code_concat(expression, scoping, aliases, &mut used).as_deref() == Some("string")
}

fn typeof_table_assignment<'a>(
    expression: &'a Expression<'a>,
) -> Option<(&'a str, &'a str, &'a str)> {
    let Expression::UnaryExpression(unary) = unparenthesized(expression) else {
        return None;
    };
    if unary.operator.as_str() != "typeof" {
        return None;
    }
    let Expression::AssignmentExpression(assignment) = unparenthesized(&unary.argument) else {
        return None;
    };
    if assignment.operator.as_str() != "=" {
        return None;
    }
    let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(alias) = &assignment.left else {
        return None;
    };
    let Expression::ComputedMemberExpression(member) = unparenthesized(&assignment.right) else {
        return None;
    };
    let Expression::Identifier(table) = unparenthesized(&member.object) else {
        return None;
    };
    let Expression::Identifier(index) = unparenthesized(&member.expression) else {
        return None;
    };
    Some((
        alias.name.as_str(),
        table.name.as_str(),
        index.name.as_str(),
    ))
}

fn typeof_identifier<'a>(expression: &'a Expression<'a>) -> Option<&'a str> {
    let Expression::UnaryExpression(unary) = unparenthesized(expression) else {
        return None;
    };
    if unary.operator.as_str() != "typeof" {
        return None;
    }
    let Expression::Identifier(identifier) = unparenthesized(&unary.argument) else {
        return None;
    };
    Some(identifier.name.as_str())
}

fn preceding_table_load<'a>(
    body: &'a oxc_ast::ast::FunctionBody<'a>,
    alias: &str,
) -> Option<(&'a str, &'a str)> {
    let [Statement::VariableDeclaration(declaration), Statement::ReturnStatement(_)] =
        body.statements.as_slice()
    else {
        return None;
    };
    let [declarator] = declaration.declarations.as_slice() else {
        return None;
    };
    let BindingPattern::BindingIdentifier(id) = &declarator.id else {
        return None;
    };
    if id.name.as_str() != alias {
        return None;
    }
    let Expression::ComputedMemberExpression(member) = declarator.init.as_ref()? else {
        return None;
    };
    let Expression::Identifier(table) = unparenthesized(&member.object) else {
        return None;
    };
    let Expression::Identifier(index) = unparenthesized(&member.expression) else {
        return None;
    };
    Some((table.name.as_str(), index.name.as_str()))
}

fn fixed_decoder_iife_wrapper_proven(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    aliases: &HashMap<SymbolId, u32>,
) -> bool {
    let Some(body) = function.body.as_ref() else {
        return false;
    };
    let Some(nested) = fixed_decoder_iife_function(body) else {
        return false;
    };
    if !fixed_decoder_iife_calls_proven(nested, scoping, aliases) {
        return false;
    }
    let Some(Statement::ReturnStatement(statement)) = body.statements.last() else {
        return false;
    };
    let Some(Expression::ConditionalExpression(conditional)) = statement.argument.as_ref() else {
        return false;
    };
    let Expression::BinaryExpression(test) = unparenthesized(&conditional.test) else {
        return false;
    };
    if !matches!(test.operator.as_str(), "==" | "===") {
        return false;
    }

    let guard = typeof_table_assignment(&test.left).map_or_else(
        || match typeof_table_assignment(&test.right) {
            Some(parts) => {
                string_literal_via_aliases(&test.left, scoping, aliases).then_some(parts)
            }
            None if string_literal_via_aliases(&test.right, scoping, aliases) => {
                typeof_identifier(&test.left).and_then(|alias| {
                    preceding_table_load(body, alias).map(|(table, index)| (alias, table, index))
                })
            }
            None if string_literal_via_aliases(&test.left, scoping, aliases) => {
                typeof_identifier(&test.right).and_then(|alias| {
                    preceding_table_load(body, alias).map(|(table, index)| (alias, table, index))
                })
            }
            None => None,
        },
        |parts| string_literal_via_aliases(&test.right, scoping, aliases).then_some(parts),
    );
    let Some((alias, _table, index)) = guard else {
        return false;
    };
    if function
        .params
        .items
        .first()
        .and_then(|param| match &param.pattern {
            BindingPattern::BindingIdentifier(id) => Some(id.name.as_str()),
            _ => None,
        })
        != Some(index)
    {
        return false;
    }

    let Expression::CallExpression(call) = unparenthesized(&conditional.consequent) else {
        return false;
    };
    let Some(called_nested) = rotation_iife_function(&call.callee) else {
        return false;
    };
    if !std::ptr::eq(called_nested, nested)
        || call.arguments.len() != 1
        || call.arguments[0]
            .as_expression()
            .and_then(|argument| match unparenthesized(argument) {
                Expression::Identifier(id) => Some(id.name.as_str()),
                _ => None,
            })
            != Some(alias)
    {
        return false;
    }
    matches!(
        unparenthesized(&conditional.alternate),
        Expression::Identifier(id) if id.name.as_str() == alias
    )
}

fn indexed_table_symbol(
    expression: &Expression<'_>,
    index_symbol: SymbolId,
    scoping: &Scoping,
) -> Option<SymbolId> {
    let Expression::ComputedMemberExpression(member) = unparenthesized(expression) else {
        return None;
    };
    if member.optional {
        return None;
    }
    let Expression::Identifier(table) = unparenthesized(&member.object) else {
        return None;
    };
    let Expression::Identifier(index) = unparenthesized(&member.expression) else {
        return None;
    };
    if statically_resolved_symbol(scoping, index.reference_id.get()?) != Some(index_symbol) {
        return None;
    }
    statically_resolved_symbol(scoping, table.reference_id.get()?)
}

fn unresolved_global_call_argument<'a>(
    expression: &'a Expression<'a>,
    name: &str,
    scoping: &Scoping,
) -> Option<&'a Expression<'a>> {
    let Expression::CallExpression(call) = unparenthesized(expression) else {
        return None;
    };
    if call.optional || call.arguments.len() != 1 || call.arguments[0].is_spread() {
        return None;
    }
    let Expression::Identifier(callee) = unparenthesized(&call.callee) else {
        return None;
    };
    if callee.name.as_str() != name
        || !statically_unresolved_global_reference(scoping, callee.reference_id.get()?)
    {
        return None;
    }
    call.arguments[0].as_expression().map(unparenthesized)
}

fn expression_resolves_to_symbol(
    expression: &Expression<'_>,
    symbol: SymbolId,
    scoping: &Scoping,
) -> bool {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return false;
    };
    identifier
        .reference_id
        .get()
        .and_then(|reference_id| statically_resolved_symbol(scoping, reference_id))
        == Some(symbol)
}

fn standard_base64_table_for_function(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
) -> Option<SymbolId> {
    if function.r#async
        || function.generator
        || !function_parameters_have_no_runtime_effects(function)
    {
        return None;
    }
    let body = function.body.as_ref()?;
    let first_param = function.params.items.first()?;
    let BindingPattern::BindingIdentifier(first_param) = &first_param.pattern else {
        return None;
    };
    let index_symbol = first_param.symbol_id.get()?;
    let parameter_symbols = function
        .params
        .items
        .iter()
        .filter_map(|parameter| parameter.pattern.get_binding_identifier()?.symbol_id.get())
        .collect::<HashSet<_>>();

    let local_assignment = |expression: &Expression<'_>| -> Option<(SymbolId, SymbolId)> {
        let (target, value) = assignment_identifier(expression)?;
        let target_symbol = statically_resolved_symbol(scoping, target.reference_id.get()?)?;
        if !parameter_symbols.contains(&target_symbol) {
            return None;
        }
        Some((
            target_symbol,
            indexed_table_symbol(value, index_symbol, scoping)?,
        ))
    };

    let atob_of_symbol = |expression: &Expression<'_>, symbol: SymbolId| -> bool {
        unresolved_global_call_argument(expression, "atob", scoping)
            .is_some_and(|argument| expression_resolves_to_symbol(argument, symbol, scoping))
    };

    match body.statements.as_slice() {
        [Statement::ReturnStatement(ret)] => {
            let argument = ret.argument.as_ref()?;
            if let Some(table) = unresolved_global_call_argument(argument, "atob", scoping)
                .and_then(|argument| indexed_table_symbol(argument, index_symbol, scoping))
            {
                return Some(table);
            }
            let Expression::SequenceExpression(sequence) = unparenthesized(argument) else {
                return None;
            };
            let [assignment, decode] = sequence.expressions.as_slice() else {
                return None;
            };
            let (alias, table) = local_assignment(assignment)?;
            atob_of_symbol(decode, alias).then_some(table)
        }
        [Statement::ExpressionStatement(load), Statement::ReturnStatement(ret)] => {
            let (alias, table) = local_assignment(&load.expression)?;
            atob_of_symbol(ret.argument.as_ref()?, alias).then_some(table)
        }
        [Statement::VariableDeclaration(declaration), Statement::ReturnStatement(ret)] => {
            let [declarator] = declaration.declarations.as_slice() else {
                return None;
            };
            let BindingPattern::BindingIdentifier(alias) = &declarator.id else {
                return None;
            };
            let alias_symbol = alias.symbol_id.get()?;
            let table = indexed_table_symbol(declarator.init.as_ref()?, index_symbol, scoping)?;
            atob_of_symbol(ret.argument.as_ref()?, alias_symbol).then_some(table)
        }
        _ => None,
    }
}

fn indexed_table_symbols_for_function(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
) -> Vec<SymbolId> {
    struct Probe<'c> {
        scoping: &'c Scoping,
        index_symbol: SymbolId,
        tables: Vec<SymbolId>,
    }
    impl<'a> Visit<'a> for Probe<'_> {
        fn visit_function(&mut self, _function: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {
            // Reads inside nested functions do not execute as part of this decoder
            // invocation and must not contaminate the candidate table set.
        }

        fn visit_arrow_function_expression(
            &mut self,
            _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
        ) {
            // Same boundary as nested function expressions/declarations above.
        }

        fn visit_computed_member_expression(
            &mut self,
            member: &oxc_ast::ast::ComputedMemberExpression<'a>,
        ) {
            if !member.optional {
                if let Expression::Identifier(index) = unparenthesized(&member.expression) {
                    if index.reference_id.get().is_some_and(|reference_id| {
                        statically_resolved_symbol(self.scoping, reference_id)
                            == Some(self.index_symbol)
                    }) {
                        if let Expression::Identifier(table) = unparenthesized(&member.object) {
                            if let Some(reference_id) = table.reference_id.get() {
                                if let Some(symbol) =
                                    statically_resolved_symbol(self.scoping, reference_id)
                                {
                                    self.tables.push(symbol);
                                }
                            }
                        }
                    }
                }
            }
            walk::walk_computed_member_expression(self, member);
        }
    }

    let Some(first_param) = function.params.items.first() else {
        return Vec::new();
    };
    let BindingPattern::BindingIdentifier(first_param) = &first_param.pattern else {
        return Vec::new();
    };
    let Some(index_symbol) = first_param.symbol_id.get() else {
        return Vec::new();
    };
    let Some(body) = function.body.as_ref() else {
        return Vec::new();
    };

    let mut probe = Probe {
        scoping,
        index_symbol,
        tables: Vec::new(),
    };
    probe.visit_function_body(body);
    probe.tables.sort();
    probe.tables.dedup();
    probe.tables
}

#[derive(Debug)]
struct DirectFnInfo {
    symbol: SymbolId,
    span: Span,
    indexed_table_symbols: Vec<SymbolId>,
    standard_base64_table: Option<SymbolId>,
    fixed_base64_alphabet: Option<String>,
    fixed_base64_algorithm_proven: bool,
}

struct DirectFnInfoCollector<'c> {
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    aliases: &'c HashMap<SymbolId, u32>,
    reference_spans: &'c HashMap<ReferenceId, Span>,
    out: Vec<DirectFnInfo>,
}

struct ExactBodyReferences<'c> {
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    valid: bool,
}

impl<'a> Visit<'a> for ExactBodyReferences<'_> {
    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        self.valid &= identifier.reference_id.get().is_some_and(|reference| {
            self.facts.resolve_reference(self.scoping, reference) != ReferenceIdentity::Dynamic
        });
    }
}

impl<'a> Visit<'a> for DirectFnInfoCollector<'_> {
    fn visit_function(&mut self, f: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if let Some(symbol) = f.id.as_ref().and_then(|id| id.symbol_id.get()) {
            if self.facts.binding_has_stable_value(self.scoping, symbol)
                && !f.r#async
                && !f.generator
                && function_parameters_have_no_runtime_effects(f)
            {
                let parameters = f
                    .params
                    .items
                    .iter()
                    .filter_map(|parameter| {
                        parameter.pattern.get_binding_identifier()?.symbol_id.get()
                    })
                    .collect::<HashSet<_>>();
                if parameters.len() == f.params.items.len() {
                    let standard_base64_table = standard_base64_table_for_function(f, self.scoping);
                    let fixed_base64_alphabet = fixed_alphabet_for_function(
                        f,
                        symbol,
                        self.scoping,
                        self.aliases,
                        self.reference_spans,
                    );
                    let fixed_base64_algorithm_proven =
                        fixed_base64_alphabet.as_deref().is_some_and(|alphabet| {
                            fixed_base64_algorithm_proven(
                                f,
                                self.scoping,
                                self.aliases,
                                self.reference_spans,
                                alphabet,
                            )
                        });
                    if standard_base64_table.is_some() || fixed_base64_algorithm_proven {
                        let mut probe = ExactBodyReferences {
                            scoping: self.scoping,
                            facts: self.facts,
                            valid: true,
                        };
                        probe.visit_function(f, flags);
                        if probe.valid {
                            self.out.push(DirectFnInfo {
                                symbol,
                                span: f.span,
                                indexed_table_symbols: indexed_table_symbols_for_function(
                                    f,
                                    self.scoping,
                                ),
                                standard_base64_table,
                                fixed_base64_alphabet,
                                fixed_base64_algorithm_proven,
                            });
                        }
                    }
                }
            }
        }
        walk::walk_function(self, f, flags);
    }
}

fn all_functions(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
    aliases: &HashMap<SymbolId, u32>,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Vec<DirectFnInfo> {
    let mut collector = DirectFnInfoCollector {
        scoping,
        facts,
        aliases,
        reference_spans,
        out: Vec::new(),
    };
    collector.visit_program(program);
    collector.out
}

#[derive(Debug)]
struct FixedDirectDecoder {
    symbol: SymbolId,
    span: Span,
    table: SymbolId,
    table_reference: ReferenceId,
    offset: i64,
}

fn fixed_direct_decoder(
    symbol: SymbolId,
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<FixedDirectDecoder> {
    let parameters = rotation_proof::simple_parameters(function)?;
    let index = *parameters.first()?;
    let [Statement::ExpressionStatement(adjust), Statement::VariableDeclaration(declaration), Statement::ReturnStatement(result)] =
        function.body.as_ref()?.statements.as_slice()
    else {
        return None;
    };
    let offset = adjusted_index_offset(&adjust.expression, index, scoping, facts)?;
    if !rotation_proof::ordinary_declaration(declaration) {
        return None;
    }
    let [declarator] = declaration.declarations.as_slice() else {
        return None;
    };
    let value = declarator.id.get_binding_identifier()?.symbol_id.get()?;
    if parameters.contains(&value) || !scoping.symbol_redeclarations(value).is_empty() {
        return None;
    }
    let Expression::ComputedMemberExpression(member) = unparenthesized(declarator.init.as_ref()?)
    else {
        return None;
    };
    if member.optional
        || exact_identifier(&member.expression, scoping, facts) != Some(index)
        || exact_identifier(result.argument.as_ref()?, scoping, facts) != Some(value)
    {
        return None;
    }
    let Expression::Identifier(table) = unparenthesized(&member.object) else {
        return None;
    };
    let table_reference = table.reference_id.get()?;
    let table = facts.resolved_symbol(scoping, table_reference)?;
    if parameters.contains(&table) || table == value || table == symbol {
        return None;
    }
    Some(FixedDirectDecoder {
        symbol,
        span: function.span,
        table,
        table_reference,
        offset,
    })
}

struct FixedDirectDecoderCollector<'c> {
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    out: Vec<FixedDirectDecoder>,
}

impl<'a> Visit<'a> for FixedDirectDecoderCollector<'_> {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        if rotation_proof::ordinary_declaration(it) {
            for declaration in &it.declarations {
                if let (Some(symbol), Some(Expression::FunctionExpression(function))) = (
                    declaration
                        .id
                        .get_binding_identifier()
                        .and_then(|id| id.symbol_id.get()),
                    declaration.init.as_ref(),
                ) {
                    if let Some(proof) =
                        fixed_direct_decoder(symbol, function, self.scoping, self.facts)
                    {
                        self.out.push(proof);
                    }
                }
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn fixed_direct_decoders(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Vec<FixedDirectDecoder> {
    let mut collector = FixedDirectDecoderCollector {
        scoping,
        facts,
        out: Vec::new(),
    };
    collector.visit_program(program);
    collector.out
}

#[derive(Debug, Clone)]
enum DecoderTransform {
    Plain,
    LowerAlphabetBase64Uri,
    LowerAlphabetBase64Rc4,
    StandardBase64,
    FixedBase64Alphabet(String),
}

#[derive(Debug, Clone)]
pub struct Decoder {
    values: Rc<[Value]>,
    proven_alias_reads: Option<Rc<HashSet<ReferenceId>>>,
    offset: i64,
    provider: SymbolId,
    provider_array_span: Span,
    transform: DecoderTransform,
}

impl DecoderTransform {
    fn transform_value(&self, value: Value, key: Option<&str>) -> Option<Value> {
        match (self, value) {
            (Self::LowerAlphabetBase64Uri, Value::String(encoded)) => {
                decode_lower_alphabet_base64_uri(&encoded).map(Value::String)
            }
            (Self::LowerAlphabetBase64Rc4, Value::String(encoded)) => {
                decode_lower_alphabet_base64_rc4(&encoded, key?).map(Value::String)
            }
            (Self::StandardBase64, Value::String(encoded)) => {
                decode_standard_base64_latin1(&encoded).map(Value::String)
            }
            (Self::FixedBase64Alphabet(alphabet), Value::String(encoded)) => {
                decode_fixed_base64_latin1(&encoded, alphabet).map(Value::String)
            }
            (
                Self::LowerAlphabetBase64Uri | Self::LowerAlphabetBase64Rc4 | Self::StandardBase64,
                _,
            ) => None,
            (Self::Plain | Self::FixedBase64Alphabet(_), value) => Some(value),
        }
    }
}

impl Decoder {
    fn permits_read(&self, reference: ReferenceId) -> bool {
        self.proven_alias_reads
            .as_ref()
            .is_none_or(|reads| reads.contains(&reference))
    }

    fn value_for_raw_rotated_with_key(
        &self,
        raw: f64,
        rotation: usize,
        key: Option<&str>,
    ) -> Option<Value> {
        // Both operands inhabit the ECMAScript Number domain before the
        // subtraction. Only an exact nonnegative integral result indexes
        // this dense table; fractional, NaN and infinite keys are unknown.
        let index = exact_usize(raw - js_number_from_i64(self.offset))?;
        // Array indexing never wraps. Rotation only maps an already-valid
        // logical table index onto the physically rotated backing array.
        if index >= self.values.len() {
            return None;
        }
        let index = index.checked_add(rotation)? % self.values.len();
        self.transform
            .transform_value(self.values.get(index)?.clone(), key)
    }

    pub(super) fn value_for_call(&self, raw: f64, key: Option<&str>) -> Option<Value> {
        self.value_for_raw_rotated_with_key(raw, 0, key)
    }
}

pub struct DecoderCallRewrite {
    pub(super) text: String,
    pub(super) stop: bool,
}

pub fn decoder_call_rewrite(
    source: &str,
    scoping: &Scoping,
    facts: &BindingFacts,
    decoders: &HashMap<SymbolId, Decoder>,
    call: &CallExpression<'_>,
) -> Option<DecoderCallRewrite> {
    if call.optional
        || !(1..=2).contains(&call.arguments.len())
        || call.arguments.iter().any(Argument::is_spread)
    {
        return None;
    }
    let callee = call.callee.without_parentheses();
    let Expression::Identifier(identifier) = callee else {
        return None;
    };
    let reference = identifier.reference_id.get()?;
    let symbol = facts.stable_callable_symbol(scoping, callee)?;
    let decoder = decoders.get(&symbol)?;
    if !decoder.permits_read(reference) {
        return None;
    }
    let key = match call.arguments.get(1) {
        Some(Argument::StringLiteral(literal)) => Some(string_literal_value(literal)?),
        Some(_) => return None,
        None => None,
    };
    let argument = call.arguments.first()?;
    let primitive_number =
        |expression: &Expression<'_>| eval(expression).map(|value| value.number());
    if let Some(raw) = argument.as_expression().and_then(primitive_number) {
        return literal_decoder_rewrite(&decoder.value_for_call(raw, key.as_deref())?);
    }
    conditional_decoder_rewrite(source, argument, |expression| {
        decoder.value_for_call(primitive_number(expression)?, key.as_deref())
    })
}

fn literal_decoder_rewrite(value: &Value) -> Option<DecoderCallRewrite> {
    Some(DecoderCallRewrite {
        text: value.render_expression()?,
        stop: false,
    })
}

fn conditional_decoder_rewrite(
    source: &str,
    argument: &Argument<'_>,
    value: impl Fn(&Expression<'_>) -> Option<Value>,
) -> Option<DecoderCallRewrite> {
    let Expression::ConditionalExpression(conditional) =
        argument.as_expression()?.without_parentheses()
    else {
        return None;
    };
    let consequent = value(&conditional.consequent)?.render()?;
    let alternate = value(&conditional.alternate)?.render()?;
    let test = fragment(source, conditional.test.span());
    Some(DecoderCallRewrite {
        text: format!("(({test}) ? ({consequent}) : ({alternate}))"),
        stop: true,
    })
}

struct DecoderOnlyCallCollector<'c> {
    source: &'c str,
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    decoders: &'c HashMap<SymbolId, Decoder>,
    protected_spans: &'c [(usize, usize)],
    replacements: Vec<Replacement>,
}

impl DecoderOnlyCallCollector<'_> {
    fn protected(&self, span: Span) -> bool {
        let start = span.start as usize;
        let end = span.end as usize;
        self.protected_spans
            .iter()
            .any(|(protected_start, protected_end)| {
                start < *protected_end && *protected_start < end
            })
    }
}

impl<'a> Visit<'a> for DecoderOnlyCallCollector<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        let Some(rewrite) =
            decoder_call_rewrite(self.source, self.scoping, self.facts, self.decoders, call)
        else {
            walk::walk_call_expression(self, call);
            return;
        };
        if self.protected(call.span) {
            return;
        }
        self.replacements.push(Replacement {
            start: call.span.start as usize,
            end: call.span.end as usize,
            text: rewrite.text,
            kind: "string_array_decode",
            arithmetic_state_proof: None,
        });
    }
}

pub struct StaticDecoderPass {
    pub(super) replacements: Vec<Replacement>,
    pub(super) decoder_count: usize,
}

pub fn static_decoder_pass(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
    budget: &WorkBudget,
) -> Result<StaticDecoderPass, BudgetExceeded> {
    let facts = BindingFacts::analyze(program, scoping);
    let analysis = analyze_decoders(source, program, scoping, &facts, reference_spans, budget)?;
    let decoder_count = analysis.decoder_count;
    let mut collector = DecoderOnlyCallCollector {
        source,
        scoping,
        facts: &facts,
        decoders: &analysis.decoders,
        protected_spans: &analysis.protected_spans,
        replacements: analysis.replacements,
    };
    collector.visit_program(program);
    Ok(StaticDecoderPass {
        replacements: collector.replacements,
        decoder_count,
    })
}

fn compile_regex(pattern: &str) -> Option<regex::Regex> {
    regex::Regex::new(pattern).ok()
}

static RC4_CHAR_CODE_AT_RE: LazyLock<Option<regex::Regex>> = LazyLock::new(|| {
    compile_regex(r"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*\.\s*charCodeAt\s*\(([^)]*)\)")
});
fn function_has_external_write(
    span: Span,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> bool {
    for symbol in scoping.symbol_ids() {
        let declaration = scoping.symbol_span(symbol);
        if span.start <= declaration.start && declaration.end <= span.end {
            continue;
        }
        for reference_id in scoping.get_resolved_reference_ids(symbol) {
            let Some(reference_span) = reference_spans.get(reference_id) else {
                continue;
            };
            if span.start <= reference_span.start && reference_span.end <= span.end {
                let reference = scoping.get_reference(*reference_id);
                if reference.is_write() || reference.flags().is_member_write_target() {
                    return true;
                }
            }
        }
    }

    for reference_ids in scoping.root_unresolved_references_ids() {
        for reference_id in reference_ids {
            let Some(reference_span) = reference_spans.get(&reference_id) else {
                continue;
            };
            if span.start <= reference_span.start && reference_span.end <= span.end {
                let reference = scoping.get_reference(reference_id);
                if reference.is_write() || reference.flags().is_member_write_target() {
                    return true;
                }
            }
        }
    }
    false
}

#[derive(Debug)]
struct DirectTableDecoder {
    table: SymbolId,
    table_read_initialized: bool,
    values: Vec<Option<Value>>,
    transform: DecoderTransform,
}

impl DirectTableDecoder {
    fn value(&self, expression: &Expression<'_>) -> Option<Value> {
        let key = exact_computed_property_key(expression, eval)?;
        let index = usize::try_from(canonical_array_index_key(&key)?).ok()?;
        self.transform
            .transform_value(self.values.get(index)?.clone()?, None)
    }

    fn rewrite(&self, source: &str, call: &CallExpression<'_>) -> Option<DecoderCallRewrite> {
        if call.optional
            || !(1..=2).contains(&call.arguments.len())
            || call.arguments.iter().any(Argument::is_spread)
            || call
                .arguments
                .get(1)
                .is_some_and(|argument| !matches!(argument, Argument::StringLiteral(_)))
        {
            return None;
        }
        let argument = call.arguments.first()?;
        if let Some(value) = self.value(argument.as_expression()?) {
            return literal_decoder_rewrite(&value);
        }
        conditional_decoder_rewrite(source, argument, |expression| self.value(expression))
    }
}

fn direct_table_transform(
    function: &DirectFnInfo,
    table_symbol: SymbolId,
) -> Option<DecoderTransform> {
    if function.standard_base64_table == Some(table_symbol) {
        Some(DecoderTransform::StandardBase64)
    } else if function.fixed_base64_algorithm_proven {
        Some(DecoderTransform::FixedBase64Alphabet(
            function.fixed_base64_alphabet.clone()?,
        ))
    } else {
        None
    }
}

fn detect_direct_table_decoders(
    program: &oxc_ast::ast::Program<'_>,
    functions: &[DirectFnInfo],
    existing: &HashMap<SymbolId, Decoder>,
    scoping: &Scoping,
    facts: &BindingFacts,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<SymbolId, DirectTableDecoder> {
    let arrays = partial_decoder_arrays(program, scoping);
    let arrays = arrays
        .iter()
        .map(|array| (array.symbol, array))
        .collect::<HashMap<_, _>>();
    let mut out = HashMap::new();
    for function in functions {
        if existing.contains_key(&function.symbol)
            || function_has_external_write(function.span, scoping, reference_spans)
        {
            continue;
        }
        let candidate_symbols = function.standard_base64_table.as_ref().map_or(
            function.indexed_table_symbols.as_slice(),
            std::slice::from_ref,
        );
        let mut candidates = candidate_symbols.iter().filter_map(|symbol| {
            let array = arrays.get(symbol)?;
            if !facts.source_local_data_binding(scoping, *symbol) {
                return None;
            }
            let [reference] = scoping.get_resolved_reference_ids(*symbol) else {
                return None;
            };
            let reference_flags = scoping.get_reference(*reference);
            let span = reference_spans.get(reference)?;
            if !reference_flags.is_read()
                || reference_flags.is_write()
                || reference_flags.flags().is_member_write_target()
                || facts.resolved_symbol(scoping, *reference) != Some(*symbol)
                || function.span.start > span.start
                || span.end > function.span.end
            {
                return None;
            }
            let transform = direct_table_transform(function, *symbol)?;
            Some(DirectTableDecoder {
                table: *symbol,
                table_read_initialized: facts.initialized_reference(scoping, *reference, *span)
                    == Some(*symbol),
                values: array.values.clone(),
                transform,
            })
        });
        let Some(candidate) = candidates.next() else {
            continue;
        };
        if candidates.next().is_none() {
            out.insert(function.symbol, candidate);
        }
    }
    out
}

struct DirectTableCallCollector<'c> {
    source: &'c str,
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    decoders: &'c HashMap<SymbolId, DirectTableDecoder>,
    budget: &'c WorkBudget,
    failure: Option<BudgetExceeded>,
    replacements: Vec<Replacement>,
}

impl DirectTableCallCollector<'_> {
    fn rewrite(
        &self,
        call: &CallExpression<'_>,
    ) -> Result<Option<DecoderCallRewrite>, BudgetExceeded> {
        let Expression::Identifier(callee) = call.callee.without_parentheses() else {
            return Ok(None);
        };
        let Some(reference) = callee.reference_id.get() else {
            return Ok(None);
        };
        let Some(symbol) = self.facts.resolved_symbol(self.scoping, reference) else {
            return Ok(None);
        };
        let Some(decoder) = self.decoders.get(&symbol) else {
            return Ok(None);
        };
        let Some(rewrite) = decoder.rewrite(self.source, call) else {
            return Ok(None);
        };
        if !decoder.table_read_initialized
            && !self.facts.proves_initialized_through_calls(
                self.scoping,
                decoder.table,
                self.scoping.get_reference(reference).scope_id(),
                call.span,
                self.budget,
            )?
        {
            return Ok(None);
        }
        Ok(Some(rewrite))
    }
}

impl<'a> Visit<'a> for DirectTableCallCollector<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if self.failure.is_some() {
            return;
        }
        match self.rewrite(call) {
            Ok(Some(rewrite)) => self.replacements.push(Replacement {
                start: call.span.start as usize,
                end: call.span.end as usize,
                text: rewrite.text,
                kind: "string_array_decode",
                arithmetic_state_proof: None,
            }),
            Ok(None) => walk::walk_call_expression(self, call),
            Err(failure) => self.failure = Some(failure),
        }
    }
}

fn parse_i64_literal(text: &str) -> Option<i64> {
    let text = text.trim();
    let (negative, text) = text.strip_prefix('-').map_or_else(
        || (false, text.strip_prefix('+').unwrap_or(text)),
        |rest| (true, rest),
    );
    let value = if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        i64::from_str_radix(hex, 16).ok()?
    } else {
        text.parse::<i64>().ok()?
    };
    Some(if negative { -value } else { value })
}

/// ECMAScript parseInt with a known radix. Zero selects the standard
/// inferred radix; explicit hexadecimal also consumes an optional prefix.
/// NaN is a proved result, whereas arithmetic beyond the representable
/// integer accumulator is deliberately unknown.
pub fn js_parse_int(text: &str, mut radix: u32) -> Option<f64> {
    let text = text.trim_start_matches(|ch: char| {
        matches!(ch,
        '\u{0009}'..='\u{000d}' | '\u{0020}' | '\u{00a0}' | '\u{1680}' |
        '\u{2000}'..='\u{200a}' | '\u{2028}' | '\u{2029}' | '\u{202f}' |
        '\u{205f}' | '\u{3000}' | '\u{feff}')
    });
    let (negative, text) = text.strip_prefix('-').map_or_else(
        || (false, text.strip_prefix('+').unwrap_or(text)),
        |rest| (true, rest),
    );
    let inferred = radix == 0;
    if inferred {
        radix = 10;
    }
    if !(2..=36).contains(&radix) {
        return Some(f64::NAN);
    }
    let hexadecimal = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X"));
    let text = if inferred || radix == 16 {
        if let Some(rest) = hexadecimal {
            radix = 16;
            rest
        } else {
            text
        }
    } else {
        text
    };
    let mut value = 0u64;
    let mut digits = 0usize;
    for ch in text.chars() {
        let Some(digit) = ch.to_digit(radix) else {
            break;
        };
        value = value
            .checked_mul(u64::from(radix))?
            .checked_add(u64::from(digit))?;
        digits += 1;
    }
    if digits == 0 {
        return Some(f64::NAN);
    }
    let value = js_number_from_u64(value);
    Some(if negative { -value } else { value })
}

#[derive(Debug, Clone)]
enum RotationOperation {
    Checksum(ChecksumExpression),
    FixedCount,
}

#[derive(Debug, Clone)]
struct RotationIife {
    provider: SymbolId,
    provider_reference: ReferenceId,
    target: i64,
    operation: Option<RotationOperation>,
    statement_span: Span,
    call_span: Span,
    execution: Option<RotationExecution>,
}

fn rotation_iife_function<'a>(expr: &'a Expression<'a>) -> Option<&'a oxc_ast::ast::Function<'a>> {
    match expr {
        Expression::FunctionExpression(function) => Some(function),
        Expression::ParenthesizedExpression(parenthesized) => {
            rotation_iife_function(&parenthesized.expression)
        }
        _ => None,
    }
}

fn rotation_iife_call<'a>(expr: &'a Expression<'a>) -> Option<&'a CallExpression<'a>> {
    match expr {
        Expression::CallExpression(call) => Some(call),
        Expression::ParenthesizedExpression(parenthesized) => {
            rotation_iife_call(&parenthesized.expression)
        }
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "!" => {
            rotation_iife_call(&unary.argument)
        }
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
struct RotationExecution {
    owner: ScopeId,
    after: Span,
}

/// Collect calls that execute once on the normal-completion path of a
/// statement. In particular, do not descend into short-circuited arms,
/// deferred function bodies, or repeating loop tests and updates.
fn guaranteed_expression_calls(expression: &Expression<'_>, visit: &mut impl FnMut(Span)) {
    match unparenthesized(expression) {
        Expression::CallExpression(call) if !call.optional => {
            guaranteed_expression_calls(&call.callee, visit);
            for argument in &call.arguments {
                if let Some(value) = argument.as_expression() {
                    guaranteed_expression_calls(value, visit);
                }
            }
            if rotation_iife_function(&call.callee).is_some() {
                visit(call.span);
            }
        }
        Expression::SequenceExpression(sequence) => {
            for expression in &sequence.expressions {
                guaranteed_expression_calls(expression, visit);
            }
        }
        Expression::UnaryExpression(unary) => guaranteed_expression_calls(&unary.argument, visit),
        Expression::BinaryExpression(binary) => {
            guaranteed_expression_calls(&binary.left, visit);
            guaranteed_expression_calls(&binary.right, visit);
        }
        Expression::LogicalExpression(logical) => guaranteed_expression_calls(&logical.left, visit),
        Expression::ConditionalExpression(conditional) => {
            guaranteed_expression_calls(&conditional.test, visit)
        }
        Expression::AssignmentExpression(assignment) if !assignment.operator.is_logical() => {
            guaranteed_expression_calls(&assignment.right, visit);
        }
        _ => {}
    }
}

#[derive(Default)]
struct RotationStatementSpanCollector {
    scopes: Vec<Option<ScopeId>>,
    spans: HashMap<(u32, u32), Span>,
    executions: HashMap<(u32, u32), RotationExecution>,
}

impl<'a> Visit<'a> for RotationStatementSpanCollector {
    fn enter_scope(&mut self, _: ScopeFlags, scope: &std::cell::Cell<Option<ScopeId>>) {
        self.scopes.push(scope.get());
    }

    fn leave_scope(&mut self) {
        self.scopes.pop();
    }

    fn visit_statements(&mut self, statements: &oxc_allocator::Vec<'a, Statement<'a>>) {
        if let (Some(Some(owner)), Some(last)) = (self.scopes.last(), statements.last()) {
            let owner = *owner;
            let end = last.span().end;
            for statement in statements {
                let span = statement.span();
                let mut record = |call: Span| {
                    self.executions.insert(
                        (call.start, call.end),
                        RotationExecution {
                            owner,
                            after: Span::new(call.end, end),
                        },
                    );
                };
                match statement {
                    Statement::ExpressionStatement(expression) => {
                        guaranteed_expression_calls(&expression.expression, &mut record);
                        if let Some(call) = rotation_iife_call(&expression.expression) {
                            self.spans.insert((call.span.start, call.span.end), span);
                        }
                    }
                    Statement::VariableDeclaration(declaration) => {
                        for declarator in &declaration.declarations {
                            if let Some(init) = &declarator.init {
                                guaranteed_expression_calls(init, &mut record);
                            }
                        }
                    }
                    Statement::ForStatement(statement) => {
                        if let Some(init) = &statement.init {
                            if let Some(expression) = init.as_expression() {
                                guaranteed_expression_calls(expression, &mut record);
                            } else if let oxc_ast::ast::ForStatementInit::VariableDeclaration(
                                declaration,
                            ) = init
                            {
                                for declarator in &declaration.declarations {
                                    if let Some(value) = &declarator.init {
                                        guaranteed_expression_calls(value, &mut record);
                                    }
                                }
                            }
                        }
                    }
                    Statement::IfStatement(statement) => {
                        guaranteed_expression_calls(&statement.test, &mut record)
                    }
                    Statement::SwitchStatement(statement) => {
                        guaranteed_expression_calls(&statement.discriminant, &mut record)
                    }
                    _ => {}
                }
            }
        }
        walk::walk_statements(self, statements);
    }
}

fn numeric_object_values(
    object: &oxc_ast::ast::ObjectExpression<'_>,
) -> Option<HashMap<String, i64>> {
    let mut values = HashMap::new();
    for item in &object.properties {
        let oxc_ast::ast::ObjectPropertyKind::ObjectProperty(property) = item else {
            return None;
        };
        if property.kind != oxc_ast::ast::PropertyKind::Init
            || property.computed
            || property.method
            || property.shorthand
        {
            return None;
        }
        let key = literal_property_key(&property.key)?;
        // In an object initializer, a non-computed `__proto__` key mutates the
        // object's prototype rather than defining an ordinary own property.
        if key == "__proto__" {
            return None;
        }
        let value = expression_integer(&property.value)?;
        values.insert(key, value);
    }
    (!values.is_empty()).then_some(values)
}

struct RotationIifeCollector<'c, 's> {
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    statement_spans: &'s RotationStatementSpanCollector,
    out: Vec<RotationIife>,
}

impl<'a> Visit<'a> for RotationIifeCollector<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional && call.arguments.is_empty() {
            if let Some(function) = rotation_iife_function(&call.callee) {
                if let Some(proof) =
                    prove_checksum_rotation(function, None, self.scoping, self.facts)
                {
                    self.out.push(RotationIife {
                        provider: proof.provider,
                        provider_reference: proof.provider_reference,
                        target: proof.target,
                        operation: Some(RotationOperation::Checksum(proof.checksum)),
                        statement_span: self
                            .statement_spans
                            .spans
                            .get(&(call.span.start, call.span.end))
                            .copied()
                            .unwrap_or(call.span),
                        call_span: call.span,
                        execution: self
                            .statement_spans
                            .executions
                            .get(&(call.span.start, call.span.end))
                            .copied(),
                    });
                }
            }
        }
        if !call.optional && call.arguments.len() == 2 {
            let provider = match &call.arguments[0] {
                Argument::Identifier(identifier) => Some(identifier),
                _ => None,
            };
            let target = argument_integer(&call.arguments[1]);
            let function = rotation_iife_function(&call.callee);
            if let (Some(provider), Some(target), Some(function)) = (provider, target, function) {
                if let Some(provider_reference) = provider.reference_id.get() {
                    let Some(provider_symbol) =
                        self.scoping.get_reference(provider_reference).symbol_id()
                    else {
                        walk::walk_call_expression(self, call);
                        return;
                    };
                    let operation = if self.facts.resolved_symbol(self.scoping, provider_reference)
                        == Some(provider_symbol)
                    {
                        if let Some(proof) = prove_checksum_rotation(
                            function,
                            Some(target),
                            self.scoping,
                            self.facts,
                        ) {
                            Some(RotationOperation::Checksum(proof.checksum))
                        } else if prove_fixed_rotation(function, target, self.scoping, self.facts)
                            .is_some()
                        {
                            Some(RotationOperation::FixedCount)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    let standalone_statement = self
                        .statement_spans
                        .spans
                        .get(&(call.span.start, call.span.end))
                        .copied();
                    self.out.push(RotationIife {
                        provider: provider_symbol,
                        provider_reference,
                        target,
                        operation,
                        statement_span: standalone_statement.unwrap_or(call.span),
                        call_span: call.span,
                        execution: self
                            .statement_spans
                            .executions
                            .get(&(call.span.start, call.span.end))
                            .copied(),
                    });
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

fn collect_rotation_iifes(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Vec<RotationIife> {
    let mut statement_spans = RotationStatementSpanCollector::default();
    statement_spans.visit_program(program);
    let mut collector = RotationIifeCollector {
        scoping,
        facts,
        statement_spans: &statement_spans,
        out: Vec::new(),
    };
    collector.visit_program(program);
    collector.out
}

fn fixed_count_rotation(iife: &RotationIife, table_len: usize) -> Option<usize> {
    if !matches!(iife.operation, Some(RotationOperation::FixedCount)) || table_len == 0 {
        return None;
    }
    usize::try_from(iife.target)
        .ok()
        .map(|count| count % table_len)
}

const fn span_contains(outer: Span, inner: Span) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

/// The exact two semantic reads are the entire table exposure.
fn fixed_rotation_references_confined(
    array: &StaticArrayInfo,
    function: &FixedDirectDecoder,
    rotation: &RotationIife,
    scoping: &Scoping,
) -> bool {
    let references = scoping.get_resolved_reference_ids(array.symbol);
    references.len() == 2
        && function.table_reference != rotation.provider_reference
        && references.contains(&function.table_reference)
        && references.contains(&rotation.provider_reference)
        && references.iter().all(|&reference| {
            let reference = scoping.get_reference(reference);
            reference.is_read()
                && !reference.is_write()
                && !reference.flags().is_member_write_target()
        })
}

fn detect_fixed_rotated_direct_decoders(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    context: &DecoderBindingContext<'_>,
    rotations: &[RotationIife],
) -> Result<DecoderDetection, BudgetExceeded> {
    let DecoderBindingContext {
        scoping,
        facts,
        reference_spans,
        budget,
    } = *context;
    let arrays = all_static_arrays(program);
    let functions = fixed_direct_decoders(program, scoping, facts);
    let arrays_by_symbol = arrays
        .iter()
        .map(|array| (array.symbol, array))
        .collect::<HashMap<_, _>>();
    let mut decoders = HashMap::new();
    let mut protected_spans = Vec::new();
    let mut replacements = Vec::new();

    for function in &functions {
        if scoping
            .get_resolved_reference_ids(function.symbol)
            .iter()
            .any(|reference_id| scoping.get_reference(*reference_id).is_write())
        {
            continue;
        }

        if !scoping
            .get_resolved_reference_ids(function.symbol)
            .iter()
            .all(|&reference| {
                reference_spans.get(&reference).is_some_and(|span| {
                    facts.initialized_reference(scoping, reference, *span) == Some(function.symbol)
                })
            })
        {
            continue;
        }
        let Some(array) = arrays_by_symbol.get(&function.table).copied() else {
            continue;
        };
        if !facts.source_local_data_binding(scoping, array.symbol)
            || !facts.binding_has_stable_value(scoping, function.symbol)
        {
            continue;
        }
        let offset = function.offset;
        let matching_rotations = rotations
            .iter()
            .filter(|rotation| {
                rotation.provider == array.symbol
                    && rotation.statement_span.end <= function.span.start
            })
            .collect::<Vec<_>>();
        if matching_rotations.len() != 1 {
            continue;
        }
        let rotation = matching_rotations[0];
        let Some(execution) = rotation.execution else {
            continue;
        };
        if execution.owner != scoping.symbol_scope_id(array.symbol) {
            continue;
        }
        let mut ordered = true;
        for &reference in scoping.get_resolved_reference_ids(function.symbol) {
            let Some(&span) = reference_spans.get(&reference) else {
                ordered = false;
                break;
            };
            let scope = scoping.get_reference(reference).scope_id();
            if !facts.proves_execution_region_through_calls(
                scoping,
                execution.owner,
                execution.after,
                (scope, span),
                budget,
            )? {
                ordered = false;
                break;
            }
        }
        if !ordered {
            continue;
        }
        let Some(amount) = fixed_count_rotation(rotation, array.values.len()) else {
            continue;
        };

        // The table must become observable only through the proven rotation
        // IIFE and the direct decoder. In particular, require the rotation
        // to be adjacent to the literal declaration so pre-materializing the
        // final table cannot change an intervening observation (including
        // direct eval or another aliasing call).
        let Some(between) =
            source.get(array.span.end as usize..rotation.statement_span.start as usize)
        else {
            continue;
        };
        if !between.chars().all(|ch| ch.is_whitespace() || ch == ';') {
            continue;
        }
        if !fixed_rotation_references_confined(array, function, rotation, scoping) {
            continue;
        }

        let mut values = array.values.clone();
        values.rotate_left(amount);
        let Some(array_text) = render_value_array(&values) else {
            continue;
        };
        replacements.push(Replacement {
            start: array.span.start as usize,
            end: array.span.end as usize,
            text: array_text,
            kind: "materialize_fixed_decoder_rotation",
            arithmetic_state_proof: None,
        });
        replacements.push(Replacement {
            start: rotation.call_span.start as usize,
            end: rotation.call_span.end as usize,
            text: "(void 0)".to_string(),
            kind: "remove_fixed_decoder_rotation_iife",
            arithmetic_state_proof: None,
        });
        protected_spans.push((
            rotation.statement_span.start as usize,
            rotation.statement_span.end as usize,
        ));
        decoders.insert(
            function.symbol,
            Decoder {
                values: values.into(),
                proven_alias_reads: None,
                offset,
                provider: array.symbol,
                provider_array_span: array.span,
                transform: DecoderTransform::Plain,
            },
        );
    }

    Ok((decoders, protected_spans, replacements))
}

#[derive(Debug, Clone)]
struct ProvenRotationIife {
    provider: SymbolId,
    start: usize,
    end: usize,
}

/// One physical rotation must agree with every view of the provider.
/// Check the entire bounded orbit: unknown results are not negative
/// witnesses, while a known NaN can safely fail the equality comparison.
fn prove_rotation_iife(
    iife: &RotationIife,
    decoders: &mut HashMap<SymbolId, Decoder>,
    budget: &WorkBudget,
) -> Result<bool, BudgetExceeded> {
    let Some(RotationOperation::Checksum(checksum)) = &iife.operation else {
        return Ok(false);
    };
    let mut table: Option<&Decoder> = None;
    for decoder in decoders
        .values()
        .filter(|decoder| decoder.provider == iife.provider)
    {
        if decoder.values.is_empty()
            || table.is_some_and(|previous| {
                previous.provider_array_span != decoder.provider_array_span
                    || !same_values(&previous.values, &decoder.values)
            })
        {
            return Ok(false);
        }
        table = Some(decoder);
    }
    let Some(table) = table else {
        return Ok(false);
    };
    let mut amount = None;
    let cost = checksum.cost();
    for rotation in 0..table.values.len() {
        budget.consume(cost)?;
        let Some(value) = checksum.evaluate(decoders, iife.provider, rotation) else {
            return Ok(false);
        };
        if value.is_finite()
            && (value - js_number_from_i64(iife.target)).abs() <= 0.0
            && amount.replace(rotation).is_some()
        {
            return Ok(false);
        }
    }
    let Some(amount) = amount else {
        return Ok(false);
    };
    let mut values = Rc::clone(&table.values);
    Rc::make_mut(&mut values).rotate_left(amount);
    for decoder in decoders
        .values_mut()
        .filter(|decoder| decoder.provider == iife.provider)
    {
        decoder.values = Rc::clone(&values);
    }
    Ok(true)
}

fn prove_rotation_iifes(
    rotation_iifes: &[RotationIife],
    decoders: &mut HashMap<SymbolId, Decoder>,
    budget: &WorkBudget,
) -> Result<Vec<ProvenRotationIife>, BudgetExceeded> {
    let mut proven_iifes = Vec::new();
    let mut ordered = rotation_iifes.iter().collect::<Vec<_>>();
    ordered.sort_unstable_by_key(|rotation| rotation.call_span.start);
    for iife in ordered {
        if !prove_rotation_iife(iife, decoders, budget)? {
            continue;
        }
        proven_iifes.push(ProvenRotationIife {
            provider: iife.provider,
            start: iife.call_span.start as usize,
            end: iife.call_span.end as usize,
        });
    }
    Ok(proven_iifes)
}

fn materializable_rotated_providers(
    decoders: &HashMap<SymbolId, Decoder>,
    proven_iifes: &[ProvenRotationIife],
) -> HashMap<SymbolId, (Span, Vec<Value>)> {
    // Materialization is stricter than decoding. Every detected decoder sharing
    // a provider must agree on the same final rotated table and literal array.
    let proven_providers = proven_iifes
        .iter()
        .map(|iife| iife.provider)
        .collect::<HashSet<_>>();
    let mut materialized: HashMap<SymbolId, (Span, Vec<Value>)> = HashMap::new();
    let mut inconsistent = HashSet::new();
    for decoder in decoders.values() {
        if !proven_providers.contains(&decoder.provider) {
            continue;
        }
        match materialized.get(&decoder.provider) {
            None => {
                materialized.insert(
                    decoder.provider,
                    (decoder.provider_array_span, decoder.values.to_vec()),
                );
            }
            Some((span, values))
                if *span == decoder.provider_array_span && same_values(values, &decoder.values) => {
            }
            Some(_) => {
                inconsistent.insert(decoder.provider);
            }
        }
    }
    for provider in inconsistent {
        materialized.remove(&provider);
    }
    materialized
}

fn rotation_replacements(
    materialized: HashMap<SymbolId, (Span, Vec<Value>)>,
    proven_iifes: &[ProvenRotationIife],
) -> Vec<Replacement> {
    let mut replacements = Vec::new();
    for (provider, (array_span, values)) in materialized {
        let Some(array_text) = render_value_array(&values) else {
            continue;
        };
        replacements.push(Replacement {
            start: array_span.start as usize,
            end: array_span.end as usize,
            text: array_text,
            kind: "materialize_decoder_rotation",
            arithmetic_state_proof: None,
        });
        replacements.extend(
            proven_iifes
                .iter()
                .filter(|iife| iife.provider == provider)
                .map(|iife| Replacement {
                    start: iife.start,
                    end: iife.end,
                    // Replace the call, not an enclosing expression statement:
                    // retain its undefined completion and any outer operator.
                    text: "(void 0)".to_string(),
                    kind: "remove_decoder_rotation_iife",
                    arithmetic_state_proof: None,
                }),
        );
    }
    replacements
}

struct RotationApplication {
    protected_spans: Vec<(usize, usize)>,
    replacements: Vec<Replacement>,
}

fn apply_proven_decoder_rotations(
    decoders: &mut HashMap<SymbolId, Decoder>,
    rotation_iifes: &[RotationIife],
    budget: &WorkBudget,
) -> Result<RotationApplication, BudgetExceeded> {
    let mut proven_iifes = prove_rotation_iifes(rotation_iifes, decoders, budget)?;

    let mut required = HashMap::<SymbolId, usize>::new();
    for iife in rotation_iifes {
        *required.entry(iife.provider).or_default() += 1;
    }
    let mut proven = HashMap::<SymbolId, usize>::new();
    for iife in &proven_iifes {
        *proven.entry(iife.provider).or_default() += 1;
    }
    let unproven_providers = required
        .into_iter()
        .filter_map(|(provider, count)| {
            (proven.get(&provider).copied().unwrap_or_default() != count).then_some(provider)
        })
        .collect::<HashSet<_>>();

    decoders.retain(|_, decoder| !unproven_providers.contains(&decoder.provider));
    proven_iifes.retain(|iife| !unproven_providers.contains(&iife.provider));
    let protected_spans = proven_iifes
        .iter()
        .map(|iife| (iife.start, iife.end))
        .collect::<Vec<_>>();
    let materialized = materializable_rotated_providers(decoders, &proven_iifes);
    let replacements = rotation_replacements(materialized, &proven_iifes);
    Ok(RotationApplication {
        protected_spans,
        replacements,
    })
}

type DecoderDetection = (
    HashMap<SymbolId, Decoder>,
    Vec<(usize, usize)>,
    Vec<Replacement>,
);

struct DecoderPatterns {
    local: regex::Regex,
    offset: regex::Regex,
    index: regex::Regex,
}

static DECODER_PATTERNS: LazyLock<Option<DecoderPatterns>> = LazyLock::new(|| {
    Some(DecoderPatterns {
        local: compile_regex(
            r"\b(?:const|let|var)\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*([A-Za-z_$][A-Za-z0-9_$]*)\(\)\s*;",
        )?,
        offset: compile_regex(
            r"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*-\s*(0[xX][0-9A-Fa-f]+|[0-9]+)\s*;",
        )?,
        index: compile_regex(
            r"\b(?:let|const|var)\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*([A-Za-z_$][A-Za-z0-9_$]*)\[([A-Za-z_$][A-Za-z0-9_$]*)\]\s*;",
        )?,
    })
});

fn decoder_patterns() -> Option<&'static DecoderPatterns> {
    DECODER_PATTERNS.as_ref()
}

fn function_name_counts(functions: &[FnInfo]) -> HashMap<String, usize> {
    let mut counts = HashMap::new();
    for function in functions {
        *counts.entry(function.name.clone()).or_default() += 1;
    }
    counts
}

struct ProviderIndex<'a> {
    by_symbol: HashMap<SymbolId, &'a FnInfo>,
    by_scope_name: HashMap<(ScopeId, String), &'a FnInfo>,
}

fn decoder_providers(functions: &[FnInfo]) -> ProviderIndex<'_> {
    let mut index = ProviderIndex {
        by_symbol: HashMap::new(),
        by_scope_name: HashMap::new(),
    };
    for function in functions
        .iter()
        .filter(|function| function.provider.is_some())
    {
        index.by_symbol.insert(function.symbol, function);
        index
            .by_scope_name
            .insert((function.scope, function.name.clone()), function);
    }
    index
}

fn decoder_transform(body: &str, keyed_decode_call: bool) -> Option<DecoderTransform> {
    if !body.contains("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/=")
        || !body.contains("decodeURIComponent")
    {
        return Some(DecoderTransform::Plain);
    }

    let char_code_at_count = body.matches(".charCodeAt(").count();
    let rc4_key_shape = RC4_CHAR_CODE_AT_RE.as_ref().is_some_and(|pattern| {
        pattern.captures_iter(body).any(|captures| {
            let key = &captures[1];
            let argument = &captures[2];
            argument.contains('%')
                && compile_regex(&format!(r"\b{}\s*\.\s*length\b", regex::escape(key)))
                    .is_some_and(|length| length.is_match(argument))
        })
    });
    if keyed_decode_call && rc4_key_shape && body.contains("0x100") && char_code_at_count >= 2 {
        return Some(DecoderTransform::LowerAlphabetBase64Rc4);
    }

    // Recognize the pure javascript-obfuscator Base64 -> percent-URI decoder
    // by its dataflow ingredients. Extra charCodeAt probes are source-sensitive
    // self-defence unless the exact decoder representation is one physical line.
    let base64_uri_shape = body.contains(".charAt(")
        && body.contains(".indexOf(")
        && body.contains("String.fromCharCode")
        && body.contains(".toString(16)");
    if !base64_uri_shape || char_code_at_count == 0 {
        return None;
    }
    if char_code_at_count > 1 && (body.contains('\n') || body.contains('\r')) {
        return None;
    }
    Some(DecoderTransform::LowerAlphabetBase64Uri)
}

fn detect_decoder_candidate(
    source: &str,
    function: &FnInfo,
    patterns: &DecoderPatterns,
    name_counts: &HashMap<String, usize>,
    providers: &ProviderIndex<'_>,
) -> Option<Decoder> {
    if !function.parameters_proven || function.params.is_empty() {
        return None;
    }
    if let Some(shape) = &function.plain_decoder {
        let provider = providers.by_symbol.get(&shape.provider_symbol)?;
        let provider_info = provider.provider.as_ref()?;
        return Some(Decoder {
            values: provider_info.values.clone().into(),
            proven_alias_reads: None,
            offset: shape.offset,
            provider: provider.symbol,
            provider_array_span: provider_info.span,
            transform: DecoderTransform::Plain,
        });
    }
    let body = fragment(source, function.span);
    let local = patterns.local.captures(body)?;
    let local_array = local[1].to_string();
    let provider = local[2].to_string();

    // Rotation proof below is textual. Fail closed if either function name
    // occurs in more than one lexical scope, so a sibling IIFE cannot
    // accidentally supply another decoder's rotation.
    if name_counts.get(&function.name).copied() != Some(1)
        || name_counts.get(&provider).copied() != Some(1)
    {
        return None;
    }
    let provider = providers.by_scope_name.get(&(function.scope, provider))?;
    let provider_info = provider.provider.as_ref()?;
    let offset_match = patterns.offset.captures(body)?;
    if offset_match[1] != offset_match[2] {
        return None;
    }
    let param = offset_match[1].to_string();
    let public_param = function.params.first()?;
    let offset = parse_i64_literal(&offset_match[3])?;
    let index = patterns.index.captures(body)?;
    if index[2] != local_array || index[3] != param {
        return None;
    }
    let value_var = index[1].to_string();
    let bare_value_return = body.contains(&format!("return {value_var};"));
    let sequence_value_return =
        body.contains(&format!(", {value_var};")) || body.contains(&format!(",{value_var};"));

    let installs_replacement_re = compile_regex(&format!(
        r"\b{}\s*=\s*function\s*\(\s*{}\b",
        regex::escape(&function.name),
        regex::escape(&param),
    ))?;
    let tail_calls_public_re = compile_regex(&format!(
        r"(?:\breturn\b|,)\s*{}\s*\(\s*{}\b",
        regex::escape(&function.name),
        regex::escape(public_param),
    ))?;
    let self_rewriting =
        installs_replacement_re.is_match(body) && tail_calls_public_re.is_match(body);

    if !(self_rewriting && (bare_value_return || sequence_value_return)) {
        return None;
    }

    let nested_key_param = compile_regex(&format!(
        r"\b{}\s*=\s*function\s*\(\s*{}\s*,\s*([A-Za-z_$][A-Za-z0-9_$]*)\b",
        regex::escape(&function.name),
        regex::escape(&param),
    ))
    .and_then(|pattern| pattern.captures(body))
    .map(|captures| captures[1].to_string());
    let keyed_decode_call = nested_key_param.is_some_and(|key| {
        compile_regex(&format!(
            r"\(\s*{}\s*,\s*{}\s*\)",
            regex::escape(&value_var),
            regex::escape(&key),
        ))
        .is_some_and(|pattern| pattern.is_match(body))
    });

    let transform = decoder_transform(body, keyed_decode_call)?;
    // Plain accessors are accepted only by the structural proof above.
    if matches!(transform, DecoderTransform::Plain) {
        return None;
    }
    Some(Decoder {
        values: provider_info.values.clone().into(),
        proven_alias_reads: None,
        offset,
        provider: provider.symbol,
        provider_array_span: provider_info.span,
        transform,
    })
}

struct DecoderBindingContext<'c> {
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    reference_spans: &'c HashMap<ReferenceId, Span>,
    budget: &'c WorkBudget,
}

/// Propagate only along proved capture edges. A read before an alias is
/// initialized is not authorized, even when later reads are exact. The
/// worklist visits each reachable alias and shares the provider table.
fn propagate_decoder_aliases(
    decoders: &mut HashMap<SymbolId, Decoder>,
    program: &oxc_ast::ast::Program<'_>,
    context: &DecoderBindingContext<'_>,
) -> Result<(), BudgetExceeded> {
    let mut collector = AliasCandidateCollector {
        context,
        by_target: HashMap::new(),
    };
    collector.visit_program(program);
    let mut pending = decoders.keys().copied().collect::<VecDeque<_>>();
    while let Some(target) = pending.pop_front() {
        context.budget.checkpoint()?;
        let Some(candidates) = collector.by_target.remove(&target) else {
            continue;
        };
        let Some(decoder) = decoders.get(&target).cloned() else {
            continue;
        };
        context
            .budget
            .consume(u64::try_from(candidates.len()).unwrap_or(u64::MAX))?;
        for candidate in candidates {
            if decoders.contains_key(&candidate.alias)
                || !decoder.permits_read(candidate.target_reference)
            {
                continue;
            }
            let Some(reads) = candidate.proven_reads(context)? else {
                continue;
            };
            let mut alias = decoder.clone();
            alias.proven_alias_reads = Some(Rc::new(reads));
            decoders.insert(candidate.alias, alias);
            pending.push_back(candidate.alias);
        }
    }
    Ok(())
}

/// Rotations may be materialized only if each executes once in the
/// provider's own allocation context, and no decoder can observe a table
/// before the last rotation. Capturing an alias also counts as an observation
/// until the capture/use chain can provide a more precise temporal proof.
fn prove_rotation_order(
    functions: &[FnInfo],
    rotations: &[RotationIife],
    decoders: &mut HashMap<SymbolId, Decoder>,
    context: &DecoderBindingContext<'_>,
) -> Result<(), BudgetExceeded> {
    let DecoderBindingContext {
        scoping,
        facts,
        reference_spans,
        budget,
    } = *context;
    let mut groups: HashMap<SymbolId, Vec<&RotationIife>> = HashMap::new();
    for rotation in rotations {
        groups.entry(rotation.provider).or_default().push(rotation);
    }
    let mut by_provider: HashMap<SymbolId, Vec<&FnInfo>> = HashMap::new();
    for function in functions {
        if let Some(decoder) = decoders.get(&function.symbol) {
            by_provider
                .entry(decoder.provider)
                .or_default()
                .push(function);
        }
    }
    let mut invalid = HashSet::new();
    for (provider, mut group) in groups {
        let Some(views) = by_provider.get(&provider) else {
            continue;
        };
        budget.checkpoint()?;
        group.sort_unstable_by_key(|rotation| rotation.call_span.start);
        let Some(last) = group.last().and_then(|rotation| rotation.execution) else {
            invalid.insert(provider);
            continue;
        };
        if last.owner != scoping.symbol_scope_id(provider)
            || group.iter().any(|rotation| {
                rotation.execution.is_none_or(|execution| {
                    execution.owner != last.owner || execution.after.end != last.after.end
                })
            })
            || group
                .windows(2)
                .any(|pair| pair[0].call_span.end > pair[1].call_span.start)
        {
            invalid.insert(provider);
            continue;
        }
        'observations: for function in views {
            let references = scoping.get_resolved_reference_ids(function.symbol);
            budget.consume(u64::try_from(references.len()).unwrap_or(u64::MAX))?;
            for &reference in references {
                let Some(&span) = reference_spans.get(&reference) else {
                    invalid.insert(provider);
                    break 'observations;
                };
                if span_contains(function.span, span)
                    || group
                        .iter()
                        .any(|rotation| span_contains(rotation.call_span, span))
                {
                    continue;
                }
                let scope = scoping.get_reference(reference).scope_id();
                if !facts.proves_execution_region_through_calls(
                    scoping,
                    last.owner,
                    last.after,
                    (scope, span),
                    budget,
                )? {
                    invalid.insert(provider);
                    break 'observations;
                }
            }
        }
    }
    decoders.retain(|_, decoder| !invalid.contains(&decoder.provider));
    Ok(())
}

fn detect_decoders(
    source: &str,
    functions: &[FnInfo],
    program: &oxc_ast::ast::Program<'_>,
    context: &DecoderBindingContext<'_>,
    rotations: &[RotationIife],
) -> Result<DecoderDetection, BudgetExceeded> {
    let DecoderBindingContext {
        scoping,
        facts,
        reference_spans,
        ..
    } = *context;
    let Some(patterns) = decoder_patterns() else {
        return Ok((HashMap::new(), Vec::new(), Vec::new()));
    };
    let name_counts = function_name_counts(functions);
    let providers = decoder_providers(functions);
    let mut decoders = functions
        .iter()
        .filter_map(|function| {
            if !facts.binding_unmodified_by_eval(scoping, function.symbol)
                || !scoping.symbol_redeclarations(function.symbol).is_empty()
                || !scoping
                    .get_resolved_reference_ids(function.symbol)
                    .iter()
                    .all(|&reference| {
                        facts.resolved_symbol(scoping, reference) == Some(function.symbol)
                            && ((!scoping.get_reference(reference).is_write()
                                && !scoping
                                    .get_reference(reference)
                                    .flags()
                                    .is_member_write_target())
                                || function.plain_decoder.as_ref().map_or_else(
                                    || {
                                        reference_spans
                                            .get(&reference)
                                            .is_some_and(|span| span_contains(function.span, *span))
                                    },
                                    |shape| shape.installation == Some(reference),
                                ))
                    })
            {
                return None;
            }
            let decoder =
                detect_decoder_candidate(source, function, patterns, &name_counts, &providers)?;
            let provider = providers.by_symbol.get(&decoder.provider)?;
            // Verify the provider referenced by the matched body, not only a
            // name that happens to be declared in its enclosing scope.
            let mut reads = scoping
                .get_resolved_reference_ids(provider.symbol)
                .iter()
                .filter(|&&reference| {
                    facts.resolved_symbol(scoping, reference) == Some(provider.symbol)
                        && reference_spans
                            .get(&reference)
                            .is_some_and(|span| span_contains(function.span, *span))
                });
            reads.next()?;
            reads.next().is_none().then_some((function.symbol, decoder))
        })
        .collect::<HashMap<_, _>>();

    // Pure return-value semantics do not justify deleting an observable
    // self-installation. Classify source-local alias/call uses before proving
    // rotations, because removing the setup can suppress installation too.
    let installations = functions
        .iter()
        .filter_map(|function| {
            let installation = function.plain_decoder.as_ref()?.installation?;
            decoders
                .contains_key(&function.symbol)
                .then_some((function.symbol, installation))
        })
        .collect::<Vec<_>>();
    if !installations.is_empty() {
        let uses = callable_observation::CallableUses::collect(program, context);
        for (symbol, installation) in installations {
            if !uses.installation_unobservable(symbol, installation)? {
                decoders.remove(&symbol);
            }
        }
    }

    // A self-installing provider returns the same mutable allocation to
    // every caller. A reference outside its own installation, a proved
    // decoder, or a recorded rotation can expose or mutate that table.
    let mut allowed: HashMap<SymbolId, Vec<Span>> = HashMap::new();
    for function in functions {
        if function.provider.is_some() {
            allowed
                .entry(function.symbol)
                .or_default()
                .push(function.span);
        }
        if let Some(decoder) = decoders.get(&function.symbol) {
            allowed
                .entry(decoder.provider)
                .or_default()
                .push(function.span);
        }
    }
    let rotation_references: HashSet<_> = rotations
        .iter()
        .map(|rotation| rotation.provider_reference)
        .collect();
    let invalid: HashSet<_> = allowed
        .iter()
        .filter_map(|(&provider, spans)| {
            scoping
                .get_resolved_reference_ids(provider)
                .iter()
                .any(|reference| {
                    !rotation_references.contains(reference)
                        && !reference_spans.get(reference).is_some_and(|span| {
                            spans.iter().any(|region| span_contains(*region, *span))
                        })
                })
                .then_some(provider)
        })
        .collect();
    decoders.retain(|_, decoder| !invalid.contains(&decoder.provider));
    prove_rotation_order(functions, rotations, &mut decoders, context)?;
    let RotationApplication {
        protected_spans,
        replacements: rotation_replacements,
    } = apply_proven_decoder_rotations(&mut decoders, rotations, context.budget)?;
    propagate_decoder_aliases(&mut decoders, program, context)?;
    Ok((decoders, protected_spans, rotation_replacements))
}

pub struct DecoderAnalysis {
    pub(super) decoders: HashMap<SymbolId, Decoder>,
    pub(super) protected_spans: Vec<(usize, usize)>,
    pub(super) replacements: Vec<Replacement>,
    pub(super) removable_helpers: HashMap<SymbolId, Span>,
    decoder_count: usize,
}

pub fn analyze_decoders(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
    reference_spans: &HashMap<ReferenceId, Span>,
    budget: &WorkBudget,
) -> Result<DecoderAnalysis, BudgetExceeded> {
    let from_char_code_aliases = crate::collect_from_char_code_aliases(program, scoping, facts);
    let direct_functions = all_functions(
        program,
        scoping,
        facts,
        &from_char_code_aliases,
        reference_spans,
    );
    let functions = all_function_declarations(program, scoping, facts);

    let rotations = collect_rotation_iifes(program, scoping, facts);
    let context = DecoderBindingContext {
        scoping,
        facts,
        reference_spans,
        budget,
    };
    let (mut decoders, mut protected_spans, mut replacements) =
        detect_decoders(source, &functions, program, &context, &rotations)?;
    let (fixed_decoders, fixed_protected, fixed_replacements) =
        detect_fixed_rotated_direct_decoders(source, program, &context, &rotations)?;
    for (symbol, decoder) in fixed_decoders {
        decoders.entry(symbol).or_insert(decoder);
    }
    protected_spans.extend(fixed_protected);
    replacements.extend(fixed_replacements);
    let direct = detect_direct_table_decoders(
        program,
        &direct_functions,
        &decoders,
        scoping,
        facts,
        reference_spans,
    );
    let mut collector = DirectTableCallCollector {
        source,
        scoping,
        facts,
        decoders: &direct,
        budget,
        failure: None,
        replacements: Vec::new(),
    };
    if !direct.is_empty() {
        collector.visit_program(program);
    }
    if let Some(failure) = collector.failure {
        return Err(failure);
    }
    replacements.extend(collector.replacements);
    let decoder_count = decoders.len() + direct.len();

    let removable_helpers = functions
        .iter()
        .filter(|function| {
            decoders.contains_key(&function.symbol) || direct.contains_key(&function.symbol)
        })
        .map(|function| (function.symbol, function.span))
        .collect();

    Ok(DecoderAnalysis {
        decoders,
        protected_spans,
        replacements,
        removable_helpers,
        decoder_count,
    })
}

#[derive(Clone, Copy)]
struct LeadingAliasRegion {
    owner: ScopeId,
    container: Span,
    initialized_after: u32,
}

impl LeadingAliasRegion {
    fn contains(self, scoping: &Scoping, scope: ScopeId, span: Span) -> bool {
        self.initialized_after <= span.start
            && span.end <= self.container.end
            && scoping
                .scope_ancestors(scope)
                .any(|ancestor| ancestor == self.owner)
    }
}

#[derive(Clone, Copy)]
enum AliasOrigin {
    Declaration(Option<LeadingAliasRegion>),
    Assignment {
        region: LeadingAliasRegion,
        write: ReferenceId,
        span: Span,
    },
}

#[derive(Clone, Copy)]
struct AliasCandidate {
    alias: SymbolId,
    target_reference: ReferenceId,
    origin: AliasOrigin,
}

impl AliasCandidate {
    fn proven_reads(
        self,
        context: &DecoderBindingContext<'_>,
    ) -> Result<Option<HashSet<ReferenceId>>, BudgetExceeded> {
        let DecoderBindingContext {
            scoping,
            facts,
            reference_spans,
            budget,
        } = *context;
        let symbol = self.alias;
        if facts.is_eval_exposed(scoping, symbol)
            || facts.is_mapped_arguments_exposed(scoping, symbol)
            || !scoping.symbol_redeclarations(symbol).is_empty()
        {
            return Ok(None);
        }
        let (prefix, write) = match self.origin {
            AliasOrigin::Declaration(prefix) => {
                if !facts.binding_has_stable_value(scoping, symbol) {
                    return Ok(None);
                }
                (prefix, None)
            }
            AliasOrigin::Assignment {
                region,
                write,
                span,
            } => {
                let reference = scoping.get_reference(write);
                let flags = scoping.symbol_flags(symbol);
                // Assignment to a parameter or initialized writable local,
                // not a TDZ, immutable, object-environment or outer binding.
                if facts.fixed_assignment_reference(scoping, write) != Some(symbol)
                    || flags.is_const_variable()
                    || flags.is_import()
                    || !facts.proves_initialized(scoping, symbol, reference.scope_id(), span)
                {
                    return Ok(None);
                }
                (Some(region), Some(write))
            }
        };
        if prefix.is_some_and(|region| scoping.symbol_scope_id(symbol) != region.owner) {
            return Ok(None);
        }
        let references = scoping.get_resolved_reference_ids(symbol);
        budget.consume(u64::try_from(references.len()).unwrap_or(u64::MAX))?;
        let mut proven = HashSet::new();
        for &reference in references {
            if write == Some(reference) {
                continue;
            }
            let info = scoping.get_reference(reference);
            // Writes invalidate the alias across all paths. Reads without
            // exact initialization evidence remain in the rewritten code.
            if !info.is_read() || info.is_write() || info.flags().is_member_write_target() {
                return Ok(None);
            }
            if facts.resolved_symbol(scoping, reference) != Some(symbol) {
                continue;
            }
            let Some(&span) = reference_spans.get(&reference) else {
                continue;
            };
            if prefix.is_some_and(|prefix| prefix.contains(scoping, info.scope_id(), span))
                || (write.is_none()
                    && facts.proves_initialized_through_calls(
                        scoping,
                        symbol,
                        info.scope_id(),
                        span,
                        budget,
                    )?)
            {
                proven.insert(reference);
            }
        }
        Ok((!proven.is_empty()).then_some(proven))
    }
}

struct AliasCandidateCollector<'c, 'p> {
    context: &'c DecoderBindingContext<'p>,
    by_target: HashMap<SymbolId, Vec<AliasCandidate>>,
}

impl AliasCandidateCollector<'_, '_> {
    fn add(&mut self, alias: SymbolId, target: &Expression<'_>, origin: AliasOrigin) {
        let Expression::Identifier(target) = target.without_parentheses() else {
            return;
        };
        let Some(reference) = target.reference_id.get() else {
            return;
        };
        let DecoderBindingContext { scoping, facts, .. } = *self.context;
        let Some(target_symbol) = facts.resolved_symbol(scoping, reference) else {
            return;
        };
        if alias == target_symbol || !facts.binding_unmodified_by_eval(scoping, target_symbol) {
            return;
        }
        // Nonleading declarations need actual execution-region evidence,
        // not just a declaration offset. Permit mutable local storage when
        // neither end depends on an ambient object-backed binding whose
        // value could change during an earlier unknown operation.
        if matches!(origin, AliasOrigin::Declaration(None))
            && !scoping.symbol_flags(alias).is_const_variable()
            && (!facts.source_local_data_binding(scoping, alias)
                || !(facts.is_private(scoping, target_symbol)
                    || facts.source_local_data_binding(scoping, target_symbol)))
        {
            return;
        }
        self.by_target
            .entry(target_symbol)
            .or_default()
            .push(AliasCandidate {
                alias,
                target_reference: reference,
                origin,
            });
    }

    fn declaration(
        &mut self,
        declarator: &oxc_ast::ast::VariableDeclarator<'_>,
        prefix: Option<LeadingAliasRegion>,
    ) {
        let Some(alias) = declarator
            .id
            .get_binding_identifier()
            .and_then(|id| id.symbol_id.get())
        else {
            return;
        };
        let Some(target) = &declarator.init else {
            return;
        };
        self.add(alias, target, AliasOrigin::Declaration(prefix));
    }

    fn execution_prefix(
        &mut self,
        statements: &[Statement<'_>],
        owner: Option<ScopeId>,
        container: Span,
    ) {
        let Some(owner) = owner else {
            return;
        };
        let Some(first) = statements.iter().find(|statement| {
            !matches!(
                statement,
                Statement::FunctionDeclaration(_) | Statement::EmptyStatement(_)
            )
        }) else {
            return;
        };
        match first {
            Statement::VariableDeclaration(declaration)
                if matches!(
                    declaration.kind,
                    VariableDeclarationKind::Const
                        | VariableDeclarationKind::Let
                        | VariableDeclarationKind::Var
                ) =>
            {
                // Nothing with an initializer precedes the captured function
                // value: earlier bare identifier declarations are inert.
                if let Some(declarator) = declaration
                    .declarations
                    .iter()
                    .find(|declarator| declarator.init.is_some())
                {
                    self.declaration(
                        declarator,
                        Some(LeadingAliasRegion {
                            owner,
                            container,
                            initialized_after: declarator.span.end,
                        }),
                    );
                }
            }
            Statement::ForStatement(statement) => {
                let Some(initializer) = statement
                    .init
                    .as_ref()
                    .and_then(|init| init.as_expression())
                else {
                    return;
                };
                let first = match initializer.without_parentheses() {
                    Expression::SequenceExpression(sequence) => sequence.expressions.first(),
                    expression => Some(expression),
                };
                let Some(expression) = first else {
                    return;
                };
                let Some((alias, target)) = assignment_identifier(expression) else {
                    return;
                };
                let Some(write) = alias.reference_id.get() else {
                    return;
                };
                let DecoderBindingContext { scoping, facts, .. } = *self.context;
                let Some(alias) = facts.fixed_assignment_reference(scoping, write) else {
                    return;
                };
                self.add(
                    alias,
                    target,
                    AliasOrigin::Assignment {
                        region: LeadingAliasRegion {
                            owner,
                            container,
                            initialized_after: expression.span().end,
                        },
                        write,
                        span: expression.span(),
                    },
                );
            }
            _ => {}
        }
    }
}

impl<'a> Visit<'a> for AliasCandidateCollector<'_, '_> {
    fn visit_variable_declaration(&mut self, declaration: &oxc_ast::ast::VariableDeclaration<'a>) {
        if rotation_proof::ordinary_declaration(declaration) {
            for declarator in &declaration.declarations {
                self.declaration(declarator, None);
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_program(&mut self, program: &oxc_ast::ast::Program<'a>) {
        self.execution_prefix(&program.body, program.scope_id.get(), program.span);
        walk::walk_program(self, program);
    }

    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if function_parameters_have_no_runtime_effects(function) {
            if let Some(body) = &function.body {
                self.execution_prefix(&body.statements, function.scope_id.get(), body.span);
            }
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        match &function.body {
            oxc_ast::ast::ArrowFunctionBody::FunctionBody(body)
                if formal_parameters_have_no_runtime_effects(&function.params) =>
            {
                self.execution_prefix(&body.statements, function.scope_id.get(), body.span);
            }
            _ => {}
        }
        walk::walk_arrow_function_expression(self, function);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decoder_rotation_updates_all_views_of_exactly_one_provider() {
        let provider = SymbolId::new(0);
        let first = SymbolId::new(1);
        let second = SymbolId::new(2);
        let unrelated = SymbolId::new(3);
        let decoder = Decoder {
            values: vec![
                Value::String("11".into()),
                Value::String("22".into()),
                Value::String("33".into()),
            ]
            .into(),
            proven_alias_reads: None,
            offset: 0,
            provider,
            provider_array_span: Span::new(0, 1),
            transform: DecoderTransform::Plain,
        };
        let mut other = decoder.clone();
        other.provider = SymbolId::new(4);
        let mut decoders = HashMap::from([
            (first, decoder.clone()),
            (second, decoder),
            (unrelated, other),
        ]);
        let iife = RotationIife {
            provider,
            provider_reference: ReferenceId::new(0),
            target: 22,
            operation: Some(RotationOperation::Checksum(ChecksumExpression::ParseInt {
                decoder: first,
                raw: 0,
                key: None,
                radix: 0,
            })),
            statement_span: Span::new(0, 10),
            call_span: Span::new(0, 10),
            execution: None,
        };
        let budget = WorkBudget::unlimited("rotation-test");
        assert!(prove_rotation_iife(&iife, &mut decoders, &budget).unwrap_or(false));
        for symbol in [first, second] {
            assert!(
                matches!(decoders[&symbol].value_for_call(0.0, None), Some(Value::String(value)) if value == "22")
            );
        }
        assert!(
            matches!(decoders[&unrelated].value_for_call(0.0,None),Some(Value::String(value)) if value == "11")
        );
        let mut invalid = decoders.clone();
        Rc::make_mut(
            &mut invalid
                .get_mut(&second)
                .unwrap_or_else(|| unreachable!())
                .values,
        )
        .rotate_left(1);
        assert!(!prove_rotation_iife(&iife, &mut invalid, &budget).unwrap_or(true));
        assert!(
            matches!(invalid[&first].value_for_call(0.0,None),Some(Value::String(value)) if value == "22")
        );
    }

    #[test]
    fn rc4_rotation_checksum_uses_literal_key_without_external_evaluation() {
        let decoder = Decoder {
            // Logical order after rotation 3: "17", "23", "hello", "world".
            values: vec![
                Value::String("xCor".into()),
                Value::String("b8khW4W9WQG=".into()),
                Value::String("gmknW5i9WQm=".into()),
                Value::String("xSov".into()),
            ]
            .into(),
            proven_alias_reads: None,
            offset: 0x10,
            provider: SymbolId::new(0),
            provider_array_span: Span::new(0, 0),
            transform: DecoderTransform::LowerAlphabetBase64Rc4,
        };
        let decoder_symbol = SymbolId::new(1);
        let provider = decoder.provider;
        let decoders = HashMap::from([(decoder_symbol, decoder)]);
        let parse = |raw| ChecksumExpression::ParseInt {
            decoder: decoder_symbol,
            raw,
            key: Some("k".into()),
            radix: 0,
        };
        let expression = ChecksumExpression::Binary(
            "+",
            Box::new(ChecksumExpression::Binary(
                "*",
                Box::new(parse(0x10)),
                Box::new(ChecksumExpression::Number(10.0)),
            )),
            Box::new(parse(0x11)),
        );
        assert_eq!(expression.evaluate(&decoders, provider, 3), Some(193.0));
        assert_eq!(expression.evaluate(&decoders, SymbolId::new(99), 3), None);
        let unknown = ChecksumExpression::ParseInt {
            decoder: decoder_symbol,
            raw: 0x99,
            key: Some("k".into()),
            radix: 0,
        };
        assert_eq!(unknown.evaluate(&decoders, provider, 3), None);
    }

    #[test]
    fn parse_int_distinguishes_inferred_radix_and_known_nan() {
        assert_eq!(js_parse_int("\u{feff}-0Xf", 0), Some(-15.0));
        assert_eq!(js_parse_int("0x10", 10), Some(0.0));
        assert_eq!(js_parse_int("0x10", 16), Some(16.0));
        assert_eq!(js_parse_int("011", 0), Some(11.0));
        assert!(js_parse_int("no digits", 0).is_some_and(f64::is_nan));
        assert!(js_parse_int("\u{0085}12", 0).is_some_and(f64::is_nan));
        assert!(js_parse_int("1", 1).is_some_and(f64::is_nan));
        assert_eq!(js_parse_int("18446744073709551616", 10), None);
    }
}
