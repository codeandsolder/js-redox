use crate::decoder_encoding::{
    decode_fixed_base64_latin1, decode_lower_alphabet_base64_rc4, decode_lower_alphabet_base64_uri,
    decode_standard_base64_latin1,
};
mod fixed_base64_proof;

use crate::binding_facts::{BindingFacts, ReferenceIdentity};
use crate::rewrite::Replacement;
use crate::value_eval::{
    canonical_array_index_key, eval, exact_computed_property_key, js_to_uint32,
    literal_property_key, render_value_array, same_values, Value,
};
use crate::{
    argument_integer, array_element, decoder_argument_integer, expression_integer, fragment,
    reference_is_statically_resolved_read, statically_resolved_symbol,
    statically_unresolved_global_reference, string_literal_value, symbol_has_only_read_references,
    symbol_of, template_element_value,
};
use fixed_base64_proof::fixed_base64_algorithm_proven;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, BindingPattern, CallExpression, Expression, ExpressionStatement, Statement,
    VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::{
    collections::{HashMap, HashSet},
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
    name: String,
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
                    name: id.name.to_string(),
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
struct SequenceDecoderShape {
    provider: String,
    provider_symbol: SymbolId,
    offset: i64,
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
    sequence_decoder: Option<SequenceDecoderShape>,
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
    if !facts.binding_unmodified_by_eval(scoping, provider)
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
fn sequence_decoder_offset(
    offset_assignment: &Expression<'_>,
    public_param_symbol: SymbolId,
    scoping: &Scoping,
) -> Option<i64> {
    let (offset_target, offset_value) = assignment_identifier(offset_assignment)?;
    if statically_resolved_symbol(scoping, offset_target.reference_id.get()?)
        != Some(public_param_symbol)
    {
        return None;
    }
    let Expression::BinaryExpression(offset_binary) = unparenthesized(offset_value) else {
        return None;
    };
    if offset_binary.operator.as_str() != "-" {
        return None;
    }
    let Expression::Identifier(offset_source) = unparenthesized(&offset_binary.left) else {
        return None;
    };
    if statically_resolved_symbol(scoping, offset_source.reference_id.get()?)
        != Some(public_param_symbol)
    {
        return None;
    }
    expression_integer(&offset_binary.right)
}

fn sequence_decoder_shape(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<SequenceDecoderShape> {
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

    let offset = sequence_decoder_offset(offset_assignment, public_param_symbol, scoping)?;

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

    Some(SequenceDecoderShape {
        provider: provider.name.to_string(),
        provider_symbol,
        offset,
    })
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
        sequence_decoder: parameters_proven
            .then(|| sequence_decoder_shape(f, scoping, facts))
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
                    let number = eval(expression)?.number()?;
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
    function.params.items.iter().all(|parameter| {
        parameter.initializer.is_none()
            && matches!(parameter.pattern, BindingPattern::BindingIdentifier(_))
    }) && function
        .params
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
struct VariableFunctionInfo {
    symbol: SymbolId,
    span: Span,
    params: Vec<String>,
}

#[derive(Default)]
struct VariableFunctionCollector {
    out: Vec<VariableFunctionInfo>,
}

impl<'a> Visit<'a> for VariableFunctionCollector {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        for declaration in &it.declarations {
            let BindingPattern::BindingIdentifier(id) = &declaration.id else {
                continue;
            };
            let Some(symbol) = id.symbol_id.get() else {
                continue;
            };
            let Some(Expression::FunctionExpression(function)) = &declaration.init else {
                continue;
            };
            let Some(params) = function
                .params
                .items
                .iter()
                .map(|param| match &param.pattern {
                    BindingPattern::BindingIdentifier(id) => Some(id.name.to_string()),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            self.out.push(VariableFunctionInfo {
                symbol,
                span: function.span,
                params,
            });
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn variable_functions(program: &oxc_ast::ast::Program<'_>) -> Vec<VariableFunctionInfo> {
    let mut collector = VariableFunctionCollector::default();
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
    values: Vec<Value>,
    offset: i64,
    provider: SymbolId,
    provider_array_span: Span,
    transform: DecoderTransform,
}

impl DecoderTransform {
    fn transform_value(&self, value: Value, key: Option<&str>) -> Option<Value> {
        match (self, value) {
            (DecoderTransform::LowerAlphabetBase64Uri, Value::String(encoded)) => {
                decode_lower_alphabet_base64_uri(&encoded).map(Value::String)
            }
            (DecoderTransform::LowerAlphabetBase64Rc4, Value::String(encoded)) => {
                decode_lower_alphabet_base64_rc4(&encoded, key?).map(Value::String)
            }
            (DecoderTransform::StandardBase64, Value::String(encoded)) => {
                decode_standard_base64_latin1(&encoded).map(Value::String)
            }
            (DecoderTransform::FixedBase64Alphabet(alphabet), Value::String(encoded)) => {
                decode_fixed_base64_latin1(&encoded, alphabet).map(Value::String)
            }
            (
                DecoderTransform::LowerAlphabetBase64Uri
                | DecoderTransform::LowerAlphabetBase64Rc4
                | DecoderTransform::StandardBase64,
                _,
            ) => None,
            (DecoderTransform::Plain | DecoderTransform::FixedBase64Alphabet(_), value) => {
                Some(value)
            }
        }
    }
}

impl Decoder {
    fn value_for_raw_rotated_with_key(
        &self,
        raw: i64,
        rotation: usize,
        key: Option<&str>,
    ) -> Option<Value> {
        let index = raw.checked_sub(self.offset)?;
        if index < 0 || self.values.is_empty() {
            return None;
        }
        let index = usize::try_from(index).ok()?;
        // Array indexing never wraps. Rotation only maps an already-valid
        // logical table index onto the physically rotated backing array.
        if index >= self.values.len() {
            return None;
        }
        let index = index.checked_add(rotation)? % self.values.len();
        self.transform
            .transform_value(self.values.get(index)?.clone(), key)
    }

    pub(super) fn value_for_call(&self, raw: i64, key: Option<&str>) -> Option<Value> {
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
    let symbol = facts.stable_callable_symbol(scoping, &call.callee)?;
    let decoder = decoders.get(&symbol)?;
    let key = match call.arguments.get(1) {
        Some(Argument::StringLiteral(literal)) => Some(string_literal_value(literal)?),
        Some(_) => return None,
        None => None,
    };
    let argument = call.arguments.first()?;
    if let Some(raw) = decoder_argument_integer(argument) {
        return literal_decoder_rewrite(decoder.value_for_call(raw, key.as_deref())?);
    }
    conditional_decoder_rewrite(source, argument, |expression| {
        decoder.value_for_call(expression_integer(expression)?, key.as_deref())
    })
}

fn literal_decoder_rewrite(value: Value) -> Option<DecoderCallRewrite> {
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

fn contains_function_reassignment(body: &str, name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    let identifier_byte =
        |byte: u8| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$') || byte >= 0x80;
    let mut search_from = 0usize;
    while let Some(relative) = body[search_from..].find(name) {
        let start = search_from + relative;
        let after_name = start + name.len();
        if start > 0 && identifier_byte(body.as_bytes()[start - 1]) {
            search_from = after_name;
            continue;
        }
        if after_name < body.len() && identifier_byte(body.as_bytes()[after_name]) {
            search_from = after_name;
            continue;
        }
        let tail = body[after_name..].trim_start_matches(char::is_whitespace);
        if let Some(after_equals) = tail.strip_prefix("=") {
            if after_equals
                .trim_start_matches(char::is_whitespace)
                .starts_with("function")
            {
                return true;
            }
        }
        search_from = after_name;
    }
    false
}

static RC4_CHAR_CODE_AT_RE: LazyLock<Option<regex::Regex>> = LazyLock::new(|| {
    compile_regex(r"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*\.\s*charCodeAt\s*\(([^)]*)\)")
});
static DIRECT_ARRAY_ACCESS_RE: LazyLock<Option<regex::Regex>> =
    LazyLock::new(|| compile_regex(r"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*\[\s*([^\s\]]+)\s*\]"));

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
            return literal_decoder_rewrite(value);
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

pub fn js_parse_int(text: &str, radix: u32) -> Option<f64> {
    if !(2..=36).contains(&radix) {
        return None;
    }
    let text = text.trim_start();
    let (negative, text) = text.strip_prefix('-').map_or_else(
        || (false, text.strip_prefix('+').unwrap_or(text)),
        |rest| (true, rest),
    );
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
        return None;
    }
    let value = js_number_from_u64(value);
    Some(if negative { -value } else { value })
}

fn rotation_static_integer(
    expression: &Expression<'_>,
    numeric_members: &HashMap<(String, String), i64>,
) -> Option<i64> {
    let expression = unparenthesized(expression);
    if let Some(value) = expression_integer(expression) {
        return Some(value);
    }
    let Expression::StaticMemberExpression(member) = expression else {
        return None;
    };
    let Expression::Identifier(object) = unparenthesized(&member.object) else {
        return None;
    };
    numeric_members
        .get(&(object.name.to_string(), member.property.name.to_string()))
        .copied()
}

fn rotation_literal_integer(expression: &Expression<'_>) -> Option<i64> {
    let expression = unparenthesized(expression);
    match expression {
        Expression::NumericLiteral(_) => expression_integer(expression),
        Expression::UnaryExpression(unary)
            if matches!(unary.operator.as_str(), "+" | "-")
                && matches!(
                    unparenthesized(&unary.argument),
                    Expression::NumericLiteral(_)
                ) =>
        {
            expression_integer(expression)
        }
        _ => None,
    }
}

fn rotation_decoder_call(
    call: &CallExpression<'_>,
    alias: &str,
    decoder: &Decoder,
    numeric_members: &HashMap<(String, String), i64>,
    rotation: usize,
) -> Option<String> {
    if call.optional
        || !(1..=2).contains(&call.arguments.len())
        || call.arguments.iter().any(Argument::is_spread)
    {
        return None;
    }
    let Expression::Identifier(callee) = unparenthesized(&call.callee) else {
        return None;
    };
    if callee.name.as_str() != alias {
        return None;
    }
    let raw = rotation_static_integer(call.arguments.first()?.as_expression()?, numeric_members)?;
    let key = match call.arguments.get(1) {
        Some(argument) => {
            let Expression::StringLiteral(literal) = unparenthesized(argument.as_expression()?)
            else {
                return None;
            };
            Some(string_literal_value(literal)?)
        }
        None => None,
    };
    decoder
        .value_for_raw_rotated_with_key(raw, rotation, key.as_deref())?
        .js_string()
}

fn eval_rotation_expression(
    expression: &Expression<'_>,
    alias: &str,
    decoder: &Decoder,
    numeric_members: &HashMap<(String, String), i64>,
    rotation: usize,
) -> Option<f64> {
    match unparenthesized(expression) {
        Expression::NumericLiteral(number) => Some(number.value),
        Expression::StaticMemberExpression(_) => {
            rotation_static_integer(expression, numeric_members).map(js_number_from_i64)
        }
        Expression::UnaryExpression(unary) => {
            let value = eval_rotation_expression(
                &unary.argument,
                alias,
                decoder,
                numeric_members,
                rotation,
            )?;
            match unary.operator.as_str() {
                "+" => Some(value),
                "-" => Some(-value),
                _ => None,
            }
        }
        Expression::BinaryExpression(binary) => {
            let left =
                eval_rotation_expression(&binary.left, alias, decoder, numeric_members, rotation)?;
            let right =
                eval_rotation_expression(&binary.right, alias, decoder, numeric_members, rotation)?;
            match binary.operator.as_str() {
                "+" => Some(left + right),
                "-" => Some(left - right),
                "*" => Some(left * right),
                "/" => Some(left / right),
                "%" => Some(left % right),
                _ => None,
            }
        }
        Expression::CallExpression(call) => {
            if call.optional || !(1..=2).contains(&call.arguments.len()) {
                return None;
            }
            let Expression::Identifier(callee) = unparenthesized(&call.callee) else {
                return None;
            };
            if callee.name.as_str() != "parseInt" {
                return None;
            }
            let decoded_call = call.arguments.first()?.as_expression()?;
            let Expression::CallExpression(decoded_call) = unparenthesized(decoded_call) else {
                return None;
            };
            let decoded_value =
                rotation_decoder_call(decoded_call, alias, decoder, numeric_members, rotation)?;
            let radix = match call.arguments.get(1) {
                Some(argument) => {
                    let radix = rotation_literal_integer(argument.as_expression()?)?;
                    u32::try_from(radix).ok()?
                }
                None => 10,
            };
            js_parse_int(&decoded_value, radix)
        }
        _ => None,
    }
}

fn eval_rotation_checksum(
    expression: &str,
    alias: &str,
    decoder: &Decoder,
    numeric_members: &HashMap<(String, String), i64>,
    rotation: usize,
) -> Option<f64> {
    let wrapped = format!("({expression});");
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, &wrapped, SourceType::cjs()).parse();
    if parsed.fatal_error || !parsed.diagnostics.is_empty() || parsed.program.body.len() != 1 {
        return None;
    }
    let Statement::ExpressionStatement(statement) = &parsed.program.body[0] else {
        return None;
    };
    eval_rotation_expression(
        &statement.expression,
        alias,
        decoder,
        numeric_members,
        rotation,
    )
}

#[derive(Debug, Clone)]
struct RotationIife {
    provider: SymbolId,
    provider_reference: ReferenceId,
    target: i64,
    array_param: String,
    count_param: String,
    numeric_members: HashMap<(String, String), i64>,
    stable_aliases: HashMap<SymbolId, String>,
    checksum_expression: Option<String>,
    proof_eligible: bool,
    body_span: Span,
    statement_span: Span,
    standalone_statement: bool,
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

#[derive(Default)]
struct RotationStatementSpanCollector {
    spans: HashMap<(u32, u32), Span>,
}

impl<'a> Visit<'a> for RotationStatementSpanCollector {
    fn visit_expression_statement(&mut self, statement: &ExpressionStatement<'a>) {
        if let Some(call) = rotation_iife_call(&statement.expression) {
            self.spans
                .insert((call.span.start, call.span.end), statement.span);
        }
        walk::walk_expression_statement(self, statement);
    }
}

fn rotation_parameter_names_unshadowed(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
) -> bool {
    let Some(body) = &function.body else {
        return false;
    };
    let parameter_symbols = function
        .params
        .items
        .iter()
        .filter_map(|param| match &param.pattern {
            BindingPattern::BindingIdentifier(id) => id.symbol_id.get(),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let parameter_names = parameter_symbols
        .iter()
        .map(|symbol| scoping.symbol_name(*symbol))
        .collect::<HashSet<_>>();

    scoping.symbol_ids().all(|symbol| {
        parameter_symbols.contains(&symbol)
            || !span_contains(body.span, scoping.symbol_span(symbol))
            || !parameter_names.contains(scoping.symbol_name(symbol))
    })
}

#[derive(Default)]
struct RotationDynamicScopeProbe {
    found: bool,
}

impl<'a> Visit<'a> for RotationDynamicScopeProbe {
    fn visit_with_statement(&mut self, _statement: &oxc_ast::ast::WithStatement<'a>) {
        self.found = true;
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if crate::is_potential_direct_eval(call) {
            self.found = true;
            return;
        }
        walk::walk_call_expression(self, call);
    }
}

fn rotation_has_dynamic_scope(function: &oxc_ast::ast::Function<'_>) -> bool {
    let Some(body) = &function.body else {
        return true;
    };
    let mut probe = RotationDynamicScopeProbe::default();
    probe.visit_function_body(body);
    probe.found
}

fn rotation_parse_int_references_are_global(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
) -> bool {
    struct Probe<'c> {
        scoping: &'c Scoping,
        valid: bool,
    }

    impl<'a> Visit<'a> for Probe<'_> {
        fn visit_identifier_reference(
            &mut self,
            identifier: &oxc_ast::ast::IdentifierReference<'a>,
        ) {
            if identifier.name.as_str() == "parseInt" {
                self.valid &= identifier.reference_id.get().is_some_and(|reference_id| {
                    statically_unresolved_global_reference(self.scoping, reference_id)
                });
            }
        }

        fn visit_function(&mut self, _function: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {}

        fn visit_arrow_function_expression(
            &mut self,
            _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
        ) {
        }
    }

    let Some(body) = &function.body else {
        return false;
    };

    let mut probe = Probe {
        scoping,
        valid: true,
    };
    probe.visit_function_body(body);
    probe.valid
}

fn stable_rotation_alias(
    alias: (SymbolId, &str),
    target_reference_id: ReferenceId,
    initialization_end: u32,
    initialization_write: Option<ReferenceId>,
    scoping: &Scoping,
    facts: &BindingFacts,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Option<(SymbolId, String)> {
    let (alias_symbol, alias_name) = alias;
    let target_symbol = facts.resolved_symbol(scoping, target_reference_id)?;
    if !facts.binding_unmodified_by_eval(scoping, alias_symbol)
        || !facts.binding_unmodified_by_eval(scoping, target_symbol)
        || !scoping.symbol_redeclarations(alias_symbol).is_empty()
    {
        return None;
    }
    if target_symbol == alias_symbol || !scoping.symbol_flags(target_symbol).is_function() {
        return None;
    }
    let stable = scoping
        .get_resolved_reference_ids(alias_symbol)
        .iter()
        .all(|reference_id| {
            if initialization_write == Some(*reference_id) {
                return true;
            }
            reference_spans.get(reference_id).is_some_and(|span| {
                span.start >= initialization_end
                    && reference_is_statically_resolved_read(scoping, *reference_id, alias_symbol)
                    && facts.resolved_symbol(scoping, *reference_id) == Some(alias_symbol)
            })
        });
    stable.then(|| (target_symbol, alias_name.to_string()))
}

fn rotation_stable_aliases(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<SymbolId, String> {
    let Some(body) = &function.body else {
        return HashMap::new();
    };
    let mut aliases = HashMap::new();
    for statement in &body.statements {
        if let Statement::VariableDeclaration(declaration) = statement {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(alias) = &declarator.id else {
                    continue;
                };
                let Some(alias_symbol) = alias.symbol_id.get() else {
                    continue;
                };
                let Some(Expression::Identifier(target)) = &declarator.init else {
                    continue;
                };
                let Some(target_reference_id) = target.reference_id.get() else {
                    continue;
                };
                if let Some((target_name, alias_name)) = stable_rotation_alias(
                    (alias_symbol, alias.name.as_str()),
                    target_reference_id,
                    target.span.end,
                    None,
                    scoping,
                    facts,
                    reference_spans,
                ) {
                    aliases.insert(target_name, alias_name);
                }
            }
        }
        let Statement::ForStatement(for_statement) = statement else {
            continue;
        };
        let assignments = match for_statement.init.as_ref() {
            Some(oxc_ast::ast::ForStatementInit::AssignmentExpression(assignment)) => {
                vec![assignment.as_ref()]
            }
            Some(oxc_ast::ast::ForStatementInit::SequenceExpression(sequence)) => sequence
                .expressions
                .iter()
                .filter_map(|expression| {
                    let Expression::AssignmentExpression(assignment) = unparenthesized(expression)
                    else {
                        return None;
                    };
                    Some(assignment.as_ref())
                })
                .collect(),
            _ => Vec::new(),
        };
        for assignment in assignments {
            if assignment.operator.as_str() != "=" {
                continue;
            }
            let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(alias) =
                &assignment.left
            else {
                continue;
            };
            let Some(alias_reference_id) = alias.reference_id.get() else {
                continue;
            };
            let alias_reference = scoping.get_reference(alias_reference_id);
            let Some(alias_symbol) = alias_reference.symbol_id() else {
                continue;
            };
            if !alias_reference.is_write() {
                continue;
            }
            let Expression::Identifier(target) = unparenthesized(&assignment.right) else {
                continue;
            };
            let Some(target_reference_id) = target.reference_id.get() else {
                continue;
            };
            if let Some((target_name, alias_name)) = stable_rotation_alias(
                (alias_symbol, alias.name.as_str()),
                target_reference_id,
                assignment.span.end,
                Some(alias_reference_id),
                scoping,
                facts,
                reference_spans,
            ) {
                aliases.insert(target_name, alias_name);
            }
        }
    }
    aliases
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

#[derive(Default)]
struct MemberReferenceSet {
    refs: HashMap<ReferenceId, u32>,
}

impl<'a> Visit<'a> for MemberReferenceSet {
    fn visit_function(&mut self, _function: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }

    fn visit_static_member_expression(
        &mut self,
        member: &oxc_ast::ast::StaticMemberExpression<'a>,
    ) {
        if let Expression::Identifier(identifier) = &member.object {
            if let Some(reference_id) = identifier.reference_id.get() {
                self.refs.insert(reference_id, identifier.span.start);
            }
        }
        walk::walk_static_member_expression(self, member);
    }
}

fn rotation_numeric_members(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
) -> HashMap<(String, String), i64> {
    let Some(function_scope) = function.scope_id.get() else {
        return HashMap::new();
    };
    let Some(body) = &function.body else {
        return HashMap::new();
    };
    let parameter_symbols = function
        .params
        .items
        .iter()
        .filter_map(|param| match &param.pattern {
            BindingPattern::BindingIdentifier(id) => id.symbol_id.get(),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut member_refs = MemberReferenceSet::default();
    member_refs.visit_function_body(body);
    let mut out = HashMap::new();

    for statement in &body.statements {
        let Statement::ForStatement(for_statement) = statement else {
            continue;
        };
        let Some(oxc_ast::ast::ForStatementInit::SequenceExpression(sequence)) =
            &for_statement.init
        else {
            continue;
        };
        for expression in &sequence.expressions {
            let Expression::AssignmentExpression(assignment) = unparenthesized(expression) else {
                continue;
            };
            if assignment.operator.as_str() != "=" {
                continue;
            }
            let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(target) =
                &assignment.left
            else {
                continue;
            };
            let Some(reference_id) = target.reference_id.get() else {
                continue;
            };
            let reference = scoping.get_reference(reference_id);
            let Some(symbol) = reference.symbol_id() else {
                continue;
            };
            if scoping.symbol_scope_id(symbol) != function_scope
                || !parameter_symbols.contains(&symbol)
                || !reference.is_write()
            {
                continue;
            }
            let Expression::ObjectExpression(object) = unparenthesized(&assignment.right) else {
                continue;
            };
            let Some(values) = numeric_object_values(object) else {
                continue;
            };
            let safe = scoping
                .get_resolved_reference_ids(symbol)
                .iter()
                .all(|candidate| {
                    if *candidate == reference_id {
                        return true;
                    }
                    reference_is_statically_resolved_read(scoping, *candidate, symbol)
                        && member_refs
                            .refs
                            .get(candidate)
                            .is_some_and(|start| *start >= assignment.span.end)
                });
            if !safe {
                continue;
            }
            for (property, value) in values {
                out.insert((target.name.to_string(), property), value);
            }
        }
    }
    out
}

fn rotation_statement_matches(source: &str, statement: &Statement<'_>, array_alias: &str) -> bool {
    let Statement::ExpressionStatement(statement) = statement else {
        return false;
    };
    let alias = regex::escape(array_alias);
    let Some(pattern) = compile_regex(&format!(
        r#"^\s*{alias}\s*(?:\.\s*push|\[\s*["']push["']\s*\])\s*\(\s*{alias}\s*(?:\.\s*shift|\[\s*["']shift["']\s*\])\s*\(\s*\)\s*\)\s*;?\s*$"#,
    )) else {
        return false;
    };
    pattern.is_match(fragment(source, statement.span))
}

/// A closed-over rotation table must come from one statically resolved,
/// zero-argument provider function; dynamic calls cannot establish the table.
fn closed_rotation_provider_symbol(
    table_decl: &oxc_ast::ast::VariableDeclarator<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<(SymbolId, ReferenceId)> {
    let Some(Expression::CallExpression(provider_call)) = &table_decl.init else {
        return None;
    };
    if provider_call.optional || !provider_call.arguments.is_empty() {
        return None;
    }
    let Expression::Identifier(provider) = &provider_call.callee else {
        return None;
    };
    let provider_reference = provider.reference_id.get()?;
    let provider_symbol = facts.resolved_symbol(scoping, provider_reference)?;
    scoping
        .symbol_flags(provider_symbol)
        .is_function()
        .then_some((provider_symbol, provider_reference))
}

fn closed_over_rotation_iife(
    source: &str,
    call: &CallExpression<'_>,
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
    statement_span: Option<Span>,
) -> Option<RotationIife> {
    if call.optional
        || !call.arguments.is_empty()
        || function.r#async
        || function.generator
        || !function.params.items.is_empty()
        || function.params.rest.is_some()
        || rotation_has_dynamic_scope(function)
    {
        return None;
    }
    let body = function.body.as_ref()?;
    let [Statement::ForStatement(for_statement)] = body.statements.as_slice() else {
        return None;
    };
    if for_statement.test.is_some() || for_statement.update.is_some() {
        return None;
    }
    let oxc_ast::ast::ForStatementInit::VariableDeclaration(init) = for_statement.init.as_ref()?
    else {
        return None;
    };
    let [decoder_decl, table_decl] = init.declarations.as_slice() else {
        return None;
    };
    let BindingPattern::BindingIdentifier(decoder_alias) = &decoder_decl.id else {
        return None;
    };
    let Some(Expression::Identifier(decoder)) = &decoder_decl.init else {
        return None;
    };
    let decoder_reference = decoder.reference_id.get()?;
    let decoder_symbol = facts.resolved_symbol(scoping, decoder_reference)?;
    if !scoping.symbol_flags(decoder_symbol).is_function() {
        return None;
    }

    let BindingPattern::BindingIdentifier(array_alias) = &table_decl.id else {
        return None;
    };
    let (provider, provider_reference) =
        closed_rotation_provider_symbol(table_decl, scoping, facts)?;

    let Statement::TryStatement(try_statement) = &for_statement.body else {
        return None;
    };
    if try_statement.finalizer.is_some() {
        return None;
    }
    let [Statement::IfStatement(if_statement), rotate_statement] =
        try_statement.block.body.as_slice()
    else {
        return None;
    };
    if if_statement.alternate.is_some()
        || !matches!(&if_statement.consequent, Statement::BreakStatement(_))
        || !rotation_statement_matches(source, rotate_statement, array_alias.name.as_str())
    {
        return None;
    }
    let handler = try_statement.handler.as_ref()?;
    let [catch_rotate] = handler.body.body.as_slice() else {
        return None;
    };
    if !rotation_statement_matches(source, catch_rotate, array_alias.name.as_str()) {
        return None;
    }

    let Expression::BinaryExpression(check) = unparenthesized(&if_statement.test) else {
        return None;
    };
    if !matches!(check.operator.as_str(), "==" | "===") {
        return None;
    }
    let (target, checksum) = if let Some(target) = expression_integer(&check.left) {
        (target, &check.right)
    } else {
        let target = expression_integer(&check.right)?;
        (target, &check.left)
    };

    let mut stable_aliases = HashMap::new();
    stable_aliases.insert(decoder_symbol, decoder_alias.name.to_string());
    let standalone = statement_span.is_some();
    Some(RotationIife {
        provider,
        provider_reference,
        target,
        array_param: array_alias.name.to_string(),
        count_param: String::new(),
        numeric_members: HashMap::new(),
        stable_aliases,
        checksum_expression: Some(fragment(source, checksum.span()).to_string()),
        proof_eligible: true,
        body_span: body.span,
        statement_span: statement_span.unwrap_or(call.span),
        standalone_statement: standalone,
    })
}

struct RotationIifeCollector<'c, 's> {
    source: &'s str,
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    statement_spans: &'s HashMap<(u32, u32), Span>,
    reference_spans: &'s HashMap<ReferenceId, Span>,
    out: Vec<RotationIife>,
}

impl<'a> Visit<'a> for RotationIifeCollector<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if call.arguments.is_empty() {
            if let Some(function) = rotation_iife_function(&call.callee) {
                let statement_span = self
                    .statement_spans
                    .get(&(call.span.start, call.span.end))
                    .copied();
                if let Some(rotation) = closed_over_rotation_iife(
                    self.source,
                    call,
                    function,
                    self.scoping,
                    self.facts,
                    statement_span,
                ) {
                    self.out.push(rotation);
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
                if let (Some(body), Some(provider_reference)) =
                    (&function.body, provider.reference_id.get())
                {
                    let Some(provider_symbol) =
                        self.scoping.get_reference(provider_reference).symbol_id()
                    else {
                        walk::walk_call_expression(self, call);
                        return;
                    };
                    let local_params = function
                        .params
                        .items
                        .iter()
                        .map(|param| match &param.pattern {
                            BindingPattern::BindingIdentifier(id) => Some(id.name.to_string()),
                            _ => None,
                        })
                        .collect::<Option<Vec<_>>>();
                    let mut references = ExactBodyReferences {
                        scoping: self.scoping,
                        facts: self.facts,
                        valid: true,
                    };
                    references.visit_function(function, ScopeFlags::Function);
                    let proof_eligible = !function.r#async
                        && !function.generator
                        && function.params.rest.is_none()
                        && function_parameters_have_no_runtime_effects(function)
                        && local_params
                            .as_ref()
                            .is_some_and(|params| params.len() >= 2)
                        && self.facts.resolved_symbol(self.scoping, provider_reference)
                            == Some(provider_symbol)
                        && references.valid
                        && rotation_parameter_names_unshadowed(function, self.scoping)
                        && rotation_parse_int_references_are_global(function, self.scoping)
                        && !rotation_has_dynamic_scope(function);
                    let local_params = local_params.unwrap_or_default();
                    let array_param = local_params.first().cloned().unwrap_or_default();
                    let count_param = local_params.get(1).cloned().unwrap_or_default();
                    let stable_aliases = rotation_stable_aliases(
                        function,
                        self.scoping,
                        self.facts,
                        self.reference_spans,
                    );
                    let numeric_members = if proof_eligible {
                        rotation_numeric_members(function, self.scoping)
                    } else {
                        HashMap::new()
                    };
                    let standalone_statement = self
                        .statement_spans
                        .get(&(call.span.start, call.span.end))
                        .copied();
                    self.out.push(RotationIife {
                        provider: provider_symbol,
                        provider_reference,
                        target,
                        array_param,
                        count_param,
                        numeric_members,
                        stable_aliases,
                        checksum_expression: None,
                        proof_eligible,
                        body_span: body.span,
                        statement_span: standalone_statement.unwrap_or(call.span),
                        standalone_statement: standalone_statement.is_some(),
                    });
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

fn collect_rotation_iifes(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Vec<RotationIife> {
    let mut statement_spans = RotationStatementSpanCollector::default();
    statement_spans.visit_program(program);
    let mut collector = RotationIifeCollector {
        source,
        scoping,
        facts,
        statement_spans: &statement_spans.spans,
        reference_spans,
        out: Vec::new(),
    };
    collector.visit_program(program);
    collector.out
}

fn fixed_count_rotation(source: &str, iife: &RotationIife, table_len: usize) -> Option<usize> {
    if !iife.proof_eligible || iife.target < 0 || table_len == 0 {
        return None;
    }
    let identifier = r"[A-Za-z_$][A-Za-z0-9_$]*";
    let body = fragment(source, iife.body_span);
    let pattern = format!(
        r#"(?s)^\{{\s*(?:const|let|var)\s+(?P<helper>{identifier})\s*=\s*function\s*\(\s*(?P<arg>{identifier})\s*\)\s*\{{\s*while\s*\(\s*--\s*(?P<while_arg>{identifier})\s*\)\s*\{{\s*{}\s*(?:\.\s*push|\[\s*["']push["']\s*\])\s*\(\s*{}\s*(?:\.\s*shift|\[\s*["']shift["']\s*\])\s*\(\s*\)\s*\)\s*;\s*\}}\s*;?\s*\}}\s*;\s*(?P<call_helper>{identifier})\s*\(\s*\+\+\s*{}\s*\)\s*;\s*\}}\s*$"#,
        regex::escape(&iife.array_param),
        regex::escape(&iife.array_param),
        regex::escape(&iife.count_param),
    );
    let captures = compile_regex(&pattern)?.captures(body)?;
    if captures.name("helper")?.as_str() != captures.name("call_helper")?.as_str()
        || captures.name("arg")?.as_str() != captures.name("while_arg")?.as_str()
    {
        return None;
    }
    usize::try_from(iife.target)
        .ok()
        .map(|count| count % table_len)
}

fn simple_direct_decoder_offset(
    source: &str,
    function: &VariableFunctionInfo,
    array: &StaticArrayInfo,
) -> Option<i64> {
    let public_param = function.params.first()?;
    let params = function
        .params
        .iter()
        .map(|param| regex::escape(param))
        .collect::<Vec<_>>()
        .join(r"\s*,\s*");
    let identifier = r"[A-Za-z_$][A-Za-z0-9_$]*";
    let pattern = format!(
        r"(?s)^function\s*\(\s*{params}\s*\)\s*\{{\s*{}\s*=\s*{}\s*-\s*(?P<offset>0[xX][0-9A-Fa-f]+|[0-9]+)\s*;\s*(?:const|let|var)\s+(?P<value>{identifier})\s*=\s*{}\s*\[\s*{}\s*\]\s*;\s*return\s+(?P<returned>{identifier})\s*;\s*\}}\s*$",
        regex::escape(public_param),
        regex::escape(public_param),
        regex::escape(&array.name),
        regex::escape(public_param),
    );
    let captures = compile_regex(&pattern)?.captures(fragment(source, function.span))?;
    if captures.name("value")?.as_str() != captures.name("returned")?.as_str() {
        return None;
    }
    parse_i64_literal(captures.name("offset")?.as_str())
}

const fn span_contains(outer: Span, inner: Span) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

/// All table references must occur exclusively in the one rotation call
/// or the one proven decoder read, without writes or outside observers.
fn fixed_rotation_references_confined(
    array: &StaticArrayInfo,
    function: &VariableFunctionInfo,
    rotation: &RotationIife,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> bool {
    let mut decoder_reads = 0usize;
    let mut rotation_reads = 0usize;
    let mut safe_references = true;
    for reference_id in scoping.get_resolved_reference_ids(array.symbol) {
        let Some(span) = reference_spans.get(reference_id).copied() else {
            safe_references = false;
            break;
        };
        let reference = scoping.get_reference(*reference_id);
        if reference.is_write() || reference.flags().is_member_write_target() {
            safe_references = false;
            break;
        }
        if span_contains(function.span, span) {
            decoder_reads += 1;
        } else if span_contains(rotation.statement_span, span) {
            rotation_reads += 1;
        } else {
            safe_references = false;
            break;
        }
    }
    safe_references && decoder_reads == 1 && rotation_reads == 1
}

/// Candidate discovery is lexical only; semantic table and rotation
/// confinement checks remain mandatory before materializing any table.
fn fixed_rotated_candidate_names(source: &str, function: &VariableFunctionInfo) -> HashSet<String> {
    let Some(public_param) = function.params.first() else {
        return HashSet::new();
    };
    let Some(access) = DIRECT_ARRAY_ACCESS_RE.as_ref() else {
        return HashSet::new();
    };
    let body = fragment(source, function.span);
    let candidate_names = access
        .captures_iter(body)
        .filter(|captures| {
            captures
                .get(2)
                .is_some_and(|capture| capture.as_str() == public_param)
        })
        .filter_map(|captures| captures.get(1).map(|capture| capture.as_str()))
        .map(str::to_owned)
        .collect::<HashSet<_>>();

    candidate_names
}

fn detect_fixed_rotated_direct_decoders(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
    reference_spans: &HashMap<ReferenceId, Span>,
    rotations: &[RotationIife],
) -> DecoderDetection {
    let arrays = all_static_arrays(program);
    let functions = variable_functions(program);
    let mut arrays_by_name: HashMap<&str, Vec<&StaticArrayInfo>> = HashMap::new();
    for array in &arrays {
        arrays_by_name
            .entry(array.name.as_str())
            .or_default()
            .push(array);
    }
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
        let candidate_names = fixed_rotated_candidate_names(source, function);
        for array in candidate_names
            .into_iter()
            .filter_map(|name| arrays_by_name.get(name.as_str()))
            .flat_map(|candidates| candidates.iter().copied())
        {
            if !facts.source_local_data_binding(scoping, array.symbol)
                || !facts.binding_has_stable_value(scoping, function.symbol)
            {
                continue;
            }
            let Some(offset) = simple_direct_decoder_offset(source, function, array) else {
                continue;
            };
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
            let Some(amount) = fixed_count_rotation(source, rotation, array.values.len()) else {
                continue;
            };

            // The table must become observable only through the proven rotation
            // IIFE and the direct decoder. In particular, require the rotation
            // to be adjacent to the literal declaration so pre-materializing the
            // final table cannot change an intervening observation (including
            // direct eval or another aliasing call).
            let between = &source[array.span.end as usize..rotation.statement_span.start as usize];
            if !between.chars().all(|ch| ch.is_whitespace() || ch == ';') {
                continue;
            }
            if !fixed_rotation_references_confined(
                array,
                function,
                rotation,
                scoping,
                reference_spans,
            ) {
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
                start: rotation.statement_span.start as usize,
                end: rotation.statement_span.end as usize,
                text: if rotation.standalone_statement {
                    String::new()
                } else {
                    "void 0".to_string()
                },
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
                    values,
                    offset,
                    provider: array.symbol,
                    provider_array_span: array.span,
                    transform: DecoderTransform::Plain,
                },
            );
            break;
        }
    }

    (decoders, protected_spans, replacements)
}

#[derive(Debug, Clone)]
struct ProvenRotationIife {
    provider: SymbolId,
    start: usize,
    end: usize,
    standalone_statement: bool,
}

fn rotation_checksum_expression(source: &str, iife: &RotationIife) -> Option<String> {
    if let Some(expression) = &iife.checksum_expression {
        return Some(expression.clone());
    }
    let body = fragment(source, iife.body_span);
    if let Some(pattern) = compile_regex(
        r"(?s)\btry\s*\{\s*(?:var|let|const)\s+[A-Za-z_$][A-Za-z0-9_$]*\s*=\s*(?P<expr>[^;]+);",
    ) {
        if let Some(captures) = pattern.captures(body) {
            return Some(captures.name("expr")?.as_str().to_string());
        }
    }

    let identifier = r"[A-Za-z_$][A-Za-z0-9_$]*";
    let target = regex::escape(&iife.count_param);
    for pattern in [
        format!(
            r"(?s)\btry\s*\{{\s*if\s*\(\s*(?P<assigned>{identifier})\s*=\s*(?P<expr>.*?),\s*{target}\s*={{2,3}}\s*(?P<compared>{identifier})\s*\)"
        ),
        format!(
            r"(?s)\btry\s*\{{\s*if\s*\(\s*(?P<assigned>{identifier})\s*=\s*(?P<expr>.*?),\s*(?P<compared>{identifier})\s*={{2,3}}\s*{target}\s*\)"
        ),
    ] {
        let Some(pattern) = compile_regex(&pattern) else {
            continue;
        };
        let Some(captures) = pattern.captures(body) else {
            continue;
        };
        if captures.name("assigned")?.as_str() == captures.name("compared")?.as_str() {
            return Some(captures.name("expr")?.as_str().to_string());
        }
    }
    None
}

fn rotation_decoder_alias(iife: &RotationIife, decoder: SymbolId) -> Option<&str> {
    iife.stable_aliases.get(&decoder).map(String::as_str)
}

/// Rotation is a physical mutation of one provider table, not a separate
/// property of each decoder that happens to read it. Find a unique shift
/// before changing any decoder, then apply it to every equivalent view.
fn prove_rotation_iife(
    source: &str,
    iife: &RotationIife,
    decoders: &mut HashMap<SymbolId, Decoder>,
) -> bool {
    if !iife.proof_eligible {
        return false;
    }
    let body = fragment(source, iife.body_span);
    if !body.contains("push") || !body.contains("shift") {
        return false;
    }
    let Some(expression) = rotation_checksum_expression(source, iife) else {
        return false;
    };
    let mut amount = None;
    let mut table: Option<&Decoder> = None;
    for (&symbol, decoder) in decoders.iter() {
        if decoder.provider != iife.provider {
            continue;
        }
        if decoder.values.is_empty()
            || table.is_some_and(|previous| {
                previous.provider_array_span != decoder.provider_array_span
                    || !same_values(&previous.values, &decoder.values)
            })
        {
            return false;
        }
        table = Some(decoder);
        let Some(alias) = rotation_decoder_alias(iife, symbol) else {
            continue;
        };
        let mut matched = None;
        for rotation in 0..decoder.values.len() {
            let Some(value) = eval_rotation_checksum(
                &expression,
                alias,
                decoder,
                &iife.numeric_members,
                rotation,
            ) else {
                continue;
            };
            // Exact JavaScript numeric equality, not an epsilon that may
            // match a nearby but observably different checksum.
            if value.is_finite()
                && (value - js_number_from_i64(iife.target)).abs() <= 0.0
                && matched.replace(rotation).is_some()
            {
                return false;
            }
        }
        if let Some(matched) = matched {
            if amount
                .replace(matched)
                .is_some_and(|previous| previous != matched)
            {
                return false;
            }
        }
    }
    let Some(amount) = amount else {
        return false;
    };
    for decoder in decoders
        .values_mut()
        .filter(|decoder| decoder.provider == iife.provider)
    {
        decoder.values.rotate_left(amount);
    }
    true
}

fn prove_rotation_iifes(
    source: &str,
    rotation_iifes: &[RotationIife],
    decoders: &mut HashMap<SymbolId, Decoder>,
) -> Vec<ProvenRotationIife> {
    let mut proven_iifes = Vec::new();
    for iife in rotation_iifes {
        if !prove_rotation_iife(source, iife, decoders) {
            continue;
        }
        proven_iifes.push(ProvenRotationIife {
            provider: iife.provider,
            start: iife.statement_span.start as usize,
            end: iife.statement_span.end as usize,
            standalone_statement: iife.standalone_statement,
        });
    }
    proven_iifes
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
                    (decoder.provider_array_span, decoder.values.clone()),
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
                    text: if iife.standalone_statement {
                        String::new()
                    } else {
                        "void 0".to_string()
                    },
                    kind: "remove_decoder_rotation_iife",
                    arithmetic_state_proof: None,
                }),
        );
    }
    replacements
}

fn apply_proven_decoder_rotations(
    source: &str,
    decoders: &mut HashMap<SymbolId, Decoder>,
    rotation_iifes: &[RotationIife],
) -> (Vec<(usize, usize)>, Vec<Replacement>) {
    let mut proven_iifes = prove_rotation_iifes(source, rotation_iifes, decoders);

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
    (protected_spans, replacements)
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

fn decoder_providers(functions: &[FnInfo]) -> HashMap<(ScopeId, String), &FnInfo> {
    functions
        .iter()
        .filter_map(|function| {
            Some((
                (function.scope, function.name.clone()),
                function.provider.as_ref().map(|_| function)?,
            ))
        })
        .collect()
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

fn inline_self_rewriting_direct_decoder(
    source: &str,
    function: &FnInfo,
    name_counts: &HashMap<String, usize>,
    providers: &HashMap<(ScopeId, String), &FnInfo>,
) -> Option<Decoder> {
    if function.params.is_empty() || name_counts.get(&function.name).copied() != Some(1) {
        return None;
    }
    let body = fragment(source, function.span);
    // The exact self-rewriting shape below necessarily contains all three of
    // these tokens. Most application functions contain none of them together;
    // rejecting those before constructing the function-specific regex avoids
    // compiling a large automaton for every ordinary named function.
    if !body.contains("-=")
        || !body.contains("return")
        || !contains_function_reassignment(body, &function.name)
    {
        return None;
    }
    let params = function
        .params
        .iter()
        .map(|param| regex::escape(param))
        .collect::<Vec<_>>()
        .join(r"\s*,\s*");
    let first = regex::escape(function.params.first()?);
    let identifier = r"[A-Za-z_$][A-Za-z0-9_$]*";
    let pattern = compile_regex(&format!(
        r"(?s)^\s*function\s+{}\s*\(\s*{}\s*\)\s*\{{\s*(?:const|let|var)\s+(?P<table>{identifier})\s*=\s*(?P<provider>{identifier})\s*\(\s*\)\s*;\s*return\s*\(\s*{}\s*=\s*function\s*\(\s*{}\s*\)\s*\{{\s*return\s+(?P<lookup>{identifier})\s*\[\s*{}\s*-=\s*(?P<offset>0[xX][0-9A-Fa-f]+|[0-9]+)\s*\]\s*;?\s*\}}\s*\)\s*\(\s*{}\s*\)\s*;?\s*\}}\s*$",
        regex::escape(&function.name),
        params,
        regex::escape(&function.name),
        params,
        first,
        params,
    ))?;
    let captures = pattern.captures(body)?;
    if captures.name("table")?.as_str() != captures.name("lookup")?.as_str() {
        return None;
    }
    let provider = captures.name("provider")?.as_str().to_string();
    if name_counts.get(&provider).copied() != Some(1) {
        return None;
    }
    let provider = providers.get(&(function.scope, provider))?;
    let provider_info = provider.provider.as_ref()?;
    let offset = parse_i64_literal(captures.name("offset")?.as_str())?;
    Some(Decoder {
        values: provider_info.values.clone(),
        offset,
        provider: provider.symbol,
        provider_array_span: provider_info.span,
        transform: DecoderTransform::Plain,
    })
}

fn detect_decoder_candidate(
    source: &str,
    function: &FnInfo,
    patterns: &DecoderPatterns,
    name_counts: &HashMap<String, usize>,
    providers: &HashMap<(ScopeId, String), &FnInfo>,
) -> Option<Decoder> {
    if !function.parameters_proven || function.params.is_empty() {
        return None;
    }
    if let Some(shape) = &function.sequence_decoder {
        if name_counts.get(&function.name).copied() != Some(1)
            || name_counts.get(&shape.provider).copied() != Some(1)
        {
            return None;
        }
        let provider = providers.get(&(function.scope, shape.provider.clone()))?;
        if provider.symbol != shape.provider_symbol {
            return None;
        }
        let provider_info = provider.provider.as_ref()?;
        return Some(Decoder {
            values: provider_info.values.clone(),
            offset: shape.offset,
            provider: provider.symbol,
            provider_array_span: provider_info.span,
            transform: DecoderTransform::Plain,
        });
    }
    if let Some(decoder) =
        inline_self_rewriting_direct_decoder(source, function, name_counts, providers)
    {
        return Some(decoder);
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
    let provider = providers.get(&(function.scope, provider))?;
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

    // Some javascript-obfuscator-style outputs use a simpler direct static
    // accessor rather than installing a memoizing replacement. Match the whole
    // function body so arbitrary application array accessors do not qualify.
    let direct_re = compile_regex(&format!(
        r"(?s)^\s*function\s+{}\s*\([^)]*\)\s*\{{\s*{}\s*=\s*{}\s*-\s*(?:0[xX][0-9A-Fa-f]+|[0-9]+)\s*;\s*(?:const|let|var)\s+{}\s*=\s*{}\s*\(\s*\)\s*;\s*(?:const|let|var)\s+{}\s*=\s*{}\s*\[\s*{}\s*\]\s*;\s*return\s+{}\s*;\s*\}}\s*$",
        regex::escape(&function.name),
        regex::escape(&param),
        regex::escape(&param),
        regex::escape(&local_array),
        regex::escape(&provider.name),
        regex::escape(&value_var),
        regex::escape(&local_array),
        regex::escape(&param),
        regex::escape(&value_var),
    ))?;
    if !direct_re.is_match(body)
        && !(self_rewriting && (bare_value_return || sequence_value_return))
    {
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

    Some(Decoder {
        values: provider_info.values.clone(),
        offset,
        provider: provider.symbol,
        provider_array_span: provider_info.span,
        transform: decoder_transform(body, keyed_decode_call)?,
    })
}

fn propagate_decoder_aliases(
    decoders: &mut HashMap<SymbolId, Decoder>,
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) {
    let aliases = collect_symbol_aliases(program, scoping, reference_spans);
    loop {
        let mut changed = false;
        for (alias_symbol, target_symbol) in &aliases {
            if decoders.contains_key(alias_symbol) {
                continue;
            }
            if let Some(decoder) = decoders.get(target_symbol).cloned() {
                decoders.insert(*alias_symbol, decoder);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

fn detect_decoders(
    source: &str,
    functions: &[FnInfo],
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
    reference_spans: &HashMap<ReferenceId, Span>,
    rotations: &[RotationIife],
) -> DecoderDetection {
    let Some(patterns) = decoder_patterns() else {
        return (HashMap::new(), Vec::new(), Vec::new());
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
                                || reference_spans
                                    .get(&reference)
                                    .is_some_and(|span| span_contains(function.span, *span)))
                    })
            {
                return None;
            }
            let decoder =
                detect_decoder_candidate(source, function, patterns, &name_counts, &providers)?;
            let provider = functions.iter().find(|candidate| {
                candidate.symbol == decoder.provider && candidate.provider.is_some()
            })?;
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
    let (protected_spans, rotation_replacements) =
        apply_proven_decoder_rotations(source, &mut decoders, rotations);
    propagate_decoder_aliases(&mut decoders, program, scoping, reference_spans);
    (decoders, protected_spans, rotation_replacements)
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

    let rotations = collect_rotation_iifes(source, program, scoping, facts, reference_spans);
    let (mut decoders, mut protected_spans, mut replacements) = detect_decoders(
        source,
        &functions,
        program,
        scoping,
        facts,
        reference_spans,
        &rotations,
    );
    let (fixed_decoders, fixed_protected, fixed_replacements) =
        detect_fixed_rotated_direct_decoders(
            source,
            program,
            scoping,
            facts,
            reference_spans,
            &rotations,
        );
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

#[derive(Debug, Clone, Copy)]
struct DominatingForContext {
    container_span: Span,
}

#[derive(Default)]
struct DirectForContextCollector {
    contexts: HashMap<(u32, u32), DominatingForContext>,
}

impl DirectForContextCollector {
    fn collect_statements(&mut self, statements: &[Statement<'_>], container_span: Span) {
        let Some(Statement::ForStatement(for_statement)) = statements.first() else {
            return;
        };
        self.contexts.insert(
            (for_statement.span.start, for_statement.span.end),
            DominatingForContext { container_span },
        );
    }
}

impl<'a> Visit<'a> for DirectForContextCollector {
    fn visit_program(&mut self, program: &oxc_ast::ast::Program<'a>) {
        self.collect_statements(&program.body, program.span);
        walk::walk_program(self, program);
    }

    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if let Some(body) = &function.body {
            self.collect_statements(&body.statements, body.span);
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        walk::walk_arrow_function_expression(self, function);
    }
}

struct SymbolAliasCollector<'s, 'r> {
    scoping: &'s Scoping,
    reference_spans: &'r HashMap<ReferenceId, Span>,
    for_contexts: &'r HashMap<(u32, u32), DominatingForContext>,
    aliases: Vec<(SymbolId, SymbolId)>,
}

impl<'a> Visit<'a> for SymbolAliasCollector<'_, '_> {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        // Nested aliases stay const-only. Mutable aliases need an explicit
        // execution-order proof and are handled separately at program scope.
        if it.kind != VariableDeclarationKind::Const {
            walk::walk_variable_declaration(self, it);
            return;
        }
        for d in &it.declarations {
            let BindingPattern::BindingIdentifier(alias) = &d.id else {
                continue;
            };
            let Some(alias_symbol) = alias.symbol_id.get() else {
                continue;
            };
            let Some(Expression::Identifier(target)) = &d.init else {
                continue;
            };
            let Some(reference_id) = target.reference_id.get() else {
                continue;
            };
            let Some(target_symbol) = statically_resolved_symbol(self.scoping, reference_id) else {
                continue;
            };
            self.aliases.push((alias_symbol, target_symbol));
        }
        walk::walk_variable_declaration(self, it);
    }

    fn visit_for_statement(&mut self, it: &oxc_ast::ast::ForStatement<'a>) {
        let Some(context) = self.for_contexts.get(&(it.span.start, it.span.end)) else {
            walk::walk_for_statement(self, it);
            return;
        };
        let assignments = match it.init.as_ref() {
            Some(oxc_ast::ast::ForStatementInit::AssignmentExpression(assignment)) => {
                vec![assignment.as_ref()]
            }
            Some(oxc_ast::ast::ForStatementInit::SequenceExpression(sequence)) => sequence
                .expressions
                .first()
                .and_then(|expression| {
                    let Expression::AssignmentExpression(assignment) = unparenthesized(expression)
                    else {
                        return None;
                    };
                    Some(vec![assignment.as_ref()])
                })
                .unwrap_or_default(),
            _ => Vec::new(),
        };

        for assignment in assignments {
            if assignment.operator.as_str() != "=" {
                continue;
            }
            let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(alias) =
                &assignment.left
            else {
                continue;
            };
            let Some(alias_reference_id) = alias.reference_id.get() else {
                continue;
            };
            let alias_reference = self.scoping.get_reference(alias_reference_id);
            let Some(alias_symbol) = alias_reference.symbol_id() else {
                continue;
            };
            if !alias_reference.is_write() {
                continue;
            }
            let Expression::Identifier(target) = unparenthesized(&assignment.right) else {
                continue;
            };
            let Some(target_reference_id) = target.reference_id.get() else {
                continue;
            };
            let Some(target_symbol) = statically_resolved_symbol(self.scoping, target_reference_id)
            else {
                continue;
            };
            if alias_symbol == target_symbol
                || !symbol_has_only_read_references(self.scoping, target_symbol)
            {
                continue;
            }
            let stable = self
                .scoping
                .get_resolved_reference_ids(alias_symbol)
                .iter()
                .all(|reference_id| {
                    if *reference_id == alias_reference_id {
                        return true;
                    }
                    let Some(span) = self.reference_spans.get(reference_id) else {
                        return false;
                    };
                    context.container_span.start <= span.start
                        && span.end <= context.container_span.end
                        && span.start >= assignment.span.end
                        && reference_is_statically_resolved_read(
                            self.scoping,
                            *reference_id,
                            alias_symbol,
                        )
                });
            if stable {
                self.aliases.push((alias_symbol, target_symbol));
            }
        }

        walk::walk_for_statement(self, it);
    }
}

fn leading_mutable_aliases_in_statements(
    statements: &[Statement<'_>],
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Vec<(SymbolId, SymbolId)> {
    let first_executable = statements.iter().find(|statement| {
        !matches!(
            statement,
            Statement::FunctionDeclaration(_) | Statement::EmptyStatement(_)
        )
    });
    let Some(Statement::VariableDeclaration(declaration)) = first_executable else {
        return Vec::new();
    };
    if declaration.kind == VariableDeclarationKind::Const {
        return Vec::new();
    }

    let mut aliases = Vec::new();
    let mut prior_initializer = false;
    for declarator in &declaration.declarations {
        let candidate = if prior_initializer {
            None
        } else {
            let BindingPattern::BindingIdentifier(alias) = &declarator.id else {
                prior_initializer |= declarator.init.is_some();
                continue;
            };
            let Some(alias_symbol) = alias.symbol_id.get() else {
                prior_initializer |= declarator.init.is_some();
                continue;
            };
            let Some(Expression::Identifier(target)) = &declarator.init else {
                prior_initializer |= declarator.init.is_some();
                continue;
            };
            let Some(target_reference_id) = target.reference_id.get() else {
                prior_initializer = true;
                continue;
            };
            let Some(target_symbol) = statically_resolved_symbol(scoping, target_reference_id)
            else {
                prior_initializer = true;
                continue;
            };
            if target_symbol == alias_symbol {
                prior_initializer = true;
                continue;
            }
            let stable =
                scoping
                    .get_resolved_reference_ids(alias_symbol)
                    .iter()
                    .all(|reference_id| {
                        reference_spans.get(reference_id).is_some_and(|span| {
                            span.start >= declarator.span.end
                                && reference_is_statically_resolved_read(
                                    scoping,
                                    *reference_id,
                                    alias_symbol,
                                )
                        })
                    });
            stable.then_some((alias_symbol, target_symbol))
        };
        if let Some(alias) = candidate {
            aliases.push(alias);
        }
        prior_initializer |= declarator.init.is_some();
    }
    aliases
}

struct LeadingMutableAliasCollector<'s, 'r> {
    scoping: &'s Scoping,
    reference_spans: &'r HashMap<ReferenceId, Span>,
    aliases: Vec<(SymbolId, SymbolId)>,
}

impl<'a> Visit<'a> for LeadingMutableAliasCollector<'_, '_> {
    fn visit_program(&mut self, program: &oxc_ast::ast::Program<'a>) {
        let mut dynamic_scope = RotationDynamicScopeProbe::default();
        dynamic_scope.visit_program(program);
        if !dynamic_scope.found {
            self.aliases.extend(leading_mutable_aliases_in_statements(
                &program.body,
                self.scoping,
                self.reference_spans,
            ));
        }
        walk::walk_program(self, program);
    }

    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if !rotation_has_dynamic_scope(function) {
            if let Some(body) = &function.body {
                self.aliases.extend(leading_mutable_aliases_in_statements(
                    &body.statements,
                    self.scoping,
                    self.reference_spans,
                ));
            }
        }
        walk::walk_function(self, function, flags);
    }
}

fn collect_symbol_aliases(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Vec<(SymbolId, SymbolId)> {
    let mut context_collector = DirectForContextCollector::default();
    context_collector.visit_program(program);
    let mut collector = SymbolAliasCollector {
        scoping,
        reference_spans,
        for_contexts: &context_collector.contexts,
        aliases: Vec::new(),
    };
    collector.visit_program(program);
    let mut mutable_collector = LeadingMutableAliasCollector {
        scoping,
        reference_spans,
        aliases: Vec::new(),
    };
    mutable_collector.visit_program(program);
    collector.aliases.extend(mutable_collector.aliases);
    collector.aliases
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn function_reassignment_probe_handles_spacing_without_suffix_matches() {
        assert!(contains_function_reassignment("f=function(){}", "f"));
        assert!(contains_function_reassignment(
            "f   =
 function(){}",
            "f"
        ));
        assert!(!contains_function_reassignment(
            "other_f = function(){}",
            "f"
        ));
        assert!(!contains_function_reassignment("f == function(){}", "f"));
    }

    #[test]
    fn rotation_decoder_alias_requires_proven_binding() {
        let base = RotationIife {
            provider: SymbolId::new(0),
            provider_reference: ReferenceId::new(0),
            target: 1,
            array_param: "array".into(),
            count_param: "target".into(),
            numeric_members: HashMap::new(),
            stable_aliases: HashMap::from([(SymbolId::new(1), "alias".into())]),
            checksum_expression: None,
            proof_eligible: true,
            body_span: Span::new(0, 0),
            statement_span: Span::new(0, 0),
            standalone_statement: true,
        };
        assert_eq!(
            rotation_decoder_alias(&base, SymbolId::new(1)),
            Some("alias")
        );

        let mut unproven_alias = base;
        unproven_alias.stable_aliases.clear();
        assert_eq!(
            rotation_decoder_alias(&unproven_alias, SymbolId::new(1)),
            None
        );
    }

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
            ],
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
        let source = "push shift";
        let iife = RotationIife {
            provider,
            provider_reference: ReferenceId::new(0),
            target: 22,
            array_param: "array".into(),
            count_param: "target".into(),
            numeric_members: HashMap::new(),
            stable_aliases: HashMap::from([(first, "alias".into())]),
            checksum_expression: Some("parseInt(alias(0))".into()),
            proof_eligible: true,
            body_span: Span::new(0, 10),
            statement_span: Span::new(0, 10),
            standalone_statement: true,
        };
        assert!(prove_rotation_iife(source, &iife, &mut decoders));
        for symbol in [first, second] {
            assert!(
                matches!(decoders[&symbol].value_for_call(0, None), Some(Value::String(value)) if value == "22")
            );
        }
        assert!(
            matches!(decoders[&unrelated].value_for_call(0,None),Some(Value::String(value)) if value == "11")
        );
        let mut invalid = decoders.clone();
        invalid
            .get_mut(&second)
            .unwrap_or_else(|| unreachable!())
            .values
            .rotate_left(1);
        assert!(!prove_rotation_iife(source, &iife, &mut invalid));
        assert!(
            matches!(invalid[&first].value_for_call(0,None),Some(Value::String(value)) if value == "22")
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
            ],
            offset: 0x10,
            provider: SymbolId::new(0),
            provider_array_span: Span::new(0, 0),
            transform: DecoderTransform::LowerAlphabetBase64Rc4,
        };
        assert_eq!(
            eval_rotation_checksum(
                "parseInt(G(0x10, 'k')) * 10 + parseInt(G(0x11, \"k\"))",
                "G",
                &decoder,
                &HashMap::new(),
                3,
            ),
            Some(193.0)
        );
        assert_eq!(
            eval_rotation_checksum(
                "parseInt(G(/* static index */ 0x0f + 1, '\\u006b')) * 10 + parseInt(G(0x11, 'k'))",
                "G",
                &decoder,
                &HashMap::new(),
                3,
            ),
            Some(193.0)
        );
        assert_eq!(
            eval_rotation_checksum(
                "parseInt(G(0x10, dynamic))",
                "G",
                &decoder,
                &HashMap::new(),
                3,
            ),
            None
        );
        assert_eq!(
            eval_rotation_checksum(
                "parseInt(G(sideEffect(), 'k'))",
                "G",
                &decoder,
                &HashMap::new(),
                3,
            ),
            None
        );
    }
}
