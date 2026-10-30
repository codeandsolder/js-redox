use crate::decoder_encoding::{
    decode_fixed_base64_latin1, decode_lower_alphabet_base64_rc4, decode_lower_alphabet_base64_uri,
    decode_standard_base64_latin1,
};
use crate::rewrite::Replacement;
use crate::value_eval::{eval, js_to_uint32, render_value_array, same_values, Value};
use crate::{
    argument_integer, array_element, decoder_argument_integer, expression_integer, fragment,
    reference_is_statically_resolved_read, statically_resolved_symbol, string_literal_value,
    symbol_has_only_read_references, symbol_of, template_element_value,
};
use oxc_ast::ast::{
    Argument, BindingPattern, CallExpression, Expression, ExpressionStatement, Statement,
    VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::{GetSpan, Span};
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::{
    collections::{HashMap, HashSet},
    sync::LazyLock,
};

/// Convert an integer into the JavaScript Number domain. Precision loss above
/// 2^53 is intentional here: JavaScript itself stores the value as IEEE-754 f64.
#[allow(clippy::cast_precision_loss)]
const fn js_number_from_u64(value: u64) -> f64 {
    value as f64
}

/// Signed counterpart; rounding is intentional JavaScript Number semantics.
#[allow(clippy::cast_precision_loss)]
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
    name: String,
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
                    oxc_ast::ast::ArrayExpressionElement::Elision(_) => Some(Value::Undefined),
                    _ => array_element(element),
                };
                values.push(value);
            }
            if valid && !values.is_empty() && values.iter().any(Option::is_some) {
                self.candidates.push(PartialStaticArrayInfo {
                    symbol,
                    name: id.name.to_string(),
                    values,
                });
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

fn decoder_static_arrays(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> Vec<StaticArrayInfo> {
    let mut candidates = all_static_arrays(program);
    candidates.retain(|candidate| symbol_has_only_read_references(scoping, candidate.symbol));
    candidates
}

#[derive(Default)]
struct DirectCallCounter {
    count: usize,
}

impl<'a> Visit<'a> for DirectCallCounter {
    fn visit_call_expression(&mut self, it: &CallExpression<'a>) {
        self.count += 1;
        walk::walk_call_expression(self, it);
    }

    fn visit_function(&mut self, _f: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {
        // Nested functions do not execute as part of the candidate decoder
        // invocation itself, so do not count calls inside them.
    }
}

fn direct_body_call_count(body: &oxc_ast::ast::FunctionBody<'_>) -> usize {
    let mut counter = DirectCallCounter::default();
    for statement in &body.statements {
        counter.visit_statement(statement);
    }
    counter.count
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
                } else if property == "fromCharCode" {
                    matches!(&member.object, Expression::Identifier(object)
                        if object.name.as_str() == "String"
                            && symbol_of(self.scoping, &member.object).is_none())
                } else {
                    false
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
    offset: i64,
}

#[derive(Debug)]
struct FnInfo {
    name: String,
    symbol: SymbolId,
    scope: ScopeId,
    params: Vec<String>,
    span: Span,
    static_arrays: HashMap<String, LocalStaticArrayInfo>,
    split_provider: Option<LocalStaticArrayInfo>,
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

fn self_rewriting_split_provider(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
) -> Option<LocalStaticArrayInfo> {
    if function.r#async || function.generator || function.params.rest.is_some() {
        return None;
    }
    let [param] = function.params.items.as_slice() else {
        return None;
    };
    let BindingPattern::BindingIdentifier(param) = &param.pattern else {
        return None;
    };
    let param_symbol = param.symbol_id.get()?;
    let provider_id = function.id.as_ref()?;
    let provider_symbol = provider_id.symbol_id.get()?;
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
    let [table_assignment, rewrite_assignment, tail_call] = sequence.expressions.as_slice() else {
        return None;
    };

    let (table_target, table_value) = assignment_identifier(table_assignment)?;
    if statically_resolved_symbol(scoping, table_target.reference_id.get()?) != Some(param_symbol) {
        return None;
    }
    let table = static_string_split(table_value)?;

    let (rewrite_target, rewrite_value) = assignment_identifier(rewrite_assignment)?;
    let rewrite_reference_id = rewrite_target.reference_id.get()?;
    if statically_resolved_symbol(scoping, rewrite_reference_id) != Some(provider_symbol)
        || !scoping.get_reference(rewrite_reference_id).is_write()
    {
        return None;
    }
    let Expression::FunctionExpression(replacement) = unparenthesized(rewrite_value) else {
        return None;
    };
    if replacement.r#async
        || replacement.generator
        || !replacement.params.items.is_empty()
        || replacement.params.rest.is_some()
    {
        return None;
    }
    let replacement_body = replacement.body.as_ref()?;
    if !replacement_body.directives.is_empty() || replacement_body.statements.len() != 1 {
        return None;
    }
    let Statement::ReturnStatement(replacement_return) = &replacement_body.statements[0] else {
        return None;
    };
    let Expression::Identifier(returned) = unparenthesized(replacement_return.argument.as_ref()?)
    else {
        return None;
    };
    if statically_resolved_symbol(scoping, returned.reference_id.get()?) != Some(param_symbol) {
        return None;
    }

    let Expression::CallExpression(call) = unparenthesized(tail_call) else {
        return None;
    };
    if call.optional || !call.arguments.is_empty() {
        return None;
    }
    let Expression::Identifier(callee) = unparenthesized(&call.callee) else {
        return None;
    };
    if statically_resolved_symbol(scoping, callee.reference_id.get()?) != Some(provider_symbol) {
        return None;
    }

    let stable_provider = scoping
        .get_resolved_reference_ids(provider_symbol)
        .iter()
        .all(|reference_id| {
            if *reference_id == rewrite_reference_id {
                return true;
            }
            reference_is_statically_resolved_read(scoping, *reference_id, provider_symbol)
        });
    stable_provider.then_some(table)
}

fn sequence_decoder_shape(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
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
    let offset = expression_integer(&offset_binary.right)?;

    let (table_target, table_value) = assignment_identifier(table_assignment)?;
    let table_symbol = statically_resolved_symbol(scoping, table_target.reference_id.get()?)?;
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
    statically_resolved_symbol(scoping, provider.reference_id.get()?)?;

    let (value_target, value_expression) = assignment_identifier(value_assignment)?;
    let value_symbol = statically_resolved_symbol(scoping, value_target.reference_id.get()?)?;
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
    if statically_resolved_symbol(scoping, table_read.reference_id.get()?) != Some(table_symbol)
        || statically_resolved_symbol(scoping, index_read.reference_id.get()?)
            != Some(public_param_symbol)
    {
        return None;
    }
    let Expression::Identifier(returned) = unparenthesized(returned) else {
        return None;
    };
    if statically_resolved_symbol(scoping, returned.reference_id.get()?) != Some(value_symbol) {
        return None;
    }

    Some(SequenceDecoderShape {
        provider: provider.name.to_string(),
        offset,
    })
}

fn function_info(f: &oxc_ast::ast::Function<'_>, scoping: &Scoping) -> Option<FnInfo> {
    if f.r#type != oxc_ast::ast::FunctionType::FunctionDeclaration {
        return None;
    }
    let id = f.id.as_ref()?;
    let symbol = id.symbol_id.get()?;
    let params = f
        .params
        .items
        .iter()
        .filter_map(|p| match &p.pattern {
            BindingPattern::BindingIdentifier(id) => Some(id.name.to_string()),
            _ => None,
        })
        .collect();

    let mut static_arrays = HashMap::new();
    if let Some(body) = &f.body {
        for stmt in &body.statements {
            let Statement::VariableDeclaration(decl) = stmt else {
                continue;
            };
            for d in &decl.declarations {
                let BindingPattern::BindingIdentifier(array_id) = &d.id else {
                    continue;
                };
                let Some(Expression::ArrayExpression(array)) = &d.init else {
                    continue;
                };
                let Some(values) = array
                    .elements
                    .iter()
                    .map(array_element)
                    .collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                if !values.is_empty() {
                    static_arrays.insert(
                        array_id.name.to_string(),
                        LocalStaticArrayInfo {
                            values,
                            span: array.span,
                        },
                    );
                }
            }
        }
    }

    Some(FnInfo {
        name: id.name.to_string(),
        symbol,
        scope: scoping.symbol_scope_id(symbol),
        params,
        span: f.span,
        static_arrays,
        split_provider: self_rewriting_split_provider(f, scoping),
        sequence_decoder: sequence_decoder_shape(f, scoping),
    })
}

struct FunctionDeclarationCollector<'s> {
    scoping: &'s Scoping,
    out: Vec<FnInfo>,
}

impl<'a> Visit<'a> for FunctionDeclarationCollector<'_> {
    fn visit_function(
        &mut self,
        it: &oxc_ast::ast::Function<'a>,
        flags: oxc_syntax::scope::ScopeFlags,
    ) {
        if let Some(info) = function_info(it, self.scoping) {
            self.out.push(info);
        }
        walk::walk_function(self, it, flags);
    }
}

fn all_function_declarations(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> Vec<FnInfo> {
    let mut collector = FunctionDeclarationCollector {
        scoping,
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
        if is_base64_alphabet(&value) && !used_aliases.is_empty() {
            self.candidates.push((value, used_aliases));
        }
    }
}

impl<'a> Visit<'a> for FixedAlphabetProbe<'_> {
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

    fn string_literal_via_aliases(
        expression: &Expression<'_>,
        scoping: &Scoping,
        aliases: &HashMap<SymbolId, u32>,
    ) -> bool {
        let mut used = HashSet::new();
        eval_from_char_code_concat(expression, scoping, aliases, &mut used).as_deref()
            == Some("string")
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
        let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(alias) = &assignment.left
        else {
            return None;
        };
        let Expression::ComputedMemberExpression(member) = unparenthesized(&assignment.right)
        else {
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

    let guard = if let Some(parts) = typeof_table_assignment(&test.left) {
        string_literal_via_aliases(&test.right, scoping, aliases).then_some(parts)
    } else if let Some(parts) = typeof_table_assignment(&test.right) {
        string_literal_via_aliases(&test.left, scoping, aliases).then_some(parts)
    } else if string_literal_via_aliases(&test.right, scoping, aliases) {
        typeof_identifier(&test.left).and_then(|alias| {
            preceding_table_load(body, alias).map(|(table, index)| (alias, table, index))
        })
    } else if string_literal_via_aliases(&test.left, scoping, aliases) {
        typeof_identifier(&test.right).and_then(|alias| {
            preceding_table_load(body, alias).map(|(table, index)| (alias, table, index))
        })
    } else {
        None
    };
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

#[derive(Debug)]
struct DirectFnInfo {
    symbol: SymbolId,
    params: Vec<String>,
    span: Span,
    body_statement_count: usize,
    direct_call_count: usize,
    fixed_decoder_control_shape: bool,
    fixed_decoder_iife_control_shape: bool,
    fixed_base64_alphabet: Option<String>,
}

struct DirectFnInfoCollector<'c> {
    scoping: &'c Scoping,
    aliases: &'c HashMap<SymbolId, u32>,
    reference_spans: &'c HashMap<ReferenceId, Span>,
    out: Vec<DirectFnInfo>,
}

impl<'a> Visit<'a> for DirectFnInfoCollector<'_> {
    fn visit_function(&mut self, f: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if let Some(id) = &f.id {
            if let Some(symbol) = id.symbol_id.get() {
                let params = f
                    .params
                    .items
                    .iter()
                    .filter_map(|p| match &p.pattern {
                        BindingPattern::BindingIdentifier(id) => Some(id.name.to_string()),
                        _ => None,
                    })
                    .collect();

                self.out.push(DirectFnInfo {
                    symbol,
                    params,
                    span: f.span,
                    body_statement_count: f.body.as_ref().map_or(0, |body| body.statements.len()),
                    direct_call_count: f
                        .body
                        .as_ref()
                        .map_or(0, |body| direct_body_call_count(body)),
                    fixed_decoder_control_shape: f
                        .body
                        .as_ref()
                        .is_some_and(|body| fixed_decoder_control_shape(body)),
                    fixed_decoder_iife_control_shape: fixed_decoder_iife_wrapper_proven(
                        f,
                        self.scoping,
                        self.aliases,
                    ),
                    fixed_base64_alphabet: fixed_alphabet_for_function(
                        f,
                        symbol,
                        self.scoping,
                        self.aliases,
                        self.reference_spans,
                    ),
                });
            }
        }
        walk::walk_function(self, f, flags);
    }
}

fn all_functions(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    aliases: &HashMap<SymbolId, u32>,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Vec<DirectFnInfo> {
    let mut collector = DirectFnInfoCollector {
        scoping,
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
    provider: String,
    provider_array_span: Span,
    transform: DecoderTransform,
}

impl Decoder {
    fn transform_value(&self, value: Value, key: Option<&str>) -> Option<Value> {
        match (&self.transform, value) {
            (DecoderTransform::LowerAlphabetBase64Uri, Value::String(encoded)) => {
                decode_lower_alphabet_base64_uri(&encoded).map(Value::String)
            }
            (DecoderTransform::LowerAlphabetBase64Uri, _) => None,
            (DecoderTransform::LowerAlphabetBase64Rc4, Value::String(encoded)) => {
                decode_lower_alphabet_base64_rc4(&encoded, key?).map(Value::String)
            }
            (DecoderTransform::LowerAlphabetBase64Rc4, _) => None,
            (DecoderTransform::StandardBase64, Value::String(encoded)) => {
                decode_standard_base64_latin1(&encoded).map(Value::String)
            }
            (DecoderTransform::StandardBase64, _) => None,
            (DecoderTransform::FixedBase64Alphabet(alphabet), Value::String(encoded)) => {
                decode_fixed_base64_latin1(&encoded, alphabet).map(Value::String)
            }
            (DecoderTransform::Plain | DecoderTransform::FixedBase64Alphabet(_), value) => {
                Some(value)
            }
        }
    }

    fn value_for_raw_rotated_with_key(
        &self,
        raw: i64,
        rotation: usize,
        key: Option<&str>,
    ) -> Option<Value> {
        let index = raw - self.offset;
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
        self.transform_value(self.values.get(index)?.clone(), key)
    }

    pub(super) fn value_for_call(&self, raw: i64, key: Option<&str>) -> Option<Value> {
        self.value_for_raw_rotated_with_key(raw, 0, key)
    }
}

pub(super) struct DecoderCallRewrite {
    pub(super) text: String,
    pub(super) stop: bool,
}

pub(super) fn decoder_call_rewrite(
    source: &str,
    scoping: &Scoping,
    decoders: &HashMap<SymbolId, Decoder>,
    call: &CallExpression<'_>,
) -> Option<DecoderCallRewrite> {
    if call.optional
        || !(1..=2).contains(&call.arguments.len())
        || call.arguments.iter().any(Argument::is_spread)
    {
        return None;
    }
    let symbol = symbol_of(scoping, &call.callee)?;
    let decoder = decoders.get(&symbol)?;
    let key = match call.arguments.get(1) {
        Some(Argument::StringLiteral(literal)) => Some(string_literal_value(literal)?),
        Some(_) => return None,
        None => None,
    };
    let argument = call.arguments.first()?;
    if let Some(raw) = decoder_argument_integer(argument) {
        let text = decoder
            .value_for_call(raw, key.as_deref())
            .and_then(|value| value.render())?;
        return Some(DecoderCallRewrite { text, stop: false });
    }

    let Argument::ConditionalExpression(conditional) = argument else {
        return None;
    };
    let consequent = expression_integer(&conditional.consequent)
        .and_then(|raw| decoder.value_for_call(raw, key.as_deref()))
        .and_then(|value| value.render())?;
    let alternate = expression_integer(&conditional.alternate)
        .and_then(|raw| decoder.value_for_call(raw, key.as_deref()))
        .and_then(|value| value.render())?;
    let test = fragment(source, conditional.test.span());
    Some(DecoderCallRewrite {
        text: format!("(({test}) ? ({consequent}) : ({alternate}))"),
        stop: true,
    })
}

struct DecoderOnlyCallCollector<'c> {
    source: &'c str,
    scoping: &'c Scoping,
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
        let Some(rewrite) = decoder_call_rewrite(self.source, self.scoping, self.decoders, call)
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

pub(super) struct StaticDecoderPass {
    pub(super) replacements: Vec<Replacement>,
    pub(super) decoder_count: usize,
}

pub(super) fn static_decoder_pass(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> StaticDecoderPass {
    let analysis = analyze_decoders(source, program, scoping, reference_spans);
    let decoder_count = analysis.decoders.len();
    let mut collector = DecoderOnlyCallCollector {
        source,
        scoping,
        decoders: &analysis.decoders,
        protected_spans: &analysis.protected_spans,
        replacements: analysis.replacements,
    };
    collector.visit_program(program);
    StaticDecoderPass {
        replacements: collector.replacements,
        decoder_count,
    }
}

fn compile_regex(pattern: &str) -> Option<regex::Regex> {
    regex::Regex::new(pattern).ok()
}

static FIXED_BASE64_ALPHABET_RE: LazyLock<Option<regex::Regex>> =
    LazyLock::new(|| compile_regex(r#"["']([A-Za-z0-9+/=]{65})["']"#));
static BASE64_SENTINEL_RE: LazyLock<Option<regex::Regex>> =
    LazyLock::new(|| compile_regex(r"(?:64\s*!=|!=\s*64)"));
static RC4_CHAR_CODE_AT_RE: LazyLock<Option<regex::Regex>> = LazyLock::new(|| {
    compile_regex(r"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*\.\s*charCodeAt\s*\(([^)]*)\)")
});
static DIRECT_ARRAY_ACCESS_RE: LazyLock<Option<regex::Regex>> =
    LazyLock::new(|| compile_regex(r"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*\[\s*([^\s\]]+)\s*\]"));

fn fixed_base64_alphabet(body: &str) -> Option<String> {
    if !body.contains("String.fromCharCode")
        || !body.contains(".indexOf")
        || !body.contains(".charAt")
    {
        return None;
    }
    let re = FIXED_BASE64_ALPHABET_RE.as_ref()?;
    let standard = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="
        .chars()
        .collect::<HashSet<_>>();
    let mut candidates = re
        .captures_iter(body)
        .filter_map(|caps| caps.get(1).map(|capture| capture.as_str().to_string()))
        .filter(|candidate| candidate.chars().collect::<HashSet<_>>() == standard)
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.dedup();
    (candidates.len() == 1).then(|| candidates.remove(0))
}

fn function_inner_source(body: &str) -> Option<&str> {
    let start = body.find('{')?.checked_add(1)?;
    let end = body.rfind('}')?;
    (start <= end).then(|| &body[start..end])
}

fn standard_base64_decoder_matches(body: &str, array: &str, param: &str) -> bool {
    let Some(inner) = function_inner_source(body) else {
        return false;
    };

    // Match the complete function body, not merely a decoder-looking
    // expression somewhere inside it. Replacing a call removes the entire
    // function execution, so accepting extra statements could silently drop
    // observable side effects.
    let Some(direct) = compile_regex(&format!(
        r"(?s)^\s*return\s+atob\s*\(\s*{}\s*\[\s*{}\s*\]\s*\)\s*;?\s*$",
        regex::escape(array),
        regex::escape(param)
    )) else {
        return false;
    };
    if direct.is_match(inner) {
        return true;
    }

    let Some(sequence) = compile_regex(&format!(
        r"(?s)^\s*return\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*{}\s*\[\s*{}\s*\]\s*,\s*atob\s*\(\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\)\s*;?\s*$",
        regex::escape(array),
        regex::escape(param)
    )) else {
        return false;
    };
    if sequence
        .captures(inner)
        .is_some_and(|caps| caps.get(1).map(|m| m.as_str()) == caps.get(2).map(|m| m.as_str()))
    {
        return true;
    }

    let Some(assignment) = compile_regex(&format!(
        r"(?s)^\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*{}\s*\[\s*{}\s*\]\s*;\s*return\s+atob\s*\(\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\)\s*;?\s*$",
        regex::escape(array),
        regex::escape(param)
    )) else {
        return false;
    };
    assignment
        .captures(inner)
        .is_some_and(|caps| caps.get(1).map(|m| m.as_str()) == caps.get(2).map(|m| m.as_str()))
}

fn fixed_base64_decoder_matches(
    body: &str,
    array: &str,
    param: &str,
    alphabet_hint: Option<&str>,
    iife_wrapper_proven: bool,
) -> Option<String> {
    let alphabet = fixed_base64_alphabet(body).or_else(|| alphabet_hint.map(str::to_owned))?;
    let guarded_load = compile_regex(&format!(
        r"typeof\s*\(?\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*{}\s*\[\s*{}\s*\]\s*\)?",
        regex::escape(array),
        regex::escape(param)
    ))?;

    if let Some(alias) = guarded_load
        .captures_iter(body)
        .find_map(|caps| caps.get(1).map(|m| m.as_str()))
    {
        let return_alias = compile_regex(&format!(r"\breturn\s+{}\s*;", regex::escape(alias)))?;
        if !return_alias.is_match(body) && !iife_wrapper_proven {
            return None;
        }
    } else if !iife_wrapper_proven {
        return None;
    }

    // Fail closed on a recognizable Base64 decoder shape rather than merely
    // seeing an alphabet and String.fromCharCode somewhere in the function.
    if !body.contains(".replace(/[^A-Za-z0-9\\+\\/\\=]/g")
        || body.matches(".indexOf(").count() != 4
        || body.matches(".charAt(").count() != 4
        || body.matches("String.fromCharCode").count() != 3
        || body.matches("<<").count() != 3
        || body.matches(">>").count() != 2
    {
        return None;
    }
    let sentinel_checks = BASE64_SENTINEL_RE.as_ref()?;
    if sentinel_checks.find_iter(body).count() != 2 {
        return None;
    }

    Some(alphabet)
}

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

#[derive(Debug, Clone)]
struct SparseDirectDecoder {
    values: Vec<Option<Value>>,
    transform: DecoderTransform,
}

impl SparseDirectDecoder {
    fn value_for_raw(&self, raw: i64) -> Option<Value> {
        let index = usize::try_from(raw).ok()?;
        let value = self.values.get(index)?.clone()?;
        match (&self.transform, value) {
            (DecoderTransform::StandardBase64, Value::String(encoded)) => {
                decode_standard_base64_latin1(&encoded).map(Value::String)
            }
            (DecoderTransform::FixedBase64Alphabet(alphabet), Value::String(encoded)) => {
                decode_fixed_base64_latin1(&encoded, alphabet).map(Value::String)
            }
            (DecoderTransform::FixedBase64Alphabet(_), value) => Some(value),
            // Sparse direct decoding is intentionally limited to the two exact
            // direct-decoder shapes proved here. Rotation/offset decoders stay
            // on the complete-table path above.
            _ => None,
        }
    }
}

fn detect_sparse_direct_table_decoders(
    source: &str,
    functions: &[DirectFnInfo],
    arrays: &[PartialStaticArrayInfo],
    complete_decoders: &HashMap<SymbolId, Decoder>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<SymbolId, SparseDirectDecoder> {
    let mut arrays_by_name: HashMap<&str, Vec<&PartialStaticArrayInfo>> = HashMap::new();
    for array in arrays {
        arrays_by_name
            .entry(array.name.as_str())
            .or_default()
            .push(array);
    }

    let mut out = HashMap::new();
    for function in functions {
        if complete_decoders.contains_key(&function.symbol)
            || scoping
                .get_resolved_reference_ids(function.symbol)
                .iter()
                .any(|reference_id| scoping.get_reference(*reference_id).is_write())
        {
            continue;
        }
        let Some(param) = function.params.first() else {
            continue;
        };
        let body = fragment(source, function.span);
        let Some(access) = DIRECT_ARRAY_ACCESS_RE.as_ref() else {
            continue;
        };
        let mut matched = access
            .captures_iter(body)
            .filter(|caps| caps.get(2).is_some_and(|capture| capture.as_str() == param))
            .filter_map(|caps| caps.get(1).map(|capture| capture.as_str()))
            .filter_map(|name| arrays_by_name.get(name))
            .flat_map(|candidates| candidates.iter().copied())
            .filter(|array| {
                let references = scoping.get_resolved_reference_ids(array.symbol);
                let [reference_id] = references else {
                    return false;
                };
                reference_spans.get(reference_id).is_some_and(|span| {
                    function.span.start <= span.start && span.end <= function.span.end
                })
            })
            .collect::<Vec<_>>();
        matched.sort_by_key(|array| array.symbol);
        matched.dedup_by_key(|array| array.symbol);
        let [array] = matched.as_slice() else {
            continue;
        };

        // The table binding is immutable, and its only resolved read is the
        // decoder lookup proved above. Dynamic elements are allowed at table
        // construction time, but they can never be substituted by this path.
        let table_references = scoping.get_resolved_reference_ids(array.symbol);
        if table_references.len() != 1 {
            continue;
        }
        let reference_id = table_references[0];
        let reference = scoping.get_reference(reference_id);
        if reference.is_write() || reference.flags().is_member_write_target() {
            continue;
        }
        let Some(reference_span) = reference_spans.get(&reference_id) else {
            continue;
        };
        if function.span.start > reference_span.start || reference_span.end > function.span.end {
            continue;
        }

        let Some(mutator) = compile_regex(&format!(
            r"\b{}\s*\.\s*(?:copyWithin|fill|pop|push|reverse|shift|sort|splice|unshift)\s*\(",
            regex::escape(&array.name)
        )) else {
            continue;
        };
        if mutator.is_match(source) {
            continue;
        }

        let transform = if standard_base64_decoder_matches(body, &array.name, param) {
            DecoderTransform::StandardBase64
        } else if ((function.body_statement_count == 3
            && function.fixed_decoder_control_shape
            && function.direct_call_count == 12)
            || ((1..=2).contains(&function.body_statement_count)
                && function.fixed_decoder_iife_control_shape))
            && !function_has_external_write(function.span, scoping, reference_spans)
        {
            let Some(alphabet) = fixed_base64_decoder_matches(
                body,
                &array.name,
                param,
                function.fixed_base64_alphabet.as_deref(),
                function.fixed_decoder_iife_control_shape,
            ) else {
                continue;
            };
            DecoderTransform::FixedBase64Alphabet(alphabet)
        } else {
            continue;
        };

        out.insert(
            function.symbol,
            SparseDirectDecoder {
                values: array.values.clone(),
                transform,
            },
        );
    }
    out
}

struct SparseDecoderCallCollector<'c> {
    scoping: &'c Scoping,
    decoders: &'c HashMap<SymbolId, SparseDirectDecoder>,
    replacements: Vec<Replacement>,
}

impl<'a> Visit<'a> for SparseDecoderCallCollector<'_> {
    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        walk::walk_function(self, function, flags);
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if call.optional || call.arguments.len() != 1 || call.arguments[0].is_spread() {
            walk::walk_call_expression(self, call);
            return;
        }
        let Some(symbol) = symbol_of(self.scoping, &call.callee) else {
            walk::walk_call_expression(self, call);
            return;
        };
        let Some(decoder) = self.decoders.get(&symbol) else {
            walk::walk_call_expression(self, call);
            return;
        };
        let Some(raw) = decoder_argument_integer(&call.arguments[0]) else {
            walk::walk_call_expression(self, call);
            return;
        };
        let Some(text) = decoder.value_for_raw(raw).and_then(|value| value.render()) else {
            walk::walk_call_expression(self, call);
            return;
        };
        self.replacements.push(Replacement {
            start: call.span.start as usize,
            end: call.span.end as usize,
            text,
            kind: "string_array_decode",
            arithmetic_state_proof: None,
        });
        // The only argument is an exact literal, so replacing this whole call
        // cannot hide nested evaluation effects.
    }
}

fn sparse_direct_decoder_replacements(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    functions: &[DirectFnInfo],
    complete_decoders: &HashMap<SymbolId, Decoder>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Vec<Replacement> {
    let arrays = partial_decoder_arrays(program, scoping);
    let decoders = detect_sparse_direct_table_decoders(
        source,
        functions,
        &arrays,
        complete_decoders,
        scoping,
        reference_spans,
    );
    if decoders.is_empty() {
        return Vec::new();
    }
    let mut collector = SparseDecoderCallCollector {
        scoping,
        decoders: &decoders,
        replacements: Vec::new(),
    };
    collector.visit_program(program);
    collector.replacements
}

fn detect_direct_table_decoders(
    source: &str,
    functions: &[DirectFnInfo],
    arrays: &[StaticArrayInfo],
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<SymbolId, Decoder> {
    let mut arrays_by_name: HashMap<&str, Vec<&StaticArrayInfo>> = HashMap::new();
    for array in arrays {
        arrays_by_name
            .entry(array.name.as_str())
            .or_default()
            .push(array);
    }

    let mut out = HashMap::new();
    for function in functions {
        if scoping
            .get_resolved_reference_ids(function.symbol)
            .iter()
            .any(|reference_id| scoping.get_reference(*reference_id).is_write())
        {
            continue;
        }
        let Some(param) = function.params.first() else {
            continue;
        };
        let body = fragment(source, function.span);
        let Some(access) = DIRECT_ARRAY_ACCESS_RE.as_ref() else {
            continue;
        };
        let mut matched = access
            .captures_iter(body)
            .filter(|caps| caps.get(2).is_some_and(|capture| capture.as_str() == param))
            .filter_map(|caps| caps.get(1).map(|capture| capture.as_str()))
            .filter_map(|name| arrays_by_name.get(name))
            .filter(|candidates| candidates.len() == 1)
            .map(|candidates| candidates[0])
            .collect::<Vec<_>>();
        matched.sort_by_key(|array| array.symbol);
        matched.dedup_by_key(|array| array.symbol);
        if matched.len() != 1 {
            continue;
        }
        let array = matched[0];

        // A direct literal-table decoder should have exactly one resolved
        // use of the table binding: the indexed load proved above. Requiring a
        // single confined read fails closed on aliases/escapes both outside
        // and *inside* the decoder (an internal alias can otherwise mutate the
        // array before the returned lookup without writing the original
        // binding itself).
        let table_references = scoping.get_resolved_reference_ids(array.symbol);
        if table_references.len() != 1 {
            continue;
        }
        let reference_id = table_references[0];
        let reference = scoping.get_reference(reference_id);
        if reference.is_write() || reference.flags().is_member_write_target() {
            continue;
        }
        let Some(span) = reference_spans.get(&reference_id) else {
            continue;
        };
        if function.span.start > span.start || span.end > function.span.end {
            continue;
        }

        let Some(mutator) = compile_regex(&format!(
            r"\b{}\s*\.\s*(?:copyWithin|fill|pop|push|reverse|shift|sort|splice|unshift)\s*\(",
            regex::escape(&array.name)
        )) else {
            continue;
        };
        if mutator.is_match(source) {
            continue;
        }

        let transform = if standard_base64_decoder_matches(body, &array.name, param) {
            DecoderTransform::StandardBase64
        } else if ((function.body_statement_count == 3
            && function.fixed_decoder_control_shape
            && function.direct_call_count == 12)
            || (function.body_statement_count == 1 && function.fixed_decoder_iife_control_shape))
            && !function_has_external_write(function.span, scoping, reference_spans)
        {
            let Some(alphabet) = fixed_base64_decoder_matches(
                body,
                &array.name,
                param,
                function.fixed_base64_alphabet.as_deref(),
                function.fixed_decoder_iife_control_shape,
            ) else {
                continue;
            };
            DecoderTransform::FixedBase64Alphabet(alphabet)
        } else {
            continue;
        };

        out.insert(
            function.symbol,
            Decoder {
                values: array.values.clone(),
                offset: 0,
                provider: array.name.clone(),
                provider_array_span: array.span,
                transform,
            },
        );
    }
    out
}

fn parse_i64_literal(text: &str) -> Option<i64> {
    let text = text.trim();
    let (negative, text) = if let Some(rest) = text.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = text.strip_prefix('+') {
        (false, rest)
    } else {
        (false, text)
    };
    let value = if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        i64::from_str_radix(hex, 16).ok()?
    } else {
        text.parse::<i64>().ok()?
    };
    Some(if negative { -value } else { value })
}

pub(super) fn js_parse_int(text: &str, radix: u32) -> Option<f64> {
    if !(2..=36).contains(&radix) {
        return None;
    }
    let text = text.trim_start();
    let (negative, text) = if let Some(rest) = text.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = text.strip_prefix('+') {
        (false, rest)
    } else {
        (false, text)
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
        return None;
    }
    let value = js_number_from_u64(value);
    Some(if negative { -value } else { value })
}

struct RotationExprParser<'a, 'd> {
    source: &'a str,
    pos: usize,
    alias: &'a str,
    decoder: &'d Decoder,
    numeric_members: &'d HashMap<(String, String), i64>,
    rotation: usize,
}

impl RotationExprParser<'_, '_> {
    fn rest(&self) -> &str {
        &self.source[self.pos..]
    }

    fn skip_ws(&mut self) {
        while let Some(ch) = self.rest().chars().next() {
            if !ch.is_whitespace() {
                break;
            }
            self.pos += ch.len_utf8();
        }
    }

    fn eat(&mut self, text: &str) -> bool {
        self.skip_ws();
        if self.rest().starts_with(text) {
            self.pos += text.len();
            true
        } else {
            false
        }
    }

    fn ident(&mut self) -> Option<String> {
        self.skip_ws();
        let rest = self.rest();
        let mut len = 0usize;
        for (i, ch) in rest.char_indices() {
            let valid = if i == 0 {
                ch == '_' || ch == '$' || ch.is_ascii_alphabetic()
            } else {
                ch == '_' || ch == '$' || ch.is_ascii_alphanumeric()
            };
            if !valid {
                break;
            }
            len = i + ch.len_utf8();
        }
        if len == 0 {
            return None;
        }
        let value = rest[..len].to_string();
        self.pos += len;
        Some(value)
    }

    fn number(&mut self) -> Option<f64> {
        self.skip_ws();
        let rest = self.rest();
        if rest.starts_with("0x") || rest.starts_with("0X") {
            let digits = rest[2..].bytes().take_while(u8::is_ascii_hexdigit).count();
            if digits == 0 {
                return None;
            }
            let len = 2 + digits;
            let value = js_number_from_i64(i64::from_str_radix(&rest[2..len], 16).ok()?);
            self.pos += len;
            return Some(value);
        }

        let bytes = rest.as_bytes();
        let mut len = 0usize;
        while len < bytes.len() && bytes[len].is_ascii_digit() {
            len += 1;
        }
        if len < bytes.len() && bytes[len] == b'.' {
            len += 1;
            while len < bytes.len() && bytes[len].is_ascii_digit() {
                len += 1;
            }
        }
        if len < bytes.len() && matches!(bytes[len], b'e' | b'E') {
            let exp_start = len;
            len += 1;
            if len < bytes.len() && matches!(bytes[len], b'+' | b'-') {
                len += 1;
            }
            let digits_start = len;
            while len < bytes.len() && bytes[len].is_ascii_digit() {
                len += 1;
            }
            if digits_start == len {
                len = exp_start;
            }
        }
        if len == 0 {
            return None;
        }
        let value = rest[..len].parse().ok()?;
        self.pos += len;
        Some(value)
    }

    fn signed_integer(&mut self) -> Option<i64> {
        self.skip_ws();
        let start = self.pos;
        if self.eat("-") || self.eat("+") {
            self.skip_ws();
        }
        let rest = self.rest();
        let len = if rest.starts_with("0x") || rest.starts_with("0X") {
            let digits = rest[2..].bytes().take_while(u8::is_ascii_hexdigit).count();
            if digits == 0 {
                self.pos = start;
                return None;
            }
            2 + digits
        } else {
            let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
            if digits == 0 {
                self.pos = start;
                return None;
            }
            digits
        };
        self.pos += len;
        parse_i64_literal(&self.source[start..self.pos].replace(char::is_whitespace, ""))
    }

    fn numeric_member(&mut self) -> Option<i64> {
        self.skip_ws();
        let start = self.pos;
        let object = self.ident()?;
        if !self.eat(".") {
            self.pos = start;
            return None;
        }
        let property = self.ident()?;
        let Some(value) = self.numeric_members.get(&(object, property)).copied() else {
            self.pos = start;
            return None;
        };
        Some(value)
    }

    fn integer_atom(&mut self) -> Option<i64> {
        let start = self.pos;
        if let Some(value) = self.signed_integer() {
            return Some(value);
        }
        self.pos = start;
        self.numeric_member()
    }

    fn string_literal(&mut self) -> Option<String> {
        self.skip_ws();
        let quote = self.rest().chars().next()?;
        if !matches!(quote, '\'' | '"') {
            return None;
        }
        self.pos += quote.len_utf8();
        let mut units = Vec::<u16>::new();
        loop {
            let ch = self.rest().chars().next()?;
            if ch == quote {
                self.pos += ch.len_utf8();
                return String::from_utf16(&units).ok();
            }
            if matches!(ch, '\n' | '\r') {
                return None;
            }
            if ch != '\\' {
                let mut buf = [0u16; 2];
                units.extend_from_slice(ch.encode_utf16(&mut buf));
                self.pos += ch.len_utf8();
                continue;
            }

            self.pos += ch.len_utf8();
            let escape = self.rest().chars().next()?;
            self.pos += escape.len_utf8();
            match escape {
                '\\' | '\'' | '"' | '/' => units.push(u16::try_from(u32::from(escape)).ok()?),
                'b' => units.push(0x08),
                'f' => units.push(0x0c),
                'n' => units.push(u16::from(b'\n')),
                'r' => units.push(u16::from(b'\r')),
                't' => units.push(u16::from(b'\t')),
                'v' => units.push(0x0b),
                '0' => {
                    if self
                        .rest()
                        .chars()
                        .next()
                        .is_some_and(|next| next.is_ascii_digit())
                    {
                        return None;
                    }
                    units.push(0);
                }
                'x' => {
                    let digits = self.rest().get(..2)?;
                    if !digits.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                        return None;
                    }
                    units.push(u16::from_str_radix(digits, 16).ok()?);
                    self.pos += 2;
                }
                'u' => {
                    if self.rest().starts_with('{') {
                        self.pos += 1;
                        let end = self.rest().find('}')?;
                        let digits = self.rest().get(..end)?;
                        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_hexdigit())
                        {
                            return None;
                        }
                        let scalar = u32::from_str_radix(digits, 16).ok()?;
                        let value = char::from_u32(scalar)?;
                        let mut buf = [0u16; 2];
                        units.extend_from_slice(value.encode_utf16(&mut buf));
                        self.pos += end + 1;
                    } else {
                        let digits = self.rest().get(..4)?;
                        if !digits.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                            return None;
                        }
                        units.push(u16::from_str_radix(digits, 16).ok()?);
                        self.pos += 4;
                    }
                }
                '\n' => {}
                '\r' => {
                    if self.rest().starts_with('\n') {
                        self.pos += 1;
                    }
                }
                other => {
                    let mut buf = [0u16; 2];
                    units.extend_from_slice(other.encode_utf16(&mut buf));
                }
            }
        }
    }

    fn decoder_call(&mut self) -> Option<String> {
        let name = self.ident()?;
        if name != self.alias || !self.eat("(") {
            return None;
        }
        let raw = self.integer_atom()?;
        let key = if self.eat(",") {
            Some(self.string_literal()?)
        } else {
            None
        };
        if !self.eat(")") {
            return None;
        }
        let value =
            self.decoder
                .value_for_raw_rotated_with_key(raw, self.rotation, key.as_deref())?;
        match value {
            Value::String(value) => Some(value),
            value => value.js_string(),
        }
    }

    fn factor(&mut self) -> Option<f64> {
        self.skip_ws();
        if self.eat("(") {
            let value = self.expr()?;
            if !self.eat(")") {
                return None;
            }
            return Some(value);
        }
        if self.eat("+") {
            return self.factor();
        }
        if self.eat("-") {
            return self.factor().map(|value| -value);
        }

        let before = self.pos;
        if let Some(name) = self.ident() {
            if name == "parseInt" && self.eat("(") {
                let decoded = self.decoder_call()?;
                let radix = if self.eat(",") {
                    let radix = self.signed_integer()?;
                    u32::try_from(radix).ok()?
                } else {
                    10
                };
                if !self.eat(")") {
                    return None;
                }
                return js_parse_int(&decoded, radix);
            }
            self.pos = before;
        }
        if let Some(value) = self.numeric_member() {
            return Some(js_number_from_i64(value));
        }
        self.number()
    }

    fn term(&mut self) -> Option<f64> {
        let mut value = self.factor()?;
        loop {
            if self.eat("*") {
                value *= self.factor()?;
            } else if self.eat("/") {
                value /= self.factor()?;
            } else if self.eat("%") {
                value %= self.factor()?;
            } else {
                break;
            }
        }
        Some(value)
    }

    fn expr(&mut self) -> Option<f64> {
        let mut value = self.term()?;
        loop {
            if self.eat("+") {
                value += self.term()?;
            } else if self.eat("-") {
                value -= self.term()?;
            } else {
                break;
            }
        }
        Some(value)
    }
}

fn eval_rotation_checksum(
    expression: &str,
    alias: &str,
    decoder: &Decoder,
    numeric_members: &HashMap<(String, String), i64>,
    rotation: usize,
) -> Option<f64> {
    let mut parser = RotationExprParser {
        source: expression,
        pos: 0,
        alias,
        decoder,
        numeric_members,
        rotation,
    };
    let value = parser.expr()?;
    parser.skip_ws();
    (parser.pos == expression.len()).then_some(value)
}

#[derive(Debug, Clone)]
struct RotationIife {
    provider: String,
    target: i64,
    array_param: String,
    count_param: String,
    numeric_members: HashMap<(String, String), i64>,
    stable_aliases: HashMap<String, String>,
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
        if matches!(
            &call.callee,
            Expression::Identifier(identifier) if identifier.name.as_str() == "eval"
        ) {
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

fn stable_rotation_alias(
    alias_symbol: SymbolId,
    alias_name: &str,
    target_reference_id: ReferenceId,
    initialization_end: u32,
    initialization_write: Option<ReferenceId>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Option<(String, String)> {
    let target_symbol = statically_resolved_symbol(scoping, target_reference_id)?;
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
            })
        });
    stable.then(|| {
        (
            scoping.symbol_name(target_symbol).to_string(),
            alias_name.to_string(),
        )
    })
}

fn rotation_stable_aliases(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<String, String> {
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
                    alias_symbol,
                    alias.name.as_str(),
                    target_reference_id,
                    target.span.end,
                    None,
                    scoping,
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
                alias_symbol,
                alias.name.as_str(),
                target_reference_id,
                assignment.span.end,
                Some(alias_reference_id),
                scoping,
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
        let key = property.key.static_name()?.into_cow_str()?.into_owned();
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

fn closed_over_rotation_iife(
    source: &str,
    call: &CallExpression<'_>,
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
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
    let decoder_symbol = statically_resolved_symbol(scoping, decoder_reference)?;
    if !scoping.symbol_flags(decoder_symbol).is_function() {
        return None;
    }

    let BindingPattern::BindingIdentifier(array_alias) = &table_decl.id else {
        return None;
    };
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
    let provider_symbol = statically_resolved_symbol(scoping, provider_reference)?;
    if !scoping.symbol_flags(provider_symbol).is_function() {
        return None;
    }

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
    stable_aliases.insert(decoder.name.to_string(), decoder_alias.name.to_string());
    let standalone = statement_span.is_some();
    Some(RotationIife {
        provider: provider.name.to_string(),
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
                if let Some(body) = &function.body {
                    let local_params = function
                        .params
                        .items
                        .iter()
                        .map(|param| match &param.pattern {
                            BindingPattern::BindingIdentifier(id) => Some(id.name.to_string()),
                            _ => None,
                        })
                        .collect::<Option<Vec<_>>>();
                    let provider_is_function = provider
                        .reference_id
                        .get()
                        .and_then(|reference_id| {
                            statically_resolved_symbol(self.scoping, reference_id)
                        })
                        .is_some_and(|symbol| self.scoping.symbol_flags(symbol).is_function());
                    let proof_eligible = !function.r#async
                        && !function.generator
                        && function.params.rest.is_none()
                        && local_params
                            .as_ref()
                            .is_some_and(|params| params.len() >= 2)
                        && provider_is_function
                        && rotation_parameter_names_unshadowed(function, self.scoping)
                        && !rotation_has_dynamic_scope(function);
                    let local_params = local_params.unwrap_or_default();
                    let array_param = local_params.first().cloned().unwrap_or_default();
                    let count_param = local_params.get(1).cloned().unwrap_or_default();
                    let stable_aliases =
                        rotation_stable_aliases(function, self.scoping, self.reference_spans);
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
                        provider: provider.name.to_string(),
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
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Vec<RotationIife> {
    let mut statement_spans = RotationStatementSpanCollector::default();
    statement_spans.visit_program(program);
    let mut collector = RotationIifeCollector {
        source,
        scoping,
        statement_spans: &statement_spans.spans,
        reference_spans,
        out: Vec::new(),
    };
    collector.visit_program(program);
    collector.out
}

fn fixed_count_rotation(source: &str, iife: &RotationIife, table_len: usize) -> Option<usize> {
    if iife.target < 0 || table_len == 0 {
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

fn span_contains(outer: Span, inner: Span) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

fn detect_fixed_rotated_direct_decoders(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> DecoderDetection {
    let arrays = all_static_arrays(program);
    let functions = variable_functions(program);
    let rotations = collect_rotation_iifes(source, program, scoping, reference_spans);
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

        for array in &arrays {
            let Some(offset) = simple_direct_decoder_offset(source, function, array) else {
                continue;
            };
            let matching_rotations = rotations
                .iter()
                .filter(|rotation| {
                    rotation.provider == array.name
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
            if !safe_references || decoder_reads != 1 || rotation_reads != 1 {
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
                    provider: array.name.clone(),
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
    provider: String,
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

fn rotation_decoder_alias(iife: &RotationIife, decoder_name: &str) -> Option<String> {
    iife.stable_aliases.get(decoder_name).cloned()
}

fn prove_rotation_iife(
    source: &str,
    iife: &RotationIife,
    decoders: &mut HashMap<String, Decoder>,
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
    let mut proven = false;

    for (decoder_name, decoder) in decoders.iter_mut() {
        if decoder.provider != iife.provider || decoder.values.is_empty() {
            continue;
        }
        let Some(alias) = rotation_decoder_alias(iife, decoder_name) else {
            continue;
        };

        let mut matches = Vec::new();
        for rotation in 0..decoder.values.len() {
            let Some(value) = eval_rotation_checksum(
                &expression,
                &alias,
                decoder,
                &iife.numeric_members,
                rotation,
            ) else {
                continue;
            };
            if value.is_finite() && (value - js_number_from_i64(iife.target)).abs() < 1e-9 {
                matches.push(rotation);
                if matches.len() > 1 {
                    break;
                }
            }
        }
        if matches.len() == 1 {
            proven = true;
            if matches[0] != 0 {
                decoder.values.rotate_left(matches[0]);
            }
        }
    }

    proven
}

fn prove_rotation_iifes(
    source: &str,
    rotation_iifes: &[RotationIife],
    decoders: &mut HashMap<String, Decoder>,
) -> Vec<ProvenRotationIife> {
    let mut proven_iifes = Vec::new();
    for iife in rotation_iifes {
        if !prove_rotation_iife(source, iife, decoders) {
            continue;
        }
        proven_iifes.push(ProvenRotationIife {
            provider: iife.provider.clone(),
            start: iife.statement_span.start as usize,
            end: iife.statement_span.end as usize,
            standalone_statement: iife.standalone_statement,
        });
    }
    proven_iifes
}

fn materializable_rotated_providers(
    decoders: &HashMap<String, Decoder>,
    proven_iifes: &[ProvenRotationIife],
) -> HashMap<String, (Span, Vec<Value>)> {
    // Materialization is stricter than decoding. Every detected decoder sharing
    // a provider must agree on the same final rotated table and literal array.
    let proven_providers = proven_iifes
        .iter()
        .map(|iife| iife.provider.clone())
        .collect::<HashSet<_>>();
    let mut materialized: HashMap<String, (Span, Vec<Value>)> = HashMap::new();
    let mut inconsistent = HashSet::new();
    for decoder in decoders.values() {
        if !proven_providers.contains(&decoder.provider) {
            continue;
        }
        match materialized.get(&decoder.provider) {
            None => {
                materialized.insert(
                    decoder.provider.clone(),
                    (decoder.provider_array_span, decoder.values.clone()),
                );
            }
            Some((span, values))
                if *span == decoder.provider_array_span && same_values(values, &decoder.values) => {
            }
            Some(_) => {
                inconsistent.insert(decoder.provider.clone());
            }
        }
    }
    for provider in inconsistent {
        materialized.remove(&provider);
    }
    materialized
}

fn rotation_replacements(
    materialized: HashMap<String, (Span, Vec<Value>)>,
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
    decoders: &mut HashMap<String, Decoder>,
    rotation_iifes: &[RotationIife],
) -> (Vec<(usize, usize)>, Vec<Replacement>) {
    let mut proven_iifes = prove_rotation_iifes(source, rotation_iifes, decoders);

    let mut required = HashMap::<String, usize>::new();
    for iife in rotation_iifes {
        *required.entry(iife.provider.clone()).or_default() += 1;
    }
    let mut proven = HashMap::<String, usize>::new();
    for iife in &proven_iifes {
        *proven.entry(iife.provider.clone()).or_default() += 1;
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

fn decoder_providers(
    source: &str,
    functions: &[FnInfo],
) -> HashMap<(ScopeId, String), LocalStaticArrayInfo> {
    let mut providers = HashMap::new();
    for function in functions {
        if let Some(values) = &function.split_provider {
            providers.insert((function.scope, function.name.clone()), values.clone());
            continue;
        }
        if !function.params.is_empty() {
            continue;
        }
        let body = fragment(source, function.span);
        let self_rewrite_assignment = body.contains(&format!("{} = function", function.name))
            || body.contains(&format!("{}=function", function.name));
        if !self_rewrite_assignment {
            continue;
        }
        let classic_self_rewrite = body.contains(&format!("return {}();", function.name));
        for (array_name, values) in &function.static_arrays {
            let inline_self_rewrite = compile_regex(&format!(
                r"(?s)^\s*function\s+{}\s*\(\s*\)\s*\{{\s*(?:const|let|var)\s+{}\s*=\s*{}\s*;\s*return\s*\(\s*{}\s*=\s*function\s*\(\s*\)\s*\{{\s*return\s+{}\s*;?\s*\}}\s*\)\s*\(\s*\)\s*;?\s*\}}\s*$",
                regex::escape(&function.name),
                regex::escape(array_name),
                regex::escape(fragment(source, values.span)),
                regex::escape(&function.name),
                regex::escape(array_name),
            ))
            .is_some_and(|pattern| pattern.is_match(body));
            if (classic_self_rewrite && body.contains(&format!("return {array_name};")))
                || inline_self_rewrite
            {
                providers.insert((function.scope, function.name.clone()), values.clone());
                break;
            }
        }
    }
    providers
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
                && compile_regex(&format!(r"\b{}\s*\.\s*length\b", regex::escape(key),))
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
    providers: &HashMap<(ScopeId, String), LocalStaticArrayInfo>,
) -> Option<Decoder> {
    if function.params.is_empty() || name_counts.get(&function.name).copied() != Some(1) {
        return None;
    }
    let body = fragment(source, function.span);
    // The exact self-rewriting shape below necessarily contains all three of
    // these tokens. Most application functions contain none of them together;
    // rejecting those before constructing the function-specific regex avoids
    // compiling a large automaton for every ordinary named function.
    if !body.contains("-=") || !body.contains("return") || !body.contains("function") {
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
    let provider_info = providers.get(&(function.scope, provider.clone()))?;
    let offset = parse_i64_literal(captures.name("offset")?.as_str())?;
    Some(Decoder {
        values: provider_info.values.clone(),
        offset,
        provider,
        provider_array_span: provider_info.span,
        transform: DecoderTransform::Plain,
    })
}

fn detect_decoder_candidate(
    source: &str,
    function: &FnInfo,
    patterns: &DecoderPatterns,
    name_counts: &HashMap<String, usize>,
    providers: &HashMap<(ScopeId, String), LocalStaticArrayInfo>,
) -> Option<Decoder> {
    if function.params.is_empty() {
        return None;
    }
    if let Some(shape) = &function.sequence_decoder {
        if name_counts.get(&function.name).copied() != Some(1)
            || name_counts.get(&shape.provider).copied() != Some(1)
        {
            return None;
        }
        let provider_info = providers.get(&(function.scope, shape.provider.clone()))?;
        return Some(Decoder {
            values: provider_info.values.clone(),
            offset: shape.offset,
            provider: shape.provider.clone(),
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
    let provider_info = providers.get(&(function.scope, provider.clone()))?;
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
        regex::escape(&provider),
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
        provider,
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
    reference_spans: &HashMap<ReferenceId, Span>,
) -> DecoderDetection {
    let Some(patterns) = decoder_patterns() else {
        return (HashMap::new(), Vec::new(), Vec::new());
    };
    let name_counts = function_name_counts(functions);
    let providers = decoder_providers(source, functions);
    let mut by_name = functions
        .iter()
        .filter_map(|function| {
            detect_decoder_candidate(source, function, patterns, &name_counts, &providers)
                .map(|decoder| (function.name.clone(), decoder))
        })
        .collect::<HashMap<_, _>>();

    let rotation_iifes = collect_rotation_iifes(source, program, scoping, reference_spans);
    let (protected_spans, rotation_replacements) =
        apply_proven_decoder_rotations(source, &mut by_name, &rotation_iifes);

    let mut out = functions
        .iter()
        .filter_map(|function| {
            by_name
                .get(&function.name)
                .cloned()
                .map(|decoder| (function.symbol, decoder))
        })
        .collect::<HashMap<_, _>>();
    propagate_decoder_aliases(&mut out, program, scoping, reference_spans);

    (out, protected_spans, rotation_replacements)
}

pub struct DecoderAnalysis {
    pub(super) decoders: HashMap<SymbolId, Decoder>,
    pub(super) protected_spans: Vec<(usize, usize)>,
    pub(super) replacements: Vec<Replacement>,
    pub(super) removable_helpers: HashMap<SymbolId, Span>,
}

pub fn analyze_decoders(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> DecoderAnalysis {
    let arrays = decoder_static_arrays(program, scoping);
    let from_char_code_aliases = crate::collect_from_char_code_aliases(program, scoping);
    let direct_functions =
        all_functions(program, scoping, &from_char_code_aliases, reference_spans);
    let functions = all_function_declarations(program, scoping);

    let (mut decoders, mut protected_spans, mut replacements) =
        detect_decoders(source, &functions, program, scoping, reference_spans);
    for (symbol, decoder) in
        detect_direct_table_decoders(source, &direct_functions, &arrays, scoping, reference_spans)
    {
        decoders.entry(symbol).or_insert(decoder);
    }
    let (fixed_decoders, fixed_protected, fixed_replacements) =
        detect_fixed_rotated_direct_decoders(source, program, scoping, reference_spans);
    for (symbol, decoder) in fixed_decoders {
        decoders.entry(symbol).or_insert(decoder);
    }
    protected_spans.extend(fixed_protected);
    replacements.extend(fixed_replacements);
    replacements.extend(sparse_direct_decoder_replacements(
        source,
        program,
        &direct_functions,
        &decoders,
        scoping,
        reference_spans,
    ));

    let removable_helpers = functions
        .iter()
        .filter(|function| decoders.contains_key(&function.symbol))
        .map(|function| (function.symbol, function.span))
        .collect();

    DecoderAnalysis {
        decoders,
        protected_spans,
        replacements,
        removable_helpers,
    }
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
    fn collect_statements<'a>(&mut self, statements: &[Statement<'a>], container_span: Span) {
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
        let candidate = if !prior_initializer {
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
        } else {
            None
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
    fn rotation_decoder_alias_requires_proven_binding() {
        let base = RotationIife {
            provider: "provider".into(),
            target: 1,
            array_param: "array".into(),
            count_param: "target".into(),
            numeric_members: HashMap::new(),
            stable_aliases: HashMap::from([("decode".into(), "alias".into())]),
            checksum_expression: None,
            proof_eligible: true,
            body_span: Span::new(0, 0),
            statement_span: Span::new(0, 0),
            standalone_statement: true,
        };
        assert_eq!(
            rotation_decoder_alias(&base, "decode"),
            Some("alias".into())
        );

        let mut unproven_alias = base;
        unproven_alias.stable_aliases.clear();
        assert_eq!(rotation_decoder_alias(&unproven_alias, "decode"), None);
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
            provider: "p".into(),
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
                "parseInt(G(0x10, dynamic))",
                "G",
                &decoder,
                &HashMap::new(),
                3,
            ),
            None
        );
    }
}
