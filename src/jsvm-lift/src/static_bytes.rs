use crate::sha256_hex;
use base64::{
    engine::general_purpose::{STANDARD, STANDARD_NO_PAD},
    Engine as _,
};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, AssignmentTarget, BindingPattern, Expression, ForStatementInit, Function,
    ObjectPropertyKind, SimpleAssignmentTarget, Statement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use rolldown_redox::ecmascript::parse_program;
use std::collections::HashMap;

const MAX_STATIC_BUFFER_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug, Clone, Eq, PartialEq)]
enum StaticValue {
    Number(usize),
    Text(String),
    BinaryString(Vec<u8>),
    Base64Decoder,
    Buffer(usize),
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct StaticBuffer {
    bytes: Vec<u8>,
    valid: bool,
    writes: usize,
    allocation_span: Span,
}

#[derive(Debug, Clone, Default, Eq, PartialEq)]
struct EvalState {
    values: HashMap<SymbolId, StaticValue>,
    buffers: Vec<StaticBuffer>,
    helper_calls_succeeded: usize,
    last_invalidation_reason: Option<&'static str>,
    sink_failure: Option<&'static str>,
}

impl EvalState {
    fn allocate(&mut self, byte_len: usize, span: Span) -> Option<StaticValue> {
        if byte_len > MAX_STATIC_BUFFER_BYTES {
            return None;
        }
        let id = self.buffers.len();
        self.buffers.push(StaticBuffer {
            bytes: vec![0; byte_len],
            valid: true,
            writes: 0,
            allocation_span: span,
        });
        Some(StaticValue::Buffer(id))
    }

    fn invalidate_all_buffers(&mut self, reason: &'static str) {
        self.last_invalidation_reason = Some(reason);
        for buffer in &mut self.buffers {
            buffer.valid = false;
        }
    }

    fn invalidate_buffer(&mut self, id: usize, reason: &'static str) {
        self.last_invalidation_reason = Some(reason);
        if let Some(buffer) = self.buffers.get_mut(id) {
            buffer.valid = false;
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct CopyHelper {
    buffer_symbol: SymbolId,
    source_param: usize,
    offset_param: usize,
    available_from: u32,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct RecoveredByteArtifact {
    pub sha256: String,
    pub bytes: Vec<u8>,
    pub sink_start: u32,
    pub sink_end: u32,
    pub sink_kind: &'static str,
    pub allocation_start: u32,
    pub allocation_end: u32,
    pub copy_writes: usize,
    pub standard_builtins_required: bool,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StaticByteRecoverySummary {
    pub artifacts: Vec<RecoveredByteArtifact>,
    pub proven_copy_helpers: usize,
    pub webassembly_sinks: usize,
    pub sink_diagnostics: Vec<SinkRecoveryDiagnostic>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SinkRecoveryDiagnostic {
    pub sink_start: u32,
    pub sink_end: u32,
    pub sink_kind: &'static str,
    pub recovered: bool,
    pub buffers_allocated: usize,
    pub valid_buffers: usize,
    pub helper_calls_succeeded: usize,
    pub last_invalidation_reason: Option<&'static str>,
    pub sink_failure: Option<&'static str>,
}

fn unparenthesized<'a>(mut expression: &'a Expression<'a>) -> &'a Expression<'a> {
    while let Expression::ParenthesizedExpression(parenthesized) = expression {
        expression = &parenthesized.expression;
    }
    expression
}

fn span_contains(outer: Span, inner: Span) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

fn statically_resolved_symbol(scoping: &Scoping, reference_id: ReferenceId) -> Option<SymbolId> {
    let reference = scoping.get_reference(reference_id);
    let symbol = reference.symbol_id()?;
    let symbol_scope = scoping.symbol_scope_id(symbol);
    for scope_id in scoping.scope_ancestors(reference.scope_id()) {
        if scope_id == symbol_scope {
            return Some(symbol);
        }
        if scoping.scope_flags(scope_id).is_with() {
            return None;
        }
    }
    None
}

fn symbol_of(scoping: &Scoping, expression: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    statically_resolved_symbol(scoping, identifier.reference_id.get()?)
}

fn simple_target_symbol(
    scoping: &Scoping,
    target: &SimpleAssignmentTarget<'_>,
) -> Option<SymbolId> {
    let SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) = target else {
        return None;
    };
    statically_resolved_symbol(scoping, identifier.reference_id.get()?)
}

fn assignment_target_symbol(scoping: &Scoping, target: &AssignmentTarget<'_>) -> Option<SymbolId> {
    let AssignmentTarget::AssignmentTargetIdentifier(identifier) = target else {
        return None;
    };
    statically_resolved_symbol(scoping, identifier.reference_id.get()?)
}

fn unresolved_global(scoping: &Scoping, expression: &Expression<'_>, expected: &str) -> bool {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return false;
    };
    if identifier.name.as_str() != expected {
        return false;
    }
    let Some(reference_id) = identifier.reference_id.get() else {
        return false;
    };
    let reference = scoping.get_reference(reference_id);
    if reference.symbol_id().is_some() {
        return false;
    }
    scoping
        .scope_ancestors(reference.scope_id())
        .all(|scope_id| !scoping.scope_flags(scope_id).is_with())
}

fn exact_usize(expression: &Expression<'_>) -> Option<usize> {
    let Expression::NumericLiteral(number) = unparenthesized(expression) else {
        return None;
    };
    if !number.value.is_finite() || number.value < 0.0 || number.value.fract() != 0.0 {
        return None;
    }
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let value = number.value as usize;
    #[allow(clippy::cast_precision_loss)]
    ((value as f64) == number.value).then_some(value)
}

fn static_member<'a>(expression: &'a Expression<'a>, property: &str) -> Option<&'a Expression<'a>> {
    let Expression::StaticMemberExpression(member) = unparenthesized(expression) else {
        return None;
    };
    (!member.optional && member.property.name.as_str() == property).then_some(&member.object)
}

fn source_length_of(
    scoping: &Scoping,
    expression: &Expression<'_>,
    source_symbol: SymbolId,
) -> bool {
    static_member(expression, "length").and_then(|object| symbol_of(scoping, object))
        == Some(source_symbol)
}

fn parameter_symbols(function: &Function<'_>) -> Option<Vec<SymbolId>> {
    if function.params.rest.is_some() {
        return None;
    }
    function
        .params
        .items
        .iter()
        .map(|parameter| {
            if parameter.initializer.is_some() {
                return None;
            }
            let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                return None;
            };
            identifier.symbol_id.get()
        })
        .collect()
}

fn update_symbol(
    expression: &Expression<'_>,
    scoping: &Scoping,
    operator: &str,
    require_postfix: bool,
) -> Option<SymbolId> {
    let Expression::UpdateExpression(update) = unparenthesized(expression) else {
        return None;
    };
    if update.operator.as_str() != operator || (require_postfix && update.prefix) {
        return None;
    }
    simple_target_symbol(scoping, &update.argument)
}

fn update_has_symbols(
    expression: &Expression<'_>,
    scoping: &Scoping,
    required: &[SymbolId],
) -> bool {
    fn one(expression: &Expression<'_>, scoping: &Scoping) -> Option<SymbolId> {
        let Expression::UpdateExpression(update) = unparenthesized(expression) else {
            return None;
        };
        if update.operator.as_str() != "++" {
            return None;
        }
        simple_target_symbol(scoping, &update.argument)
    }

    let seen = match unparenthesized(expression) {
        Expression::SequenceExpression(sequence) => sequence
            .expressions
            .iter()
            .map(|item| one(item, scoping))
            .collect::<Option<Vec<_>>>(),
        other => one(other, scoping).map(|symbol| vec![symbol]),
    };
    let Some(seen) = seen else {
        return false;
    };
    seen.len() == required.len() && required.iter().all(|symbol| seen.contains(symbol))
}

fn copy_assignment(
    statement: &Statement<'_>,
    scoping: &Scoping,
    buffer_symbol: SymbolId,
    source_symbol: SymbolId,
    offset_symbol: SymbolId,
    index_symbol: SymbolId,
    offset_incremented: bool,
) -> bool {
    let statement = match statement {
        Statement::BlockStatement(block) if block.body.len() == 1 => &block.body[0],
        other => other,
    };
    let Statement::ExpressionStatement(expression_statement) = statement else {
        return false;
    };
    let Expression::AssignmentExpression(assignment) = &expression_statement.expression else {
        return false;
    };
    if assignment.operator.as_str() != "=" {
        return false;
    }
    let AssignmentTarget::ComputedMemberExpression(target) = &assignment.left else {
        return false;
    };
    if target.optional || symbol_of(scoping, &target.object) != Some(buffer_symbol) {
        return false;
    }

    let index_matches = if offset_incremented {
        symbol_of(scoping, &target.expression) == Some(offset_symbol)
    } else {
        let Expression::BinaryExpression(index) = unparenthesized(&target.expression) else {
            return false;
        };
        if index.operator.as_str() != "+" {
            return false;
        }
        let left = symbol_of(scoping, &index.left);
        let right = symbol_of(scoping, &index.right);
        (left == Some(offset_symbol) && right == Some(index_symbol))
            || (left == Some(index_symbol) && right == Some(offset_symbol))
    };
    if !index_matches {
        return false;
    }

    let Expression::CallExpression(call) = unparenthesized(&assignment.right) else {
        return false;
    };
    if call.optional || call.arguments.len() != 1 || call.arguments[0].is_spread() {
        return false;
    }
    let Some(object) = static_member(&call.callee, "charCodeAt") else {
        return false;
    };
    if symbol_of(scoping, object) != Some(source_symbol) {
        return false;
    }
    call.arguments[0]
        .as_expression()
        .and_then(|argument| symbol_of(scoping, argument))
        == Some(index_symbol)
}

fn helper_buffer_symbol(statement: &Statement<'_>, scoping: &Scoping) -> Option<SymbolId> {
    let statement = match statement {
        Statement::BlockStatement(block) if block.body.len() == 1 => &block.body[0],
        other => other,
    };
    let Statement::ExpressionStatement(expression_statement) = statement else {
        return None;
    };
    let Expression::AssignmentExpression(assignment) = &expression_statement.expression else {
        return None;
    };
    let AssignmentTarget::ComputedMemberExpression(target) = &assignment.left else {
        return None;
    };
    symbol_of(scoping, &target.object)
}

fn classify_copy_helper(
    function: &Function<'_>,
    scoping: &Scoping,
    available_from: u32,
) -> Option<CopyHelper> {
    if function.r#async || function.generator {
        return None;
    }
    let params = parameter_symbols(function)?;
    if params.len() < 2 {
        return None;
    }
    let body = function.body.as_ref()?;
    let [Statement::ForStatement(for_statement)] = body.statements.as_slice() else {
        return None;
    };
    let Some(ForStatementInit::VariableDeclaration(initializer)) = &for_statement.init else {
        return None;
    };
    let [declaration] = initializer.declarations.as_slice() else {
        return None;
    };
    let BindingPattern::BindingIdentifier(index_identifier) = &declaration.id else {
        return None;
    };
    let index_symbol = index_identifier.symbol_id.get()?;
    let init = declaration.init.as_ref()?;
    let buffer_symbol = helper_buffer_symbol(&for_statement.body, scoping)?;
    if params.contains(&buffer_symbol) || buffer_symbol == index_symbol {
        return None;
    }

    for (source_param, source_symbol) in params.iter().copied().enumerate() {
        for (offset_param, offset_symbol) in params.iter().copied().enumerate() {
            if source_param == offset_param {
                continue;
            }

            let forward = exact_usize(init) == Some(0)
                && for_statement.test.as_ref().is_some_and(|test| {
                    let Expression::BinaryExpression(test) = unparenthesized(test) else {
                        return false;
                    };
                    test.operator.as_str() == "<"
                        && symbol_of(scoping, &test.left) == Some(index_symbol)
                        && source_length_of(scoping, &test.right, source_symbol)
                });

            let reverse = source_length_of(scoping, init, source_symbol)
                && for_statement.update.is_none()
                && for_statement.test.as_ref().is_some_and(|test| {
                    update_symbol(test, scoping, "--", true) == Some(index_symbol)
                });

            if !forward && !reverse {
                continue;
            }

            let offset_incremented = if forward {
                let Some(update) = for_statement.update.as_ref() else {
                    continue;
                };
                if update_has_symbols(update, scoping, &[index_symbol]) {
                    false
                } else if update_has_symbols(update, scoping, &[index_symbol, offset_symbol]) {
                    true
                } else {
                    continue;
                }
            } else {
                false
            };

            if copy_assignment(
                &for_statement.body,
                scoping,
                buffer_symbol,
                source_symbol,
                offset_symbol,
                index_symbol,
                offset_incremented,
            ) {
                return Some(CopyHelper {
                    buffer_symbol,
                    source_param,
                    offset_param,
                    available_from,
                });
            }
        }
    }
    None
}

struct HelperCollector<'c> {
    scoping: &'c Scoping,
    helpers: HashMap<SymbolId, CopyHelper>,
}

impl HelperCollector<'_> {
    fn insert_if_stable(&mut self, symbol: SymbolId, helper: CopyHelper) {
        let stable = self
            .scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .all(|reference_id| !self.scoping.get_reference(*reference_id).is_write());
        if stable {
            self.helpers.insert(symbol, helper);
        }
    }
}

impl<'a> Visit<'a> for HelperCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(identifier) = &function.id {
            if let Some(symbol) = identifier.symbol_id.get() {
                if let Some(helper) = classify_copy_helper(function, self.scoping, 0) {
                    self.insert_if_stable(symbol, helper);
                }
            }
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_variable_declaration(&mut self, declaration: &oxc_ast::ast::VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                continue;
            };
            let Some(Expression::FunctionExpression(function)) = &declarator.init else {
                continue;
            };
            if let Some(helper) = classify_copy_helper(function, self.scoping, declarator.span.end)
            {
                self.insert_if_stable(symbol, helper);
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

struct DirectCalleeReferenceCollector {
    references: std::collections::HashSet<ReferenceId>,
}

impl<'a> Visit<'a> for DirectCalleeReferenceCollector {
    fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
        if let Expression::Identifier(identifier) = unparenthesized(&call.callee) {
            if let Some(reference_id) = identifier.reference_id.get() {
                self.references.insert(reference_id);
            }
        }
        walk::walk_call_expression(self, call);
    }
}

fn collect_helpers(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, CopyHelper> {
    let mut collector = HelperCollector {
        scoping,
        helpers: HashMap::new(),
    };
    collector.visit_program(program);

    let mut direct_calls = DirectCalleeReferenceCollector {
        references: std::collections::HashSet::new(),
    };
    direct_calls.visit_program(program);
    collector.helpers.retain(|symbol, _| {
        scoping
            .get_resolved_reference_ids(*symbol)
            .iter()
            .all(|reference_id| {
                direct_calls.references.contains(reference_id)
                    && statically_resolved_symbol(scoping, *reference_id) == Some(*symbol)
            })
    });
    collector.helpers
}

#[derive(Debug, Clone, Copy)]
struct Sink {
    span: Span,
    kind: &'static str,
}

fn webassembly_member(scoping: &Scoping, expression: &Expression<'_>, property: &str) -> bool {
    let Some(object) = static_member(expression, property) else {
        return false;
    };
    if unresolved_global(scoping, object, "WebAssembly") {
        return true;
    }
    let Expression::StaticMemberExpression(namespace) = unparenthesized(object) else {
        return false;
    };
    !namespace.optional
        && namespace.property.name.as_str() == "WebAssembly"
        && matches!(
            unparenthesized(&namespace.object),
            Expression::Identifier(global)
                if matches!(global.name.as_str(), "window" | "globalThis" | "self")
                    && global.reference_id.get().is_some_and(|reference_id| {
                        scoping.get_reference(reference_id).symbol_id().is_none()
                    })
        )
}

struct SinkCollector<'c> {
    scoping: &'c Scoping,
    sinks: Vec<Sink>,
}

impl<'a> Visit<'a> for SinkCollector<'_> {
    fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
        if !call.optional && webassembly_member(self.scoping, &call.callee, "instantiate") {
            self.sinks.push(Sink {
                span: call.span,
                kind: "WebAssembly.instantiate",
            });
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
        if webassembly_member(self.scoping, &expression.callee, "Module") {
            self.sinks.push(Sink {
                span: expression.span,
                kind: "new WebAssembly.Module",
            });
        }
        walk::walk_new_expression(self, expression);
    }
}

fn decode_atob(text: &str) -> Option<Vec<u8>> {
    let compact = text
        .bytes()
        .filter(|byte| !matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | 0x0c))
        .collect::<Vec<_>>();
    if compact.len() > MAX_STATIC_BUFFER_BYTES.saturating_mul(4) / 3 + 4 {
        return None;
    }
    STANDARD
        .decode(&compact)
        .or_else(|_| STANDARD_NO_PAD.decode(&compact))
        .ok()
}

struct Evaluator<'c, 'h> {
    scoping: &'c Scoping,
    helpers: &'h HashMap<SymbolId, CopyHelper>,
}

impl Evaluator<'_, '_> {
    fn eval(&self, expression: &Expression<'_>, state: &mut EvalState) -> Option<StaticValue> {
        match unparenthesized(expression) {
            Expression::NumericLiteral(_) => exact_usize(expression).map(StaticValue::Number),
            Expression::StringLiteral(literal) => literal
                .value
                .as_str()
                .map(|value| StaticValue::Text(value.to_string())),
            Expression::Identifier(_) => {
                if unresolved_global(self.scoping, expression, "atob") {
                    return Some(StaticValue::Base64Decoder);
                }
                state
                    .values
                    .get(&symbol_of(self.scoping, expression)?)
                    .cloned()
            }
            Expression::CallExpression(call)
                if !call.optional && !call.arguments.iter().any(Argument::is_spread) =>
            {
                let decoder = self.eval(&call.callee, state)?;
                if decoder != StaticValue::Base64Decoder || call.arguments.len() != 1 {
                    return None;
                }
                let StaticValue::Text(encoded) =
                    self.eval(call.arguments[0].as_expression()?, state)?
                else {
                    return None;
                };
                decode_atob(&encoded).map(StaticValue::BinaryString)
            }
            Expression::NewExpression(new_expression)
                if !new_expression.arguments.iter().any(Argument::is_spread)
                    && unresolved_global(self.scoping, &new_expression.callee, "Uint8Array") =>
            {
                let [argument] = new_expression.arguments.as_slice() else {
                    return None;
                };
                let StaticValue::Number(byte_len) = self.eval(argument.as_expression()?, state)?
                else {
                    return None;
                };
                state.allocate(byte_len, new_expression.span)
            }
            Expression::StaticMemberExpression(member) if !member.optional => {
                if member.property.name.as_str() != "length" {
                    return None;
                }
                match self.eval(&member.object, state)? {
                    StaticValue::Text(value) => {
                        Some(StaticValue::Number(value.encode_utf16().count()))
                    }
                    StaticValue::BinaryString(value) => Some(StaticValue::Number(value.len())),
                    StaticValue::Buffer(id) => state
                        .buffers
                        .get(id)
                        .map(|buffer| StaticValue::Number(buffer.bytes.len())),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn helper_call(&self, call: &oxc_ast::ast::CallExpression<'_>, state: &mut EvalState) -> bool {
        if call.optional || call.arguments.iter().any(Argument::is_spread) {
            return false;
        }
        let Some(symbol) = symbol_of(self.scoping, &call.callee) else {
            return false;
        };
        let Some(helper) = self.helpers.get(&symbol) else {
            return false;
        };
        if call.span.start < helper.available_from
            || call.arguments.len() <= helper.source_param.max(helper.offset_param)
        {
            return false;
        }

        let Some(source_expression) = call.arguments[helper.source_param].as_expression() else {
            return false;
        };
        let Some(offset_expression) = call.arguments[helper.offset_param].as_expression() else {
            return false;
        };
        let Some(source) = self.eval(source_expression, state) else {
            return false;
        };
        let Some(StaticValue::Number(offset)) = self.eval(offset_expression, state) else {
            return false;
        };

        let bytes = match source {
            StaticValue::BinaryString(bytes) => bytes,
            StaticValue::Text(text) => {
                let mut bytes = Vec::with_capacity(text.len());
                for unit in text.encode_utf16() {
                    let Ok(byte) = u8::try_from(unit) else {
                        return false;
                    };
                    bytes.push(byte);
                }
                bytes
            }
            _ => return false,
        };

        let Some(StaticValue::Buffer(buffer_id)) = state.values.get(&helper.buffer_symbol).cloned()
        else {
            return false;
        };
        let Some(buffer) = state.buffers.get_mut(buffer_id) else {
            return false;
        };
        let Some(end) = offset.checked_add(bytes.len()) else {
            buffer.valid = false;
            state.last_invalidation_reason = Some("copy_offset_overflow");
            return true;
        };
        if end > buffer.bytes.len() {
            buffer.valid = false;
            state.last_invalidation_reason = Some("copy_out_of_bounds");
            return true;
        }
        buffer.bytes[offset..end].copy_from_slice(&bytes);
        buffer.writes += 1;
        state.helper_calls_succeeded += 1;
        true
    }
}

fn expression_buffer_ids(
    expression: &Expression<'_>,
    scoping: &Scoping,
    state: &EvalState,
) -> Vec<usize> {
    struct Collector<'c, 's> {
        scoping: &'c Scoping,
        state: &'s EvalState,
        out: Vec<usize>,
    }
    impl<'a> Visit<'a> for Collector<'_, '_> {
        fn visit_identifier_reference(
            &mut self,
            identifier: &oxc_ast::ast::IdentifierReference<'a>,
        ) {
            let Some(reference_id) = identifier.reference_id.get() else {
                return;
            };
            let Some(symbol) = statically_resolved_symbol(self.scoping, reference_id) else {
                return;
            };
            if let Some(StaticValue::Buffer(id)) = self.state.values.get(&symbol) {
                if !self.out.contains(id) {
                    self.out.push(*id);
                }
            }
        }
    }

    let mut collector = Collector {
        scoping,
        state,
        out: Vec::new(),
    };
    collector.visit_expression(expression);
    collector.out
}

fn normal_expression(
    expression: &Expression<'_>,
    evaluator: &Evaluator<'_, '_>,
    state: &mut EvalState,
) {
    match unparenthesized(expression) {
        Expression::SequenceExpression(sequence) => {
            for item in &sequence.expressions {
                normal_expression(item, evaluator, state);
            }
        }
        Expression::AssignmentExpression(assignment) if assignment.operator.as_str() == "=" => {
            if let Some(symbol) = assignment_target_symbol(evaluator.scoping, &assignment.left) {
                if let Some(value) = evaluator.eval(&assignment.right, state) {
                    state.values.insert(symbol, value);
                } else {
                    normal_expression(&assignment.right, evaluator, state);
                    state.values.remove(&symbol);
                }
            } else {
                for id in expression_buffer_ids(expression, evaluator.scoping, state) {
                    state.invalidate_buffer(id, "unsupported_buffer_assignment");
                }
            }
        }
        Expression::CallExpression(call) => {
            if evaluator.helper_call(call, state) || evaluator.eval(expression, state).is_some() {
                return;
            }
            let local_callee = symbol_of(evaluator.scoping, &call.callee).is_some();
            let direct_eval = unresolved_global(evaluator.scoping, &call.callee, "eval");
            if local_callee || direct_eval {
                state.invalidate_all_buffers("unknown_local_call_or_direct_eval");
                return;
            }
            for argument in &call.arguments {
                let Some(argument) = argument.as_expression() else {
                    state.invalidate_all_buffers("spread_argument_to_unknown_call");
                    continue;
                };
                for id in expression_buffer_ids(argument, evaluator.scoping, state) {
                    state.invalidate_buffer(id, "buffer_passed_to_unknown_call");
                }
            }
        }
        _ => {
            for id in expression_buffer_ids(expression, evaluator.scoping, state) {
                state.invalidate_buffer(id, "unsupported_buffer_use");
            }
        }
    }
}

fn normal_statement(
    statement: &Statement<'_>,
    evaluator: &Evaluator<'_, '_>,
    state: &mut EvalState,
) {
    match statement {
        Statement::VariableDeclaration(declaration) => {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    state.invalidate_all_buffers("unsupported_binding_pattern");
                    continue;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    state.invalidate_all_buffers("unsupported_binding_pattern");
                    continue;
                };
                let Some(initializer) = &declarator.init else {
                    state.values.remove(&symbol);
                    continue;
                };
                if matches!(
                    initializer,
                    Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_)
                ) {
                    state.values.remove(&symbol);
                    continue;
                }
                if let Some(value) = evaluator.eval(initializer, state) {
                    state.values.insert(symbol, value);
                } else {
                    normal_expression(initializer, evaluator, state);
                    state.values.remove(&symbol);
                }
            }
        }
        Statement::ExpressionStatement(statement) => {
            normal_expression(&statement.expression, evaluator, state);
        }
        Statement::FunctionDeclaration(_) | Statement::EmptyStatement(_) => {}
        _ => state.invalidate_all_buffers("unsupported_statement"),
    }
}

fn sink_argument<'a>(expression: &'a Expression<'a>, sink: Sink) -> Option<&'a Expression<'a>> {
    match unparenthesized(expression) {
        Expression::CallExpression(call) if call.span == sink.span => {
            call.arguments.first()?.as_expression()
        }
        Expression::NewExpression(new_expression) if new_expression.span == sink.span => {
            new_expression.arguments.first()?.as_expression()
        }
        _ => None,
    }
}

fn artifact_at_sink(
    expression: &Expression<'_>,
    sink: Sink,
    evaluator: &Evaluator<'_, '_>,
    state: &mut EvalState,
) -> Option<RecoveredByteArtifact> {
    let Some(argument) = sink_argument(expression, sink) else {
        state.sink_failure = Some("sink_argument_missing");
        return None;
    };
    let Some(value) = evaluator.eval(argument, state) else {
        state.sink_failure = Some("sink_argument_not_static");
        return None;
    };
    let StaticValue::Buffer(id) = value else {
        state.sink_failure = Some("sink_argument_not_buffer");
        return None;
    };
    let Some(buffer) = state.buffers.get(id) else {
        state.sink_failure = Some("sink_buffer_missing");
        return None;
    };
    if !buffer.valid {
        state.sink_failure = Some("sink_buffer_invalid");
        return None;
    }
    if !buffer.bytes.starts_with(b"\0asm") {
        state.sink_failure = Some("sink_buffer_not_wasm_magic");
        return None;
    }
    Some(RecoveredByteArtifact {
        sha256: sha256_hex(&buffer.bytes),
        bytes: buffer.bytes.clone(),
        sink_start: sink.span.start,
        sink_end: sink.span.end,
        sink_kind: sink.kind,
        allocation_start: buffer.allocation_span.start,
        allocation_end: buffer.allocation_span.end,
        copy_writes: buffer.writes,
        standard_builtins_required: true,
    })
}

fn expression_to_sink(
    expression: &Expression<'_>,
    sink: Sink,
    evaluator: &Evaluator<'_, '_>,
    state: &mut EvalState,
) -> Option<RecoveredByteArtifact> {
    if expression.span() == sink.span {
        return artifact_at_sink(expression, sink, evaluator, state);
    }

    match unparenthesized(expression) {
        Expression::SequenceExpression(sequence) => {
            for item in &sequence.expressions {
                if span_contains(item.span(), sink.span) {
                    return expression_to_sink(item, sink, evaluator, state);
                }
                normal_expression(item, evaluator, state);
            }
            None
        }
        Expression::AssignmentExpression(assignment) => {
            if span_contains(assignment.right.span(), sink.span) {
                expression_to_sink(&assignment.right, sink, evaluator, state)
            } else {
                None
            }
        }
        Expression::CallExpression(call) => {
            if span_contains(call.callee.span(), sink.span) {
                return expression_to_sink(&call.callee, sink, evaluator, state);
            }
            normal_expression(&call.callee, evaluator, state);
            for argument in &call.arguments {
                let Some(argument) = argument.as_expression() else {
                    state.invalidate_all_buffers("unsupported_binding_pattern");
                    continue;
                };
                if span_contains(argument.span(), sink.span) {
                    return expression_to_sink(argument, sink, evaluator, state);
                }
                normal_expression(argument, evaluator, state);
            }
            None
        }
        Expression::StaticMemberExpression(member) => {
            expression_to_sink(&member.object, sink, evaluator, state)
        }
        Expression::ComputedMemberExpression(member) => {
            if span_contains(member.object.span(), sink.span) {
                expression_to_sink(&member.object, sink, evaluator, state)
            } else if span_contains(member.expression.span(), sink.span) {
                normal_expression(&member.object, evaluator, state);
                expression_to_sink(&member.expression, sink, evaluator, state)
            } else {
                None
            }
        }
        Expression::ConditionalExpression(conditional) => {
            normal_expression(&conditional.test, evaluator, state);
            if span_contains(conditional.consequent.span(), sink.span) {
                expression_to_sink(&conditional.consequent, sink, evaluator, state)
            } else if span_contains(conditional.alternate.span(), sink.span) {
                expression_to_sink(&conditional.alternate, sink, evaluator, state)
            } else {
                None
            }
        }
        Expression::LogicalExpression(logical) => {
            if span_contains(logical.left.span(), sink.span) {
                expression_to_sink(&logical.left, sink, evaluator, state)
            } else if span_contains(logical.right.span(), sink.span) {
                normal_expression(&logical.left, evaluator, state);
                expression_to_sink(&logical.right, sink, evaluator, state)
            } else {
                None
            }
        }
        Expression::UnaryExpression(unary) => {
            expression_to_sink(&unary.argument, sink, evaluator, state)
        }
        Expression::ArrayExpression(array) => array
            .elements
            .iter()
            .filter_map(|element| element.as_expression())
            .find(|element| span_contains(element.span(), sink.span))
            .and_then(|element| expression_to_sink(element, sink, evaluator, state)),
        Expression::ObjectExpression(object) => object.properties.iter().find_map(|item| {
            let ObjectPropertyKind::ObjectProperty(property) = item else {
                return None;
            };
            span_contains(property.value.span(), sink.span)
                .then(|| expression_to_sink(&property.value, sink, evaluator, state))
                .flatten()
        }),
        Expression::FunctionExpression(function) => {
            *state = EvalState::default();
            statements_to_sink(&function.body.as_ref()?.statements, sink, evaluator, state)
        }
        Expression::ArrowFunctionExpression(function) => {
            let oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) = &function.body else {
                return None;
            };
            *state = EvalState::default();
            statements_to_sink(&body.statements, sink, evaluator, state)
        }
        _ => None,
    }
}

fn statement_to_sink(
    statement: &Statement<'_>,
    sink: Sink,
    evaluator: &Evaluator<'_, '_>,
    state: &mut EvalState,
) -> Option<RecoveredByteArtifact> {
    match statement {
        Statement::BlockStatement(block) => statements_to_sink(&block.body, sink, evaluator, state),
        Statement::IfStatement(branch) => {
            normal_expression(&branch.test, evaluator, state);
            if span_contains(branch.consequent.span(), sink.span) {
                statement_to_sink(&branch.consequent, sink, evaluator, state)
            } else if branch
                .alternate
                .as_ref()
                .is_some_and(|alternate| span_contains(alternate.span(), sink.span))
            {
                statement_to_sink(branch.alternate.as_ref()?, sink, evaluator, state)
            } else {
                None
            }
        }
        Statement::ExpressionStatement(statement) => {
            expression_to_sink(&statement.expression, sink, evaluator, state)
        }
        Statement::VariableDeclaration(declaration) => {
            for declarator in &declaration.declarations {
                let Some(initializer) = &declarator.init else {
                    continue;
                };
                if span_contains(initializer.span(), sink.span) {
                    return expression_to_sink(initializer, sink, evaluator, state);
                }
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    state.invalidate_all_buffers("unsupported_binding_pattern");
                    continue;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    state.invalidate_all_buffers("unsupported_binding_pattern");
                    continue;
                };
                if matches!(
                    initializer,
                    Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_)
                ) {
                    state.values.remove(&symbol);
                    continue;
                }
                if let Some(value) = evaluator.eval(initializer, state) {
                    state.values.insert(symbol, value);
                } else {
                    normal_expression(initializer, evaluator, state);
                    state.values.remove(&symbol);
                }
            }
            None
        }
        Statement::FunctionDeclaration(function) => {
            *state = EvalState::default();
            statements_to_sink(&function.body.as_ref()?.statements, sink, evaluator, state)
        }
        Statement::ReturnStatement(statement) => statement
            .argument
            .as_ref()
            .filter(|argument| span_contains(argument.span(), sink.span))
            .and_then(|argument| expression_to_sink(argument, sink, evaluator, state)),
        _ => None,
    }
}

fn statements_to_sink(
    statements: &[Statement<'_>],
    sink: Sink,
    evaluator: &Evaluator<'_, '_>,
    state: &mut EvalState,
) -> Option<RecoveredByteArtifact> {
    for statement in statements {
        if span_contains(statement.span(), sink.span) {
            return statement_to_sink(statement, sink, evaluator, state);
        }
        if statement.span().end <= sink.span.start {
            normal_statement(statement, evaluator, state);
        }
    }
    None
}

#[must_use]
pub fn recover_webassembly_byte_artifacts_from_program(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> StaticByteRecoverySummary {
    let helpers = collect_helpers(program, scoping);
    let mut sink_collector = SinkCollector {
        scoping,
        sinks: Vec::new(),
    };
    sink_collector.visit_program(program);

    let evaluator = Evaluator {
        scoping,
        helpers: &helpers,
    };
    let sink_count = sink_collector.sinks.len();
    let mut out = Vec::new();
    let mut sink_diagnostics = Vec::with_capacity(sink_count);
    for sink in sink_collector.sinks {
        let mut state = EvalState::default();
        let artifact = statements_to_sink(&program.body, sink, &evaluator, &mut state);
        let recovered = artifact.is_some();
        if let Some(artifact) = artifact {
            out.push(artifact);
        } else if state.sink_failure.is_none() {
            state.sink_failure = Some("sink_path_not_reached");
        }
        sink_diagnostics.push(SinkRecoveryDiagnostic {
            sink_start: sink.span.start,
            sink_end: sink.span.end,
            sink_kind: sink.kind,
            recovered,
            buffers_allocated: state.buffers.len(),
            valid_buffers: state.buffers.iter().filter(|buffer| buffer.valid).count(),
            helper_calls_succeeded: state.helper_calls_succeeded,
            last_invalidation_reason: state.last_invalidation_reason,
            sink_failure: state.sink_failure,
        });
    }
    out.sort_by_key(|artifact| artifact.sink_start);
    StaticByteRecoverySummary {
        artifacts: out,
        proven_copy_helpers: helpers.len(),
        webassembly_sinks: sink_count,
        sink_diagnostics,
    }
}

/// Recover exact byte buffers that are proven to reach a WebAssembly compilation sink.
///
/// This evaluates only a bounded set of deterministic local byte-building operations.
/// It does not execute JavaScript and fails closed when buffers escape, writes are
/// ambiguous, or dynamic scope prevents static name resolution.
pub fn analyze_webassembly_byte_artifacts(
    source: &str,
) -> anyhow::Result<StaticByteRecoverySummary> {
    for source_type in [SourceType::unambiguous(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, source_type);
        if !parsed.is_clean() {
            continue;
        }
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        if !semantic.diagnostics.is_empty() {
            continue;
        }
        return Ok(recover_webassembly_byte_artifacts_from_program(
            &parsed.program,
            semantic.semantic.scoping(),
        ));
    }
    anyhow::bail!("JavaScript did not parse as unambiguous or CommonJS source")
}

pub fn recover_webassembly_byte_artifacts(
    source: &str,
) -> anyhow::Result<Vec<RecoveredByteArtifact>> {
    Ok(analyze_webassembly_byte_artifacts(source)?.artifacts)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn recover(source: &str) -> Vec<RecoveredByteArtifact> {
        recover_webassembly_byte_artifacts(source).unwrap_or_default()
    }

    #[test]
    fn recovers_split_base64_byte_builder_without_target_specific_names() {
        let source = r#"
            function load(imports) {
                var output = new Uint8Array(8);
                var decode = atob;
                var reverse = function(chunk, offset) {
                    for (var index = chunk.length; index--;) {
                        output[offset + index] = chunk.charCodeAt(index);
                    }
                };
                var forward = function(offset, chunk) {
                    for (var index = 0; index < chunk.length; index++)
                        output[offset + index] = chunk.charCodeAt(index);
                };
                forward(0, decode("AGFz"));
                reverse(decode("bQEAAAA="), 3);
                return WebAssembly.instantiate(output, imports);
            }
        "#;
        let artifacts = recover(source);
        assert_eq!(artifacts.len(), 1);
        assert_eq!(artifacts[0].bytes, b"\0asm\x01\0\0\0");
        assert_eq!(artifacts[0].copy_writes, 2);
    }

    #[test]
    fn supports_offset_increment_copy_helpers_and_extra_call_arguments() {
        let source = r#"
            function load(imports) {
                var bytes = new Uint8Array(8), decode = atob;
                var append = function(chunk, offset) {
                    for (var i = 0; i < chunk.length; offset++, i++) {
                        bytes[offset] = chunk.charCodeAt(i);
                    }
                };
                append(decode("AGFzbQ=="), 0, 12345);
                append(decode("AQAAAA=="), 4);
                return WebAssembly.instantiate(bytes, imports);
            }
        "#;
        let artifacts = recover(source);
        assert_eq!(artifacts.len(), 1);
        assert_eq!(artifacts[0].bytes, b"\0asm\x01\0\0\0");
    }

    #[test]
    fn fails_closed_when_buffer_escapes_or_copy_is_out_of_bounds() {
        let escaped = r#"
            function load(imports) {
                var bytes = new Uint8Array(8), decode = atob;
                var copy = function(offset, chunk) {
                    for (var i = 0; i < chunk.length; i++)
                        bytes[offset + i] = chunk.charCodeAt(i);
                };
                copy(0, decode("AGFzbQEAAAA="));
                unknownLocal(bytes);
                return WebAssembly.instantiate(bytes, imports);
            }
        "#;
        assert!(recover(escaped).is_empty());

        let out_of_bounds = r#"
            function load(imports) {
                var bytes = new Uint8Array(4), decode = atob;
                var copy = function(offset, chunk) {
                    for (var i = 0; i < chunk.length; i++)
                        bytes[offset + i] = chunk.charCodeAt(i);
                };
                copy(0, decode("AGFzbQEAAAA="));
                return WebAssembly.instantiate(bytes, imports);
            }
        "#;
        assert!(recover(out_of_bounds).is_empty());
    }

    #[test]
    fn shadowed_atob_or_uint8array_is_not_assumed_builtin() {
        let source = r#"
            function load(imports, atob, Uint8Array) {
                var bytes = new Uint8Array(8), decode = atob;
                var copy = function(offset, chunk) {
                    for (var i = 0; i < chunk.length; i++)
                        bytes[offset + i] = chunk.charCodeAt(i);
                };
                copy(0, decode("AGFzbQEAAAA="));
                return WebAssembly.instantiate(bytes, imports);
            }
        "#;
        assert!(recover(source).is_empty());
    }

    #[test]
    fn dynamic_with_scope_blocks_builtin_resolution_without_poisoning_siblings() {
        let blocked = r#"
            function load(imports, scope) {
                var bytes = new Uint8Array(8);
                var decode;
                with (scope) { decode = atob; }
                var copy = function(offset, chunk) {
                    for (var i = 0; i < chunk.length; i++)
                        bytes[offset + i] = chunk.charCodeAt(i);
                };
                copy(0, decode("AGFzbQEAAAA="));
                return WebAssembly.instantiate(bytes, imports);
            }
        "#;
        assert!(recover(blocked).is_empty());

        let safe = r#"
            function load(imports, scope) {
                with (scope) { void maybeDynamic; }
                var bytes = new Uint8Array(8), decode = atob;
                var copy = function(offset, chunk) {
                    for (var i = 0; i < chunk.length; i++)
                        bytes[offset + i] = chunk.charCodeAt(i);
                };
                copy(0, decode("AGFzbQEAAAA="));
                return WebAssembly.instantiate(bytes, imports);
            }
        "#;
        assert_eq!(recover(safe).len(), 1);
    }

    #[test]
    fn traverses_semantically_transparent_unary_iife_wrapper() {
        let source = r#"
            !function wrapper() {
                var bytes = new Uint8Array(8), decode = atob;
                var copy = function(offset, chunk) {
                    for (var i = 0; i < chunk.length; i++)
                        bytes[offset + i] = chunk.charCodeAt(i);
                };
                copy(0, decode("AGFzbQEAAAA="));
                WebAssembly.instantiate(bytes, {});
            }();
        "#;
        assert_eq!(recover(source).len(), 1);
    }

    #[test]
    fn traverses_function_values_in_literal_dispatch_containers() {
        let source = r#"
            const table = [
                7,
                flag ? function load(imports) {
                    var bytes = new Uint8Array(8), decode = atob;
                    var copy = function(offset, chunk) {
                        for (var i = 0; i < chunk.length; i++)
                            bytes[offset + i] = chunk.charCodeAt(i);
                    };
                    copy(0, decode("AGFzbQEAAAA="));
                    return WebAssembly.instantiate(bytes, imports);
                } : 9
            ];
        "#;
        assert_eq!(recover(source).len(), 1);

        let object = r#"
            const table = {
                load: function(imports) {
                    var bytes = new Uint8Array(8), decode = atob;
                    var copy = function(offset, chunk) {
                        for (var i = 0; i < chunk.length; i++)
                            bytes[offset + i] = chunk.charCodeAt(i);
                    };
                    copy(0, decode("AGFzbQEAAAA="));
                    return WebAssembly.instantiate(bytes, imports);
                }
            };
        "#;
        assert_eq!(recover(object).len(), 1);
    }

    #[test]
    fn rejects_copy_helpers_that_escape_direct_call_control() {
        let source = r#"
            function load(imports, observer) {
                var bytes = new Uint8Array(8), decode = atob;
                var copy = function(offset, chunk) {
                    for (var i = 0; i < chunk.length; i++)
                        bytes[offset + i] = chunk.charCodeAt(i);
                };
                observer(copy);
                copy(0, decode("AGFzbQEAAAA="));
                return WebAssembly.instantiate(bytes, imports);
            }
        "#;
        assert!(recover(source).is_empty());
    }

    #[test]
    fn rejects_buffer_capture_escaping_through_unknown_callback() {
        let source = r#"
            function load(imports) {
                var bytes = new Uint8Array(8), decode = atob;
                var copy = function(offset, chunk) {
                    for (var i = 0; i < chunk.length; i++)
                        bytes[offset + i] = chunk.charCodeAt(i);
                };
                copy(0, decode("AGFzbQEAAAA="));
                setTimeout(function() { bytes[0] = 7; }, 0);
                return WebAssembly.instantiate(bytes, imports);
            }
        "#;
        assert!(recover(source).is_empty());
    }
}
