use jsvm_safe_core::{eval_static_primitive, string_literal_value};
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, AssignmentTarget, BindingPattern, CallExpression, Expression,
    Function, FunctionBody, NewExpression, ObjectPropertyKind, Program, Statement,
    VariableDeclaration,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::GetSpan;
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct FunctionKey {
    start: u32,
    end: u32,
}

impl FunctionKey {
    fn of(function: &Function<'_>) -> Self {
        Self {
            start: function.span.start,
            end: function.span.end,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ObjectOrigin {
    allocation_start: u32,
    allocation_end: u32,
    constructor: FunctionKey,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProvenOriginContext {
    pub function_start: u32,
    pub function_end: u32,
    pub allocation_start: u32,
    pub allocation_end: u32,
    pub constructor_start: u32,
    pub constructor_end: u32,
    pub this_origin: bool,
    pub parameter_indices: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenOriginDirectCall {
    pub call_start: u32,
    pub call_end: u32,
    pub caller: ProvenOriginContext,
    pub callee: ProvenOriginContext,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenMemberReceiverOrigin {
    pub context: ProvenOriginContext,
    pub call_start: u32,
    pub call_end: u32,
    pub receiver_start: u32,
    pub receiver_end: u32,
    pub property: String,
    pub allocation_start: u32,
    pub allocation_end: u32,
    pub constructor_start: u32,
    pub constructor_end: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenMemberWriteOrigin {
    pub context: ProvenOriginContext,
    pub write_start: u32,
    pub write_end: u32,
    pub receiver_start: u32,
    pub receiver_end: u32,
    /// `None` means the receiver identity is exact but the computed key is not.
    pub property: Option<String>,
    pub allocation_start: u32,
    pub allocation_end: u32,
    pub constructor_start: u32,
    pub constructor_end: u32,
    pub operation: &'static str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenOriginExposure {
    pub context: ProvenOriginContext,
    pub exposure_start: u32,
    pub exposure_end: u32,
    pub allocation_start: u32,
    pub allocation_end: u32,
    pub constructor_start: u32,
    pub constructor_end: u32,
    pub kind: &'static str,
}

#[derive(Clone)]
struct FunctionInfo {
    parameters: Vec<SymbolId>,
    dynamic_scope: bool,
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

fn parameter_symbols(function: &Function<'_>) -> Option<Vec<SymbolId>> {
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

#[derive(Default)]
struct DynamicScopeProbe {
    direct_eval: bool,
    with_statement: bool,
}

impl<'a> Visit<'a> for DynamicScopeProbe {
    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }

    fn visit_with_statement(&mut self, _statement: &oxc_ast::ast::WithStatement<'a>) {
        self.with_statement = true;
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if let Expression::Identifier(identifier) = last_sequence_expression(&call.callee) {
            if identifier.name.as_str() == "eval" {
                self.direct_eval = true;
            }
        }
        walk::walk_call_expression(self, call);
    }
}

fn has_dynamic_scope(body: &FunctionBody<'_>) -> bool {
    let mut probe = DynamicScopeProbe::default();
    probe.visit_function_body(body);
    probe.direct_eval || probe.with_statement
}

struct FunctionCollector {
    by_key: HashMap<FunctionKey, FunctionInfo>,
    by_symbol: HashMap<SymbolId, FunctionKey>,
}

impl FunctionCollector {
    fn new() -> Self {
        Self {
            by_key: HashMap::new(),
            by_symbol: HashMap::new(),
        }
    }

    fn record(&mut self, function: &Function<'_>) {
        if function.r#async || function.generator {
            return;
        }
        let (Some(body), Some(parameters)) = (&function.body, parameter_symbols(function)) else {
            return;
        };
        let key = FunctionKey::of(function);
        self.by_key.entry(key).or_insert_with(|| FunctionInfo {
            parameters,
            dynamic_scope: has_dynamic_scope(body),
        });
        if let Some(symbol) = function
            .id
            .as_ref()
            .and_then(|identifier| identifier.symbol_id.get())
        {
            self.by_symbol.insert(symbol, key);
        }
    }
}

impl<'a> Visit<'a> for FunctionCollector {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.record(function);
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
            self.record(function);
            if let Some(symbol) = identifier.symbol_id.get() {
                self.by_symbol.insert(symbol, FunctionKey::of(function));
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FunctionContext {
    function: FunctionKey,
    this_origin: Option<ObjectOrigin>,
    parameter_origins: Vec<Option<ObjectOrigin>>,
}

impl FunctionContext {
    fn proven_origin_context(&self, origin: ObjectOrigin) -> Option<ProvenOriginContext> {
        let parameter_indices = self
            .parameter_origins
            .iter()
            .enumerate()
            .filter_map(|(index, candidate)| (*candidate == Some(origin)).then_some(index))
            .collect::<Vec<_>>();
        let this_origin = self.this_origin == Some(origin);
        if !this_origin && parameter_indices.is_empty() {
            return None;
        }
        Some(ProvenOriginContext {
            function_start: self.function.start,
            function_end: self.function.end,
            allocation_start: origin.allocation_start,
            allocation_end: origin.allocation_end,
            constructor_start: origin.constructor.start,
            constructor_end: origin.constructor.end,
            this_origin,
            parameter_indices,
        })
    }
}

struct AllocationCollector<'c, 'f> {
    scoping: &'c Scoping,
    functions: &'f HashMap<SymbolId, FunctionKey>,
    contexts: Vec<FunctionContext>,
}

impl<'a> Visit<'a> for AllocationCollector<'_, '_> {
    fn visit_new_expression(&mut self, expression: &NewExpression<'a>) {
        let callee = last_sequence_expression(&expression.callee);
        if let Some(symbol) = reference_symbol(self.scoping, callee)
            .filter(|symbol| symbol_binding_is_stable(self.scoping, *symbol))
        {
            if let Some(function) = self.functions.get(&symbol).copied() {
                let origin = ObjectOrigin {
                    allocation_start: expression.span.start,
                    allocation_end: expression.span.end,
                    constructor: function,
                };
                self.contexts.push(FunctionContext {
                    function,
                    this_origin: Some(origin),
                    parameter_origins: Vec::new(),
                });
            }
        }
        walk::walk_new_expression(self, expression);
    }
}

struct ContextProbe<'c, 'f> {
    scoping: &'c Scoping,
    functions: &'f HashMap<SymbolId, FunctionKey>,
    function_info: &'f HashMap<FunctionKey, FunctionInfo>,
    context: &'f FunctionContext,
    parameter_origins: HashMap<SymbolId, ObjectOrigin>,
    local_origins: HashMap<SymbolId, ObjectOrigin>,
    discovered: Vec<FunctionContext>,
    member_calls: Vec<ProvenMemberReceiverOrigin>,
    member_writes: Vec<ProvenMemberWriteOrigin>,
    exposures: Vec<ProvenOriginExposure>,
    direct_calls: Vec<ProvenOriginDirectCall>,
    target: FunctionKey,
    active: bool,
}

impl<'c, 'f> ContextProbe<'c, 'f> {
    fn new(
        scoping: &'c Scoping,
        functions: &'f HashMap<SymbolId, FunctionKey>,
        function_info: &'f HashMap<FunctionKey, FunctionInfo>,
        context: &'f FunctionContext,
        info: &FunctionInfo,
    ) -> Self {
        let parameter_origins = info
            .parameters
            .iter()
            .zip(context.parameter_origins.iter())
            .filter_map(|(symbol, origin)| origin.map(|origin| (*symbol, origin)))
            .collect();
        Self {
            scoping,
            functions,
            function_info,
            context,
            parameter_origins,
            local_origins: HashMap::new(),
            discovered: Vec::new(),
            member_calls: Vec::new(),
            member_writes: Vec::new(),
            exposures: Vec::new(),
            direct_calls: Vec::new(),
            target: context.function,
            active: false,
        }
    }

    fn expression_origin(&self, expression: &Expression<'_>) -> Option<ObjectOrigin> {
        match expression {
            Expression::ParenthesizedExpression(parenthesized) => {
                self.expression_origin(&parenthesized.expression)
            }
            Expression::SequenceExpression(sequence) => sequence
                .expressions
                .last()
                .and_then(|expression| self.expression_origin(expression)),
            Expression::Identifier(_) => {
                let symbol = reference_symbol(self.scoping, expression)?;
                if !symbol_binding_is_stable(self.scoping, symbol) {
                    return None;
                }
                self.parameter_origins
                    .get(&symbol)
                    .or_else(|| self.local_origins.get(&symbol))
                    .copied()
            }
            Expression::ThisExpression(_) => self.context.this_origin,
            _ => None,
        }
    }

    fn direct_callee(&self, expression: &Expression<'_>) -> Option<FunctionKey> {
        let expression = last_sequence_expression(expression);
        let symbol = reference_symbol(self.scoping, expression)?;
        if !symbol_binding_is_stable(self.scoping, symbol) {
            return None;
        }
        self.functions.get(&symbol).copied()
    }

    fn record_direct_call(&mut self, call: &CallExpression<'_>, callee: FunctionKey) {
        let Some(info) = self.function_info.get(&callee) else {
            return;
        };
        if info.dynamic_scope {
            return;
        }
        let parameter_origins = info
            .parameters
            .iter()
            .enumerate()
            .map(|(index, _)| {
                call.arguments
                    .get(index)
                    .and_then(Argument::as_expression)
                    .and_then(|argument| self.expression_origin(argument))
            })
            .collect::<Vec<_>>();
        if parameter_origins.iter().all(Option::is_none) {
            return;
        }
        let child = FunctionContext {
            function: callee,
            this_origin: None,
            parameter_origins,
        };
        let origins = child
            .parameter_origins
            .iter()
            .filter_map(|origin| *origin)
            .collect::<HashSet<_>>();
        for origin in origins {
            if let (Some(caller), Some(callee)) = (
                self.context.proven_origin_context(origin),
                child.proven_origin_context(origin),
            ) {
                self.direct_calls.push(ProvenOriginDirectCall {
                    call_start: call.span.start,
                    call_end: call.span.end,
                    caller,
                    callee,
                });
            }
        }
        self.discovered.push(child);
    }

    fn record_exposure(
        &mut self,
        expression: &Expression<'_>,
        span: oxc_span::Span,
        kind: &'static str,
    ) {
        let Some(origin) = self.expression_origin(expression) else {
            return;
        };
        let Some(context) = self.context.proven_origin_context(origin) else {
            return;
        };
        self.exposures.push(ProvenOriginExposure {
            context,
            exposure_start: span.start,
            exposure_end: span.end,
            allocation_start: origin.allocation_start,
            allocation_end: origin.allocation_end,
            constructor_start: origin.constructor.start,
            constructor_end: origin.constructor.end,
            kind,
        });
    }

    fn record_member_write(
        &mut self,
        receiver: &Expression<'_>,
        property: Option<String>,
        span: oxc_span::Span,
        operation: &'static str,
    ) {
        let Some(origin) = self.expression_origin(receiver) else {
            return;
        };
        let Some(context) = self.context.proven_origin_context(origin) else {
            return;
        };
        self.member_writes.push(ProvenMemberWriteOrigin {
            context,
            write_start: span.start,
            write_end: span.end,
            receiver_start: receiver.span().start,
            receiver_end: receiver.span().end,
            property,
            allocation_start: origin.allocation_start,
            allocation_end: origin.allocation_end,
            constructor_start: origin.constructor.start,
            constructor_end: origin.constructor.end,
            operation,
        });
    }

    fn assignment_member<'e>(
        &self,
        target: &'e AssignmentTarget<'e>,
    ) -> Option<(&'e Expression<'e>, Option<String>)> {
        match target {
            AssignmentTarget::StaticMemberExpression(member) if !member.optional => {
                Some((&member.object, Some(member.property.name.to_string())))
            }
            AssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
                let property = match last_sequence_expression(&member.expression) {
                    Expression::StringLiteral(property) => string_literal_value(property),
                    _ => None,
                };
                Some((&member.object, property))
            }
            _ => None,
        }
    }

    fn static_member<'e>(
        &self,
        expression: &'e Expression<'e>,
    ) -> Option<(&'e Expression<'e>, String)> {
        match last_sequence_expression(expression) {
            Expression::StaticMemberExpression(member) if !member.optional => {
                Some((&member.object, member.property.name.to_string()))
            }
            Expression::ComputedMemberExpression(member) if !member.optional => {
                let Expression::StringLiteral(property) =
                    last_sequence_expression(&member.expression)
                else {
                    return None;
                };
                Some((&member.object, string_literal_value(property)?))
            }
            _ => None,
        }
    }
}

impl<'a> Visit<'a> for ContextProbe<'_, '_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        let key = FunctionKey::of(function);
        if self.active {
            return;
        }
        if key == self.target {
            self.active = true;
            if let Some(body) = &function.body {
                self.visit_function_body(body);
            }
            self.active = false;
            return;
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        if !self.active {
            walk::walk_arrow_function_expression(self, function);
        }
    }

    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        if self.active {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    continue;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    continue;
                };
                if !symbol_binding_is_stable(self.scoping, symbol) {
                    continue;
                }
                let Some(init) = declarator.init.as_ref() else {
                    continue;
                };
                if let Some(origin) = self.expression_origin(init) {
                    self.local_origins.insert(symbol, origin);
                }
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_return_statement(&mut self, statement: &oxc_ast::ast::ReturnStatement<'a>) {
        if self.active {
            if let Some(argument) = statement.argument.as_ref() {
                self.record_exposure(argument, statement.span, "return");
            }
        }
        walk::walk_return_statement(self, statement);
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if self.active {
            if let Some((receiver, property)) = self.assignment_member(&assignment.left) {
                self.record_member_write(receiver, property, assignment.span, "assignment");
                self.record_exposure(&assignment.right, assignment.span, "store");
            } else if !matches!(
                assignment.left,
                AssignmentTarget::AssignmentTargetIdentifier(_)
            ) {
                self.record_exposure(&assignment.right, assignment.span, "store");
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_update_expression(&mut self, update: &oxc_ast::ast::UpdateExpression<'a>) {
        if self.active {
            match &update.argument {
                oxc_ast::ast::SimpleAssignmentTarget::StaticMemberExpression(member)
                    if !member.optional =>
                {
                    self.record_member_write(
                        &member.object,
                        Some(member.property.name.to_string()),
                        update.span,
                        "update",
                    );
                }
                oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member)
                    if !member.optional =>
                {
                    let property = match last_sequence_expression(&member.expression) {
                        Expression::StringLiteral(property) => string_literal_value(property),
                        _ => None,
                    };
                    self.record_member_write(&member.object, property, update.span, "update");
                }
                _ => {}
            }
        }
        walk::walk_update_expression(self, update);
    }

    fn visit_unary_expression(&mut self, unary: &oxc_ast::ast::UnaryExpression<'a>) {
        if self.active && unary.operator.as_str() == "delete" {
            match last_sequence_expression(&unary.argument) {
                Expression::StaticMemberExpression(member) if !member.optional => {
                    self.record_member_write(
                        &member.object,
                        Some(member.property.name.to_string()),
                        unary.span,
                        "delete",
                    );
                }
                Expression::ComputedMemberExpression(member) if !member.optional => {
                    let property = match last_sequence_expression(&member.expression) {
                        Expression::StringLiteral(property) => string_literal_value(property),
                        _ => None,
                    };
                    self.record_member_write(&member.object, property, unary.span, "delete");
                }
                _ => {}
            }
        }
        walk::walk_unary_expression(self, unary);
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !self.active {
            walk::walk_call_expression(self, call);
            return;
        }
        if !call.optional {
            let direct_callee = self.direct_callee(&call.callee);
            if let Some(callee) = direct_callee {
                self.record_direct_call(call, callee);
            } else if let Some((receiver, property)) = self.static_member(&call.callee) {
                if let Some(origin) = self.expression_origin(receiver) {
                    let Some(context) = self.context.proven_origin_context(origin) else {
                        walk::walk_call_expression(self, call);
                        return;
                    };
                    self.member_calls.push(ProvenMemberReceiverOrigin {
                        context,
                        call_start: call.span.start,
                        call_end: call.span.end,
                        receiver_start: receiver.span().start,
                        receiver_end: receiver.span().end,
                        property,
                        allocation_start: origin.allocation_start,
                        allocation_end: origin.allocation_end,
                        constructor_start: origin.constructor.start,
                        constructor_end: origin.constructor.end,
                    });
                }
            }

            let proven_parameter_count = direct_callee
                .and_then(|callee| self.function_info.get(&callee))
                .filter(|info| !info.dynamic_scope)
                .map_or(0, |info| info.parameters.len());
            for (index, argument) in call.arguments.iter().enumerate() {
                let Some(argument) = argument.as_expression() else {
                    continue;
                };
                if direct_callee.is_none() || index >= proven_parameter_count {
                    self.record_exposure(argument, argument.span(), "call_argument");
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProvenOriginFlow {
    pub member_calls: Vec<ProvenMemberReceiverOrigin>,
    pub member_writes: Vec<ProvenMemberWriteOrigin>,
    pub exposures: Vec<ProvenOriginExposure>,
    pub direct_calls: Vec<ProvenOriginDirectCall>,
}

fn analyze_origin_contexts(
    program: &Program<'_>,
    scoping: &Scoping,
    functions: &FunctionCollector,
    initial_contexts: impl IntoIterator<Item = FunctionContext>,
) -> ProvenOriginFlow {
    let mut queue = initial_contexts.into_iter().collect::<VecDeque<_>>();
    let mut seen = HashSet::new();
    let mut flow = ProvenOriginFlow::default();
    while let Some(mut context) = queue.pop_front() {
        let Some(info) = functions.by_key.get(&context.function) else {
            continue;
        };
        if info.dynamic_scope {
            continue;
        }
        if context.parameter_origins.len() < info.parameters.len() {
            context
                .parameter_origins
                .resize(info.parameters.len(), None);
        }
        if !seen.insert(context.clone()) {
            continue;
        }
        let mut probe = ContextProbe::new(
            scoping,
            &functions.by_symbol,
            &functions.by_key,
            &context,
            info,
        );
        probe.visit_program(program);
        queue.extend(probe.discovered);
        flow.member_calls.extend(probe.member_calls);
        flow.member_writes.extend(probe.member_writes);
        flow.exposures.extend(probe.exposures);
        flow.direct_calls.extend(probe.direct_calls);
    }

    flow.member_calls.sort_by_key(|call| {
        (
            call.call_start,
            call.call_end,
            call.context.allocation_start,
            call.context.function_start,
        )
    });
    flow.member_calls.dedup();
    flow.member_writes.sort_by_key(|write| {
        (
            write.write_start,
            write.write_end,
            write.context.allocation_start,
            write.context.function_start,
        )
    });
    flow.member_writes.dedup();
    flow.exposures.sort_by_key(|exposure| {
        (
            exposure.exposure_start,
            exposure.exposure_end,
            exposure.context.allocation_start,
            exposure.context.function_start,
            exposure.kind,
        )
    });
    flow.exposures.dedup();
    flow.direct_calls.sort_by_key(|call| {
        (
            call.call_start,
            call.call_end,
            call.caller.allocation_start,
            call.caller.function_start,
            call.callee.function_start,
        )
    });
    flow.direct_calls.dedup();
    flow
}

#[must_use]
pub fn structurally_proven_origin_flow(
    program: &Program<'_>,
    scoping: &Scoping,
) -> ProvenOriginFlow {
    let mut functions = FunctionCollector::new();
    functions.visit_program(program);

    let mut allocations = AllocationCollector {
        scoping,
        functions: &functions.by_symbol,
        contexts: Vec::new(),
    };
    allocations.visit_program(program);
    analyze_origin_contexts(program, scoping, &functions, allocations.contexts)
}

/// Continue exact-origin propagation from contexts proven by another theorem.
///
/// This function validates that each seed names a regular, statically collected
/// function and that its parameter indices are in range, but it deliberately
/// does not re-prove the seed itself. Callers must only construct seeds from
/// already-proven object identity and call-target facts.
#[must_use]
pub fn propagate_proven_origin_contexts(
    program: &Program<'_>,
    scoping: &Scoping,
    seeds: &[ProvenOriginContext],
) -> ProvenOriginFlow {
    let mut functions = FunctionCollector::new();
    functions.visit_program(program);

    let initial_contexts = seeds.iter().filter_map(|seed| {
        let function = FunctionKey {
            start: seed.function_start,
            end: seed.function_end,
        };
        let constructor = FunctionKey {
            start: seed.constructor_start,
            end: seed.constructor_end,
        };
        let info = functions.by_key.get(&function)?;
        functions.by_key.get(&constructor)?;
        if seed
            .parameter_indices
            .iter()
            .any(|index| *index >= info.parameters.len())
        {
            return None;
        }
        let origin = ObjectOrigin {
            allocation_start: seed.allocation_start,
            allocation_end: seed.allocation_end,
            constructor,
        };
        let mut parameter_origins = vec![None; info.parameters.len()];
        for index in &seed.parameter_indices {
            parameter_origins[*index] = Some(origin);
        }
        (seed.this_origin || !seed.parameter_indices.is_empty()).then_some(FunctionContext {
            function,
            this_origin: seed.this_origin.then_some(origin),
            parameter_origins,
        })
    });

    analyze_origin_contexts(program, scoping, &functions, initial_contexts)
}

#[must_use]
pub fn structurally_proven_member_receiver_origins(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenMemberReceiverOrigin> {
    structurally_proven_origin_flow(program, scoping).member_calls
}

#[must_use]
pub fn structurally_proven_member_write_origins(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenMemberWriteOrigin> {
    structurally_proven_origin_flow(program, scoping).member_writes
}

#[must_use]
pub fn structurally_proven_origin_exposures(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenOriginExposure> {
    structurally_proven_origin_flow(program, scoping).exposures
}

#[must_use]
pub fn structurally_proven_origin_direct_calls(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenOriginDirectCall> {
    structurally_proven_origin_flow(program, scoping).direct_calls
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenFunctionValue {
    pub function_start: u32,
    pub function_end: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenPrototypeMethodAssignment {
    pub constructor_start: u32,
    pub constructor_end: u32,
    pub property: String,
    /// Every regular-function value the assignment can select from the supported
    /// pure expression subset. Multiple entries preserve environment-dependent
    /// conditionals without guessing which arm wins.
    pub possible_functions: Vec<ProvenFunctionValue>,
    pub assignment_start: u32,
    pub assignment_end: u32,
    /// Resolving this assignment as an installed own prototype method requires ordinary
    /// function-prototype / Object.prototype property semantics at runtime.
    pub standard_prototype_semantics_required: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenPrototypeMethodLookupTarget {
    pub constructor_start: u32,
    pub constructor_end: u32,
    pub property: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
    pub possible_functions: Vec<ProvenFunctionValue>,
    /// The proof permits standard ECMAScript property-key coercion for otherwise
    /// effect-free literals such as an empty array and ordinary function/Object
    /// prototype lookup semantics. It is not assumption-free rewrite evidence.
    pub standard_prototype_semantics_required: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrototypeMethodCallCandidate {
    pub call: ProvenMemberReceiverOrigin,
    pub lookup_target: ProvenPrototypeMethodLookupTarget,
    pub receiver_effects: ProvenPrototypeMethodReceiverEffects,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenPrototypeMethodReceiverEffects {
    pub constructor_start: u32,
    pub constructor_end: u32,
    pub property: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
    pub possible_functions: Vec<ProvenFunctionValue>,
    /// Static own/inherited receiver properties read by at least one possible body.
    /// A lookup consumer must separately prove these reads cannot invoke a hostile getter.
    pub receiver_reads: Vec<String>,
    /// Static methods called with the receiver as `this` by at least one possible body.
    /// These are recursive effect obligations, not automatically safe calls.
    pub receiver_calls: Vec<String>,
    /// True when a possible body directly writes, updates, or deletes a receiver member.
    pub mutates_receiver: bool,
    /// True when a possible body exposes the receiver as a value (return/argument/alias/etc.).
    pub exposes_receiver: bool,
    /// True when a possible body performs a computed receiver access whose key is not a
    /// supported static string literal.
    pub dynamic_receiver_access: bool,
}

fn regular_function_key(function: &Function<'_>) -> Option<FunctionKey> {
    (!function.r#async && !function.generator).then(|| FunctionKey::of(function))
}

fn possible_regular_functions(expression: &Expression<'_>) -> Option<Vec<FunctionKey>> {
    let mut functions = match last_sequence_expression(expression) {
        Expression::FunctionExpression(function) => vec![regular_function_key(function)?],
        Expression::CallExpression(call) => returned_regular_functions(call)?,
        Expression::ConditionalExpression(conditional) => {
            let mut functions = possible_regular_functions(&conditional.consequent)?;
            functions.extend(possible_regular_functions(&conditional.alternate)?);
            functions
        }
        _ => return None,
    };
    functions.sort_by_key(|function| (function.start, function.end));
    functions.dedup();
    (!functions.is_empty()).then_some(functions)
}

fn returned_regular_functions(call: &CallExpression<'_>) -> Option<Vec<FunctionKey>> {
    if call.optional || !call.arguments.is_empty() {
        return None;
    }
    let Expression::FunctionExpression(factory) = last_sequence_expression(&call.callee) else {
        return None;
    };
    if factory.r#async || factory.generator {
        return None;
    }
    let body = factory.body.as_ref()?;
    let [Statement::ReturnStatement(ret)] = body.statements.as_slice() else {
        return None;
    };
    possible_regular_functions(ret.argument.as_ref()?)
}

fn proof_property_key(
    expression: &Expression<'_>,
    scoping: &Scoping,
    bindings: &HashMap<SymbolId, String>,
) -> Option<String> {
    match last_sequence_expression(expression) {
        Expression::Identifier(_) => {
            let symbol = reference_symbol(scoping, last_sequence_expression(expression))?;
            bindings.get(&symbol).cloned()
        }
        Expression::ArrayExpression(array) if array.elements.is_empty() => Some(String::new()),
        expression => eval_static_primitive(expression)?.js_string(),
    }
}

struct PropertyKeyCollector<'c> {
    scoping: &'c Scoping,
    bindings: HashMap<SymbolId, String>,
}

impl<'a> Visit<'a> for PropertyKeyCollector<'_> {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                continue;
            };
            if !symbol_binding_is_stable(self.scoping, symbol) {
                continue;
            }
            let Some(init) = declarator.init.as_ref() else {
                continue;
            };
            if let Some(key) = proof_property_key(init, self.scoping, &self.bindings) {
                self.bindings.insert(symbol, key);
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

fn collect_property_key_bindings(
    program: &Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, String> {
    let mut collector = PropertyKeyCollector {
        scoping,
        bindings: HashMap::new(),
    };
    collector.visit_program(program);
    collector.bindings
}

fn static_member_name<'a>(expression: &'a Expression<'a>) -> Option<(&'a Expression<'a>, String)> {
    match last_sequence_expression(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => {
            Some((&member.object, member.property.name.to_string()))
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = last_sequence_expression(&member.expression)
            else {
                return None;
            };
            Some((&member.object, string_literal_value(property)?))
        }
        _ => None,
    }
}

struct PrototypeMentionProbe<'c, 'f, 'a> {
    scoping: &'c Scoping,
    constructors: &'f HashMap<SymbolId, FunctionKey>,
    aliases: &'a HashMap<SymbolId, FunctionKey>,
    owners: HashSet<FunctionKey>,
}

impl<'a> Visit<'a> for PrototypeMentionProbe<'_, '_, '_> {
    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        if let Some(symbol) = identifier
            .reference_id
            .get()
            .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
        {
            if let Some(owner) = self.aliases.get(&symbol).copied() {
                self.owners.insert(owner);
            }
        }
    }

    fn visit_static_member_expression(
        &mut self,
        member: &oxc_ast::ast::StaticMemberExpression<'a>,
    ) {
        if !member.optional && member.property.name.as_str() == "prototype" {
            if let Some(symbol) = reference_symbol(self.scoping, &member.object) {
                if symbol_binding_is_stable(self.scoping, symbol) {
                    if let Some(owner) = self.constructors.get(&symbol).copied() {
                        self.owners.insert(owner);
                    }
                }
            }
        }
        walk::walk_static_member_expression(self, member);
    }
}

struct ConstructorEscapeProbe<'c, 'f, 'k> {
    scoping: &'c Scoping,
    constructors: &'f HashMap<SymbolId, FunctionKey>,
    property_keys: &'k HashMap<SymbolId, String>,
    owners: HashSet<FunctionKey>,
}

impl ConstructorEscapeProbe<'_, '_, '_> {
    fn constructor_value(&self, expression: &Expression<'_>) -> Option<FunctionKey> {
        let symbol = reference_symbol(self.scoping, last_sequence_expression(expression))?;
        symbol_binding_is_stable(self.scoping, symbol)
            .then(|| self.constructors.get(&symbol).copied())
            .flatten()
    }
}

impl<'a> Visit<'a> for ConstructorEscapeProbe<'_, '_, '_> {
    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }

    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        if let Some(symbol) = identifier
            .reference_id
            .get()
            .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
        {
            if let Some(owner) = self.constructors.get(&symbol).copied() {
                self.owners.insert(owner);
            }
        }
    }

    fn visit_new_expression(&mut self, expression: &NewExpression<'a>) {
        if self.constructor_value(&expression.callee).is_some() {
            for argument in &expression.arguments {
                if let Some(argument) = argument.as_expression() {
                    self.visit_expression(argument);
                } else {
                    walk::walk_argument(self, argument);
                }
            }
            return;
        }
        walk::walk_new_expression(self, expression);
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if self.constructor_value(&call.callee).is_some() {
            for argument in &call.arguments {
                if let Some(argument) = argument.as_expression() {
                    self.visit_expression(argument);
                } else {
                    walk::walk_argument(self, argument);
                }
            }
            return;
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_static_member_expression(
        &mut self,
        member: &oxc_ast::ast::StaticMemberExpression<'a>,
    ) {
        if self.constructor_value(&member.object).is_some() {
            return;
        }
        walk::walk_static_member_expression(self, member);
    }

    fn visit_computed_member_expression(
        &mut self,
        member: &oxc_ast::ast::ComputedMemberExpression<'a>,
    ) {
        if let Some(owner) = self.constructor_value(&member.object) {
            let property = proof_property_key(&member.expression, self.scoping, self.property_keys);
            if property
                .as_deref()
                .is_none_or(|property| property == "prototype")
            {
                self.owners.insert(owner);
            }
            self.visit_expression(&member.expression);
            return;
        }
        walk::walk_computed_member_expression(self, member);
    }
}

struct PrototypeMethodProof<'c, 'f> {
    scoping: &'c Scoping,
    constructors: &'f HashMap<SymbolId, FunctionKey>,
    property_keys: &'f HashMap<SymbolId, String>,
    aliases: HashMap<SymbolId, FunctionKey>,
    methods: HashMap<(FunctionKey, String), ProvenPrototypeMethodAssignment>,
    conflicts: HashSet<(FunctionKey, String)>,
    invalid_constructors: HashSet<FunctionKey>,
    lookup_invalid_constructors: HashSet<FunctionKey>,
}

impl<'c, 'f> PrototypeMethodProof<'c, 'f> {
    fn new(
        scoping: &'c Scoping,
        constructors: &'f HashMap<SymbolId, FunctionKey>,
        property_keys: &'f HashMap<SymbolId, String>,
    ) -> Self {
        Self {
            scoping,
            constructors,
            property_keys,
            aliases: HashMap::new(),
            methods: HashMap::new(),
            conflicts: HashSet::new(),
            invalid_constructors: HashSet::new(),
            lookup_invalid_constructors: HashSet::new(),
        }
    }

    fn constructor_prototype(&self, expression: &Expression<'_>) -> Option<FunctionKey> {
        let (object, property) = static_member_name(expression)?;
        if property != "prototype" {
            return None;
        }
        let symbol = reference_symbol(self.scoping, last_sequence_expression(object))?;
        symbol_binding_is_stable(self.scoping, symbol)
            .then(|| self.constructors.get(&symbol).copied())
            .flatten()
    }

    fn prototype_value(&self, expression: &Expression<'_>) -> Option<FunctionKey> {
        let expression = last_sequence_expression(expression);
        if let Some(owner) = self.constructor_prototype(expression) {
            return Some(owner);
        }
        let symbol = reference_symbol(self.scoping, expression)?;
        self.aliases.get(&symbol).copied()
    }

    fn constructor_value(&self, expression: &Expression<'_>) -> Option<FunctionKey> {
        let symbol = reference_symbol(self.scoping, last_sequence_expression(expression))?;
        symbol_binding_is_stable(self.scoping, symbol)
            .then(|| self.constructors.get(&symbol).copied())
            .flatten()
    }

    fn constructor_value_owners(&self, expression: &Expression<'_>) -> HashSet<FunctionKey> {
        match expression {
            Expression::ParenthesizedExpression(parenthesized) => {
                self.constructor_value_owners(&parenthesized.expression)
            }
            Expression::SequenceExpression(sequence) => sequence
                .expressions
                .last()
                .map_or_else(HashSet::new, |expression| {
                    self.constructor_value_owners(expression)
                }),
            Expression::ConditionalExpression(conditional) => {
                let mut owners = self.constructor_value_owners(&conditional.consequent);
                owners.extend(self.constructor_value_owners(&conditional.alternate));
                owners
            }
            Expression::LogicalExpression(logical) => {
                let mut owners = self.constructor_value_owners(&logical.left);
                owners.extend(self.constructor_value_owners(&logical.right));
                owners
            }
            Expression::AssignmentExpression(assignment) if assignment.operator.is_assign() => {
                self.constructor_value_owners(&assignment.right)
            }
            Expression::ArrayExpression(array) => {
                let mut owners = HashSet::new();
                for element in &array.elements {
                    match element {
                        ArrayExpressionElement::SpreadElement(spread) => {
                            owners.extend(self.constructor_value_owners(&spread.argument));
                        }
                        ArrayExpressionElement::Elision(_) => {}
                        element => {
                            if let Some(expression) = element.as_expression() {
                                owners.extend(self.constructor_value_owners(expression));
                            }
                        }
                    }
                }
                owners
            }
            Expression::ObjectExpression(object) => {
                let mut owners = HashSet::new();
                for property in &object.properties {
                    match property {
                        ObjectPropertyKind::ObjectProperty(property) => {
                            owners.extend(self.constructor_value_owners(&property.value));
                        }
                        ObjectPropertyKind::SpreadProperty(spread) => {
                            owners.extend(self.constructor_value_owners(&spread.argument));
                        }
                    }
                }
                owners
            }
            _ => self.constructor_value(expression).into_iter().collect(),
        }
    }

    fn prototype_value_owners(&self, expression: &Expression<'_>) -> HashSet<FunctionKey> {
        match expression {
            Expression::ParenthesizedExpression(parenthesized) => {
                self.prototype_value_owners(&parenthesized.expression)
            }
            Expression::SequenceExpression(sequence) => sequence
                .expressions
                .last()
                .map_or_else(HashSet::new, |expression| {
                    self.prototype_value_owners(expression)
                }),
            Expression::ConditionalExpression(conditional) => {
                let mut owners = self.prototype_value_owners(&conditional.consequent);
                owners.extend(self.prototype_value_owners(&conditional.alternate));
                owners
            }
            Expression::LogicalExpression(logical) => {
                let mut owners = self.prototype_value_owners(&logical.left);
                owners.extend(self.prototype_value_owners(&logical.right));
                owners
            }
            Expression::AssignmentExpression(assignment) if assignment.operator.is_assign() => {
                self.prototype_value_owners(&assignment.right)
            }
            Expression::ArrayExpression(array) => {
                let mut owners = HashSet::new();
                for element in &array.elements {
                    match element {
                        ArrayExpressionElement::SpreadElement(spread) => {
                            owners.extend(self.prototype_value_owners(&spread.argument));
                        }
                        ArrayExpressionElement::Elision(_) => {}
                        element => {
                            if let Some(expression) = element.as_expression() {
                                owners.extend(self.prototype_value_owners(expression));
                            }
                        }
                    }
                }
                owners
            }
            Expression::ObjectExpression(object) => {
                let mut owners = HashSet::new();
                for property in &object.properties {
                    match property {
                        ObjectPropertyKind::ObjectProperty(property) => {
                            owners.extend(self.prototype_value_owners(&property.value));
                        }
                        ObjectPropertyKind::SpreadProperty(spread) => {
                            owners.extend(self.prototype_value_owners(&spread.argument));
                        }
                    }
                }
                owners
            }
            Expression::ComputedMemberExpression(member) if !member.optional => {
                if let Some(owner) = self.constructor_value(&member.object) {
                    let property =
                        proof_property_key(&member.expression, self.scoping, self.property_keys);
                    if property
                        .as_deref()
                        .is_none_or(|property| property == "prototype")
                    {
                        return [owner].into_iter().collect();
                    }
                }
                self.prototype_value(expression).into_iter().collect()
            }
            _ => self.prototype_value(expression).into_iter().collect(),
        }
    }

    fn member_receiver_owner(&self, expression: &Expression<'_>) -> Option<FunctionKey> {
        match last_sequence_expression(expression) {
            Expression::StaticMemberExpression(member) if !member.optional => {
                self.prototype_value(&member.object)
            }
            Expression::ComputedMemberExpression(member) if !member.optional => {
                self.prototype_value(&member.object)
            }
            _ => None,
        }
    }

    fn invalidate_property(&mut self, owner: FunctionKey, property: String) {
        self.conflicts.insert((owner, property.clone()));
        self.methods.remove(&(owner, property));
    }

    fn invalidate_constructor(&mut self, owner: FunctionKey) {
        self.invalid_constructors.insert(owner);
        self.lookup_invalid_constructors.insert(owner);
        self.methods.retain(|(candidate, _), _| *candidate != owner);
    }

    fn invalidate_lookup(&mut self, owner: FunctionKey) {
        self.lookup_invalid_constructors.insert(owner);
    }

    fn record_method(
        &mut self,
        owner: FunctionKey,
        property: String,
        functions: Vec<FunctionKey>,
        assignment_start: u32,
        assignment_end: u32,
    ) {
        let key = (owner, property.clone());
        if self.invalid_constructors.contains(&owner) || self.conflicts.contains(&key) {
            return;
        }
        let method = ProvenPrototypeMethodAssignment {
            constructor_start: owner.start,
            constructor_end: owner.end,
            property,
            possible_functions: functions
                .into_iter()
                .map(|function| ProvenFunctionValue {
                    function_start: function.start,
                    function_end: function.end,
                })
                .collect(),
            assignment_start,
            assignment_end,
            standard_prototype_semantics_required: true,
        };
        if self.methods.insert(key.clone(), method).is_some() {
            self.invalidate_property(owner, key.1);
        }
    }

    fn process_statement_list(&mut self, statements: &[Statement<'_>]) {
        self.aliases.clear();
        for statement in statements {
            match statement {
                Statement::ExpressionStatement(statement) => {
                    self.process_expression(&statement.expression);
                }
                Statement::VariableDeclaration(declaration) => {
                    for declarator in &declaration.declarations {
                        let Some(init) = declarator.init.as_ref() else {
                            continue;
                        };
                        self.process_expression(init);
                        if let Some(owner) = self.constructor_value(init) {
                            self.invalidate_constructor(owner);
                        }
                        let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                            self.aliases.clear();
                            continue;
                        };
                        let Some(symbol) = identifier.symbol_id.get() else {
                            self.aliases.clear();
                            continue;
                        };
                        if let Some(owner) = self.prototype_value(init) {
                            self.aliases.insert(symbol, owner);
                        } else {
                            self.aliases.remove(&symbol);
                        }
                    }
                }
                Statement::FunctionDeclaration(_) | Statement::EmptyStatement(_) => {}
                _ => {
                    // We do not model branch/loop execution as a stable installation
                    // sequence. Any prototype identity mentioned inside such a
                    // construct may participate in a conditional mutation or escape,
                    // so stable lookup fails closed for that constructor.
                    let mut probe = PrototypeMentionProbe {
                        scoping: self.scoping,
                        constructors: self.constructors,
                        aliases: &self.aliases,
                        owners: HashSet::new(),
                    };
                    probe.visit_statement(statement);
                    for owner in probe.owners {
                        self.invalidate_lookup(owner);
                    }
                    let mut constructor_probe = ConstructorEscapeProbe {
                        scoping: self.scoping,
                        constructors: self.constructors,
                        property_keys: self.property_keys,
                        owners: HashSet::new(),
                    };
                    constructor_probe.visit_statement(statement);
                    for owner in constructor_probe.owners {
                        self.invalidate_constructor(owner);
                    }
                    self.aliases.clear();
                }
            }
        }
    }

    fn invalidate_static_prototype_member(&mut self, object: &Expression<'_>, property: String) {
        if property == "prototype" {
            if let Some(constructor) = self.constructor_value(object) {
                self.invalidate_constructor(constructor);
                return;
            }
            if let Some(symbol) = reference_symbol(self.scoping, object) {
                if let Some(constructor) = self.constructors.get(&symbol).copied() {
                    self.invalidate_constructor(constructor);
                }
            }
            return;
        }
        if let Some(owner) = self.prototype_value(object) {
            self.invalidate_property(owner, property);
        }
    }

    fn invalidate_computed_prototype_member(
        &mut self,
        object: &Expression<'_>,
        property: &Expression<'_>,
    ) {
        let property = proof_property_key(property, self.scoping, self.property_keys);
        if let Some(constructor) = self.constructor_value(object) {
            if property
                .as_deref()
                .is_none_or(|property| property == "prototype")
            {
                self.invalidate_constructor(constructor);
                return;
            }
        }
        let Some(owner) = self.prototype_value(object) else {
            return;
        };
        if let Some(property) = property {
            self.invalidate_property(owner, property);
        } else {
            self.invalidate_lookup(owner);
        }
    }

    fn process_expression(&mut self, expression: &Expression<'_>) {
        match expression {
            Expression::ParenthesizedExpression(parenthesized) => {
                self.process_expression(&parenthesized.expression);
            }
            Expression::SequenceExpression(sequence) => {
                for expression in &sequence.expressions {
                    self.process_expression(expression);
                }
            }
            Expression::AssignmentExpression(assignment) => {
                if assignment.operator.as_str() != "=" {
                    match &assignment.left {
                        AssignmentTarget::AssignmentTargetIdentifier(identifier) => {
                            if let Some(symbol) =
                                identifier.reference_id.get().and_then(|reference_id| {
                                    self.scoping.get_reference(reference_id).symbol_id()
                                })
                            {
                                self.aliases.remove(&symbol);
                            }
                        }
                        AssignmentTarget::StaticMemberExpression(member) => {
                            self.invalidate_static_prototype_member(
                                &member.object,
                                member.property.name.to_string(),
                            );
                        }
                        AssignmentTarget::ComputedMemberExpression(member) => {
                            self.invalidate_computed_prototype_member(
                                &member.object,
                                &member.expression,
                            );
                        }
                        _ => {}
                    }
                    self.aliases.clear();
                    return;
                }

                if let AssignmentTarget::AssignmentTargetIdentifier(identifier) = &assignment.left {
                    self.process_expression(&assignment.right);
                    if let Some(owner) = self.constructor_value(&assignment.right) {
                        self.invalidate_constructor(owner);
                    }
                    let Some(symbol) = identifier.reference_id.get().and_then(|reference_id| {
                        self.scoping.get_reference(reference_id).symbol_id()
                    }) else {
                        self.aliases.clear();
                        return;
                    };
                    if let Some(owner) = self.prototype_value(&assignment.right) {
                        self.aliases.insert(symbol, owner);
                    } else {
                        self.aliases.remove(&symbol);
                    }
                    return;
                }

                if let Some(owner) = self.prototype_value(&assignment.right) {
                    self.invalidate_lookup(owner);
                }

                match &assignment.left {
                    AssignmentTarget::StaticMemberExpression(member) => {
                        self.process_expression(&member.object);
                        let owner = self.prototype_value(&member.object);
                        let property = member.property.name.to_string();
                        self.process_expression(&assignment.right);
                        if property == "prototype" {
                            if let Some(symbol) = reference_symbol(self.scoping, &member.object) {
                                if let Some(constructor) = self.constructors.get(&symbol).copied() {
                                    self.invalidate_constructor(constructor);
                                }
                            }
                            return;
                        }
                        if let Some(owner) = owner {
                            if let Some(functions) = possible_regular_functions(&assignment.right) {
                                self.record_method(
                                    owner,
                                    property,
                                    functions,
                                    assignment.span.start,
                                    assignment.span.end,
                                );
                            } else {
                                self.invalidate_property(owner, property);
                            }
                        }
                    }
                    AssignmentTarget::ComputedMemberExpression(member) => {
                        self.process_expression(&member.object);
                        let owner = self.prototype_value(&member.object);
                        self.process_expression(&member.expression);
                        let property = proof_property_key(
                            &member.expression,
                            self.scoping,
                            self.property_keys,
                        );
                        if let Some(constructor) = self.constructor_value(&member.object) {
                            if property
                                .as_deref()
                                .is_none_or(|property| property == "prototype")
                            {
                                self.invalidate_constructor(constructor);
                            }
                        }
                        self.process_expression(&assignment.right);
                        if let Some(owner) = owner {
                            if let Some(property) = property {
                                if let Some(functions) =
                                    possible_regular_functions(&assignment.right)
                                {
                                    self.record_method(
                                        owner,
                                        property,
                                        functions,
                                        assignment.span.start,
                                        assignment.span.end,
                                    );
                                } else {
                                    self.invalidate_property(owner, property);
                                }
                            } else {
                                self.invalidate_lookup(owner);
                            }
                        }
                    }
                    _ => {
                        self.process_expression(&assignment.right);
                        self.aliases.clear();
                    }
                }
            }
            Expression::StaticMemberExpression(member) => self.process_expression(&member.object),
            Expression::ComputedMemberExpression(member) => {
                self.process_expression(&member.object);
                self.process_expression(&member.expression);
            }
            Expression::CallExpression(call) => {
                if let Some(owner) = self.prototype_value(&call.callee) {
                    self.invalidate_lookup(owner);
                }
                if let Some(owner) = self.member_receiver_owner(&call.callee) {
                    self.invalidate_lookup(owner);
                }
                let argument_owners = call
                    .arguments
                    .iter()
                    .filter_map(Argument::as_expression)
                    .flat_map(|argument| self.prototype_value_owners(argument))
                    .collect::<HashSet<_>>();
                for owner in argument_owners {
                    self.invalidate_lookup(owner);
                }
                let constructor_owners = call
                    .arguments
                    .iter()
                    .filter_map(Argument::as_expression)
                    .flat_map(|argument| self.constructor_value_owners(argument))
                    .collect::<HashSet<_>>();
                for owner in constructor_owners {
                    self.invalidate_constructor(owner);
                }
                self.process_expression(&call.callee);
                for argument in &call.arguments {
                    if let Some(argument) = argument.as_expression() {
                        self.process_expression(argument);
                    } else {
                        self.aliases.clear();
                    }
                }
                self.aliases.clear();
            }
            Expression::ConditionalExpression(conditional) => {
                self.process_expression(&conditional.test);
                self.aliases.clear();
            }
            Expression::LogicalExpression(logical) => {
                self.process_expression(&logical.left);
                self.aliases.clear();
            }
            Expression::UpdateExpression(update) => {
                match &update.argument {
                    oxc_ast::ast::SimpleAssignmentTarget::StaticMemberExpression(member) => {
                        self.invalidate_static_prototype_member(
                            &member.object,
                            member.property.name.to_string(),
                        );
                    }
                    oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member) => {
                        self.invalidate_computed_prototype_member(
                            &member.object,
                            &member.expression,
                        );
                    }
                    _ => {}
                }
                self.aliases.clear();
            }
            Expression::UnaryExpression(unary) => {
                if unary.operator.as_str() == "delete" {
                    match last_sequence_expression(&unary.argument) {
                        Expression::StaticMemberExpression(member) => {
                            self.invalidate_static_prototype_member(
                                &member.object,
                                member.property.name.to_string(),
                            );
                        }
                        Expression::ComputedMemberExpression(member) => {
                            self.invalidate_computed_prototype_member(
                                &member.object,
                                &member.expression,
                            );
                        }
                        _ => self.process_expression(&unary.argument),
                    }
                    self.aliases.clear();
                } else {
                    self.process_expression(&unary.argument);
                }
            }
            Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_) => {}
            _ => {}
        }
    }
}

struct PrototypeMethodCollector<'c, 'f> {
    proof: PrototypeMethodProof<'c, 'f>,
}

impl<'a> Visit<'a> for PrototypeMethodCollector<'_, '_> {
    fn visit_program(&mut self, program: &Program<'a>) {
        self.proof.process_statement_list(&program.body);
        walk::walk_program(self, program);
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(body) = &function.body {
            self.proof.process_statement_list(&body.statements);
        }
        walk::walk_function(self, function, flags);
    }
}

#[must_use]
fn collect_prototype_method_proof<'c, 'f>(
    program: &Program<'_>,
    scoping: &'c Scoping,
    constructors: &'f HashMap<SymbolId, FunctionKey>,
    property_keys: &'f HashMap<SymbolId, String>,
) -> PrototypeMethodProof<'c, 'f> {
    let proof = PrototypeMethodProof::new(scoping, constructors, property_keys);
    let mut collector = PrototypeMethodCollector { proof };
    collector.visit_program(program);
    collector.proof
}

#[must_use]
pub fn structurally_proven_prototype_method_assignments(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenPrototypeMethodAssignment> {
    let mut functions = FunctionCollector::new();
    functions.visit_program(program);
    let property_keys = collect_property_key_bindings(program, scoping);
    let proof =
        collect_prototype_method_proof(program, scoping, &functions.by_symbol, &property_keys);
    let mut methods = proof.methods.into_values().collect::<Vec<_>>();
    methods.sort_by_key(|method| {
        (
            method.constructor_start,
            method.property.clone(),
            method.assignment_start,
        )
    });
    methods
}

#[must_use]
pub fn structurally_proven_prototype_method_lookup_targets(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenPrototypeMethodLookupTarget> {
    let mut functions = FunctionCollector::new();
    functions.visit_program(program);
    let property_keys = collect_property_key_bindings(program, scoping);
    let proof =
        collect_prototype_method_proof(program, scoping, &functions.by_symbol, &property_keys);
    let invalid = proof.lookup_invalid_constructors;
    let mut targets = proof
        .methods
        .into_values()
        .filter(|method| {
            let owner = FunctionKey {
                start: method.constructor_start,
                end: method.constructor_end,
            };
            !invalid.contains(&owner)
        })
        .map(|method| ProvenPrototypeMethodLookupTarget {
            constructor_start: method.constructor_start,
            constructor_end: method.constructor_end,
            property: method.property,
            assignment_start: method.assignment_start,
            assignment_end: method.assignment_end,
            possible_functions: method.possible_functions,
            standard_prototype_semantics_required: true,
        })
        .collect::<Vec<_>>();
    targets.sort_by_key(|target| {
        (
            target.constructor_start,
            target.property.clone(),
            target.assignment_start,
        )
    });
    targets
}

fn direct_this(expression: &Expression<'_>) -> bool {
    matches!(
        last_sequence_expression(expression),
        Expression::ThisExpression(_)
    )
}

fn assignment_target_direct_this_member(target: &AssignmentTarget<'_>) -> bool {
    match target {
        AssignmentTarget::StaticMemberExpression(member) => direct_this(&member.object),
        AssignmentTarget::ComputedMemberExpression(member) => direct_this(&member.object),
        _ => false,
    }
}

#[derive(Default)]
struct ReceiverEffectProbe {
    reads: HashSet<String>,
    calls: HashSet<String>,
    mutates: bool,
    exposes: bool,
    dynamic_access: bool,
}

impl<'a> Visit<'a> for ReceiverEffectProbe {
    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        // Arrow bodies capture the surrounding `this`. Treat any such closure as
        // an exposure obligation instead of recursively pretending it executes now.
        let mut nested = ReceiverEffectProbe::default();
        walk::walk_arrow_function_expression(&mut nested, function);
        if !nested.reads.is_empty()
            || !nested.calls.is_empty()
            || nested.mutates
            || nested.exposes
            || nested.dynamic_access
        {
            self.exposes = true;
        }
    }

    fn visit_this_expression(&mut self, _expression: &oxc_ast::ast::ThisExpression) {
        self.exposes = true;
    }

    fn visit_return_statement(&mut self, statement: &oxc_ast::ast::ReturnStatement<'a>) {
        if let Some(argument) = statement.argument.as_ref() {
            if direct_this(argument) {
                self.exposes = true;
                return;
            }
            self.visit_expression(argument);
        }
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment_target_direct_this_member(&assignment.left) {
            self.mutates = true;
            self.visit_expression(&assignment.right);
            return;
        }
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_update_expression(&mut self, expression: &oxc_ast::ast::UpdateExpression<'a>) {
        match &expression.argument {
            oxc_ast::ast::SimpleAssignmentTarget::StaticMemberExpression(member)
                if direct_this(&member.object) =>
            {
                self.mutates = true
            }
            oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member)
                if direct_this(&member.object) =>
            {
                self.mutates = true
            }
            _ => walk::walk_update_expression(self, expression),
        }
    }

    fn visit_unary_expression(&mut self, expression: &oxc_ast::ast::UnaryExpression<'a>) {
        if expression.operator.as_str() == "delete" {
            match last_sequence_expression(&expression.argument) {
                Expression::StaticMemberExpression(member) if direct_this(&member.object) => {
                    self.mutates = true;
                    return;
                }
                Expression::ComputedMemberExpression(member) if direct_this(&member.object) => {
                    self.mutates = true;
                    return;
                }
                _ => {}
            }
        }
        walk::walk_unary_expression(self, expression);
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if let Some((receiver, property)) = static_member_name(&call.callee) {
            if direct_this(receiver) {
                self.calls.insert(property);
                for argument in &call.arguments {
                    if let Some(argument) = argument.as_expression() {
                        self.visit_expression(argument);
                    } else {
                        self.exposes = true;
                    }
                }
                return;
            }
        }
        for argument in &call.arguments {
            if let Some(argument) = argument.as_expression() {
                if direct_this(argument) {
                    self.exposes = true;
                } else {
                    self.visit_expression(argument);
                }
            } else {
                self.exposes = true;
            }
        }
        self.visit_expression(&call.callee);
    }

    fn visit_static_member_expression(
        &mut self,
        member: &oxc_ast::ast::StaticMemberExpression<'a>,
    ) {
        if direct_this(&member.object) {
            self.reads.insert(member.property.name.to_string());
            return;
        }
        walk::walk_static_member_expression(self, member);
    }

    fn visit_computed_member_expression(
        &mut self,
        member: &oxc_ast::ast::ComputedMemberExpression<'a>,
    ) {
        if direct_this(&member.object) {
            match last_sequence_expression(&member.expression) {
                Expression::StringLiteral(property) => {
                    if let Some(property) = string_literal_value(property) {
                        self.reads.insert(property);
                    } else {
                        self.dynamic_access = true;
                    }
                }
                _ => self.dynamic_access = true,
            }
            self.visit_expression(&member.expression);
            return;
        }
        walk::walk_computed_member_expression(self, member);
    }
}

struct FunctionEffectCollector<'e> {
    targets: &'e HashSet<FunctionKey>,
    effects: HashMap<FunctionKey, ReceiverEffectProbe>,
}

impl<'a> Visit<'a> for FunctionEffectCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        let key = FunctionKey::of(function);
        if self.targets.contains(&key) {
            let mut effect = ReceiverEffectProbe::default();
            if let Some(body) = &function.body {
                effect.visit_function_body(body);
            }
            self.effects.insert(key, effect);
            return;
        }
        walk::walk_function(self, function, flags);
    }
}

#[must_use]
pub fn structurally_proven_prototype_method_receiver_effects(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenPrototypeMethodReceiverEffects> {
    let assignments = structurally_proven_prototype_method_assignments(program, scoping);
    let targets = assignments
        .iter()
        .flat_map(|assignment| assignment.possible_functions.iter())
        .map(|function| FunctionKey {
            start: function.function_start,
            end: function.function_end,
        })
        .collect::<HashSet<_>>();
    let mut collector = FunctionEffectCollector {
        targets: &targets,
        effects: HashMap::new(),
    };
    collector.visit_program(program);

    assignments
        .into_iter()
        .filter_map(|assignment| {
            let mut reads = HashSet::new();
            let mut calls = HashSet::new();
            let mut mutates = false;
            let mut exposes = false;
            let mut dynamic_access = false;
            for function in &assignment.possible_functions {
                let key = FunctionKey {
                    start: function.function_start,
                    end: function.function_end,
                };
                let effect = collector.effects.get(&key)?;
                reads.extend(effect.reads.iter().cloned());
                calls.extend(effect.calls.iter().cloned());
                mutates |= effect.mutates;
                exposes |= effect.exposes;
                dynamic_access |= effect.dynamic_access;
            }
            let mut receiver_reads = reads.into_iter().collect::<Vec<_>>();
            receiver_reads.sort();
            let mut receiver_calls = calls.into_iter().collect::<Vec<_>>();
            receiver_calls.sort();
            Some(ProvenPrototypeMethodReceiverEffects {
                constructor_start: assignment.constructor_start,
                constructor_end: assignment.constructor_end,
                property: assignment.property,
                assignment_start: assignment.assignment_start,
                assignment_end: assignment.assignment_end,
                possible_functions: assignment.possible_functions,
                receiver_reads,
                receiver_calls,
                mutates_receiver: mutates,
                exposes_receiver: exposes,
                dynamic_receiver_access: dynamic_access,
            })
        })
        .collect()
}

/// Match exact-origin member calls to independently proven stable prototype
/// lookup targets and their finite receiver-effect summaries.
///
/// This is intentionally not a call-time lookup proof. It only joins the
/// structural facts needed by a later ordering/barrier theorem. Ambiguous
/// lookup targets or effect summaries fail closed.
#[must_use]
pub fn structurally_matched_prototype_method_calls(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<PrototypeMethodCallCandidate> {
    type MethodKey = (u32, u32, String);

    let calls = structurally_proven_member_receiver_origins(program, scoping);
    let mut targets = HashMap::<MethodKey, Vec<ProvenPrototypeMethodLookupTarget>>::new();
    for target in structurally_proven_prototype_method_lookup_targets(program, scoping) {
        targets
            .entry((
                target.constructor_start,
                target.constructor_end,
                target.property.clone(),
            ))
            .or_default()
            .push(target);
    }
    let mut effects = HashMap::<MethodKey, Vec<ProvenPrototypeMethodReceiverEffects>>::new();
    for effect in structurally_proven_prototype_method_receiver_effects(program, scoping) {
        effects
            .entry((
                effect.constructor_start,
                effect.constructor_end,
                effect.property.clone(),
            ))
            .or_default()
            .push(effect);
    }

    let mut matched = calls
        .into_iter()
        .filter_map(|call| {
            let key = (
                call.constructor_start,
                call.constructor_end,
                call.property.clone(),
            );
            let [lookup_target] = targets.get(&key)?.as_slice() else {
                return None;
            };
            let [receiver_effects] = effects.get(&key)?.as_slice() else {
                return None;
            };
            (lookup_target.assignment_start == receiver_effects.assignment_start
                && lookup_target.assignment_end == receiver_effects.assignment_end
                && lookup_target.possible_functions == receiver_effects.possible_functions)
                .then(|| PrototypeMethodCallCandidate {
                    call,
                    lookup_target: lookup_target.clone(),
                    receiver_effects: receiver_effects.clone(),
                })
        })
        .collect::<Vec<_>>();
    matched.sort_by_key(|candidate| {
        (
            candidate.call.call_start,
            candidate.call.call_end,
            candidate.call.allocation_start,
            candidate.call.property.clone(),
        )
    });
    matched.dedup();
    matched
}

#[cfg(test)]
mod tests {
    use super::{
        propagate_proven_origin_contexts, structurally_matched_prototype_method_calls,
        structurally_proven_member_receiver_origins, structurally_proven_member_write_origins,
        structurally_proven_origin_direct_calls, structurally_proven_origin_exposures,
        structurally_proven_prototype_method_assignments,
        structurally_proven_prototype_method_lookup_targets,
        structurally_proven_prototype_method_receiver_effects,
    };
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;
    use std::collections::HashSet;

    fn method_assignments(source: &str) -> Vec<super::ProvenPrototypeMethodAssignment> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        structurally_proven_prototype_method_assignments(
            &parsed.program,
            semantic.semantic.scoping(),
        )
    }

    fn lookup_targets(source: &str) -> Vec<super::ProvenPrototypeMethodLookupTarget> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        structurally_proven_prototype_method_lookup_targets(
            &parsed.program,
            semantic.semantic.scoping(),
        )
    }

    fn calls(source: &str) -> Vec<super::ProvenMemberReceiverOrigin> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        structurally_proven_member_receiver_origins(&parsed.program, semantic.semantic.scoping())
    }

    fn writes(source: &str) -> Vec<super::ProvenMemberWriteOrigin> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        structurally_proven_member_write_origins(&parsed.program, semantic.semantic.scoping())
    }

    #[test]
    fn matches_exact_origin_member_call_to_stable_prototype_method() {
        let source = r#"
            const C = function() { launch(this); };
            function launch(state) { state.run(); }
            C.prototype.run = function() { return this.value; };
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let matched = structurally_matched_prototype_method_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        );
        assert_eq!(matched.len(), 1);
        assert_eq!(matched[0].call.property, "run");
        assert_eq!(matched[0].receiver_effects.receiver_reads, vec!["value"]);
        assert!(!matched[0].receiver_effects.mutates_receiver);
    }

    #[test]
    fn does_not_match_method_from_different_constructor() {
        let source = r#"
            const A = function() { launch(this); };
            const B = function() {};
            function launch(state) { state.run(); }
            B.prototype.run = function() {};
            new A();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        assert!(structurally_matched_prototype_method_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .is_empty());
    }

    #[test]
    fn propagates_already_proven_method_this_through_direct_calls() {
        let source = r#"
            const C = function() { this.marker = 1; };
            C.prototype.run = function() { bridge(this); };
            function bridge(state) { state.finish(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());

        let origin =
            structurally_proven_member_write_origins(&parsed.program, semantic.semantic.scoping())
                .into_iter()
                .find(|write| write.property.as_deref() == Some("marker"))
                .expect("constructor-origin write");
        let method = structurally_proven_prototype_method_assignments(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .into_iter()
        .find(|method| method.property == "run")
        .expect("run assignment");
        let [function] = method.possible_functions.as_slice() else {
            panic!("one run body");
        };
        let seed = super::ProvenOriginContext {
            function_start: function.function_start,
            function_end: function.function_end,
            allocation_start: origin.allocation_start,
            allocation_end: origin.allocation_end,
            constructor_start: origin.constructor_start,
            constructor_end: origin.constructor_end,
            this_origin: true,
            parameter_indices: Vec::new(),
        };

        let flow =
            propagate_proven_origin_contexts(&parsed.program, semantic.semantic.scoping(), &[seed]);
        assert_eq!(flow.direct_calls.len(), 1);
        assert_eq!(flow.member_calls.len(), 1);
        assert_eq!(flow.member_calls[0].property, "finish");
        assert_eq!(flow.member_calls[0].context.parameter_indices, vec![0]);
    }

    #[test]
    fn tracks_stable_local_origin_aliases_without_exposing_them() {
        let source = r#"
            const C = function() { const alias = this; bridge(alias); };
            function bridge(state) { state.run(); }
            new C();
        "#;
        let proven = calls(source);
        assert_eq!(proven.len(), 1);
        assert_eq!(proven[0].property, "run");
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(
            structurally_proven_origin_exposures(&parsed.program, semantic.semantic.scoping(),)
                .is_empty()
        );
    }

    #[test]
    fn records_origin_passed_to_unresolved_call_as_exposure() {
        let source = r#"
            const C = function() { unknown(this); };
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let exposures =
            structurally_proven_origin_exposures(&parsed.program, semantic.semantic.scoping());
        assert_eq!(exposures.len(), 1);
        assert_eq!(exposures[0].kind, "call_argument");
    }

    #[test]
    fn records_returned_origin_as_exposure() {
        let source = r#"
            const C = function() { return this; };
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let exposures =
            structurally_proven_origin_exposures(&parsed.program, semantic.semantic.scoping());
        assert_eq!(exposures.len(), 1);
        assert_eq!(exposures[0].kind, "return");
    }

    #[test]
    fn propagates_constructor_this_through_direct_calls() {
        let source = r#"
            const C = function() { start(this); };
            function start(state) { bridge(state); }
            function bridge(state) { state.run(); }
            new C();
        "#;
        let proven = calls(source);
        assert_eq!(proven.len(), 1);
        assert_eq!(proven[0].property, "run");
        assert_eq!(
            &source[proven[0].receiver_start as usize..proven[0].receiver_end as usize],
            "state"
        );
    }

    #[test]
    fn propagates_origin_across_multipurpose_helper_depth() {
        let source = r#"
            const C = function() { setup(this); };
            function setup(state) { schedule(state); }
            function schedule(state) { dispatch(state); }
            function dispatch(state) { route(state); }
            function route(state) { state.run(); state.run(); }
            new C();
        "#;
        let proven = calls(source);
        assert_eq!(proven.len(), 2);
        assert!(proven.iter().all(|call| call.property == "run"));
        assert!(proven
            .windows(2)
            .all(|pair| pair[0].allocation_start == pair[1].allocation_start));
    }

    #[test]
    fn keeps_allocations_context_sensitive() {
        let source = r#"
            const C = function() { start(this); };
            function start(state) { state.run(); }
            new C();
            new C();
        "#;
        let proven = calls(source);
        assert_eq!(proven.len(), 2);
        assert_ne!(proven[0].allocation_start, proven[1].allocation_start);
    }

    #[test]
    fn rejects_reassigned_origin_parameter() {
        let source = r#"
            const C = function() { start(this); };
            function start(state) { state = other; state.run(); }
            new C();
        "#;
        assert!(calls(source).is_empty());
    }

    #[test]
    fn rejects_dynamic_scope_hop() {
        let source = r#"
            const C = function() { start(this); };
            function start(state) { eval("state = other"); state.run(); }
            new C();
        "#;
        assert!(calls(source).is_empty());
    }

    #[test]
    fn records_context_sensitive_origin_direct_call_chain() {
        let source = r#"
            const C = function() { setup(this); };
            function setup(state) { schedule(state); }
            function schedule(state) { state.run(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        let calls =
            structurally_proven_origin_direct_calls(&parsed.program, semantic.semantic.scoping());
        assert_eq!(calls.len(), 2);
        assert!(calls[0].caller.this_origin);
        assert!(calls[0].caller.parameter_indices.is_empty());
        assert_eq!(calls[0].callee.parameter_indices, vec![0]);
        assert_eq!(calls[1].caller.parameter_indices, vec![0]);
        assert_eq!(calls[1].callee.parameter_indices, vec![0]);
        assert_eq!(
            calls[0].caller.allocation_start,
            calls[1].caller.allocation_start
        );
    }

    #[test]
    fn keeps_multipurpose_helper_origin_positions_distinct() {
        let source = r#"
            const C = function() { setup(this); };
            function setup(state) {
                helper(state, other);
                helper(other, state);
            }
            function helper(left, right) {
                left.run();
                right.run();
            }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        let calls =
            structurally_proven_origin_direct_calls(&parsed.program, semantic.semantic.scoping());
        let helper_contexts = calls
            .iter()
            .filter(|call| call.callee.parameter_indices.len() == 1)
            .map(|call| call.callee.parameter_indices.clone())
            .collect::<HashSet<_>>();
        assert!(helper_contexts.contains(&vec![0]));
        assert!(helper_contexts.contains(&vec![1]));
    }

    #[test]
    fn prototype_property_value_argument_does_not_escape_prototype_object() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            sink(C.prototype.token);
        "#;
        let targets = lookup_targets(source);
        assert_eq!(targets.len(), 1);
        assert_eq!(targets[0].property, "run");
    }

    #[test]
    fn direct_prototype_value_argument_invalidates_lookup() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            sink(C.prototype);
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn conditional_prototype_value_argument_invalidates_lookup() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            sink(flag ? C.prototype : {});
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn proves_straight_line_prototype_alias_iife_method() {
        let source = r#"
            const C = function() {};
            var p;
            p = C.prototype;
            p.run = function(seed) {
                return (seed = 1, function(value) { return value + seed; });
            }();
        "#;
        let proven = method_assignments(source);
        assert_eq!(proven.len(), 1);
        assert_eq!(proven[0].property, "run");
        assert!(proven[0].standard_prototype_semantics_required);
        assert!(
            source[proven[0].possible_functions[0].function_start as usize
                ..proven[0].possible_functions[0].function_end as usize]
                .starts_with("function(value)")
        );
    }

    #[test]
    fn rejects_prototype_alias_across_unknown_call() {
        let source = r#"
            const C = function() {};
            var p;
            p = C.prototype;
            unknown();
            p.run = function() {};
        "#;
        assert!(method_assignments(source).is_empty());
    }

    #[test]
    fn dynamic_property_write_does_not_destroy_prototype_alias_identity() {
        let source = r#"
            const C = function() {};
            var p;
            p = C.prototype;
            p[key] = 1;
            p.run = function() {};
        "#;
        let proven = method_assignments(source);
        assert_eq!(proven.len(), 1);
        assert_eq!(proven[0].property, "run");
    }

    #[test]
    fn lookup_target_accepts_resolved_nonconflicting_empty_array_key() {
        let source = r#"
            const C = function() {};
            const empty = [];
            C.prototype.run = function() {};
            C.prototype[empty] = 1;
        "#;
        let targets = lookup_targets(source);
        assert_eq!(targets.len(), 1);
        assert_eq!(targets[0].property, "run");
    }

    #[test]
    fn lookup_target_rejects_constructor_escape_to_unknown_call() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            unknown(C);
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_constructor_alias_creation() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            const Alias = C;
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_dynamic_constructor_property_write() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            C[key] = value;
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_dynamic_constructor_property_escape() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            unknown(C[key]);
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_keeps_static_constructor_property_value_escape_distinct() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            unknown(C.other);
        "#;
        let targets = lookup_targets(source);
        assert_eq!(targets.len(), 1);
        assert_eq!(targets[0].property, "run");
    }

    #[test]
    fn lookup_target_rejects_conditional_constructor_escape() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            if (flag) unknown(C);
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_keeps_constructor_new_expression_distinct_from_escape() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            function make() { return new C(); }
        "#;
        let targets = lookup_targets(source);
        assert_eq!(targets.len(), 1);
        assert_eq!(targets[0].property, "run");
    }

    #[test]
    fn lookup_target_rejects_conditional_prototype_mutation() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            if (flag) C.prototype.run = function() {};
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_conditional_alias_prototype_mutation() {
        let source = r#"
            const C = function() {};
            let p = C.prototype;
            p.run = function() {};
            if (flag) p.run = function() {};
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_compound_prototype_method_write() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            C.prototype.run += 1;
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_prototype_method_update() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            C.prototype.run++;
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_prototype_method_delete() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            delete C.prototype.run;
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_unresolved_computed_prototype_write() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            C.prototype[key] = 1;
        "#;
        assert!(lookup_targets(source).is_empty());
        assert_eq!(method_assignments(source).len(), 1);
    }

    #[test]
    fn lookup_target_rejects_prototype_escape_to_unknown_call() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            unknown(C.prototype);
        "#;
        assert!(lookup_targets(source).is_empty());
        assert_eq!(method_assignments(source).len(), 1);
    }

    #[test]
    fn lookup_target_rejects_unknown_method_call_on_prototype_alias() {
        let source = r#"
            const C = function() {};
            let p = C.prototype;
            p.run = function() {};
            p.touch();
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_unknown_computed_method_call_on_prototype_alias() {
        let source = r#"
            const C = function() {};
            let p = C.prototype;
            p.run = function() {};
            p[key]();
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_nested_prototype_escape_to_unknown_call() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            unknown([C.prototype]);
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_prototype_nested_in_object_value() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            unknown({ value: C.prototype });
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn proves_exact_origin_member_writes_through_direct_calls() {
        let source = r#"
            const C = function() { setup(this); };
            function setup(state) {
                state.ready = 1;
                state[key] = 2;
                state.count++;
                delete state.old;
            }
            new C();
        "#;
        let proven = writes(source);
        assert_eq!(proven.len(), 4);
        assert_eq!(proven[0].property.as_deref(), Some("ready"));
        assert_eq!(proven[1].property, None);
        assert_eq!(proven[2].property.as_deref(), Some("count"));
        assert_eq!(proven[3].property.as_deref(), Some("old"));
        assert_eq!(proven[2].operation, "update");
        assert_eq!(proven[3].operation, "delete");
        assert!(proven
            .windows(2)
            .all(|pair| { pair[0].allocation_start == pair[1].allocation_start }));
    }

    #[test]
    fn member_write_origin_does_not_enter_uninvoked_closure() {
        let source = r#"
            const C = function() { setup(this); };
            function setup(state) {
                function later() { state.shadow = 1; }
            }
            new C();
        "#;
        assert!(writes(source).is_empty());
    }

    #[test]
    fn proves_finite_conditional_prototype_function_values() {
        let source = r#"
            const C = function() {};
            C.prototype.clock = flag
                ? function() { return this.base + host.now(); }
                : function() { return 0; };
        "#;
        let proven = method_assignments(source);
        assert_eq!(proven.len(), 1);
        assert_eq!(proven[0].property, "clock");
        assert_eq!(proven[0].possible_functions.len(), 2);
    }

    #[test]
    fn summarizes_receiver_requirements_across_all_possible_method_bodies() {
        let source = r#"
            const C = function() {};
            C.prototype.clock = flag
                ? function() { return this.base + host.now(); }
                : function() { return 0; };
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        let effects = structurally_proven_prototype_method_receiver_effects(
            &parsed.program,
            semantic.semantic.scoping(),
        );
        assert_eq!(effects.len(), 1);
        assert_eq!(effects[0].receiver_reads, vec!["base"]);
        assert!(effects[0].receiver_calls.is_empty());
        assert!(!effects[0].mutates_receiver);
        assert!(!effects[0].exposes_receiver);
        assert!(!effects[0].dynamic_receiver_access);
    }

    #[test]
    fn summarizes_receiver_mutation_call_and_exposure_obligations() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function(arg) {
                this.count++;
                this.step(arg);
                unknown(this);
                return this[key];
            };
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        let effects = structurally_proven_prototype_method_receiver_effects(
            &parsed.program,
            semantic.semantic.scoping(),
        );
        assert_eq!(effects.len(), 1);
        assert_eq!(effects[0].receiver_calls, vec!["step"]);
        assert!(effects[0].mutates_receiver);
        assert!(effects[0].exposes_receiver);
        assert!(effects[0].dynamic_receiver_access);
    }

    #[test]
    fn does_not_descend_into_uninvoked_nested_functions() {
        let source = r#"
            const C = function() { start(this); };
            function start(state) {
                function later() { state.run(); }
            }
            new C();
        "#;
        assert!(calls(source).is_empty());
    }
}
