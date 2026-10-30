use crate::{
    cfg_order::{
        prove_event_before_barriers, prove_event_completion_before_event,
        prove_event_completion_before_nested_event,
    },
    numeric::exact_i64,
    state_flatten::{
        prove_function_if_ladder_event_before_barriers,
        prove_function_if_ladder_event_unreachable_with_integer_parameters,
        prove_function_protected_if_ladder_event_unreachable_with_call_arguments,
        prove_function_structured_branch_event_unreachable_with_integer_parameters,
        prove_function_switch_event_unreachable_with_integer_parameters,
    },
};
use jsvm_safe_core::{eval_static_primitive, string_literal_value};
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, AssignmentTarget, BindingPattern, CallExpression, Expression,
    Function, FunctionBody, NewExpression, ObjectPropertyKind, Program, Statement,
    VariableDeclaration,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, Semantic};
use oxc_span::{GetSpan, Span};
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

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
    pub evaluation_order: u64,
    pub caller: ProvenOriginContext,
    pub callee: ProvenOriginContext,
    /// True when this edge is a statically bound `function.call(thisArg, ...)`
    /// invocation and therefore depends on ordinary Function.prototype.call semantics.
    pub standard_function_call_semantics_required: bool,
    /// Source spans for callee arguments in formal-parameter order. For
    /// `function.call(thisArg, ...)`, the `thisArg` operand is intentionally
    /// excluded so downstream parameter specialization stays index-correct.
    /// exact expressions used to establish parameter-origin mappings and let
    /// downstream proofs specialize callee control flow without textual search.
    pub argument_spans: Vec<(u32, u32)>,
    /// Exact integer value of each argument when its value-producing final
    /// expression is independently static. Earlier sequence operands may have
    /// side effects; conditional on the call occurring they cannot change the
    /// value of a static final operand.
    pub exact_integer_arguments: Vec<Option<i64>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenMemberReceiverOrigin {
    pub context: ProvenOriginContext,
    pub call_start: u32,
    pub call_end: u32,
    pub evaluation_order: u64,
    pub receiver_start: u32,
    pub receiver_end: u32,
    pub property: String,
    pub allocation_start: u32,
    pub allocation_end: u32,
    pub constructor_start: u32,
    pub constructor_end: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenMemberReadOrigin {
    pub context: ProvenOriginContext,
    pub read_start: u32,
    pub read_end: u32,
    pub evaluation_order: u64,
    pub receiver_start: u32,
    pub receiver_end: u32,
    /// `None` means the receiver identity is exact but the computed key is not.
    pub property: Option<String>,
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
    pub evaluation_order: u64,
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
    pub evaluation_order: u64,
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

fn exact_syntactic_integer(expression: &Expression<'_>) -> Option<i64> {
    match last_sequence_expression(expression) {
        Expression::NumericLiteral(number) => exact_i64(number.value),
        Expression::UnaryExpression(unary) => {
            let value = exact_syntactic_integer(&unary.argument)?;
            match unary.operator.as_str() {
                "+" => Some(value),
                "-" => value.checked_neg(),
                _ => None,
            }
        }
        _ => None,
    }
}

#[derive(Default)]
struct DynamicScopeProbe {
    direct_eval: bool,
    with_statement: bool,
    arguments_object: bool,
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

    fn visit_identifier_reference(&mut self, identifier: &oxc_ast::ast::IdentifierReference<'a>) {
        if identifier.name.as_str() == "arguments" {
            self.arguments_object = true;
        }
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
    probe.direct_eval || probe.with_statement || probe.arguments_object
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
    property_keys: &'f HashMap<SymbolId, String>,
    context: &'f FunctionContext,
    parameter_origins: HashMap<SymbolId, ObjectOrigin>,
    local_origins: HashMap<SymbolId, ObjectOrigin>,
    discovered: Vec<FunctionContext>,
    member_calls: Vec<ProvenMemberReceiverOrigin>,
    member_reads: Vec<ProvenMemberReadOrigin>,
    member_writes: Vec<ProvenMemberWriteOrigin>,
    exposures: Vec<ProvenOriginExposure>,
    direct_calls: Vec<ProvenOriginDirectCall>,
    suppressed_member_reads: HashSet<(u32, u32)>,
    evaluation_order: u64,
    target: FunctionKey,
    active: bool,
}

impl<'c, 'f> ContextProbe<'c, 'f> {
    fn new(
        scoping: &'c Scoping,
        functions: &'f HashMap<SymbolId, FunctionKey>,
        function_info: &'f HashMap<FunctionKey, FunctionInfo>,
        property_keys: &'f HashMap<SymbolId, String>,
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
            property_keys,
            context,
            parameter_origins,
            local_origins: HashMap::new(),
            discovered: Vec::new(),
            member_calls: Vec::new(),
            member_reads: Vec::new(),
            member_writes: Vec::new(),
            exposures: Vec::new(),
            direct_calls: Vec::new(),
            suppressed_member_reads: HashSet::new(),
            evaluation_order: 0,
            target: context.function,
            active: false,
        }
    }

    fn next_evaluation_order(&mut self) -> u64 {
        let order = self.evaluation_order;
        self.evaluation_order = self.evaluation_order.saturating_add(1);
        order
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

    fn record_direct_call(
        &mut self,
        call: &CallExpression<'_>,
        callee: FunctionKey,
        argument_offset: usize,
        this_origin: Option<ObjectOrigin>,
        standard_function_call_semantics_required: bool,
    ) {
        let Some(info) = self.function_info.get(&callee) else {
            return;
        };
        if info.dynamic_scope {
            return;
        }
        let mapped_arguments = call
            .arguments
            .iter()
            .skip(argument_offset)
            .collect::<Vec<_>>();
        let parameter_origins = info
            .parameters
            .iter()
            .enumerate()
            .map(|(index, _)| {
                mapped_arguments
                    .get(index)
                    .and_then(|argument| argument.as_expression())
                    .and_then(|argument| self.expression_origin(argument))
            })
            .collect::<Vec<_>>();
        if this_origin.is_none() && parameter_origins.iter().all(Option::is_none) {
            return;
        }
        let child = FunctionContext {
            function: callee,
            this_origin,
            parameter_origins,
        };
        let origins = child
            .this_origin
            .into_iter()
            .chain(child.parameter_origins.iter().filter_map(|origin| *origin))
            .collect::<HashSet<_>>();
        let evaluation_order = self.next_evaluation_order();
        for origin in origins {
            if let (Some(caller), Some(callee)) = (
                self.context.proven_origin_context(origin),
                child.proven_origin_context(origin),
            ) {
                self.direct_calls.push(ProvenOriginDirectCall {
                    call_start: call.span.start,
                    call_end: call.span.end,
                    evaluation_order,
                    caller,
                    callee,
                    standard_function_call_semantics_required,
                    argument_spans: mapped_arguments
                        .iter()
                        .map(|argument| (argument.span().start, argument.span().end))
                        .collect(),
                    exact_integer_arguments: mapped_arguments
                        .iter()
                        .map(|argument| {
                            let expression = argument.as_expression()?;
                            exact_syntactic_integer(expression)
                        })
                        .collect(),
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
        let evaluation_order = self.next_evaluation_order();
        self.exposures.push(ProvenOriginExposure {
            context,
            exposure_start: span.start,
            exposure_end: span.end,
            evaluation_order,
            allocation_start: origin.allocation_start,
            allocation_end: origin.allocation_end,
            constructor_start: origin.constructor.start,
            constructor_end: origin.constructor.end,
            kind,
        });
    }

    fn record_member_read(
        &mut self,
        receiver: &Expression<'_>,
        property: Option<String>,
        span: oxc_span::Span,
    ) {
        let Some(origin) = self.expression_origin(receiver) else {
            return;
        };
        let Some(context) = self.context.proven_origin_context(origin) else {
            return;
        };
        let evaluation_order = self.next_evaluation_order();
        self.member_reads.push(ProvenMemberReadOrigin {
            context,
            read_start: span.start,
            read_end: span.end,
            evaluation_order,
            receiver_start: receiver.span().start,
            receiver_end: receiver.span().end,
            property,
            allocation_start: origin.allocation_start,
            allocation_end: origin.allocation_end,
            constructor_start: origin.constructor.start,
            constructor_end: origin.constructor.end,
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
        let evaluation_order = self.next_evaluation_order();
        self.member_writes.push(ProvenMemberWriteOrigin {
            context,
            write_start: span.start,
            write_end: span.end,
            evaluation_order,
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
                let property =
                    proof_property_key(&member.expression, self.scoping, self.property_keys);
                Some((&member.object, property))
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
        walk::walk_return_statement(self, statement);
        if self.active {
            if let Some(argument) = statement.argument.as_ref() {
                self.record_exposure(argument, statement.span, "return");
            }
        }
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        let member_target = self
            .active
            .then(|| self.assignment_member(&assignment.left))
            .flatten();
        let suppressed = (assignment.operator.is_assign())
            .then(|| member_target.as_ref())
            .flatten()
            .map(|_| {
                let span = assignment.left.span();
                let key = (span.start, span.end);
                self.suppressed_member_reads.insert(key);
                key
            });
        walk::walk_assignment_expression(self, assignment);
        if let Some(key) = suppressed {
            self.suppressed_member_reads.remove(&key);
        }
        if self.active {
            if let Some((receiver, property)) = member_target {
                let internal_self_store = self
                    .expression_origin(receiver)
                    .zip(self.expression_origin(&assignment.right))
                    .is_some_and(|(destination, value)| destination == value);
                self.record_member_write(receiver, property, assignment.span, "assignment");
                if !internal_self_store {
                    self.record_exposure(&assignment.right, assignment.span, "store");
                }
            } else if !matches!(
                assignment.left,
                AssignmentTarget::AssignmentTargetIdentifier(_)
            ) {
                self.record_exposure(&assignment.right, assignment.span, "store");
            }
        }
    }

    fn visit_update_expression(&mut self, update: &oxc_ast::ast::UpdateExpression<'a>) {
        walk::walk_update_expression(self, update);
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
                    let property =
                        proof_property_key(&member.expression, self.scoping, self.property_keys);
                    self.record_member_write(&member.object, property, update.span, "update");
                }
                _ => {}
            }
        }
    }

    fn visit_unary_expression(&mut self, unary: &oxc_ast::ast::UnaryExpression<'a>) {
        let delete_member = if self.active && unary.operator.as_str() == "delete" {
            match last_sequence_expression(&unary.argument) {
                Expression::StaticMemberExpression(member) if !member.optional => Some((
                    &member.object,
                    Some(member.property.name.to_string()),
                    member.span,
                )),
                Expression::ComputedMemberExpression(member) if !member.optional => {
                    let property =
                        proof_property_key(&member.expression, self.scoping, self.property_keys);
                    Some((&member.object, property, member.span))
                }
                _ => None,
            }
        } else {
            None
        };
        if let Some((_, _, span)) = delete_member.as_ref() {
            self.suppressed_member_reads.insert((span.start, span.end));
        }
        walk::walk_unary_expression(self, unary);
        if let Some((receiver, property, span)) = delete_member {
            self.suppressed_member_reads.remove(&(span.start, span.end));
            self.record_member_write(receiver, property, unary.span, "delete");
        }
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !self.active {
            walk::walk_call_expression(self, call);
            return;
        }

        let ordinary_callee = (!call.optional)
            .then(|| self.direct_callee(&call.callee))
            .flatten();
        let function_call_callee = if !call.optional && ordinary_callee.is_none() {
            match last_sequence_expression(&call.callee) {
                Expression::StaticMemberExpression(member)
                    if !member.optional && member.property.name.as_str() == "call" =>
                {
                    self.direct_callee(&member.object)
                }
                _ => None,
            }
        } else {
            None
        };
        let invocation = ordinary_callee
            .map(|callee| (callee, 0usize, None, false))
            .or_else(|| {
                let callee = function_call_callee?;
                let this_origin = call
                    .arguments
                    .first()
                    .and_then(Argument::as_expression)
                    .and_then(|argument| self.expression_origin(argument));
                Some((callee, 1usize, this_origin, true))
            })
            .filter(|(callee, _, _, _)| {
                self.function_info
                    .get(callee)
                    .is_some_and(|info| !info.dynamic_scope)
            });

        let exact_member_callee = if invocation.is_none() {
            match last_sequence_expression(&call.callee) {
                Expression::StaticMemberExpression(member) => {
                    self.expression_origin(&member.object).map(|origin| {
                        (
                            &member.object,
                            Some(member.property.name.to_string()),
                            origin,
                            member.optional,
                            member.span,
                        )
                    })
                }
                Expression::ComputedMemberExpression(member) => {
                    self.expression_origin(&member.object).map(|origin| {
                        let property = proof_property_key(
                            &member.expression,
                            self.scoping,
                            self.property_keys,
                        );
                        (
                            &member.object,
                            property,
                            origin,
                            member.optional,
                            member.span,
                        )
                    })
                }
                _ => None,
            }
        } else {
            None
        };
        let member_receiver = exact_member_callee.as_ref().and_then(
            |(receiver, property, origin, member_optional, _)| {
                (!call.optional && !*member_optional)
                    .then(|| {
                        property
                            .clone()
                            .map(|property| (*receiver, property, *origin))
                    })
                    .flatten()
            },
        );
        let unresolved_member_barrier =
            exact_member_callee
                .as_ref()
                .and_then(|(receiver, property, _, member_optional, _)| {
                    (call.optional || *member_optional || property.is_none()).then_some(*receiver)
                });
        let suppressed_callee = exact_member_callee.as_ref().map(|(_, _, _, _, span)| {
            let key = (span.start, span.end);
            self.suppressed_member_reads.insert(key);
            key
        });

        let proven_parameter_count = invocation
            .and_then(|(callee, _, _, _)| self.function_info.get(&callee))
            .map_or(0, |info| info.parameters.len());
        let argument_offset = invocation.map_or(0, |(_, offset, _, _)| offset);

        // JavaScript evaluates callee/receiver and arguments before invocation.
        // Record nested effects first, then the invocation/exposure event.
        walk::walk_call_expression(self, call);
        if let Some(key) = suppressed_callee {
            self.suppressed_member_reads.remove(&key);
        }

        if let Some((callee, offset, this_origin, standard_call)) = invocation {
            self.record_direct_call(call, callee, offset, this_origin, standard_call);
        } else if let Some((receiver, property, origin)) = member_receiver {
            if let Some(context) = self.context.proven_origin_context(origin) {
                let evaluation_order = self.next_evaluation_order();
                self.member_calls.push(ProvenMemberReceiverOrigin {
                    context,
                    call_start: call.span.start,
                    call_end: call.span.end,
                    evaluation_order,
                    receiver_start: receiver.span().start,
                    receiver_end: receiver.span().end,
                    property,
                    allocation_start: origin.allocation_start,
                    allocation_end: origin.allocation_end,
                    constructor_start: origin.constructor.start,
                    constructor_end: origin.constructor.end,
                });
            }
        } else if let Some(receiver) = unresolved_member_barrier {
            self.record_exposure(receiver, call.span, "unresolved_member_call");
        }

        for (index, argument) in call.arguments.iter().enumerate() {
            let Some(argument) = argument.as_expression() else {
                continue;
            };
            let consumed_as_this = invocation.is_some() && argument_offset == 1 && index == 0;
            let mapped_index = index.checked_sub(argument_offset);
            let consumed_as_parameter =
                mapped_index.is_some_and(|index| index < proven_parameter_count);
            if invocation.is_none() || (!consumed_as_this && !consumed_as_parameter) {
                self.record_exposure(argument, argument.span(), "call_argument");
            }
        }
    }

    fn visit_static_member_expression(
        &mut self,
        member: &oxc_ast::ast::StaticMemberExpression<'a>,
    ) {
        walk::walk_static_member_expression(self, member);
        if self.active
            && !self
                .suppressed_member_reads
                .contains(&(member.span.start, member.span.end))
        {
            self.record_member_read(
                &member.object,
                Some(member.property.name.to_string()),
                member.span,
            );
        }
    }

    fn visit_computed_member_expression(
        &mut self,
        member: &oxc_ast::ast::ComputedMemberExpression<'a>,
    ) {
        walk::walk_computed_member_expression(self, member);
        if self.active
            && !self
                .suppressed_member_reads
                .contains(&(member.span.start, member.span.end))
        {
            let property = proof_property_key(&member.expression, self.scoping, self.property_keys);
            self.record_member_read(&member.object, property, member.span);
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProvenOriginFlow {
    pub member_calls: Vec<ProvenMemberReceiverOrigin>,
    pub member_reads: Vec<ProvenMemberReadOrigin>,
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
    let property_keys = collect_property_key_bindings(program, scoping);
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
            &property_keys,
            &context,
            info,
        );
        probe.visit_program(program);
        queue.extend(probe.discovered);
        flow.member_calls.extend(probe.member_calls);
        flow.member_reads.extend(probe.member_reads);
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
    flow.member_reads.sort_by_key(|read| {
        (
            read.read_start,
            read.read_end,
            read.context.allocation_start,
            read.context.function_start,
        )
    });
    flow.member_reads.dedup();
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

fn origin_prefix_is_fresh(
    flow: &ProvenOriginFlow,
    context: &ProvenOriginContext,
    before_order: u64,
    stable_prototypes: &HashSet<(u32, u32)>,
) -> bool {
    !flow
        .exposures
        .iter()
        .any(|exposure| &exposure.context == context && exposure.evaluation_order < before_order)
        && !flow.member_reads.iter().any(|read| {
            &read.context == context
                && read.evaluation_order < before_order
                && (!stable_prototypes.contains(&(read.constructor_start, read.constructor_end))
                    || read
                        .property
                        .as_deref()
                        .is_none_or(|property| property == "__proto__"))
        })
        && !flow
            .member_calls
            .iter()
            .any(|call| &call.context == context && call.evaluation_order < before_order)
        && !flow
            .direct_calls
            .iter()
            .any(|call| &call.caller == context && call.evaluation_order < before_order)
        && !flow.member_writes.iter().any(|write| {
            &write.context == context
                && write.evaluation_order < before_order
                && write
                    .property
                    .as_deref()
                    .is_none_or(|property| property == "__proto__")
        })
}

#[must_use]
pub fn structurally_proven_own_data_field_initializations(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenOwnDataFieldInitialization> {
    let flow = structurally_proven_origin_flow(program, scoping);
    let stable = structurally_proven_stable_constructor_prototypes(program, scoping)
        .into_iter()
        .map(|prototype| (prototype.constructor_start, prototype.constructor_end))
        .collect::<HashSet<_>>();

    let mut fresh_contexts = HashSet::new();
    for context in flow
        .member_calls
        .iter()
        .map(|call| &call.context)
        .chain(flow.member_reads.iter().map(|read| &read.context))
        .chain(flow.member_writes.iter().map(|write| &write.context))
        .chain(flow.exposures.iter().map(|exposure| &exposure.context))
        .chain(
            flow.direct_calls
                .iter()
                .flat_map(|call| [&call.caller, &call.callee]),
        )
    {
        if context.this_origin
            && context.function_start == context.constructor_start
            && context.function_end == context.constructor_end
        {
            fresh_contexts.insert(context.clone());
        }
    }

    loop {
        let mut changed = false;
        for call in &flow.direct_calls {
            if fresh_contexts.contains(&call.caller)
                && !fresh_contexts.contains(&call.callee)
                && origin_prefix_is_fresh(&flow, &call.caller, call.evaluation_order, &stable)
            {
                fresh_contexts.insert(call.callee.clone());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut proven = flow
        .member_writes
        .iter()
        .filter_map(|write| {
            let property = write.property.as_ref()?;
            if write.operation != "assignment"
                || property == "__proto__"
                || !fresh_contexts.contains(&write.context)
                || !stable.contains(&(write.constructor_start, write.constructor_end))
                || !origin_prefix_is_fresh(&flow, &write.context, write.evaluation_order, &stable)
                || flow.member_writes.iter().any(|earlier| {
                    earlier.context == write.context
                        && earlier.evaluation_order < write.evaluation_order
                        && earlier.property.as_deref() == Some(property.as_str())
                })
            {
                return None;
            }
            Some(ProvenOwnDataFieldInitialization {
                context: write.context.clone(),
                property: property.clone(),
                write_start: write.write_start,
                write_end: write.write_end,
                evaluation_order: write.evaluation_order,
                allocation_start: write.allocation_start,
                allocation_end: write.allocation_end,
                constructor_start: write.constructor_start,
                constructor_end: write.constructor_end,
                standard_prototype_semantics_required: true,
            })
        })
        .collect::<Vec<_>>();
    proven.sort_by_key(|field| {
        (
            field.allocation_start,
            field.context.function_start,
            field.evaluation_order,
            field.property.clone(),
        )
    });
    proven.dedup();
    proven
}

fn static_member_read_is_getter_free(
    read: &ProvenMemberReadOrigin,
    stable_prototypes: &HashSet<(u32, u32)>,
) -> bool {
    stable_prototypes.contains(&(read.constructor_start, read.constructor_end))
        && read
            .property
            .as_deref()
            .is_some_and(|property| property != "__proto__")
}

fn member_write_preserves_field(
    write: &ProvenMemberWriteOrigin,
    property: &str,
    stable_prototypes: &HashSet<(u32, u32)>,
    preserve_exact_value: bool,
) -> bool {
    let Some(candidate) = write.property.as_deref() else {
        return false;
    };
    if !stable_prototypes.contains(&(write.constructor_start, write.constructor_end))
        || candidate == "__proto__"
    {
        return false;
    }
    if candidate != property {
        return true;
    }
    !preserve_exact_value && write.operation != "delete"
}

type PreservationKey = (
    u32,
    u32,
    ProvenOriginContext,
    ProvenOriginContext,
    String,
    bool,
);

fn direct_call_preserves_field(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    flow: &ProvenOriginFlow,
    call: &ProvenOriginDirectCall,
    property: &str,
    stable_prototypes: &HashSet<(u32, u32)>,
    preserve_exact_value: bool,
    memo: &mut HashMap<PreservationKey, bool>,
    visiting: &mut HashSet<PreservationKey>,
) -> bool {
    let key = (
        call.call_start,
        call.call_end,
        call.caller.clone(),
        call.callee.clone(),
        property.to_string(),
        preserve_exact_value,
    );
    if let Some(result) = memo.get(&key) {
        return *result;
    }
    if !visiting.insert(key.clone()) {
        return false;
    }

    let unreachable = |start: u32, end: u32| {
        proven_origin_direct_call_event_unreachable(
            source,
            program,
            scoping,
            call,
            Span::new(start, end),
        )
    };

    let mut result = true;
    for exposure in flow
        .exposures
        .iter()
        .filter(|event| event.context == call.callee)
    {
        if !unreachable(exposure.exposure_start, exposure.exposure_end) {
            result = false;
            break;
        }
    }
    if result {
        for read in flow
            .member_reads
            .iter()
            .filter(|event| event.context == call.callee)
        {
            if !unreachable(read.read_start, read.read_end)
                && !static_member_read_is_getter_free(read, stable_prototypes)
            {
                result = false;
                break;
            }
        }
    }
    if result {
        for write in flow
            .member_writes
            .iter()
            .filter(|event| event.context == call.callee)
        {
            if !unreachable(write.write_start, write.write_end)
                && !member_write_preserves_field(
                    write,
                    property,
                    stable_prototypes,
                    preserve_exact_value,
                )
            {
                result = false;
                break;
            }
        }
    }
    if result {
        for member_call in flow
            .member_calls
            .iter()
            .filter(|event| event.context == call.callee)
        {
            if !unreachable(member_call.call_start, member_call.call_end) {
                result = false;
                break;
            }
        }
    }
    if result {
        for nested in flow
            .direct_calls
            .iter()
            .filter(|nested| nested.caller == call.callee)
        {
            if unreachable(nested.call_start, nested.call_end) {
                continue;
            }
            if !direct_call_preserves_field(
                source,
                program,
                scoping,
                flow,
                nested,
                property,
                stable_prototypes,
                preserve_exact_value,
                memo,
                visiting,
            ) {
                result = false;
                break;
            }
        }
    }

    visiting.remove(&key);
    memo.insert(key, result);
    result
}

/// Prove that one exact-origin direct call preserves a named ordinary own-data
/// field of the tracked receiver across all supported reachable effects.
///
/// Call-site-specialized unreachable effects are ignored only when independently
/// proven unreachable; recursive cycles and unsupported reachable effects fail closed.
#[must_use]
pub fn proven_origin_direct_call_preserves_own_field(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    call: &ProvenOriginDirectCall,
    property: &str,
) -> bool {
    let flow = structurally_proven_origin_flow(program, scoping);
    let stable_prototypes = structurally_proven_stable_constructor_prototypes(program, scoping)
        .into_iter()
        .map(|prototype| (prototype.constructor_start, prototype.constructor_end))
        .collect::<HashSet<_>>();
    direct_call_preserves_field(
        source,
        program,
        scoping,
        &flow,
        call,
        property,
        &stable_prototypes,
        false,
        &mut HashMap::new(),
        &mut HashSet::new(),
    )
}

/// Prove that one exact-origin direct call preserves the exact current value of
/// a named receiver property. Any reachable write, update, or delete of that
/// property invalidates the theorem.
#[must_use]
pub fn proven_origin_direct_call_preserves_exact_property(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    call: &ProvenOriginDirectCall,
    property: &str,
) -> bool {
    let flow = structurally_proven_origin_flow(program, scoping);
    let stable_prototypes = structurally_proven_stable_constructor_prototypes(program, scoping)
        .into_iter()
        .map(|prototype| (prototype.constructor_start, prototype.constructor_end))
        .collect::<HashSet<_>>();
    direct_call_preserves_field(
        source,
        program,
        scoping,
        &flow,
        call,
        property,
        &stable_prototypes,
        true,
        &mut HashMap::new(),
        &mut HashSet::new(),
    )
}

fn root_context_segment_preserves_field(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    flow: &ProvenOriginFlow,
    context: &ProvenOriginContext,
    after_order: u64,
    before_order: u64,
    property: &str,
    stable_prototypes: &HashSet<(u32, u32)>,
    preserve_exact_value: bool,
    memo: &mut HashMap<PreservationKey, bool>,
    visiting: &mut HashSet<PreservationKey>,
) -> bool {
    if flow.exposures.iter().any(|event| {
        event.context == *context
            && after_order < event.evaluation_order
            && event.evaluation_order < before_order
    }) || flow.member_calls.iter().any(|event| {
        event.context == *context
            && after_order < event.evaluation_order
            && event.evaluation_order < before_order
    }) || flow.member_reads.iter().any(|event| {
        event.context == *context
            && after_order < event.evaluation_order
            && event.evaluation_order < before_order
            && !static_member_read_is_getter_free(event, stable_prototypes)
    }) || flow.member_writes.iter().any(|event| {
        event.context == *context
            && after_order < event.evaluation_order
            && event.evaluation_order < before_order
            && !member_write_preserves_field(
                event,
                property,
                stable_prototypes,
                preserve_exact_value,
            )
    }) {
        return false;
    }

    flow.direct_calls
        .iter()
        .filter(|nested| {
            nested.caller == *context
                && after_order < nested.evaluation_order
                && nested.evaluation_order < before_order
        })
        .all(|nested| {
            direct_call_preserves_field(
                source,
                program,
                scoping,
                flow,
                nested,
                property,
                stable_prototypes,
                preserve_exact_value,
                memo,
                visiting,
            )
        })
}

fn direct_call_prefix_preserves_field(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    flow: &ProvenOriginFlow,
    entry: &ProvenOriginDirectCall,
    before_order: u64,
    property: &str,
    stable_prototypes: &HashSet<(u32, u32)>,
    preserve_exact_value: bool,
    memo: &mut HashMap<PreservationKey, bool>,
    visiting: &mut HashSet<PreservationKey>,
) -> bool {
    for exposure in flow
        .exposures
        .iter()
        .filter(|event| event.context == entry.callee && event.evaluation_order < before_order)
    {
        if !proven_origin_direct_call_event_unreachable(
            source,
            program,
            scoping,
            entry,
            Span::new(exposure.exposure_start, exposure.exposure_end),
        ) {
            return false;
        }
    }
    for read in flow
        .member_reads
        .iter()
        .filter(|event| event.context == entry.callee && event.evaluation_order < before_order)
    {
        if !proven_origin_direct_call_event_unreachable(
            source,
            program,
            scoping,
            entry,
            Span::new(read.read_start, read.read_end),
        ) && !static_member_read_is_getter_free(read, stable_prototypes)
        {
            return false;
        }
    }
    for write in flow
        .member_writes
        .iter()
        .filter(|event| event.context == entry.callee && event.evaluation_order < before_order)
    {
        if !proven_origin_direct_call_event_unreachable(
            source,
            program,
            scoping,
            entry,
            Span::new(write.write_start, write.write_end),
        ) && !member_write_preserves_field(
            write,
            property,
            stable_prototypes,
            preserve_exact_value,
        ) {
            return false;
        }
    }
    for member_call in flow
        .member_calls
        .iter()
        .filter(|event| event.context == entry.callee && event.evaluation_order < before_order)
    {
        if !proven_origin_direct_call_event_unreachable(
            source,
            program,
            scoping,
            entry,
            Span::new(member_call.call_start, member_call.call_end),
        ) {
            return false;
        }
    }
    for nested in flow
        .direct_calls
        .iter()
        .filter(|nested| nested.caller == entry.callee && nested.evaluation_order < before_order)
    {
        if proven_origin_direct_call_event_unreachable(
            source,
            program,
            scoping,
            entry,
            Span::new(nested.call_start, nested.call_end),
        ) {
            continue;
        }
        if !direct_call_preserves_field(
            source,
            program,
            scoping,
            flow,
            nested,
            property,
            stable_prototypes,
            preserve_exact_value,
            memo,
            visiting,
        ) {
            return false;
        }
    }
    true
}

/// Prove that a freshly initialized ordinary own-data field survives from its
/// initialization context through a concrete exact-origin direct call and up
/// to a receiver member call in that callee.
///
/// This is intentionally a prefix theorem. Receiver method calls are barriers;
/// nested direct calls are recursively summarized, and call-site-specialized
/// unreachable events are ignored only when independently proven unreachable.
#[must_use]
pub fn structurally_proven_own_data_fields_at_member_calls(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
) -> Vec<ProvenOwnDataFieldAtMemberCall> {
    let scoping = semantic.scoping();
    let flow = structurally_proven_origin_flow(program, scoping);
    let initializations = structurally_proven_own_data_field_initializations(program, scoping);
    let stable_prototypes = structurally_proven_stable_constructor_prototypes(program, scoping)
        .into_iter()
        .map(|prototype| (prototype.constructor_start, prototype.constructor_end))
        .collect::<HashSet<_>>();
    let mut memo = HashMap::new();
    let mut visiting = HashSet::new();
    let mut proven = Vec::new();

    for initialization in &initializations {
        for entry in flow.direct_calls.iter().filter(|call| {
            call.caller == initialization.context
                && initialization.evaluation_order < call.evaluation_order
                && prove_event_completion_before_event(
                    semantic,
                    Span::new(initialization.write_start, initialization.write_end),
                    Span::new(call.call_start, call.call_end),
                )
        }) {
            if !root_context_segment_preserves_field(
                source,
                program,
                scoping,
                &flow,
                &initialization.context,
                initialization.evaluation_order,
                entry.evaluation_order,
                &initialization.property,
                &stable_prototypes,
                false,
                &mut memo,
                &mut visiting,
            ) {
                continue;
            }
            for member_call in flow
                .member_calls
                .iter()
                .filter(|member_call| member_call.context == entry.callee)
            {
                if direct_call_prefix_preserves_field(
                    source,
                    program,
                    scoping,
                    &flow,
                    entry,
                    member_call.evaluation_order,
                    &initialization.property,
                    &stable_prototypes,
                    false,
                    &mut memo,
                    &mut visiting,
                ) {
                    proven.push(ProvenOwnDataFieldAtMemberCall {
                        initialization: initialization.clone(),
                        entry_call: entry.clone(),
                        member_call: member_call.clone(),
                    });
                }
            }
        }
    }
    proven.sort_by_key(|proof| {
        (
            proof.initialization.allocation_start,
            proof.initialization.property.clone(),
            proof.entry_call.call_start,
            proof.member_call.call_start,
        )
    });
    proven.dedup();
    proven
}

/// Prove that the exact value written by a fresh ordinary own-data field
/// initialization is unchanged at one already-proven nested exact-origin
/// direct call.
///
/// The target must itself occur in the structural exact-origin flow. The proof
/// has two explicit segments:
/// 1. initialization -> an incoming direct call in the initialization context;
/// 2. that call's callee entry -> `target`.
///
/// Both segments use the same fail-closed exact-property preservation theorem.
/// The initialization must dominate the incoming call in the semantic CFG.
#[must_use]
pub fn proven_exact_own_data_field_at_direct_call(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    property: &str,
    target: &ProvenOriginDirectCall,
) -> Vec<ProvenExactOwnDataFieldAtDirectCall> {
    let scoping = semantic.scoping();
    let flow = structurally_proven_origin_flow(program, scoping);
    if !flow.direct_calls.contains(target) {
        return Vec::new();
    }
    let initializations = structurally_proven_own_data_field_initializations(program, scoping);
    let stable_prototypes = structurally_proven_stable_constructor_prototypes(program, scoping)
        .into_iter()
        .map(|prototype| (prototype.constructor_start, prototype.constructor_end))
        .collect::<HashSet<_>>();
    let mut memo = HashMap::new();
    let mut visiting = HashSet::new();
    let mut proven = Vec::new();

    for initialization in initializations
        .iter()
        .filter(|initialization| initialization.property == property)
    {
        for entry in flow.direct_calls.iter().filter(|call| {
            call.caller == initialization.context
                && call.callee == target.caller
                && initialization.evaluation_order < call.evaluation_order
                && prove_event_completion_before_event(
                    semantic,
                    Span::new(initialization.write_start, initialization.write_end),
                    Span::new(call.call_start, call.call_end),
                )
        }) {
            if !root_context_segment_preserves_field(
                source,
                program,
                scoping,
                &flow,
                &initialization.context,
                initialization.evaluation_order,
                entry.evaluation_order,
                &initialization.property,
                &stable_prototypes,
                true,
                &mut memo,
                &mut visiting,
            ) {
                continue;
            }
            if direct_call_prefix_preserves_field(
                source,
                program,
                scoping,
                &flow,
                entry,
                target.evaluation_order,
                &initialization.property,
                &stable_prototypes,
                true,
                &mut memo,
                &mut visiting,
            ) {
                proven.push(ProvenExactOwnDataFieldAtDirectCall {
                    initialization: initialization.clone(),
                    entry_call: entry.clone(),
                    direct_call: target.clone(),
                });
            }
        }
    }

    proven.sort_by_key(|proof| {
        (
            proof.initialization.allocation_start,
            proof.initialization.write_start,
            proof.entry_call.call_start,
        )
    });
    proven.dedup();
    proven
}

fn collect_unique_direct_call_path(
    flow: &ProvenOriginFlow,
    root: &ProvenOriginContext,
    target: &ProvenOriginContext,
) -> Option<Vec<ProvenOriginDirectCall>> {
    fn visit(
        flow: &ProvenOriginFlow,
        current: &ProvenOriginContext,
        target: &ProvenOriginContext,
        visiting: &mut HashSet<ProvenOriginContext>,
        path: &mut Vec<ProvenOriginDirectCall>,
        matches: &mut Vec<Vec<ProvenOriginDirectCall>>,
    ) {
        if matches.len() > 1 {
            return;
        }
        if current == target {
            matches.push(path.clone());
            return;
        }
        if !visiting.insert(current.clone()) {
            return;
        }
        for call in flow
            .direct_calls
            .iter()
            .filter(|call| call.caller == *current)
        {
            path.push(call.clone());
            visit(flow, &call.callee, target, visiting, path, matches);
            path.pop();
            if matches.len() > 1 {
                break;
            }
        }
        visiting.remove(current);
    }

    let mut matches = Vec::new();
    visit(
        flow,
        root,
        target,
        &mut HashSet::new(),
        &mut Vec::new(),
        &mut matches,
    );
    let [path] = matches.as_slice() else {
        return None;
    };
    Some(path.clone())
}

fn context_field_prefix_before_event(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    flow: &ProvenOriginFlow,
    stable_prototypes: &HashSet<(u32, u32)>,
    runtime_calls: &[ProvenPrototypeMethodCallTarget],
    context: &ProvenOriginContext,
    entry: &ProvenOriginDirectCall,
    event: Span,
    event_direct_call: Option<&ProvenOriginDirectCall>,
    event_member_call: Option<&ProvenMemberReceiverOrigin>,
    property: &str,
    discharged_preserving_method_calls: &mut Vec<ProvenMemberReceiverOrigin>,
    standard_function_call_semantics_required: &mut bool,
) -> bool {
    if proven_origin_direct_call_event_unreachable(
        source,
        program,
        semantic.scoping(),
        entry,
        event,
    ) {
        return false;
    }
    let unreachable = |start, end| {
        proven_origin_direct_call_event_unreachable(
            source,
            program,
            semantic.scoping(),
            entry,
            Span::new(start, end),
        )
    };
    let mut barriers = Vec::new();

    for exposure in flow
        .exposures
        .iter()
        .filter(|candidate| candidate.context == *context)
    {
        if !unreachable(exposure.exposure_start, exposure.exposure_end) {
            barriers.push(Span::new(exposure.exposure_start, exposure.exposure_end));
        }
    }
    for read in flow
        .member_reads
        .iter()
        .filter(|candidate| candidate.context == *context)
    {
        if !unreachable(read.read_start, read.read_end)
            && !static_member_read_is_getter_free(read, stable_prototypes)
        {
            barriers.push(Span::new(read.read_start, read.read_end));
        }
    }
    for write in flow
        .member_writes
        .iter()
        .filter(|candidate| candidate.context == *context)
    {
        if !unreachable(write.write_start, write.write_end)
            && !member_write_preserves_field(write, property, stable_prototypes, false)
        {
            barriers.push(Span::new(write.write_start, write.write_end));
        }
    }

    for member_call in flow
        .member_calls
        .iter()
        .filter(|candidate| candidate.context == *context)
    {
        if event_member_call.is_some_and(|target| target == member_call)
            || unreachable(member_call.call_start, member_call.call_end)
        {
            continue;
        }
        let mut targets = runtime_calls
            .iter()
            .filter(|target| target.candidate.call == *member_call);
        let Some(target) = targets.next() else {
            barriers.push(Span::new(member_call.call_start, member_call.call_end));
            continue;
        };
        if targets.next().is_some() {
            barriers.push(Span::new(member_call.call_start, member_call.call_end));
            continue;
        }
        let Some(summary) = proven_prototype_method_receiver_preservation_summary(
            source, program, semantic, target,
        ) else {
            barriers.push(Span::new(member_call.call_start, member_call.call_end));
            continue;
        };
        if summary
            .required_own_data_fields
            .iter()
            .all(|required| required == property)
        {
            *standard_function_call_semantics_required |=
                summary.standard_function_call_semantics_required;
            discharged_preserving_method_calls.push(member_call.clone());
        } else {
            barriers.push(Span::new(member_call.call_start, member_call.call_end));
        }
    }

    for direct in flow
        .direct_calls
        .iter()
        .filter(|candidate| candidate.caller == *context)
    {
        if event_direct_call.is_some_and(|target| target == direct)
            || unreachable(direct.call_start, direct.call_end)
        {
            continue;
        }
        if !direct_call_preserves_field(
            source,
            program,
            semantic.scoping(),
            flow,
            direct,
            property,
            stable_prototypes,
            false,
            &mut HashMap::new(),
            &mut HashSet::new(),
        ) {
            barriers.push(Span::new(direct.call_start, direct.call_end));
        } else {
            *standard_function_call_semantics_required |=
                direct.standard_function_call_semantics_required;
        }
    }

    barriers.sort_by_key(|barrier| (barrier.start, barrier.end));
    barriers.dedup();
    if barriers.is_empty() {
        return true;
    }
    prove_event_before_barriers(semantic, event, &barriers)
        || prove_function_if_ladder_event_before_barriers(
            source,
            program,
            context.function_start,
            context.function_end,
            event,
            &barriers,
        )
}

fn prove_own_data_field_at_runtime_method_call_with_facts(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    flow: &ProvenOriginFlow,
    stable_prototypes: &HashSet<(u32, u32)>,
    runtime_calls: &[ProvenPrototypeMethodCallTarget],
    initialization: &ProvenOwnDataFieldInitialization,
    target: &ProvenPrototypeMethodCallTarget,
) -> Option<ProvenOwnDataFieldAtRuntimeMethodCall> {
    let scoping = semantic.scoping();
    let call = &target.candidate.call;
    if initialization.allocation_start != call.allocation_start
        || initialization.allocation_end != call.allocation_end
        || initialization.constructor_start != call.constructor_start
        || initialization.constructor_end != call.constructor_end
    {
        return None;
    }
    let path = collect_unique_direct_call_path(flow, &initialization.context, &call.context)?;
    let mut discharged_preserving_method_calls = Vec::new();
    let mut standard_function_call_semantics_required = false;

    if path.is_empty() {
        if !prove_event_completion_before_event(
            semantic,
            Span::new(initialization.write_start, initialization.write_end),
            Span::new(call.call_start, call.call_end),
        ) || !root_context_segment_preserves_field(
            source,
            program,
            scoping,
            flow,
            &initialization.context,
            initialization.evaluation_order,
            call.evaluation_order,
            &initialization.property,
            stable_prototypes,
            false,
            &mut HashMap::new(),
            &mut HashSet::new(),
        ) {
            return None;
        }
    } else {
        let first = &path[0];
        if first.caller != initialization.context
            || initialization.evaluation_order >= first.evaluation_order
            || !prove_event_completion_before_event(
                semantic,
                Span::new(initialization.write_start, initialization.write_end),
                Span::new(first.call_start, first.call_end),
            )
            || !root_context_segment_preserves_field(
                source,
                program,
                scoping,
                flow,
                &initialization.context,
                initialization.evaluation_order,
                first.evaluation_order,
                &initialization.property,
                stable_prototypes,
                false,
                &mut HashMap::new(),
                &mut HashSet::new(),
            )
        {
            return None;
        }
        standard_function_call_semantics_required |=
            first.standard_function_call_semantics_required;

        for (index, entry) in path.iter().enumerate() {
            let context = &entry.callee;
            let (event, event_direct_call, event_member_call) =
                if let Some(next) = path.get(index + 1) {
                    if next.caller != *context {
                        return None;
                    }
                    (Span::new(next.call_start, next.call_end), Some(next), None)
                } else {
                    if call.context != *context {
                        return None;
                    }
                    (Span::new(call.call_start, call.call_end), None, Some(call))
                };
            if !context_field_prefix_before_event(
                source,
                program,
                semantic,
                flow,
                stable_prototypes,
                runtime_calls,
                context,
                entry,
                event,
                event_direct_call,
                event_member_call,
                &initialization.property,
                &mut discharged_preserving_method_calls,
                &mut standard_function_call_semantics_required,
            ) {
                return None;
            }
            if let Some(next) = path.get(index + 1) {
                standard_function_call_semantics_required |=
                    next.standard_function_call_semantics_required;
            }
        }
    }

    discharged_preserving_method_calls
        .sort_by_key(|call| (call.call_start, call.call_end, call.property.clone()));
    discharged_preserving_method_calls.dedup();
    Some(ProvenOwnDataFieldAtRuntimeMethodCall {
        initialization: initialization.clone(),
        call_target: target.clone(),
        direct_call_path: path,
        discharged_preserving_method_calls,
        standard_function_call_semantics_required,
    })
}

/// Prove one named ordinary own-data field live at one already runtime-proven
/// prototype method call.
///
/// This focused form requires exactly one matching initialization fact for the
/// concrete allocation and constructor. Ambiguous initialization histories fail
/// closed rather than selecting by source order.
#[must_use]
pub fn proven_own_data_field_at_runtime_method_call(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    target: &ProvenPrototypeMethodCallTarget,
    property: &str,
) -> Option<ProvenOwnDataFieldAtRuntimeMethodCall> {
    let scoping = semantic.scoping();
    let flow = structurally_proven_origin_flow(program, scoping);
    let mut initializations = structurally_proven_own_data_field_initializations(program, scoping)
        .into_iter()
        .filter(|initialization| {
            let call = &target.candidate.call;
            initialization.property == property
                && initialization.allocation_start == call.allocation_start
                && initialization.allocation_end == call.allocation_end
                && initialization.constructor_start == call.constructor_start
                && initialization.constructor_end == call.constructor_end
        });
    let initialization = initializations.next()?;
    if initializations.next().is_some() {
        return None;
    }
    let runtime_calls = structurally_proven_prototype_method_calls_at_runtime(program, semantic);
    if !runtime_calls.iter().any(|candidate| candidate == target) {
        return None;
    }
    let stable_prototypes = structurally_proven_stable_constructor_prototypes(program, scoping)
        .into_iter()
        .map(|prototype| (prototype.constructor_start, prototype.constructor_end))
        .collect::<HashSet<_>>();
    prove_own_data_field_at_runtime_method_call_with_facts(
        source,
        program,
        semantic,
        &flow,
        &stable_prototypes,
        &runtime_calls,
        &initialization,
        target,
    )
}

/// Prove ordinary own-data field liveness at runtime-proven prototype method
/// calls reachable through a unique exact-origin direct-call path.
///
/// Each call-path prefix is checked against all field-invalidating effects in
/// that exact origin context. Already-proven receiver-preserving prototype calls
/// may be crossed when all their own-data requirements are the field currently
/// being tracked. Ambiguous call paths, dynamic property effects and unresolved
/// barriers fail closed.
#[must_use]
pub fn structurally_proven_own_data_fields_at_runtime_method_calls(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
) -> Vec<ProvenOwnDataFieldAtRuntimeMethodCall> {
    let scoping = semantic.scoping();
    let flow = structurally_proven_origin_flow(program, scoping);
    let initializations = structurally_proven_own_data_field_initializations(program, scoping);
    let runtime_calls = structurally_proven_prototype_method_calls_at_runtime(program, semantic);
    let stable_prototypes = structurally_proven_stable_constructor_prototypes(program, scoping)
        .into_iter()
        .map(|prototype| (prototype.constructor_start, prototype.constructor_end))
        .collect::<HashSet<_>>();
    let mut proven = Vec::new();

    for initialization in &initializations {
        for target in &runtime_calls {
            if let Some(proof) = prove_own_data_field_at_runtime_method_call_with_facts(
                source,
                program,
                semantic,
                &flow,
                &stable_prototypes,
                &runtime_calls,
                initialization,
                target,
            ) {
                proven.push(proof);
            }
        }
    }
    proven.sort_by_key(|proof| {
        (
            proof.initialization.allocation_start,
            proof.initialization.property.clone(),
            proof.call_target.candidate.call.call_start,
        )
    });
    proven.dedup();
    proven
}

fn context_prefix_preserves_exact_property(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    flow: &ProvenOriginFlow,
    context: &ProvenOriginContext,
    before_order: u64,
    property: &str,
    stable_prototypes: &HashSet<(u32, u32)>,
    memo: &mut HashMap<PreservationKey, bool>,
    visiting: &mut HashSet<PreservationKey>,
) -> bool {
    if flow
        .exposures
        .iter()
        .any(|event| event.context == *context && event.evaluation_order < before_order)
        || flow
            .member_calls
            .iter()
            .any(|event| event.context == *context && event.evaluation_order < before_order)
        || flow.member_reads.iter().any(|event| {
            event.context == *context
                && event.evaluation_order < before_order
                && !static_member_read_is_getter_free(event, stable_prototypes)
        })
        || flow.member_writes.iter().any(|event| {
            event.context == *context
                && event.evaluation_order < before_order
                && !member_write_preserves_field(event, property, stable_prototypes, true)
        })
    {
        return false;
    }

    flow.direct_calls
        .iter()
        .filter(|nested| nested.caller == *context && nested.evaluation_order < before_order)
        .all(|nested| {
            direct_call_preserves_field(
                source,
                program,
                scoping,
                flow,
                nested,
                property,
                stable_prototypes,
                true,
                memo,
                visiting,
            )
        })
}

/// Prove direct calls reached from one concrete allocation while an inherited
/// string-valued prototype property still has its exact value.
///
/// This is a must-analysis over the exact-origin context graph: a merged helper
/// context is admitted only when every reachable incoming edge is itself proven
/// from a valid context and its caller prefix preserves the exact property
/// value. Cycles that cannot be established from already-proven predecessors
/// remain unproven.
#[must_use]
pub fn proven_prototype_string_at_direct_calls(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    string: &ProvenPrototypeStringAtAllocation,
) -> Vec<ProvenPrototypeStringAtDirectCall> {
    let scoping = semantic.scoping();
    let flow = structurally_proven_origin_flow(program, scoping);
    let stable_prototypes = structurally_proven_stable_constructor_prototypes(program, scoping)
        .into_iter()
        .map(|prototype| (prototype.constructor_start, prototype.constructor_end))
        .collect::<HashSet<_>>();
    let same_origin = |context: &ProvenOriginContext| {
        context.allocation_start == string.allocation_start
            && context.allocation_end == string.allocation_end
            && context.constructor_start == string.assignment.constructor_start
            && context.constructor_end == string.assignment.constructor_end
    };
    let roots = flow
        .direct_calls
        .iter()
        .flat_map(|call| [&call.caller, &call.callee])
        .filter(|context| {
            same_origin(context)
                && context.this_origin
                && context.function_start == string.assignment.constructor_start
                && context.function_end == string.assignment.constructor_end
        })
        .cloned()
        .collect::<HashSet<_>>();
    if roots.is_empty() {
        return Vec::new();
    }

    let calls = flow
        .direct_calls
        .iter()
        .filter(|call| same_origin(&call.caller) && same_origin(&call.callee))
        .cloned()
        .collect::<Vec<_>>();
    let mut reachable = roots.clone();
    loop {
        let mut changed = false;
        for call in &calls {
            if reachable.contains(&call.caller) && reachable.insert(call.callee.clone()) {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut valid = roots;
    let mut valid_edges = HashSet::<(u32, u32, ProvenOriginContext, ProvenOriginContext)>::new();
    let mut memo = HashMap::new();
    let mut visiting = HashSet::new();
    loop {
        let mut changed = false;
        for call in &calls {
            if !valid.contains(&call.caller) {
                continue;
            }
            let edge_key = (
                call.call_start,
                call.call_end,
                call.caller.clone(),
                call.callee.clone(),
            );
            if valid_edges.contains(&edge_key) {
                continue;
            }
            if context_prefix_preserves_exact_property(
                source,
                program,
                scoping,
                &flow,
                &call.caller,
                call.evaluation_order,
                &string.assignment.property,
                &stable_prototypes,
                &mut memo,
                &mut visiting,
            ) {
                valid_edges.insert(edge_key);
                changed = true;
            }
        }

        for context in &reachable {
            if valid.contains(context) {
                continue;
            }
            let incoming = calls
                .iter()
                .filter(|call| call.callee == *context && reachable.contains(&call.caller))
                .collect::<Vec<_>>();
            if incoming.is_empty() {
                continue;
            }
            if incoming.iter().all(|call| {
                valid.contains(&call.caller)
                    && valid_edges.contains(&(
                        call.call_start,
                        call.call_end,
                        call.caller.clone(),
                        call.callee.clone(),
                    ))
            }) {
                valid.insert(context.clone());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut proven = calls
        .into_iter()
        .filter(|call| {
            valid.contains(&call.caller)
                && valid_edges.contains(&(
                    call.call_start,
                    call.call_end,
                    call.caller.clone(),
                    call.callee.clone(),
                ))
        })
        .map(|call| ProvenPrototypeStringAtDirectCall {
            string: string.clone(),
            call,
        })
        .collect::<Vec<_>>();
    proven.sort_by_key(|proof| {
        (
            proof.call.call_start,
            proof.call.call_end,
            proof.call.caller.function_start,
            proof.call.caller.parameter_indices.clone(),
        )
    });
    proven.dedup();
    proven
}

#[must_use]
pub fn structurally_proven_member_receiver_origins(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenMemberReceiverOrigin> {
    structurally_proven_origin_flow(program, scoping).member_calls
}

#[must_use]
pub fn structurally_proven_member_read_origins(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenMemberReadOrigin> {
    structurally_proven_origin_flow(program, scoping).member_reads
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

/// Prove that one event in the callee of an exact-origin direct call cannot
/// execute for the call site's exact scalar facts. This composes the supported
/// structured switch, ordinary flattened-ladder, and protected try/catch
/// ladder theorems; unsupported control remains reachable/unknown.
#[must_use]
pub fn proven_origin_direct_call_event_unreachable(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    call: &ProvenOriginDirectCall,
    event: Span,
) -> bool {
    let bindings = call
        .exact_integer_arguments
        .iter()
        .enumerate()
        .filter_map(|(index, value)| value.map(|value| (index, value)))
        .collect::<BTreeMap<_, _>>();
    prove_function_if_ladder_event_unreachable_with_integer_parameters(
        source,
        program,
        scoping,
        call.callee.function_start,
        call.callee.function_end,
        event,
        &bindings,
    ) || prove_function_switch_event_unreachable_with_integer_parameters(
        program,
        scoping,
        call.callee.function_start,
        call.callee.function_end,
        event,
        &bindings,
    ) || prove_function_structured_branch_event_unreachable_with_integer_parameters(
        program,
        scoping,
        call.callee.function_start,
        call.callee.function_end,
        event,
        &bindings,
    ) || prove_function_protected_if_ladder_event_unreachable_with_call_arguments(
        source,
        program,
        scoping,
        call.callee.function_start,
        call.callee.function_end,
        event,
        call.argument_spans.len(),
        &bindings,
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenOwnDataFieldInitialization {
    pub context: ProvenOriginContext,
    pub property: String,
    pub write_start: u32,
    pub write_end: u32,
    pub evaluation_order: u64,
    pub allocation_start: u32,
    pub allocation_end: u32,
    pub constructor_start: u32,
    pub constructor_end: u32,
    /// The proof relies on ordinary ECMAScript object/prototype semantics.
    pub standard_prototype_semantics_required: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenOwnDataFieldAtMemberCall {
    pub initialization: ProvenOwnDataFieldInitialization,
    pub entry_call: ProvenOriginDirectCall,
    pub member_call: ProvenMemberReceiverOrigin,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenExactOwnDataFieldAtDirectCall {
    pub initialization: ProvenOwnDataFieldInitialization,
    /// First exact-origin direct call reached after the initialization in the
    /// same context.
    pub entry_call: ProvenOriginDirectCall,
    /// Nested direct call in `entry_call`'s callee at which the exact field
    /// value is still proven unchanged.
    pub direct_call: ProvenOriginDirectCall,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenOwnDataFieldAtRuntimeMethodCall {
    pub initialization: ProvenOwnDataFieldInitialization,
    pub call_target: ProvenPrototypeMethodCallTarget,
    pub direct_call_path: Vec<ProvenOriginDirectCall>,
    pub discharged_preserving_method_calls: Vec<ProvenMemberReceiverOrigin>,
    pub standard_function_call_semantics_required: bool,
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
pub struct ProvenPrototypeStringAssignment {
    pub constructor_start: u32,
    pub constructor_end: u32,
    pub property: String,
    pub value: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
    pub standard_prototype_semantics_required: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenPrototypeStringAtAllocation {
    pub assignment: ProvenPrototypeStringAssignment,
    pub allocation_start: u32,
    pub allocation_end: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenPrototypeStringAtDirectCall {
    pub string: ProvenPrototypeStringAtAllocation,
    pub call: ProvenOriginDirectCall,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenStableConstructorPrototype {
    pub constructor_start: u32,
    pub constructor_end: u32,
    /// The theorem depends on ordinary Function.prototype/Object.prototype
    /// behavior. Constructor/prototype escape, dynamic writes and prototype
    /// chain mutation invalidate this proof.
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
pub struct ProvenPrototypeMethodCallTarget {
    pub candidate: PrototypeMethodCallCandidate,
    /// This proof depends on ordinary ECMAScript prototype/property semantics.
    pub standard_prototype_semantics_required: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenPrototypeMethodReceiverPreservationSummary {
    pub call_target: ProvenPrototypeMethodCallTarget,
    /// Ordinary own-data receiver fields that must already exist at method entry.
    pub required_own_data_fields: Vec<String>,
    /// At least one exact direct edge used ordinary `Function.prototype.call` semantics.
    pub standard_function_call_semantics_required: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenReceiverPreservingPrototypeMethodCall {
    pub candidate: PrototypeMethodCallCandidate,
    pub own_data_reads: Vec<ProvenOwnDataFieldAtRuntimeMethodCall>,
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
    strings: HashMap<(FunctionKey, String), ProvenPrototypeStringAssignment>,
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
            strings: HashMap::new(),
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
        self.methods.remove(&(owner, property.clone()));
        self.strings.remove(&(owner, property));
    }

    fn invalidate_constructor(&mut self, owner: FunctionKey) {
        self.invalid_constructors.insert(owner);
        self.lookup_invalid_constructors.insert(owner);
        self.methods.retain(|(candidate, _), _| *candidate != owner);
        self.strings.retain(|(candidate, _), _| *candidate != owner);
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

    fn record_string(
        &mut self,
        owner: FunctionKey,
        property: String,
        value: String,
        assignment_start: u32,
        assignment_end: u32,
    ) {
        let key = (owner, property.clone());
        if self.invalid_constructors.contains(&owner) || self.conflicts.contains(&key) {
            return;
        }
        let assignment = ProvenPrototypeStringAssignment {
            constructor_start: owner.start,
            constructor_end: owner.end,
            property,
            value,
            assignment_start,
            assignment_end,
            standard_prototype_semantics_required: true,
        };
        if self.strings.insert(key.clone(), assignment).is_some() {
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
            if property == "__proto__" {
                // Under the theorem's ordinary Object.prototype semantics,
                // assigning this inherited accessor changes the prototype
                // chain rather than installing an ordinary own data property.
                self.invalidate_constructor(owner);
            } else {
                self.invalidate_property(owner, property);
            }
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
                            if property == "__proto__" {
                                self.invalidate_constructor(owner);
                            } else if let Some(functions) =
                                possible_regular_functions(&assignment.right)
                            {
                                self.record_method(
                                    owner,
                                    property,
                                    functions,
                                    assignment.span.start,
                                    assignment.span.end,
                                );
                            } else if let Expression::StringLiteral(value) =
                                last_sequence_expression(&assignment.right)
                            {
                                if let Some(value) = string_literal_value(value) {
                                    self.record_string(
                                        owner,
                                        property,
                                        value,
                                        assignment.span.start,
                                        assignment.span.end,
                                    );
                                } else {
                                    self.invalidate_property(owner, property);
                                }
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
                                if property == "__proto__" {
                                    self.invalidate_constructor(owner);
                                } else if let Some(functions) =
                                    possible_regular_functions(&assignment.right)
                                {
                                    self.record_method(
                                        owner,
                                        property,
                                        functions,
                                        assignment.span.start,
                                        assignment.span.end,
                                    );
                                } else if let Expression::StringLiteral(value) =
                                    last_sequence_expression(&assignment.right)
                                {
                                    if let Some(value) = string_literal_value(value) {
                                        self.record_string(
                                            owner,
                                            property,
                                            value,
                                            assignment.span.start,
                                            assignment.span.end,
                                        );
                                    } else {
                                        self.invalidate_property(owner, property);
                                    }
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
pub fn structurally_proven_prototype_string_assignments(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenPrototypeStringAssignment> {
    let mut functions = FunctionCollector::new();
    functions.visit_program(program);
    let property_keys = collect_property_key_bindings(program, scoping);
    let proof =
        collect_prototype_method_proof(program, scoping, &functions.by_symbol, &property_keys);
    let mut strings = proof.strings.into_values().collect::<Vec<_>>();
    strings.sort_by_key(|assignment| {
        (
            assignment.constructor_start,
            assignment.property.clone(),
            assignment.assignment_start,
        )
    });
    strings
}

#[must_use]
pub fn proven_prototype_string_at_allocation(
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    constructor_start: u32,
    constructor_end: u32,
    allocation: Span,
    property: &str,
) -> Option<ProvenPrototypeStringAtAllocation> {
    let mut assignments =
        structurally_proven_prototype_string_assignments(program, semantic.scoping())
            .into_iter()
            .filter(|assignment| {
                assignment.constructor_start == constructor_start
                    && assignment.constructor_end == constructor_end
                    && assignment.property == property
            });
    let assignment = assignments.next()?;
    if assignments.next().is_some()
        || !prove_event_completion_before_nested_event(
            semantic,
            Span::new(assignment.assignment_start, assignment.assignment_end),
            allocation,
        )
    {
        return None;
    }
    Some(ProvenPrototypeStringAtAllocation {
        assignment,
        allocation_start: allocation.start,
        allocation_end: allocation.end,
    })
}

#[must_use]
pub fn structurally_proven_stable_constructor_prototypes(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenStableConstructorPrototype> {
    let mut functions = FunctionCollector::new();
    functions.visit_program(program);
    let property_keys = collect_property_key_bindings(program, scoping);
    let proof =
        collect_prototype_method_proof(program, scoping, &functions.by_symbol, &property_keys);
    let invalid = proof.lookup_invalid_constructors;
    let mut constructors = functions
        .by_symbol
        .values()
        .copied()
        .collect::<HashSet<_>>()
        .into_iter()
        .filter(|constructor| !invalid.contains(constructor))
        .map(|constructor| ProvenStableConstructorPrototype {
            constructor_start: constructor.start,
            constructor_end: constructor.end,
            standard_prototype_semantics_required: true,
        })
        .collect::<Vec<_>>();
    constructors
        .sort_by_key(|constructor| (constructor.constructor_start, constructor.constructor_end));
    constructors
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
fn match_prototype_method_calls(
    program: &Program<'_>,
    scoping: &Scoping,
    calls: impl IntoIterator<Item = ProvenMemberReceiverOrigin>,
) -> Vec<PrototypeMethodCallCandidate> {
    type MethodKey = (u32, u32, String);

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

#[must_use]
pub fn structurally_matched_prototype_method_calls(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<PrototypeMethodCallCandidate> {
    match_prototype_method_calls(
        program,
        scoping,
        structurally_proven_member_receiver_origins(program, scoping),
    )
}

/// Match prototype method calls found in an independently seeded exact-origin
/// flow. This reuses the same constructor/property identity and ambiguity rules
/// as the global origin flow; the caller is responsible only for the seed proof.
#[must_use]
pub fn structurally_matched_prototype_method_calls_in_flow(
    program: &Program<'_>,
    scoping: &Scoping,
    flow: &ProvenOriginFlow,
) -> Vec<PrototypeMethodCallCandidate> {
    match_prototype_method_calls(program, scoping, flow.member_calls.iter().cloned())
}

fn prove_runtime_prototype_method_call_targets(
    semantic: &Semantic<'_>,
    candidates: impl IntoIterator<Item = PrototypeMethodCallCandidate>,
) -> Vec<ProvenPrototypeMethodCallTarget> {
    let mut proven = candidates
        .into_iter()
        .filter_map(|candidate| {
            prove_event_completion_before_nested_event(
                semantic,
                Span::new(
                    candidate.lookup_target.assignment_start,
                    candidate.lookup_target.assignment_end,
                ),
                Span::new(
                    candidate.call.allocation_start,
                    candidate.call.allocation_end,
                ),
            )
            .then_some(ProvenPrototypeMethodCallTarget {
                candidate,
                standard_prototype_semantics_required: true,
            })
        })
        .collect::<Vec<_>>();
    proven.sort_by_key(|proof| {
        (
            proof.candidate.call.call_start,
            proof.candidate.call.call_end,
            proof.candidate.call.property.clone(),
        )
    });
    proven.dedup();
    proven
}

/// Upgrade structural prototype-call matches to runtime lookup targets for a
/// concrete allocation.
///
/// The prototype assignment must have completed before that allocation could
/// execute. Stable-prototype evidence from the structural candidate then keeps
/// the installed target valid through the later member call. The ordering proof
/// supports same-function allocations and allocations inside later-created
/// function expressions/arrows; unsupported interprocedural timing fails closed.
#[must_use]
pub fn structurally_proven_prototype_method_calls_at_runtime(
    program: &Program<'_>,
    semantic: &Semantic<'_>,
) -> Vec<ProvenPrototypeMethodCallTarget> {
    prove_runtime_prototype_method_call_targets(
        semantic,
        structurally_matched_prototype_method_calls(program, semantic.scoping()),
    )
}

/// Upgrade prototype calls from an independently seeded exact-origin flow to
/// runtime lookup targets for the same concrete allocation.
#[must_use]
pub fn structurally_proven_prototype_method_calls_at_runtime_in_flow(
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    flow: &ProvenOriginFlow,
) -> Vec<ProvenPrototypeMethodCallTarget> {
    prove_runtime_prototype_method_call_targets(
        semantic,
        structurally_matched_prototype_method_calls_in_flow(program, semantic.scoping(), flow),
    )
}

/// Propagate exact receiver origin into every finite possible method body of a
/// structurally matched prototype call.
///
/// This does not upgrade the structural match into a call-time lookup theorem;
/// callers must separately prove that the matched lookup is valid at the call.
/// Given that premise, each possible regular method body receives the same
/// concrete allocation as `this`, and ordinary exact-origin propagation applies.
#[must_use]
pub fn propagate_matched_prototype_method_call_origins(
    program: &Program<'_>,
    scoping: &Scoping,
    candidate: &PrototypeMethodCallCandidate,
) -> ProvenOriginFlow {
    let seeds = candidate
        .lookup_target
        .possible_functions
        .iter()
        .map(|function| ProvenOriginContext {
            function_start: function.function_start,
            function_end: function.function_end,
            allocation_start: candidate.call.allocation_start,
            allocation_end: candidate.call.allocation_end,
            constructor_start: candidate.call.constructor_start,
            constructor_end: candidate.call.constructor_end,
            this_origin: true,
            parameter_indices: Vec::new(),
        })
        .collect::<Vec<_>>();
    propagate_proven_origin_contexts(program, scoping, &seeds)
}

/// Propagate exact receiver origin from a runtime-proven prototype method call.
#[must_use]
pub fn propagate_proven_prototype_method_call_origins(
    program: &Program<'_>,
    scoping: &Scoping,
    proof: &ProvenPrototypeMethodCallTarget,
) -> ProvenOriginFlow {
    propagate_matched_prototype_method_call_origins(program, scoping, &proof.candidate)
}

#[derive(Clone, Default)]
struct ReceiverPreservationRequirements {
    own_data_fields: HashSet<String>,
    standard_function_call_semantics_required: bool,
}

impl ReceiverPreservationRequirements {
    fn merge(&mut self, other: Self) {
        self.own_data_fields.extend(other.own_data_fields);
        self.standard_function_call_semantics_required |=
            other.standard_function_call_semantics_required;
    }
}

type MethodPreservationKey = (u32, u32, u32, u32, String);
type ContextPreservationKey = (ProvenOriginContext, Option<(u32, u32)>);

fn direct_call_event_unreachable_if_specialized(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    entry: Option<&ProvenOriginDirectCall>,
    start: u32,
    end: u32,
) -> bool {
    entry.is_some_and(|call| {
        proven_origin_direct_call_event_unreachable(
            source,
            program,
            scoping,
            call,
            Span::new(start, end),
        )
    })
}

fn summarize_receiver_context(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    flow: &ProvenOriginFlow,
    runtime_calls: &[ProvenPrototypeMethodCallTarget],
    context: &ProvenOriginContext,
    entry: Option<&ProvenOriginDirectCall>,
    method_memo: &mut HashMap<MethodPreservationKey, Option<ReceiverPreservationRequirements>>,
    method_visiting: &mut HashSet<MethodPreservationKey>,
    context_visiting: &mut HashSet<ContextPreservationKey>,
) -> Option<ReceiverPreservationRequirements> {
    let key = (
        context.clone(),
        entry.map(|call| (call.call_start, call.call_end)),
    );
    if !context_visiting.insert(key.clone()) {
        return None;
    }
    let scoping = semantic.scoping();
    let unreachable = |start, end| {
        direct_call_event_unreachable_if_specialized(source, program, scoping, entry, start, end)
    };
    let mut requirements = ReceiverPreservationRequirements::default();

    if flow.exposures.iter().any(|event| {
        event.context == *context && !unreachable(event.exposure_start, event.exposure_end)
    }) || flow
        .member_writes
        .iter()
        .any(|event| event.context == *context && !unreachable(event.write_start, event.write_end))
    {
        context_visiting.remove(&key);
        return None;
    }

    for read in flow
        .member_reads
        .iter()
        .filter(|event| event.context == *context)
    {
        if unreachable(read.read_start, read.read_end) {
            continue;
        }
        let property = read.property.as_ref()?;
        if property == "__proto__" {
            context_visiting.remove(&key);
            return None;
        }
        requirements.own_data_fields.insert(property.clone());
    }

    for member_call in flow
        .member_calls
        .iter()
        .filter(|event| event.context == *context)
    {
        if unreachable(member_call.call_start, member_call.call_end) {
            continue;
        }
        let mut matches = runtime_calls
            .iter()
            .filter(|proof| proof.candidate.call == *member_call);
        let nested = matches.next()?;
        if matches.next().is_some() {
            context_visiting.remove(&key);
            return None;
        }
        let nested_requirements = summarize_runtime_prototype_method_preservation(
            source,
            program,
            semantic,
            nested,
            method_memo,
            method_visiting,
        )?;
        requirements.merge(nested_requirements);
    }

    for direct in flow
        .direct_calls
        .iter()
        .filter(|call| call.caller == *context)
    {
        if unreachable(direct.call_start, direct.call_end) {
            continue;
        }
        requirements.standard_function_call_semantics_required |=
            direct.standard_function_call_semantics_required;
        let nested = summarize_receiver_context(
            source,
            program,
            semantic,
            flow,
            runtime_calls,
            &direct.callee,
            Some(direct),
            method_memo,
            method_visiting,
            context_visiting,
        )?;
        requirements.merge(nested);
    }

    context_visiting.remove(&key);
    Some(requirements)
}

fn summarize_runtime_prototype_method_preservation(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    target: &ProvenPrototypeMethodCallTarget,
    memo: &mut HashMap<MethodPreservationKey, Option<ReceiverPreservationRequirements>>,
    visiting: &mut HashSet<MethodPreservationKey>,
) -> Option<ReceiverPreservationRequirements> {
    let candidate = &target.candidate;
    let key = (
        candidate.call.call_start,
        candidate.call.call_end,
        candidate.call.allocation_start,
        candidate.call.allocation_end,
        candidate.call.property.clone(),
    );
    if let Some(cached) = memo.get(&key) {
        return cached.clone();
    }
    if !visiting.insert(key.clone()) {
        return None;
    }

    let flow = propagate_proven_prototype_method_call_origins(program, semantic.scoping(), target);
    let runtime_calls =
        structurally_proven_prototype_method_calls_at_runtime_in_flow(program, semantic, &flow);
    let mut requirements = ReceiverPreservationRequirements::default();
    let mut context_visiting = HashSet::new();
    let mut success = true;
    for function in &candidate.lookup_target.possible_functions {
        let context = ProvenOriginContext {
            function_start: function.function_start,
            function_end: function.function_end,
            allocation_start: candidate.call.allocation_start,
            allocation_end: candidate.call.allocation_end,
            constructor_start: candidate.call.constructor_start,
            constructor_end: candidate.call.constructor_end,
            this_origin: true,
            parameter_indices: Vec::new(),
        };
        let Some(summary) = summarize_receiver_context(
            source,
            program,
            semantic,
            &flow,
            &runtime_calls,
            &context,
            None,
            memo,
            visiting,
            &mut context_visiting,
        ) else {
            success = false;
            break;
        };
        requirements.merge(summary);
    }
    visiting.remove(&key);
    let result = success.then_some(requirements);
    memo.insert(key, result.clone());
    result
}

/// Summarize one already runtime-proven prototype method call.
///
/// The result is conditional on the listed ordinary own-data fields existing
/// at method entry. This focused form is useful to consumers that already hold
/// the exact call target and avoids recomputing summaries for unrelated calls.
#[must_use]
pub fn proven_prototype_method_receiver_preservation_summary(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    target: &ProvenPrototypeMethodCallTarget,
) -> Option<ProvenPrototypeMethodReceiverPreservationSummary> {
    let requirements = summarize_runtime_prototype_method_preservation(
        source,
        program,
        semantic,
        target,
        &mut HashMap::new(),
        &mut HashSet::new(),
    )?;
    let mut required_own_data_fields = requirements.own_data_fields.into_iter().collect::<Vec<_>>();
    required_own_data_fields.sort();
    Some(ProvenPrototypeMethodReceiverPreservationSummary {
        call_target: target.clone(),
        required_own_data_fields,
        standard_function_call_semantics_required: requirements
            .standard_function_call_semantics_required,
    })
}

/// Prove runtime-targeted prototype methods that preserve receiver identity and
/// member shape, conditional only on a finite set of ordinary own-data fields
/// already existing at method entry. Exact direct-call scalar facts discharge
/// unreachable effects; nested runtime-proven prototype calls are summarized
/// recursively. Cycles and unresolved receiver effects fail closed.
#[must_use]
pub fn structurally_proven_prototype_method_receiver_preservation_summaries(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
) -> Vec<ProvenPrototypeMethodReceiverPreservationSummary> {
    let mut memo = HashMap::new();
    let mut visiting = HashSet::new();
    let mut proven = Vec::new();
    for target in structurally_proven_prototype_method_calls_at_runtime(program, semantic) {
        let Some(requirements) = summarize_runtime_prototype_method_preservation(
            source,
            program,
            semantic,
            &target,
            &mut memo,
            &mut visiting,
        ) else {
            continue;
        };
        let mut required_own_data_fields =
            requirements.own_data_fields.into_iter().collect::<Vec<_>>();
        required_own_data_fields.sort();
        proven.push(ProvenPrototypeMethodReceiverPreservationSummary {
            call_target: target,
            required_own_data_fields,
            standard_function_call_semantics_required: requirements
                .standard_function_call_semantics_required,
        });
    }
    proven.sort_by_key(|proof| {
        (
            proof.call_target.candidate.call.call_start,
            proof.call_target.candidate.call.call_end,
            proof.call_target.candidate.call.property.clone(),
        )
    });
    proven.dedup();
    proven
}

/// Prove exact-origin prototype method calls that preserve receiver identity and
/// shape on every normal-return path represented by the supported effect model.
/// Static receiver reads must be discharged as ordinary own-data fields at the
/// exact call site; mutation, receiver exposure, dynamic access, or recursive
/// receiver-method calls remain barriers.
/// Prove one runtime-targeted prototype method call fully receiver-preserving,
/// including liveness of every ordinary own-data field required by its
/// transitive preservation summary.
#[must_use]
pub fn proven_receiver_preserving_prototype_method_call(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
    target: &ProvenPrototypeMethodCallTarget,
) -> Option<ProvenReceiverPreservingPrototypeMethodCall> {
    let summary =
        proven_prototype_method_receiver_preservation_summary(source, program, semantic, target)?;
    let mut reads = Vec::new();
    for property in &summary.required_own_data_fields {
        reads.push(proven_own_data_field_at_runtime_method_call(
            source, program, semantic, target, property,
        )?);
    }
    Some(ProvenReceiverPreservingPrototypeMethodCall {
        candidate: target.candidate.clone(),
        own_data_reads: reads,
    })
}

#[must_use]
pub fn structurally_proven_receiver_preserving_prototype_method_calls(
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
) -> Vec<ProvenReceiverPreservingPrototypeMethodCall> {
    let scoping = semantic.scoping();
    let flow = structurally_proven_origin_flow(program, scoping);
    let initializations = structurally_proven_own_data_field_initializations(program, scoping);
    let runtime_calls = structurally_proven_prototype_method_calls_at_runtime(program, semantic);
    let stable_prototypes = structurally_proven_stable_constructor_prototypes(program, scoping)
        .into_iter()
        .map(|prototype| (prototype.constructor_start, prototype.constructor_end))
        .collect::<HashSet<_>>();
    let mut proven = Vec::new();

    for summary in structurally_proven_prototype_method_receiver_preservation_summaries(
        source, program, semantic,
    ) {
        let target = summary.call_target;
        let call = &target.candidate.call;
        let mut reads = Vec::new();
        let mut all_reads_proven = true;
        for property in &summary.required_own_data_fields {
            let mut matching = initializations.iter().filter(|initialization| {
                initialization.property == *property
                    && initialization.allocation_start == call.allocation_start
                    && initialization.allocation_end == call.allocation_end
                    && initialization.constructor_start == call.constructor_start
                    && initialization.constructor_end == call.constructor_end
            });
            let Some(initialization) = matching.next() else {
                all_reads_proven = false;
                break;
            };
            if matching.next().is_some() {
                all_reads_proven = false;
                break;
            }
            let Some(field) = prove_own_data_field_at_runtime_method_call_with_facts(
                source,
                program,
                semantic,
                &flow,
                &stable_prototypes,
                &runtime_calls,
                initialization,
                &target,
            ) else {
                all_reads_proven = false;
                break;
            };
            reads.push(field);
        }
        if all_reads_proven {
            proven.push(ProvenReceiverPreservingPrototypeMethodCall {
                candidate: target.candidate,
                own_data_reads: reads,
            });
        }
    }
    proven.sort_by_key(|proof| {
        (
            proof.candidate.call.call_start,
            proof.candidate.call.call_end,
            proof.candidate.call.property.clone(),
        )
    });
    proven.dedup();
    proven
}

#[cfg(test)]
mod tests {
    use super::{
        propagate_proven_origin_contexts, proven_origin_direct_call_preserves_exact_property,
        proven_origin_direct_call_preserves_own_field, proven_prototype_string_at_allocation,
        proven_prototype_string_at_direct_calls, structurally_matched_prototype_method_calls,
        structurally_proven_member_receiver_origins, structurally_proven_member_write_origins,
        structurally_proven_origin_direct_calls, structurally_proven_origin_exposures,
        structurally_proven_origin_flow,
        structurally_proven_own_data_fields_at_runtime_method_calls,
        structurally_proven_prototype_method_assignments,
        structurally_proven_prototype_method_calls_at_runtime,
        structurally_proven_prototype_method_calls_at_runtime_in_flow,
        structurally_proven_prototype_method_lookup_targets,
        structurally_proven_prototype_method_receiver_effects,
        structurally_proven_prototype_method_receiver_preservation_summaries,
        structurally_proven_prototype_string_assignments,
    };
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::{SourceType, Span};
    use rolldown_redox::ecmascript::parse_program;
    use std::collections::HashSet;

    fn prototype_strings(source: &str) -> Vec<super::ProvenPrototypeStringAssignment> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        structurally_proven_prototype_string_assignments(
            &parsed.program,
            semantic.semantic.scoping(),
        )
    }

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
    fn proves_seeded_nested_method_call_runtime_target() {
        let source = r#"
            (function() {
                const C = function() { use(this); };
                function helper() { this.read(); }
                C.prototype.outer = function() { helper.call(this); };
                C.prototype.read = function() { return 1; };
                function use(state) { state.outer(); }
                api.make = function() { return new C(); };
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let outer = structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        )
        .into_iter()
        .find(|proof| proof.candidate.call.property == "outer")
        .expect("runtime outer call");
        let seeded = super::propagate_proven_prototype_method_call_origins(
            &parsed.program,
            semantic.semantic.scoping(),
            &outer,
        );
        let nested = structurally_proven_prototype_method_calls_at_runtime_in_flow(
            &parsed.program,
            &semantic.semantic,
            &seeded,
        );
        assert!(nested
            .iter()
            .any(|proof| proof.candidate.call.property == "read"));
    }

    #[test]
    fn proves_runtime_method_install_before_direct_allocation() {
        let source = r#"
            (function() {
                const C = function() { launch(this); };
                function launch(state) { state.run(); }
                C.prototype.run = function() { return 1; };
                new C();
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proven = structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        );
        assert!(proven
            .iter()
            .any(|proof| proof.candidate.call.property == "run"));
    }

    #[test]
    fn proves_runtime_method_install_before_nested_allocation_factory() {
        let source = r#"
            (function() {
                const C = function() { launch(this); };
                function launch(state) { state.run(); }
                C.prototype.run = function() { return 1; };
                api.make = function() { return new C(); };
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proven = structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        );
        assert!(proven
            .iter()
            .any(|proof| proof.candidate.call.property == "run"));
    }

    #[test]
    fn runtime_method_install_rejects_factory_created_before_assignment() {
        let source = r#"
            (function() {
                const C = function() { launch(this); };
                function launch(state) { state.run(); }
                api.make = function() { return new C(); };
                C.prototype.run = function() { return 1; };
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        )
        .iter()
        .all(|proof| proof.candidate.call.property != "run"));
    }

    #[test]
    fn runtime_method_install_rejects_function_declaration_factory() {
        let source = r#"
            (function() {
                const C = function() { launch(this); };
                function launch(state) { state.run(); }
                C.prototype.run = function() { return 1; };
                function make() { return new C(); }
                api.make = make;
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        )
        .iter()
        .all(|proof| proof.candidate.call.property != "run"));
    }

    #[test]
    fn proves_stable_prototype_string_assignment() {
        let strings = prototype_strings(
            r#"
                const C = function() {};
                const p = C.prototype;
                p.factory = "create";
                new C();
            "#,
        );
        assert_eq!(strings.len(), 1);
        assert_eq!(strings[0].property, "factory");
        assert_eq!(strings[0].value, "create");
    }

    #[test]
    fn proves_prototype_string_before_nested_allocation() {
        let source = r#"
            const C = function() {};
            C.prototype.factory = "create";
            const build = function() { return new C(); };
            use(build);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let assignment = prototype_strings(source).pop().expect("prototype string");
        let allocation_start = source.find("new C()").expect("allocation") as u32;
        let allocation_end = allocation_start + u32::try_from("new C()".len()).unwrap();
        let proof = proven_prototype_string_at_allocation(
            &parsed.program,
            &semantic.semantic,
            assignment.constructor_start,
            assignment.constructor_end,
            Span::new(allocation_start, allocation_end),
            "factory",
        )
        .expect("runtime prototype string");
        assert_eq!(proof.assignment.value, "create");
    }

    #[test]
    fn rejects_conflicting_prototype_string_assignment() {
        assert!(prototype_strings(
            r#"
                const C = function() {};
                C.prototype.factory = "create";
                C.prototype.factory = "other";
                new C();
            "#,
        )
        .is_empty());
    }

    #[test]
    fn propagates_matched_method_this_through_function_call() {
        let source = r#"
            const C = function() { use(this); };
            C.prototype.run = function() { bridge.call(this, 7); };
            function bridge(selector) { this.finish(); }
            function use(state) { state.run(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let candidate = structurally_matched_prototype_method_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .into_iter()
        .find(|candidate| candidate.call.property == "run")
        .unwrap();
        let flow = super::propagate_matched_prototype_method_call_origins(
            &parsed.program,
            semantic.semantic.scoping(),
            &candidate,
        );
        let edge = flow
            .direct_calls
            .iter()
            .find(|call| call.standard_function_call_semantics_required)
            .expect(".call edge from method body");
        assert!(edge.caller.this_origin);
        assert!(edge.callee.this_origin);
        assert_eq!(edge.exact_integer_arguments, vec![Some(7)]);
        assert!(flow
            .member_calls
            .iter()
            .any(|call| { call.context == edge.callee && call.property == "finish" }));
    }

    #[test]
    fn proves_own_field_across_unique_direct_path_and_preserving_method() {
        let source = r#"
            (function() {
                const C = function() {
                    this.value = 1;
                    first(this);
                };
                function first(state) {
                    state.read();
                    second(state);
                }
                function second(state) { state.target(); }
                C.prototype.read = function() { return this.value; };
                C.prototype.target = function() { return this.value; };
                api.make = function() { return new C(); };
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proofs = structurally_proven_own_data_fields_at_runtime_method_calls(
            source,
            &parsed.program,
            &semantic.semantic,
        );
        let proof = proofs
            .iter()
            .find(|proof| {
                proof.initialization.property == "value"
                    && proof.call_target.candidate.call.property == "target"
            })
            .expect("value live at target call");
        assert_eq!(proof.direct_call_path.len(), 2);
        assert!(proof
            .discharged_preserving_method_calls
            .iter()
            .any(|call| call.property == "read"));
    }

    #[test]
    fn own_field_runtime_call_rejects_ambiguous_direct_path() {
        let source = r#"
            (function() {
                const C = function(flag) {
                    this.value = 1;
                    if (flag) first(this); else alternate(this);
                };
                function first(state) { second(state); }
                function alternate(state) { second(state); }
                function second(state) { state.target(); }
                C.prototype.target = function() { return this.value; };
                api.make = function(flag) { return new C(flag); };
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(structurally_proven_own_data_fields_at_runtime_method_calls(
            source,
            &parsed.program,
            &semantic.semantic,
        )
        .iter()
        .all(|proof| {
            proof.initialization.property != "value"
                || proof.call_target.candidate.call.property != "target"
        }));
    }

    #[test]
    fn own_field_runtime_call_rejects_unresolved_receiver_barrier() {
        let source = r#"
            (function() {
                const C = function() {
                    this.value = 1;
                    first(this);
                };
                function first(state) {
                    state.unknown();
                    second(state);
                }
                function second(state) { state.target(); }
                C.prototype.target = function() { return this.value; };
                api.make = function() { return new C(); };
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(structurally_proven_own_data_fields_at_runtime_method_calls(
            source,
            &parsed.program,
            &semantic.semantic,
        )
        .iter()
        .all(|proof| {
            proof.initialization.property != "value"
                || proof.call_target.candidate.call.property != "target"
        }));
    }

    #[test]
    fn summarizes_transitive_receiver_preservation_requirements() {
        let source = r#"
            (function() {
                const C = function() { this.value = 1; use(this); };
                function helper(selector) {
                    let state = 5;
                    while (state != 27) {
                        if (state == 5) state = selector == 14 ? 32 : 92;
                        else if (state == 32) state = 61;
                        else if (state == 61) this.read(), state = 85;
                        else if (state == 85) return;
                        else if (state == 92) this.bad = 1, state = 27;
                    }
                }
                C.prototype.outer = function() { helper.call(this, 14); };
                C.prototype.read = function() { return this.value; };
                function use(state) { state.outer(); }
                api.make = function() { return new C(); };
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let summaries = structurally_proven_prototype_method_receiver_preservation_summaries(
            source,
            &parsed.program,
            &semantic.semantic,
        );
        let outer = summaries
            .iter()
            .find(|summary| summary.call_target.candidate.call.property == "outer")
            .expect("preserving outer summary");
        assert_eq!(outer.required_own_data_fields, vec!["value"]);
        assert!(outer.standard_function_call_semantics_required);
    }

    #[test]
    fn transitive_receiver_preservation_rejects_reachable_mutation() {
        let source = r#"
            (function() {
                const C = function() { use(this); };
                function helper(selector) {
                    let state = 5;
                    while (state != 27) {
                        if (state == 5) state = selector == 14 ? 32 : 92;
                        else if (state == 32) state = 85;
                        else if (state == 85) return;
                        else if (state == 92) this.bad = 1, state = 27;
                    }
                }
                C.prototype.outer = function() { helper.call(this, 15); };
                function use(state) { state.outer(); }
                api.make = function() { return new C(); };
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(
            structurally_proven_prototype_method_receiver_preservation_summaries(
                source,
                &parsed.program,
                &semantic.semantic,
            )
            .iter()
            .all(|summary| summary.call_target.candidate.call.property != "outer")
        );
    }

    #[test]
    fn transitive_receiver_preservation_rejects_method_cycle() {
        let source = r#"
            (function() {
                const C = function() { use(this); };
                C.prototype.loop = function() { this.loop(); };
                function use(state) { state.loop(); }
                api.make = function() { return new C(); };
            })();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(
            structurally_proven_prototype_method_receiver_preservation_summaries(
                source,
                &parsed.program,
                &semantic.semantic,
            )
            .iter()
            .all(|summary| summary.call_target.candidate.call.property != "loop")
        );
    }

    #[test]
    fn proves_receiver_preserving_method_when_own_data_reads_are_live() {
        let source = r#"
            const C = function() { this.value = 1; use(this); };
            C.prototype.read = function() { return this.value; };
            function use(state) { state.read(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let calls = super::structurally_proven_receiver_preserving_prototype_method_calls(
            source,
            &parsed.program,
            &semantic.semantic,
        );
        assert!(calls.iter().any(|call| {
            call.candidate.call.property == "read"
                && call
                    .own_data_reads
                    .iter()
                    .any(|field| field.initialization.property == "value")
        }));
    }

    #[test]
    fn receiver_preserving_method_rejects_receiver_mutation() {
        let source = r#"
            const C = function() { this.value = 1; use(this); };
            C.prototype.read = function() { this.value = 2; return this.value; };
            function use(state) { state.read(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        assert!(
            super::structurally_proven_receiver_preserving_prototype_method_calls(
                source,
                &parsed.program,
                &semantic.semantic,
            )
            .iter()
            .all(|call| call.candidate.call.property != "read")
        );
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
    fn inventories_exact_origin_reads_without_counting_write_or_delete_targets() {
        let source = r#"
            const C = function() { use(this, "run"); };
            function use(state, key) {
                const value = state.value;
                state.write = value;
                delete state.gone;
                state.counter++;
                state[key]();
            }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let read_properties = flow
            .member_reads
            .iter()
            .map(|read| read.property.as_deref())
            .collect::<Vec<_>>();
        assert!(read_properties.contains(&Some("value")));
        assert!(read_properties.contains(&Some("counter")));
        assert!(!read_properties.contains(&Some("write")));
        assert!(!read_properties.contains(&Some("gone")));
        assert_eq!(
            flow.member_writes
                .iter()
                .filter_map(|write| write.property.as_deref())
                .collect::<Vec<_>>(),
            vec!["write", "gone", "counter"]
        );
        assert!(flow.exposures.iter().any(|exposure| {
            exposure.kind == "unresolved_member_call"
                && &source[exposure.exposure_start as usize..exposure.exposure_end as usize]
                    == "state[key]()"
        }));
    }

    #[test]
    fn resolves_stable_empty_array_computed_read_key() {
        let source = r#"
            const KEY = [];
            const C = function() { use(this); };
            function use(state) { void state[KEY]; }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let reads = super::structurally_proven_member_read_origins(
            &parsed.program,
            semantic.semantic.scoping(),
        );
        assert!(reads
            .iter()
            .any(|read| read.property.as_deref() == Some("")));
    }

    #[test]
    fn proves_early_own_data_field_through_fresh_direct_parameter() {
        let source = r#"
            const C = function() { init(this); };
            function init(state) {
                state.other = 1;
                state.field = 2;
                later(state);
                state.after = 4;
            }
            function later(state) { state.done = 3; }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let fields = super::structurally_proven_own_data_field_initializations(
            &parsed.program,
            semantic.semantic.scoping(),
        );
        let names = fields
            .iter()
            .map(|field| field.property.as_str())
            .collect::<HashSet<_>>();
        assert!(names.contains("other"));
        assert!(names.contains("field"));
        assert!(names.contains("done"));
        assert!(!names.contains("after"));
    }

    #[test]
    fn proves_own_data_field_survives_known_call_prefix_to_member_call() {
        let source = r#"
            const C = function() { init(this); };
            function init(state) {
                state.field = 1;
                helper(state);
                use(state);
            }
            function helper(state) { state.other = 2; }
            function use(state) { state.read(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proofs = super::structurally_proven_own_data_fields_at_member_calls(
            source,
            &parsed.program,
            &semantic.semantic,
        );
        assert!(proofs.iter().any(|proof| {
            proof.initialization.property == "field" && proof.member_call.property == "read"
        }));
    }

    #[test]
    fn proves_exact_own_data_field_value_at_nested_direct_call() {
        let source = r#"
            const C = function() { init(this); };
            function init(state) {
                state.cell = {};
                install(state);
            }
            function install(state) {
                helper(state);
            }
            function helper(state) {}
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proofs = {
            let flow = super::structurally_proven_origin_flow(
                &parsed.program,
                semantic.semantic.scoping(),
            );
            let target = flow
                .direct_calls
                .iter()
                .find(|call| {
                    source
                        .get(call.call_start as usize..call.call_end as usize)
                        .is_some_and(|call| call == "helper(state)")
                })
                .expect("helper call must be in exact-origin flow");
            super::proven_exact_own_data_field_at_direct_call(
                source,
                &parsed.program,
                &semantic.semantic,
                "cell",
                target,
            )
        };
        assert!(proofs.iter().any(|proof| {
            proof.initialization.property == "cell"
                && source
                    .get(proof.direct_call.call_start as usize..proof.direct_call.call_end as usize)
                    .is_some_and(|call| call == "helper(state)")
        }));
    }

    #[test]
    fn exact_own_data_field_value_rejects_nested_prior_write() {
        let source = r#"
            const C = function() { init(this); };
            function init(state) {
                state.cell = {};
                install(state);
            }
            function install(state) {
                state.cell = {};
                helper(state);
            }
            function helper(state) {}
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proofs = {
            let flow = super::structurally_proven_origin_flow(
                &parsed.program,
                semantic.semantic.scoping(),
            );
            let target = flow
                .direct_calls
                .iter()
                .find(|call| {
                    source
                        .get(call.call_start as usize..call.call_end as usize)
                        .is_some_and(|call| call == "helper(state)")
                })
                .expect("helper call must be in exact-origin flow");
            super::proven_exact_own_data_field_at_direct_call(
                source,
                &parsed.program,
                &semantic.semantic,
                "cell",
                target,
            )
        };
        assert!(!proofs.iter().any(|proof| {
            proof.initialization.property == "cell"
                && source
                    .get(proof.direct_call.call_start as usize..proof.direct_call.call_end as usize)
                    .is_some_and(|call| call == "helper(state)")
        }));
    }

    #[test]
    fn own_data_field_survival_requires_initialization_to_dominate_entry_call() {
        let source = r#"
            const C = function(flag) { init(this, flag); };
            function init(state, flag) {
                if (flag) state.field = 1;
                use(state);
            }
            function use(state) { state.read(); }
            new C(false);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proofs = super::structurally_proven_own_data_fields_at_member_calls(
            source,
            &parsed.program,
            &semantic.semantic,
        );
        assert!(!proofs.iter().any(|proof| {
            proof.initialization.property == "field" && proof.member_call.property == "read"
        }));
    }

    #[test]
    fn own_data_field_survival_allows_static_getter_free_helper_read() {
        let source = r#"
            const C = function() { init(this); };
            function init(state) {
                state.field = 1;
                helper(state);
                use(state);
            }
            function helper(state) { void state.missing; }
            function use(state) { state.read(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proofs = super::structurally_proven_own_data_fields_at_member_calls(
            source,
            &parsed.program,
            &semantic.semantic,
        );
        assert!(proofs.iter().any(|proof| {
            proof.initialization.property == "field" && proof.member_call.property == "read"
        }));
    }

    #[test]
    fn own_data_field_survival_rejects_dynamic_helper_read() {
        let source = r#"
            const C = function(key) { init(this, key); };
            function init(state, key) {
                state.field = 1;
                helper(state, key);
                use(state);
            }
            function helper(state, key) { void state[key]; }
            function use(state) { state.read(); }
            new C(window.key);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proofs = super::structurally_proven_own_data_fields_at_member_calls(
            source,
            &parsed.program,
            &semantic.semantic,
        );
        assert!(!proofs.iter().any(|proof| {
            proof.initialization.property == "field" && proof.member_call.property == "read"
        }));
    }

    #[test]
    fn own_data_field_survival_rejects_nested_direct_call_exposure() {
        let source = r#"
            const C = function() { init(this); };
            function init(state) {
                state.field = 1;
                helper(state);
                use(state);
            }
            function helper(state) { unknown(state); }
            function use(state) { state.read(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let proofs = super::structurally_proven_own_data_fields_at_member_calls(
            source,
            &parsed.program,
            &semantic.semantic,
        );
        assert!(!proofs.iter().any(|proof| {
            proof.initialization.property == "field" && proof.member_call.property == "read"
        }));
    }

    #[test]
    fn own_data_field_proof_rejects_prior_external_exposure() {
        let source = r#"
            const C = function() { init(this); };
            function init(state) {
                unknown(state);
                state.field = 2;
            }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(super::structurally_proven_own_data_field_initializations(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .iter()
        .all(|field| field.property != "field"));
    }

    #[test]
    fn same_origin_self_store_is_not_an_exposure() {
        let source = r#"
            const C = function() { this.self = this; };
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(
            structurally_proven_origin_exposures(&parsed.program, semantic.semantic.scoping())
                .is_empty()
        );
        let writes =
            structurally_proven_member_write_origins(&parsed.program, semantic.semantic.scoping());
        assert_eq!(writes.len(), 1);
        assert_eq!(writes[0].property.as_deref(), Some("self"));
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
    fn propagates_exact_origin_through_function_prototype_call() {
        let source = r#"
            const C = function() { bridge.call(this, 7); };
            function bridge(selector) { this.finish(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let edge = flow
            .direct_calls
            .iter()
            .find(|call| call.standard_function_call_semantics_required)
            .expect("Function.prototype.call edge");
        assert!(edge.callee.this_origin);
        assert_eq!(edge.callee.parameter_indices, Vec::<usize>::new());
        assert_eq!(edge.exact_integer_arguments, vec![Some(7)]);
        assert!(flow
            .member_calls
            .iter()
            .any(|call| { call.context == edge.callee && call.property == "finish" }));
        assert!(flow.exposures.is_empty());
    }

    #[test]
    fn exact_origin_direct_call_rejects_arguments_object_aliasing() {
        let source = r#"
            const C = function() { helper(this); };
            function helper(state) { unknown(arguments[0]); state.done(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(structurally_proven_origin_direct_calls(
            &parsed.program,
            semantic.semantic.scoping(),
        )
        .is_empty());
    }

    #[test]
    fn direct_call_records_static_final_sequence_argument_value() {
        let source = r#"
            const C = function() { helper(this, (unknown(), 47), null, true); };
            function helper(state, selector, nullable, flag) { state.done(); }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let calls =
            structurally_proven_origin_direct_calls(&parsed.program, semantic.semantic.scoping());
        let call = calls
            .iter()
            .find(|call| call.exact_integer_arguments.len() == 4)
            .unwrap();
        assert_eq!(
            call.exact_integer_arguments,
            vec![None, Some(47), None, None]
        );
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
    fn propagates_exact_prototype_string_through_all_incoming_edges() {
        let source = r#"
            const C = function() { first(this); second(this); };
            C.prototype.factory = "create";
            function first(state) { shared(state); }
            function second(state) { shared(state); }
            function shared(state) { sink(state); }
            function sink(state) { state.other = 1; }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let assignment = prototype_strings(source).pop().expect("prototype string");
        let allocation_start = source.find("new C()").expect("allocation") as u32;
        let string = proven_prototype_string_at_allocation(
            &parsed.program,
            &semantic.semantic,
            assignment.constructor_start,
            assignment.constructor_end,
            Span::new(allocation_start, allocation_start + 7),
            "factory",
        )
        .expect("runtime string");
        let calls = proven_prototype_string_at_direct_calls(
            source,
            &parsed.program,
            &semantic.semantic,
            &string,
        );
        assert!(calls.iter().any(|proof| {
            source[proof.call.call_start as usize..proof.call.call_end as usize]
                .starts_with("sink(")
        }));
    }

    #[test]
    fn exact_prototype_string_join_rejects_one_mutating_incoming_path() {
        let source = r#"
            const C = function() { clean(this); dirty(this); };
            C.prototype.factory = "create";
            function clean(state) { shared(state); }
            function dirty(state) { state.factory = "changed"; shared(state); }
            function shared(state) { sink(state); }
            function sink(state) {}
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&parsed.program);
        let assignment = prototype_strings(source).pop().expect("prototype string");
        let allocation_start = source.find("new C()").expect("allocation") as u32;
        let string = proven_prototype_string_at_allocation(
            &parsed.program,
            &semantic.semantic,
            assignment.constructor_start,
            assignment.constructor_end,
            Span::new(allocation_start, allocation_start + 7),
            "factory",
        )
        .expect("runtime string");
        let calls = proven_prototype_string_at_direct_calls(
            source,
            &parsed.program,
            &semantic.semantic,
            &string,
        );
        assert!(!calls.iter().any(|proof| {
            source[proof.call.call_start as usize..proof.call.call_end as usize]
                .starts_with("sink(")
        }));
    }

    #[test]
    fn exact_property_preservation_allows_other_static_writes() {
        let source = r#"
            const C = function() { helper(this); };
            function helper(state) { state.other = 2; }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let call =
            structurally_proven_origin_direct_calls(&parsed.program, semantic.semantic.scoping())
                .into_iter()
                .next()
                .expect("direct origin call");
        assert!(proven_origin_direct_call_preserves_exact_property(
            source,
            &parsed.program,
            semantic.semantic.scoping(),
            &call,
            "token",
        ));
    }

    #[test]
    fn exact_property_preservation_rejects_same_property_assignment() {
        let source = r#"
            const C = function() { helper(this); };
            function helper(state) { state.token = "changed"; }
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let call =
            structurally_proven_origin_direct_calls(&parsed.program, semantic.semantic.scoping())
                .into_iter()
                .next()
                .expect("direct origin call");
        assert!(proven_origin_direct_call_preserves_own_field(
            source,
            &parsed.program,
            semantic.semantic.scoping(),
            &call,
            "token",
        ));
        assert!(!proven_origin_direct_call_preserves_exact_property(
            source,
            &parsed.program,
            semantic.semantic.scoping(),
            &call,
            "token",
        ));
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
    fn stable_constructor_prototype_rejects_proto_chain_mutation() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            C.prototype.__proto__ = {};
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let stable = super::structurally_proven_stable_constructor_prototypes(
            &parsed.program,
            semantic.semantic.scoping(),
        );
        assert!(stable.is_empty());
    }

    #[test]
    fn lookup_target_rejects_static_proto_chain_mutation() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            C.prototype.__proto__ = {};
        "#;
        assert!(lookup_targets(source).is_empty());
    }

    #[test]
    fn lookup_target_rejects_computed_proto_chain_mutation() {
        let source = r#"
            const C = function() {};
            C.prototype.run = function() {};
            C.prototype["__proto__"] = {};
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
    fn records_exact_origin_effects_in_evaluation_order() {
        let source = r#"
            const C = function() {
                this.n0 = (this.T = [], 1);
                unknown(this);
            };
            new C();
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        let flow = structurally_proven_origin_flow(&parsed.program, semantic.semantic.scoping());
        let t = flow
            .member_writes
            .iter()
            .find(|write| write.property.as_deref() == Some("T"))
            .unwrap();
        let n0 = flow
            .member_writes
            .iter()
            .find(|write| write.property.as_deref() == Some("n0"))
            .unwrap();
        let exposure = flow
            .exposures
            .iter()
            .find(|exposure| exposure.kind == "call_argument")
            .unwrap();
        assert!(t.evaluation_order < n0.evaluation_order);
        assert!(n0.evaluation_order < exposure.evaluation_order);
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
