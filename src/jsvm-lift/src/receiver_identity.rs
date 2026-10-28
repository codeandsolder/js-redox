use jsvm_safe_core::string_literal_value;
use oxc_ast::ast::{
    Argument, BindingPattern, CallExpression, Expression, Function, FunctionBody, NewExpression,
    Program, VariableDeclaration,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenMemberReceiverOrigin {
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
    discovered: Vec<FunctionContext>,
    member_calls: Vec<ProvenMemberReceiverOrigin>,
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
            discovered: Vec::new(),
            member_calls: Vec::new(),
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
                symbol_binding_is_stable(self.scoping, symbol)
                    .then(|| self.parameter_origins.get(&symbol).copied())
                    .flatten()
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
        self.discovered.push(FunctionContext {
            function: callee,
            this_origin: None,
            parameter_origins,
        });
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

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !self.active {
            walk::walk_call_expression(self, call);
            return;
        }
        if !call.optional {
            if let Some(callee) = self.direct_callee(&call.callee) {
                self.record_direct_call(call, callee);
            } else if let Some((receiver, property)) = self.static_member(&call.callee) {
                if let Some(origin) = self.expression_origin(receiver) {
                    self.member_calls.push(ProvenMemberReceiverOrigin {
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
        }
        walk::walk_call_expression(self, call);
    }
}

#[must_use]
pub fn structurally_proven_member_receiver_origins(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenMemberReceiverOrigin> {
    let mut functions = FunctionCollector::new();
    functions.visit_program(program);

    let mut allocations = AllocationCollector {
        scoping,
        functions: &functions.by_symbol,
        contexts: Vec::new(),
    };
    allocations.visit_program(program);

    let mut queue = VecDeque::from(allocations.contexts);
    let mut seen = HashSet::new();
    let mut calls = Vec::new();
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
        calls.extend(probe.member_calls);
    }

    calls.sort_by_key(|call| (call.call_start, call.call_end, call.allocation_start));
    calls.dedup();
    calls
}

#[cfg(test)]
mod tests {
    use super::structurally_proven_member_receiver_origins;
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

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
