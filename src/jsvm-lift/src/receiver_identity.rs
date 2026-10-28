use jsvm_safe_core::string_literal_value;
use oxc_ast::ast::{
    Argument, AssignmentTarget, BindingPattern, CallExpression, Expression, Function, FunctionBody,
    NewExpression, Program, Statement, VariableDeclaration,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenMemberWriteOrigin {
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
    member_writes: Vec<ProvenMemberWriteOrigin>,
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
            member_writes: Vec::new(),
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
        self.member_writes.push(ProvenMemberWriteOrigin {
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

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if self.active {
            if let Some((receiver, property)) = self.assignment_member(&assignment.left) {
                self.record_member_write(receiver, property, assignment.span, "assignment");
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

#[must_use]
pub fn structurally_proven_member_write_origins(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenMemberWriteOrigin> {
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
    let mut writes = Vec::new();
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
        writes.extend(probe.member_writes);
    }

    writes.sort_by_key(|write| (write.write_start, write.write_end, write.allocation_start));
    writes.dedup();
    writes
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

struct PrototypeMethodProof<'c, 'f> {
    scoping: &'c Scoping,
    constructors: &'f HashMap<SymbolId, FunctionKey>,
    aliases: HashMap<SymbolId, FunctionKey>,
    methods: HashMap<(FunctionKey, String), ProvenPrototypeMethodAssignment>,
    conflicts: HashSet<(FunctionKey, String)>,
    invalid_constructors: HashSet<FunctionKey>,
}

impl<'c, 'f> PrototypeMethodProof<'c, 'f> {
    fn new(scoping: &'c Scoping, constructors: &'f HashMap<SymbolId, FunctionKey>) -> Self {
        Self {
            scoping,
            constructors,
            aliases: HashMap::new(),
            methods: HashMap::new(),
            conflicts: HashSet::new(),
            invalid_constructors: HashSet::new(),
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

    fn invalidate_property(&mut self, owner: FunctionKey, property: String) {
        self.conflicts.insert((owner, property.clone()));
        self.methods.remove(&(owner, property));
    }

    fn invalidate_constructor(&mut self, owner: FunctionKey) {
        self.invalid_constructors.insert(owner);
        self.methods.retain(|(candidate, _), _| *candidate != owner);
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
                _ => self.aliases.clear(),
            }
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
                    if let AssignmentTarget::AssignmentTargetIdentifier(identifier) =
                        &assignment.left
                    {
                        if let Some(symbol) =
                            identifier.reference_id.get().and_then(|reference_id| {
                                self.scoping.get_reference(reference_id).symbol_id()
                            })
                        {
                            self.aliases.remove(&symbol);
                        }
                    }
                    self.aliases.clear();
                    return;
                }

                if let AssignmentTarget::AssignmentTargetIdentifier(identifier) = &assignment.left {
                    self.process_expression(&assignment.right);
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
                        let property = match last_sequence_expression(&member.expression) {
                            Expression::StringLiteral(property) => string_literal_value(property),
                            _ => None,
                        };
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
            Expression::UnaryExpression(unary) => self.process_expression(&unary.argument),
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
pub fn structurally_proven_prototype_method_assignments(
    program: &Program<'_>,
    scoping: &Scoping,
) -> Vec<ProvenPrototypeMethodAssignment> {
    let mut functions = FunctionCollector::new();
    functions.visit_program(program);
    let proof = PrototypeMethodProof::new(scoping, &functions.by_symbol);
    let mut collector = PrototypeMethodCollector { proof };
    collector.visit_program(program);
    let mut methods = collector.proof.methods.into_values().collect::<Vec<_>>();
    methods.sort_by_key(|method| {
        (
            method.constructor_start,
            method.property.clone(),
            method.assignment_start,
        )
    });
    methods
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

#[cfg(test)]
mod tests {
    use super::{
        structurally_proven_member_receiver_origins, structurally_proven_member_write_origins,
        structurally_proven_prototype_method_assignments,
        structurally_proven_prototype_method_receiver_effects,
    };
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

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
