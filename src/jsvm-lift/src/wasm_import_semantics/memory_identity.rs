use super::bulk_import::proof_primitive_expression;
use super::import_object::WasmInstantiationSite;
use super::{
    assignment_import_object, collect_global_aliases, global_constructor, parameter_symbols,
    symbol_binding_is_stable, symbol_of, unparenthesized,
};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, AssignmentTarget, BindingPattern, BlockStatement,
    CallExpression, Expression, Function, Program, Statement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmInstanceExportCall {
    pub export_name: String,
    pub call_start: u32,
    pub call_end: u32,
    pub argument_count: usize,
    /// Per argument, the exact element count when the value is proven to be a
    /// stable `Uint32Array` constructed from a fixed array literal.
    pub static_uint32_array_argument_lengths: Vec<Option<usize>>,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmModuleMemoryIdentityProof {
    pub import_module: String,
    pub import_name: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
    pub import_object: String,
    pub instance_binding: String,
    pub instance_identity_kind: &'static str,
    pub exports_binding: String,
    pub memory_export_name: String,
    pub initializer_function: String,
    pub initializer_parameter: usize,
    pub initializer_call_starts: Vec<u32>,
    pub initializer_exports_write_dominates_normal_exit: bool,
    /// Present only when proof-only normalization shows that the initializer's
    /// sole call through the exact exports binding is this zero-argument export.
    pub initializer_only_wasm_export_call: Option<String>,
    /// Proof-only normalized initializer has no non-start effects capable of
    /// mutating or observing linear memory through user-defined accessors.
    pub initializer_non_start_effects_memory_disjoint: bool,
    pub standard_js_numeric_builtin_semantics_required: bool,
    pub instantiation_site: WasmInstantiationSite,
    pub export_calls: Vec<WasmInstanceExportCall>,
    pub successful_memory_getter_execution_required: bool,
    pub standard_webassembly_builtin_semantics_required: bool,
}

#[derive(Debug, Clone)]
struct FunctionInfo {
    name: String,
    params: Vec<SymbolId>,
}

struct FunctionCollector<'c> {
    scoping: &'c Scoping,
    functions: HashMap<SymbolId, FunctionInfo>,
}

impl<'a> Visit<'a> for FunctionCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(identifier) = &function.id {
            if let Some(symbol) = identifier.symbol_id.get() {
                if symbol_binding_is_stable(self.scoping, symbol) {
                    if let Some(params) = parameter_symbols(function) {
                        self.functions.insert(
                            symbol,
                            FunctionInfo {
                                name: identifier.name.to_string(),
                                params,
                            },
                        );
                    }
                }
            }
        }
        walk::walk_function(self, function, flags);
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct ExportsWrite {
    helper: SymbolId,
    parameter: usize,
}

struct ExportsWriteCollector<'c, 'f> {
    scoping: &'c Scoping,
    functions: &'f HashMap<SymbolId, FunctionInfo>,
    function_stack: Vec<Option<SymbolId>>,
    writes: HashMap<SymbolId, Vec<Option<ExportsWrite>>>,
}

impl ExportsWriteCollector<'_, '_> {
    fn classify_exports_expression(&self, expression: &Expression<'_>) -> Option<ExportsWrite> {
        let helper = self.function_stack.last().copied().flatten()?;
        let info = self.functions.get(&helper)?;
        let object = member_object_named(expression, "exports")?;
        let parameter_symbol = symbol_of(self.scoping, object)?;
        let parameter = info
            .params
            .iter()
            .position(|symbol| *symbol == parameter_symbol)?;
        symbol_binding_is_stable(self.scoping, parameter_symbol)
            .then_some(ExportsWrite { helper, parameter })
    }
}

impl<'a> Visit<'a> for ExportsWriteCollector<'_, '_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        let symbol = function
            .id
            .as_ref()
            .and_then(|identifier| identifier.symbol_id.get());
        self.function_stack.push(symbol);
        walk::walk_function(self, function, flags);
        self.function_stack.pop();
    }

    fn visit_variable_declaration(&mut self, declaration: &oxc_ast::ast::VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            if declarator.init.is_some() {
                if let Some(symbol) = identifier.symbol_id.get() {
                    self.writes.entry(symbol).or_default().push(None);
                }
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if let AssignmentTarget::AssignmentTargetIdentifier(identifier) = &assignment.left {
            if let Some(symbol) = identifier
                .reference_id
                .get()
                .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
            {
                let write = (assignment.operator.as_str() == "=")
                    .then(|| self.classify_exports_expression(&assignment.right))
                    .flatten();
                self.writes.entry(symbol).or_default().push(write);
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }
}

fn member_object_named<'a>(
    expression: &'a Expression<'a>,
    expected: &str,
) -> Option<&'a Expression<'a>> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member)
            if !member.optional && member.property.name.as_str() == expected =>
        {
            Some(&member.object)
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            (property.value.as_str() == expected).then_some(&member.object)
        }
        _ => None,
    }
}

fn member_name_and_object<'a>(
    expression: &'a Expression<'a>,
) -> Option<(&'a str, &'a Expression<'a>)> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => {
            Some((member.property.name.as_str(), &member.object))
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            Some((property.value.as_str(), &member.object))
        }
        _ => None,
    }
}

fn single_memory_getter_binding(
    function: &Function<'_>,
    scoping: &Scoping,
) -> Option<(SymbolId, String)> {
    if function.r#async || function.generator || !function.params.items.is_empty() {
        return None;
    }
    let body = function.body.as_ref()?;
    let [Statement::ReturnStatement(statement)] = body.statements.as_slice() else {
        return None;
    };
    let object = member_object_named(statement.argument.as_ref()?, "memory")?;
    let symbol = symbol_of(scoping, object)?;
    Some((symbol, scoping.symbol_name(symbol).to_string()))
}

#[derive(Debug, Clone)]
struct MemoryGetterCandidate {
    import_module: String,
    import_name: String,
    assignment_start: u32,
    assignment_end: u32,
    import_object: String,
    exports_symbol: SymbolId,
    exports_binding: String,
}

struct MemoryGetterCollector<'c> {
    scoping: &'c Scoping,
    candidates: Vec<MemoryGetterCandidate>,
}

impl<'a> Visit<'a> for MemoryGetterCollector<'_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment.operator.as_str() == "=" {
            if let Expression::FunctionExpression(function) = unparenthesized(&assignment.right) {
                if let Some((symbol, import_object, import_module, import_name)) =
                    assignment_import_object(self.scoping, &assignment.left)
                {
                    if symbol_binding_is_stable(self.scoping, symbol) {
                        if let Some((exports_symbol, exports_binding)) =
                            single_memory_getter_binding(function, self.scoping)
                        {
                            self.candidates.push(MemoryGetterCandidate {
                                import_module,
                                import_name,
                                assignment_start: assignment.span.start,
                                assignment_end: assignment.span.end,
                                import_object,
                                exports_symbol,
                                exports_binding,
                            });
                        }
                    }
                }
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
enum InstanceKey {
    Binding(SymbolId),
    PromiseResult(SymbolId),
}

fn instance_key(scoping: &Scoping, expression: &Expression<'_>) -> Option<InstanceKey> {
    let expression = unparenthesized(expression);
    if let Some(symbol) = symbol_of(scoping, expression) {
        return symbol_binding_is_stable(scoping, symbol).then_some(InstanceKey::Binding(symbol));
    }
    let owner = member_object_named(expression, "instance")?;
    let symbol = symbol_of(scoping, owner)?;
    symbol_binding_is_stable(scoping, symbol).then_some(InstanceKey::PromiseResult(symbol))
}

fn instance_display(scoping: &Scoping, key: InstanceKey) -> String {
    match key {
        InstanceKey::Binding(symbol) => scoping.symbol_name(symbol).to_string(),
        InstanceKey::PromiseResult(symbol) => format!("{}.instance", scoping.symbol_name(symbol)),
    }
}

fn instance_kind(key: InstanceKey) -> &'static str {
    match key {
        InstanceKey::Binding(_) => "stable_instance_binding",
        InstanceKey::PromiseResult(_) => "instantiate_promise_result",
    }
}

#[derive(Debug, Clone)]
struct ExactInstancePath {
    key: InstanceKey,
    site_start: u32,
    site_end: u32,
}

struct InstanceBindingCollector<'c> {
    scoping: &'c Scoping,
    paths: Vec<ExactInstancePath>,
}

impl<'a> Visit<'a> for InstanceBindingCollector<'_> {
    fn visit_variable_declaration(&mut self, declaration: &oxc_ast::ast::VariableDeclaration<'a>) {
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
            let Some(Expression::NewExpression(expression)) = declarator
                .init
                .as_ref()
                .map(|expression| unparenthesized(expression))
            else {
                continue;
            };
            self.paths.push(ExactInstancePath {
                key: InstanceKey::Binding(symbol),
                site_start: expression.span.start,
                site_end: expression.span.end,
            });
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

struct PromiseInstanceCollector<'c> {
    scoping: &'c Scoping,
    paths: Vec<ExactInstancePath>,
}

impl<'a> Visit<'a> for PromiseInstanceCollector<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Some(("then", promise)) = member_name_and_object(&call.callee) {
                if let Expression::CallExpression(instantiation) = unparenthesized(promise) {
                    if !instantiation.optional
                        && !instantiation.arguments.iter().any(Argument::is_spread)
                    {
                        if let Some(callback) =
                            call.arguments.first().and_then(Argument::as_expression)
                        {
                            if let Expression::FunctionExpression(function) =
                                unparenthesized(callback)
                            {
                                if let Some(parameter) = function.params.items.first() {
                                    if let BindingPattern::BindingIdentifier(identifier) =
                                        &parameter.pattern
                                    {
                                        if let Some(symbol) = identifier.symbol_id.get() {
                                            if symbol_binding_is_stable(self.scoping, symbol) {
                                                self.paths.push(ExactInstancePath {
                                                    key: InstanceKey::PromiseResult(symbol),
                                                    site_start: instantiation.span.start,
                                                    site_end: instantiation.span.end,
                                                });
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

#[derive(Debug, Clone, Copy)]
struct HelperCall {
    start: u32,
    key: InstanceKey,
}

fn direct_helper_call(
    scoping: &Scoping,
    helper: SymbolId,
    parameter: usize,
    expression: &Expression<'_>,
) -> Option<HelperCall> {
    let Expression::CallExpression(call) = unparenthesized(expression) else {
        return None;
    };
    if call.optional
        || call.arguments.iter().any(Argument::is_spread)
        || symbol_of(scoping, &call.callee) != Some(helper)
    {
        return None;
    }
    let key = call
        .arguments
        .get(parameter)
        .and_then(Argument::as_expression)
        .and_then(|expression| instance_key(scoping, expression))?;
    Some(HelperCall {
        start: call.span.start,
        key,
    })
}

struct HelperReferenceCollector<'c> {
    scoping: &'c Scoping,
    helper: SymbolId,
    parameter: usize,
    calls: Vec<Option<HelperCall>>,
}

impl<'a> Visit<'a> for HelperReferenceCollector<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if symbol_of(self.scoping, &call.callee) == Some(self.helper) {
            let call = if call.optional || call.arguments.iter().any(Argument::is_spread) {
                None
            } else {
                call.arguments
                    .get(self.parameter)
                    .and_then(Argument::as_expression)
                    .and_then(|expression| instance_key(self.scoping, expression))
                    .map(|key| HelperCall {
                        start: call.span.start,
                        key,
                    })
            };
            self.calls.push(call);
        }
        walk::walk_call_expression(self, call);
    }
}

struct PromiseModuleReferenceCollector<'c> {
    scoping: &'c Scoping,
    symbol: SymbolId,
    count: usize,
}

impl<'a> Visit<'a> for PromiseModuleReferenceCollector<'_> {
    fn visit_static_member_expression(
        &mut self,
        member: &oxc_ast::ast::StaticMemberExpression<'a>,
    ) {
        if !member.optional
            && member.property.name.as_str() == "module"
            && symbol_of(self.scoping, &member.object) == Some(self.symbol)
        {
            self.count += 1;
        }
        walk::walk_static_member_expression(self, member);
    }

    fn visit_computed_member_expression(
        &mut self,
        member: &oxc_ast::ast::ComputedMemberExpression<'a>,
    ) {
        if !member.optional {
            if let Expression::StringLiteral(property) = unparenthesized(&member.expression) {
                if property.value.as_str() == "module"
                    && symbol_of(self.scoping, &member.object) == Some(self.symbol)
                {
                    self.count += 1;
                }
            }
        }
        walk::walk_computed_member_expression(self, member);
    }
}

struct StatementHelperCallCollector<'c> {
    scoping: &'c Scoping,
    helper: SymbolId,
    count: usize,
}

impl<'a> Visit<'a> for StatementHelperCallCollector<'_> {
    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if symbol_of(self.scoping, &call.callee) == Some(self.helper) {
            self.count += 1;
        }
        walk::walk_call_expression(self, call);
    }
}

#[derive(Debug, Clone)]
struct RegionExportCall {
    statement_index: usize,
    key: InstanceKey,
    call: WasmInstanceExportCall,
}

fn fixed_array_literal_length(expression: &Expression<'_>) -> Option<usize> {
    let Expression::ArrayExpression(array) = unparenthesized(expression) else {
        return None;
    };
    (!array
        .elements
        .iter()
        .any(|element| matches!(element, ArrayExpressionElement::SpreadElement(_))))
    .then_some(array.elements.len())
}

fn direct_uint32_array_length(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    expression: &Expression<'_>,
) -> Option<usize> {
    let Expression::NewExpression(new_expression) = unparenthesized(expression) else {
        return None;
    };
    global_constructor(
        scoping,
        global_aliases,
        &new_expression.callee,
        "Uint32Array",
    )?;
    let [argument] = new_expression.arguments.as_slice() else {
        return None;
    };
    fixed_array_literal_length(argument.as_expression()?)
}

struct StableUint32ArrayLengthCollector<'c, 'g> {
    scoping: &'c Scoping,
    global_aliases: &'g HashMap<SymbolId, String>,
    lengths: HashMap<SymbolId, usize>,
}

impl<'a> Visit<'a> for StableUint32ArrayLengthCollector<'_, '_> {
    fn visit_variable_declaration(&mut self, declaration: &oxc_ast::ast::VariableDeclaration<'a>) {
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
            let Some(initializer) = declarator.init.as_ref() else {
                continue;
            };
            if let Some(length) =
                direct_uint32_array_length(self.scoping, self.global_aliases, initializer)
            {
                self.lengths.insert(symbol, length);
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

fn static_uint32_array_length(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    known_lengths: &HashMap<SymbolId, usize>,
    expression: &Expression<'_>,
) -> Option<usize> {
    direct_uint32_array_length(scoping, global_aliases, expression).or_else(|| {
        let symbol = symbol_of(scoping, expression)?;
        // A stable binding fixes object identity, but its ArrayBuffer could still
        // be detached if the object escaped before this call. Restrict the
        // length proof to a fresh local whose only resolved use is this export
        // argument; later/earlier aliases then fail closed rather than assuming
        // an undetached buffer.
        (scoping.get_resolved_reference_ids(symbol).len() == 1)
            .then(|| known_lengths.get(&symbol).copied())
            .flatten()
    })
}

struct ExportCallCollector<'c, 'g, 'l> {
    scoping: &'c Scoping,
    global_aliases: &'g HashMap<SymbolId, String>,
    uint32_array_lengths: &'l HashMap<SymbolId, usize>,
    calls: Vec<(InstanceKey, WasmInstanceExportCall)>,
}

impl<'a> Visit<'a> for ExportCallCollector<'_, '_, '_> {
    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional && !call.arguments.iter().any(Argument::is_spread) {
            if let Some((export_name, exports_expression)) = member_name_and_object(&call.callee) {
                if let Some(instance_expression) =
                    member_object_named(exports_expression, "exports")
                {
                    if let Some(key) = instance_key(self.scoping, instance_expression) {
                        self.calls.push((
                            key,
                            WasmInstanceExportCall {
                                export_name: export_name.to_string(),
                                call_start: call.span.start,
                                call_end: call.span.end,
                                argument_count: call.arguments.len(),
                                static_uint32_array_argument_lengths: call
                                    .arguments
                                    .iter()
                                    .map(|argument| {
                                        argument.as_expression().and_then(|expression| {
                                            static_uint32_array_length(
                                                self.scoping,
                                                self.global_aliases,
                                                self.uint32_array_lengths,
                                                expression,
                                            )
                                        })
                                    })
                                    .collect(),
                            },
                        ));
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

fn catch_always_exits(statement: &oxc_ast::ast::TryStatement<'_>) -> bool {
    let Some(handler) = &statement.handler else {
        return false;
    };
    matches!(
        handler.body.body.last(),
        Some(Statement::ReturnStatement(_) | Statement::ThrowStatement(_))
    )
}

fn guaranteed_helper_call(
    statement: &Statement<'_>,
    scoping: &Scoping,
    helper: SymbolId,
    parameter: usize,
) -> Option<HelperCall> {
    match statement {
        Statement::ExpressionStatement(statement) => {
            direct_helper_call(scoping, helper, parameter, &statement.expression)
        }
        Statement::TryStatement(statement)
            if statement.finalizer.is_none() && catch_always_exits(statement) =>
        {
            let [Statement::ExpressionStatement(expression)] = statement.block.body.as_slice()
            else {
                return None;
            };
            direct_helper_call(scoping, helper, parameter, &expression.expression)
        }
        _ => None,
    }
}

#[derive(Debug, Clone)]
struct RegionInitializer {
    statement_index: usize,
    call: HelperCall,
}

#[derive(Debug, Clone, Default)]
struct RegionFacts {
    helper_call_indices: Vec<usize>,
    initializers: Vec<RegionInitializer>,
    exports: Vec<RegionExportCall>,
}

fn analyze_region(
    statements: &[Statement<'_>],
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    uint32_array_lengths: &HashMap<SymbolId, usize>,
    helper: SymbolId,
    parameter: usize,
) -> RegionFacts {
    let mut facts = RegionFacts::default();
    for (index, statement) in statements.iter().enumerate() {
        let mut helper_calls = StatementHelperCallCollector {
            scoping,
            helper,
            count: 0,
        };
        helper_calls.visit_statement(statement);
        if helper_calls.count > 0 {
            facts.helper_call_indices.push(index);
        }
        if let Some(call) = guaranteed_helper_call(statement, scoping, helper, parameter) {
            facts.initializers.push(RegionInitializer {
                statement_index: index,
                call,
            });
        }
        let mut exports = ExportCallCollector {
            scoping,
            global_aliases,
            uint32_array_lengths,
            calls: Vec::new(),
        };
        exports.visit_statement(statement);
        facts.exports.extend(
            exports
                .calls
                .into_iter()
                .map(|(key, call)| RegionExportCall {
                    statement_index: index,
                    key,
                    call,
                }),
        );
    }
    facts
}

struct RegionCollector<'c, 'g, 'l> {
    scoping: &'c Scoping,
    global_aliases: &'g HashMap<SymbolId, String>,
    uint32_array_lengths: &'l HashMap<SymbolId, usize>,
    helper: SymbolId,
    parameter: usize,
    regions: Vec<RegionFacts>,
}

impl RegionCollector<'_, '_, '_> {
    fn record(&mut self, statements: &[Statement<'_>]) {
        let facts = analyze_region(
            statements,
            self.scoping,
            self.global_aliases,
            self.uint32_array_lengths,
            self.helper,
            self.parameter,
        );
        if !facts.initializers.is_empty() || !facts.exports.is_empty() {
            self.regions.push(facts);
        }
    }
}

impl<'a> Visit<'a> for RegionCollector<'_, '_, '_> {
    fn visit_program(&mut self, program: &Program<'a>) {
        self.record(&program.body);
        walk::walk_program(self, program);
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some(body) = &function.body {
            self.record(&body.statements);
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_block_statement(&mut self, block: &BlockStatement<'a>) {
        self.record(&block.body);
        walk::walk_block_statement(self, block);
    }
}

fn exact_instance_references_are_closed(
    program: &Program<'_>,
    scoping: &Scoping,
    key: InstanceKey,
    helper_calls: &[HelperCall],
    export_calls: &HashSet<(InstanceKey, u32, u32)>,
) -> bool {
    let recognized_instance_references = helper_calls.iter().filter(|call| call.key == key).count()
        + export_calls
            .iter()
            .filter(|(export_key, _, _)| *export_key == key)
            .count();
    match key {
        InstanceKey::Binding(symbol) => {
            scoping.get_resolved_reference_ids(symbol).len() == recognized_instance_references
        }
        InstanceKey::PromiseResult(symbol) => {
            let mut module_references = PromiseModuleReferenceCollector {
                scoping,
                symbol,
                count: 0,
            };
            module_references.visit_program(program);
            scoping.get_resolved_reference_ids(symbol).len()
                == recognized_instance_references + module_references.count
        }
    }
}

fn exact_write_relation(
    scoping: &Scoping,
    writes: &HashMap<SymbolId, Vec<Option<ExportsWrite>>>,
    exports_symbol: SymbolId,
) -> Option<ExportsWrite> {
    let entries = writes.get(&exports_symbol)?;
    let [Some(write)] = entries.as_slice() else {
        return None;
    };
    let semantic_write_count = scoping
        .get_resolved_reference_ids(exports_symbol)
        .iter()
        .filter(|reference_id| scoping.get_reference(**reference_id).is_write())
        .count();
    (semantic_write_count == 1).then_some(*write)
}

#[derive(Clone, Copy, Default)]
struct ExitFlow {
    normal_unassigned: bool,
    normal_assigned: bool,
    good_return: bool,
    bad_return: bool,
}

impl ExitFlow {
    fn normal(assigned: bool) -> Self {
        Self {
            normal_unassigned: !assigned,
            normal_assigned: assigned,
            good_return: false,
            bad_return: false,
        }
    }

    fn merge(&mut self, other: Self) {
        self.normal_unassigned |= other.normal_unassigned;
        self.normal_assigned |= other.normal_assigned;
        self.good_return |= other.good_return;
        self.bad_return |= other.bad_return;
    }
}

fn span_contains(outer: Span, inner: Span) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

fn expression_has_unconditional_write(expression: &Expression<'_>, write_span: Span) -> bool {
    if !span_contains(expression.span(), write_span) {
        return false;
    }
    match unparenthesized(expression) {
        Expression::AssignmentExpression(assignment) => assignment.span == write_span,
        Expression::SequenceExpression(sequence) => sequence
            .expressions
            .iter()
            .any(|expression| expression_has_unconditional_write(expression, write_span)),
        _ => false,
    }
}

fn statement_flow(statement: &Statement<'_>, assigned: bool, write_span: Span) -> Option<ExitFlow> {
    match statement {
        Statement::BlockStatement(block) => statements_flow(&block.body, assigned, write_span),
        Statement::ExpressionStatement(expression) => {
            let contains = span_contains(expression.expression.span(), write_span);
            if contains && !expression_has_unconditional_write(&expression.expression, write_span) {
                return None;
            }
            Some(ExitFlow::normal(assigned || contains))
        }
        Statement::VariableDeclaration(declaration) => {
            let mut contains = false;
            for declarator in &declaration.declarations {
                let Some(initializer) = &declarator.init else {
                    continue;
                };
                if span_contains(initializer.span(), write_span) {
                    if contains || !expression_has_unconditional_write(initializer, write_span) {
                        return None;
                    }
                    contains = true;
                }
            }
            Some(ExitFlow::normal(assigned || contains))
        }
        Statement::IfStatement(statement) => {
            if span_contains(statement.test.span(), write_span) {
                return None;
            }
            let mut flow = statement_flow(&statement.consequent, assigned, write_span)?;
            if let Some(alternate) = &statement.alternate {
                flow.merge(statement_flow(alternate, assigned, write_span)?);
            } else {
                flow.merge(ExitFlow::normal(assigned));
            }
            Some(flow)
        }
        Statement::ReturnStatement(statement) => {
            let contains = statement
                .argument
                .as_ref()
                .is_some_and(|argument| span_contains(argument.span(), write_span));
            if contains
                && !statement.argument.as_ref().is_some_and(|argument| {
                    expression_has_unconditional_write(argument, write_span)
                })
            {
                return None;
            }
            let assigned = assigned || contains;
            Some(ExitFlow {
                good_return: assigned,
                bad_return: !assigned,
                ..ExitFlow::default()
            })
        }
        Statement::ThrowStatement(_) => Some(ExitFlow::default()),
        Statement::EmptyStatement(_)
        | Statement::DebuggerStatement(_)
        | Statement::FunctionDeclaration(_)
        | Statement::ClassDeclaration(_) => {
            (!span_contains(statement.span(), write_span)).then_some(ExitFlow::normal(assigned))
        }
        Statement::BreakStatement(_)
        | Statement::ContinueStatement(_)
        | Statement::DoWhileStatement(_)
        | Statement::ForInStatement(_)
        | Statement::ForOfStatement(_)
        | Statement::ForStatement(_)
        | Statement::LabeledStatement(_)
        | Statement::SwitchStatement(_)
        | Statement::TryStatement(_)
        | Statement::WhileStatement(_)
        | Statement::WithStatement(_) => None,
        _ => (!span_contains(statement.span(), write_span)).then_some(ExitFlow::normal(assigned)),
    }
}

fn statements_flow(
    statements: &[Statement<'_>],
    assigned: bool,
    write_span: Span,
) -> Option<ExitFlow> {
    let mut normal_unassigned = !assigned;
    let mut normal_assigned = assigned;
    let mut completed = ExitFlow::default();
    for statement in statements {
        let mut next_unassigned = false;
        let mut next_assigned = false;
        if normal_unassigned {
            let flow = statement_flow(statement, false, write_span)?;
            next_unassigned |= flow.normal_unassigned;
            next_assigned |= flow.normal_assigned;
            completed.good_return |= flow.good_return;
            completed.bad_return |= flow.bad_return;
        }
        if normal_assigned {
            let flow = statement_flow(statement, true, write_span)?;
            next_unassigned |= flow.normal_unassigned;
            next_assigned |= flow.normal_assigned;
            completed.good_return |= flow.good_return;
            completed.bad_return |= flow.bad_return;
        }
        normal_unassigned = next_unassigned;
        normal_assigned = next_assigned;
        if !normal_unassigned && !normal_assigned {
            break;
        }
    }
    completed.normal_unassigned = normal_unassigned;
    completed.normal_assigned = normal_assigned;
    Some(completed)
}

struct NormalizedWriteCollector<'c> {
    scoping: &'c Scoping,
    parameter_symbol: SymbolId,
    target_name: String,
    candidates: Vec<(SymbolId, Span)>,
}

impl<'a> Visit<'a> for NormalizedWriteCollector<'_> {
    fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(
        &mut self,
        _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment.operator.as_str() == "=" {
            if let AssignmentTarget::AssignmentTargetIdentifier(identifier) = &assignment.left {
                if let Some(symbol) = identifier
                    .reference_id
                    .get()
                    .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
                {
                    if self.scoping.symbol_name(symbol) == self.target_name
                        && member_object_named(&assignment.right, "exports")
                            .and_then(|object| symbol_of(self.scoping, object))
                            == Some(self.parameter_symbol)
                    {
                        self.candidates.push((symbol, assignment.span));
                    }
                }
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NormalizedInitializerProof {
    write_dominates_normal_exit: bool,
    only_start_export_call: bool,
    non_start_effects_memory_disjoint: bool,
}

fn normalized_initializer_proof(
    source: &str,
    helper_name: &str,
    exports_binding: &str,
    parameter: usize,
) -> Option<NormalizedInitializerProof> {
    let normalized = jsvm_safe_core::deobfuscate_with_standard_numeric_builtins(source, 16)?;
    for source_type in [SourceType::unambiguous(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &normalized.source, source_type);
        if !parsed.is_clean() {
            continue;
        }
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        if !semantic.diagnostics.is_empty() {
            continue;
        }
        let scoping = semantic.semantic.scoping();
        let global_aliases = collect_global_aliases(&parsed.program, scoping);
        let mut proven = Vec::new();
        struct HelperFinder<'c, 's> {
            scoping: &'c Scoping,
            helper_name: &'s str,
            exports_binding: &'s str,
            parameter: usize,
            global_aliases: &'s HashMap<SymbolId, String>,
            proven: &'s mut Vec<NormalizedInitializerProof>,
        }
        impl<'a> Visit<'a> for HelperFinder<'_, '_> {
            fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
                if function
                    .id
                    .as_ref()
                    .is_some_and(|identifier| identifier.name.as_str() == self.helper_name)
                {
                    let Some(params) = parameter_symbols(function) else {
                        self.proven.push(NormalizedInitializerProof {
                            write_dominates_normal_exit: false,
                            only_start_export_call: false,
                            non_start_effects_memory_disjoint: false,
                        });
                        return;
                    };
                    let Some(parameter_symbol) = params.get(self.parameter).copied() else {
                        self.proven.push(NormalizedInitializerProof {
                            write_dominates_normal_exit: false,
                            only_start_export_call: false,
                            non_start_effects_memory_disjoint: false,
                        });
                        return;
                    };
                    let Some(body) = &function.body else {
                        self.proven.push(NormalizedInitializerProof {
                            write_dominates_normal_exit: false,
                            only_start_export_call: false,
                            non_start_effects_memory_disjoint: false,
                        });
                        return;
                    };
                    let mut writes = NormalizedWriteCollector {
                        scoping: self.scoping,
                        parameter_symbol,
                        target_name: self.exports_binding.to_string(),
                        candidates: Vec::new(),
                    };
                    for statement in &body.statements {
                        writes.visit_statement(statement);
                    }
                    let [candidate] = writes.candidates.as_slice() else {
                        self.proven.push(NormalizedInitializerProof {
                            write_dominates_normal_exit: false,
                            only_start_export_call: false,
                            non_start_effects_memory_disjoint: false,
                        });
                        return;
                    };
                    let (target_symbol, write_span) = *candidate;
                    let write_count = self
                        .scoping
                        .get_resolved_reference_ids(target_symbol)
                        .iter()
                        .filter(|reference_id| {
                            self.scoping.get_reference(**reference_id).is_write()
                        })
                        .count();
                    let Some(flow) = statements_flow(&body.statements, false, write_span) else {
                        self.proven.push(NormalizedInitializerProof {
                            write_dominates_normal_exit: false,
                            only_start_export_call: false,
                            non_start_effects_memory_disjoint: false,
                        });
                        return;
                    };
                    let write_dominates_normal_exit = write_count == 1
                        && !flow.bad_return
                        && !flow.normal_unassigned
                        && (flow.good_return || flow.normal_assigned);

                    struct InitializerVerifier<'c, 'g> {
                        scoping: &'c Scoping,
                        global_aliases: &'g HashMap<SymbolId, String>,
                        parameter_symbol: SymbolId,
                        target_symbol: SymbolId,
                        primitive_symbols: HashSet<SymbolId>,
                        exports_assigned: bool,
                        start_calls: usize,
                    }
                    impl InitializerVerifier<'_, '_> {
                        fn verify_statements(&mut self, statements: &[Statement<'_>]) -> bool {
                            statements
                                .iter()
                                .all(|statement| self.verify_statement(statement))
                        }

                        fn verify_statement(&mut self, statement: &Statement<'_>) -> bool {
                            match statement {
                                Statement::BlockStatement(block) => {
                                    self.verify_statements(&block.body)
                                }
                                Statement::EmptyStatement(_) => true,
                                Statement::VariableDeclaration(declaration) => {
                                    for declarator in &declaration.declarations {
                                        let BindingPattern::BindingIdentifier(identifier) =
                                            &declarator.id
                                        else {
                                            return false;
                                        };
                                        let Some(symbol) = identifier.symbol_id.get() else {
                                            return false;
                                        };
                                        if let Some(initializer) = &declarator.init {
                                            if !proof_primitive_expression(
                                                initializer,
                                                self.scoping,
                                                self.global_aliases,
                                                &self.primitive_symbols,
                                            ) {
                                                return false;
                                            }
                                            self.primitive_symbols.insert(symbol);
                                        }
                                    }
                                    true
                                }
                                Statement::ExpressionStatement(statement) => {
                                    let expression = unparenthesized(&statement.expression);
                                    if let Expression::AssignmentExpression(assignment) = expression
                                    {
                                        if assignment.operator.as_str() != "=" {
                                            return false;
                                        }
                                        let AssignmentTarget::AssignmentTargetIdentifier(left) =
                                            &assignment.left
                                        else {
                                            return false;
                                        };
                                        let Some(target) =
                                            left.reference_id.get().and_then(|reference_id| {
                                                self.scoping.get_reference(reference_id).symbol_id()
                                            })
                                        else {
                                            return false;
                                        };
                                        if target == self.target_symbol {
                                            if self.exports_assigned {
                                                return false;
                                            }
                                            let property = match unparenthesized(&assignment.right)
                                            {
                                                Expression::StaticMemberExpression(member)
                                                    if !member.optional
                                                        && symbol_of(
                                                            self.scoping,
                                                            &member.object,
                                                        ) == Some(self.parameter_symbol) =>
                                                {
                                                    Some(member.property.name.as_str())
                                                }
                                                Expression::ComputedMemberExpression(member)
                                                    if !member.optional
                                                        && symbol_of(
                                                            self.scoping,
                                                            &member.object,
                                                        ) == Some(self.parameter_symbol) =>
                                                {
                                                    match unparenthesized(&member.expression) {
                                                        Expression::StringLiteral(property) => {
                                                            Some(property.value.as_str())
                                                        }
                                                        _ => None,
                                                    }
                                                }
                                                _ => None,
                                            };
                                            if property != Some("exports") {
                                                return false;
                                            }
                                            self.exports_assigned = true;
                                            return true;
                                        }
                                        if !proof_primitive_expression(
                                            &assignment.right,
                                            self.scoping,
                                            self.global_aliases,
                                            &self.primitive_symbols,
                                        ) {
                                            return false;
                                        }
                                        self.primitive_symbols.insert(target);
                                        true
                                    } else if let Expression::CallExpression(call) = expression {
                                        if !self.exports_assigned
                                            || call.optional
                                            || !call.arguments.is_empty()
                                        {
                                            return false;
                                        }
                                        let export = match unparenthesized(&call.callee) {
                                            Expression::StaticMemberExpression(member)
                                                if !member.optional
                                                    && symbol_of(self.scoping, &member.object)
                                                        == Some(self.target_symbol) =>
                                            {
                                                Some(member.property.name.as_str())
                                            }
                                            Expression::ComputedMemberExpression(member)
                                                if !member.optional
                                                    && symbol_of(self.scoping, &member.object)
                                                        == Some(self.target_symbol) =>
                                            {
                                                match unparenthesized(&member.expression) {
                                                    Expression::StringLiteral(property) => {
                                                        Some(property.value.as_str())
                                                    }
                                                    _ => None,
                                                }
                                            }
                                            _ => None,
                                        };
                                        if export != Some("__wbindgen_start") {
                                            return false;
                                        }
                                        self.start_calls += 1;
                                        self.start_calls == 1
                                    } else {
                                        false
                                    }
                                }
                                Statement::ReturnStatement(statement) => {
                                    statement.argument.as_ref().is_none_or(|argument| {
                                        symbol_of(self.scoping, argument)
                                            == Some(self.target_symbol)
                                    })
                                }
                                _ => false,
                            }
                        }
                    }
                    let mut verifier = InitializerVerifier {
                        scoping: self.scoping,
                        global_aliases: self.global_aliases,
                        parameter_symbol,
                        target_symbol,
                        primitive_symbols: HashSet::new(),
                        exports_assigned: false,
                        start_calls: 0,
                    };
                    let non_start_effects_memory_disjoint =
                        verifier.verify_statements(&body.statements) && verifier.exports_assigned;
                    self.proven.push(NormalizedInitializerProof {
                        write_dominates_normal_exit,
                        only_start_export_call: non_start_effects_memory_disjoint
                            && verifier.start_calls == 1,
                        non_start_effects_memory_disjoint,
                    });
                    return;
                }
                walk::walk_function(self, function, flags);
            }
        }
        let mut finder = HelperFinder {
            scoping,
            helper_name,
            exports_binding,
            parameter,
            global_aliases: &global_aliases,
            proven: &mut proven,
        };
        finder.visit_program(&parsed.program);
        if let [proof] = proven.as_slice() {
            return Some(*proof);
        }
    }
    None
}

fn unique_exact_instance_paths(
    scoping: &Scoping,
    getter: &MemoryGetterCandidate,
    instantiation_sites: &HashMap<(u32, u32), Vec<WasmInstantiationSite>>,
    bindings: &[ExactInstancePath],
    promises: &[ExactInstancePath],
) -> HashMap<InstanceKey, WasmInstantiationSite> {
    let Some(sites) = instantiation_sites.get(&(getter.assignment_start, getter.assignment_end))
    else {
        return HashMap::new();
    };
    let exact_sites = sites
        .iter()
        .filter(|site| {
            site.exact_import_object_identity_proven && site.exact_module_identity_proven
        })
        .collect::<Vec<_>>();
    let mut candidates = HashMap::<InstanceKey, Vec<WasmInstantiationSite>>::new();
    for path in bindings.iter().chain(promises) {
        for site in &exact_sites {
            if site.start == path.site_start && site.end == path.site_end {
                candidates
                    .entry(path.key)
                    .or_default()
                    .push((*site).clone());
            }
        }
    }
    candidates
        .into_iter()
        .filter_map(|(key, mut sites)| {
            sites.sort_by_key(|site| (site.start, site.end));
            sites.dedup();
            (sites.len() == 1).then(|| (key, sites.remove(0)))
        })
        .filter(|(key, _)| !instance_display(scoping, *key).is_empty())
        .collect()
}

pub(super) fn collect_module_memory_identity_proofs(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    instantiation_sites: &HashMap<(u32, u32), Vec<WasmInstantiationSite>>,
) -> Vec<WasmModuleMemoryIdentityProof> {
    let mut function_collector = FunctionCollector {
        scoping,
        functions: HashMap::new(),
    };
    function_collector.visit_program(program);

    let mut write_collector = ExportsWriteCollector {
        scoping,
        functions: &function_collector.functions,
        function_stack: Vec::new(),
        writes: HashMap::new(),
    };
    write_collector.visit_program(program);

    let mut getter_collector = MemoryGetterCollector {
        scoping,
        candidates: Vec::new(),
    };
    getter_collector.visit_program(program);

    let mut binding_collector = InstanceBindingCollector {
        scoping,
        paths: Vec::new(),
    };
    binding_collector.visit_program(program);

    let mut promise_collector = PromiseInstanceCollector {
        scoping,
        paths: Vec::new(),
    };
    promise_collector.visit_program(program);

    let mut length_collector = StableUint32ArrayLengthCollector {
        scoping,
        global_aliases,
        lengths: HashMap::new(),
    };
    length_collector.visit_program(program);

    let mut proofs = Vec::new();
    for getter in getter_collector.candidates {
        if scoping
            .symbol_ids()
            .filter(|symbol| scoping.symbol_name(*symbol) == getter.exports_binding)
            .count()
            != 1
        {
            continue;
        }
        let Some(write) =
            exact_write_relation(scoping, &write_collector.writes, getter.exports_symbol)
        else {
            continue;
        };
        let Some(function) = function_collector.functions.get(&write.helper) else {
            continue;
        };
        let Some(initializer_proof) = normalized_initializer_proof(
            source,
            &function.name,
            &getter.exports_binding,
            write.parameter,
        ) else {
            continue;
        };
        if !initializer_proof.write_dominates_normal_exit {
            continue;
        }
        let exact_instances = unique_exact_instance_paths(
            scoping,
            &getter,
            instantiation_sites,
            &binding_collector.paths,
            &promise_collector.paths,
        );
        if exact_instances.is_empty() {
            continue;
        }

        let mut helper_references = HelperReferenceCollector {
            scoping,
            helper: write.helper,
            parameter: write.parameter,
            calls: Vec::new(),
        };
        helper_references.visit_program(program);
        let resolved_reference_count = scoping.get_resolved_reference_ids(write.helper).len();
        if helper_references.calls.is_empty()
            || helper_references.calls.len() != resolved_reference_count
            || helper_references.calls.iter().any(Option::is_none)
        {
            continue;
        }
        let helper_calls = helper_references
            .calls
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if helper_calls
            .iter()
            .any(|call| !exact_instances.contains_key(&call.key))
        {
            continue;
        }

        let mut regions = RegionCollector {
            scoping,
            global_aliases,
            uint32_array_lengths: &length_collector.lengths,
            helper: write.helper,
            parameter: write.parameter,
            regions: Vec::new(),
        };
        regions.visit_program(program);
        let all_export_calls = regions
            .regions
            .iter()
            .flat_map(|region| &region.exports)
            .filter(|export| exact_instances.contains_key(&export.key))
            .map(|export| (export.key, export.call.call_start, export.call.call_end))
            .collect::<HashSet<_>>();
        if exact_instances.keys().copied().any(|key| {
            !exact_instance_references_are_closed(
                program,
                scoping,
                key,
                &helper_calls,
                &all_export_calls,
            )
        }) {
            continue;
        }
        let proof_start = proofs.len();
        let observed_exports = all_export_calls;
        let mut covered_exports = HashSet::new();
        for region in regions.regions {
            for initializer in &region.initializers {
                let Some(site) = exact_instances.get(&initializer.call.key) else {
                    continue;
                };
                if site.end > initializer.call.start {
                    continue;
                }
                let mut export_calls = region
                    .exports
                    .iter()
                    .filter(|export| {
                        export.key == initializer.call.key
                            && export.statement_index > initializer.statement_index
                            && export.call.call_start > initializer.call.start
                            && !region.helper_call_indices.iter().any(|index| {
                                *index > initializer.statement_index
                                    && *index <= export.statement_index
                            })
                    })
                    .map(|export| export.call.clone())
                    .collect::<Vec<_>>();
                export_calls.sort_by(|left, right| {
                    left.call_start
                        .cmp(&right.call_start)
                        .then_with(|| left.export_name.cmp(&right.export_name))
                });
                export_calls.dedup();
                if export_calls.is_empty() {
                    continue;
                }
                for call in &export_calls {
                    covered_exports.insert((initializer.call.key, call.call_start, call.call_end));
                }
                proofs.push(WasmModuleMemoryIdentityProof {
                    import_module: getter.import_module.clone(),
                    import_name: getter.import_name.clone(),
                    assignment_start: getter.assignment_start,
                    assignment_end: getter.assignment_end,
                    import_object: getter.import_object.clone(),
                    instance_binding: instance_display(scoping, initializer.call.key),
                    instance_identity_kind: instance_kind(initializer.call.key),
                    exports_binding: getter.exports_binding.clone(),
                    memory_export_name: "memory".to_string(),
                    initializer_function: function.name.clone(),
                    initializer_parameter: write.parameter,
                    initializer_call_starts: vec![initializer.call.start],
                    initializer_exports_write_dominates_normal_exit: true,
                    initializer_only_wasm_export_call: initializer_proof
                        .only_start_export_call
                        .then(|| "__wbindgen_start".to_string()),
                    initializer_non_start_effects_memory_disjoint: initializer_proof
                        .non_start_effects_memory_disjoint,
                    standard_js_numeric_builtin_semantics_required: true,
                    instantiation_site: site.clone(),
                    export_calls,
                    successful_memory_getter_execution_required: true,
                    standard_webassembly_builtin_semantics_required: true,
                });
            }
        }
        if observed_exports != covered_exports {
            proofs.truncate(proof_start);
        }
    }
    proofs.sort_by(|left, right| {
        left.assignment_start
            .cmp(&right.assignment_start)
            .then_with(|| {
                left.instantiation_site
                    .start
                    .cmp(&right.instantiation_site.start)
            })
            .then_with(|| left.instance_binding.cmp(&right.instance_binding))
    });
    proofs.dedup();
    proofs
}
