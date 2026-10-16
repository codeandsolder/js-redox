use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, AssignmentTarget, BindingPattern, CallExpression, Expression, Function, Program,
    Statement, VariableDeclaration,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::SourceType;
use oxc_syntax::symbol::SymbolId;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::collections::HashMap;

mod bulk_import;
mod import_object;
mod module_identity;
use bulk_import::analyze_import_handler;
pub use bulk_import::{WasmImportHandlerSemantic, WasmImportHandlerShape};
use import_object::{assignment_import_object, collect_instantiation_sites};
pub use import_object::{WasmImportObjectUsage, WasmInstantiationSite};
use module_identity::collect_exact_module_sites;

/// Independent JavaScript-side proofs relevant to WebAssembly import correlation.
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Default)]
pub struct WasmImportSemanticsAnalysis {
    pub shapes: Vec<WasmImportDataViewSetU32Shape>,
    pub handler_semantics: Vec<WasmImportHandlerShape>,
    pub import_object_usages: Vec<WasmImportObjectUsage>,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmImportDataViewSetU32Shape {
    pub import_module: Option<String>,
    pub import_name: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
    pub memory_param: usize,
    pub base_param: usize,
    pub offset_param: usize,
    pub offset_value: Option<u32>,
    pub width_bits: u8,
    pub endian: &'static str,
    pub normal_return_set_u32_call_proven: bool,
    pub standard_builtin_semantics_required: bool,
    pub global_object: String,
    pub constructor: &'static str,
    pub method: &'static str,
}

fn unparenthesized<'a>(mut expression: &'a Expression<'a>) -> &'a Expression<'a> {
    while let Expression::ParenthesizedExpression(parenthesized) = expression {
        expression = &parenthesized.expression;
    }
    expression
}

fn symbol_of(scoping: &Scoping, expression: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()
}

fn expression_property_name<'a>(expression: &'a Expression<'a>) -> Option<&'a str> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => {
            Some(member.property.name.as_str())
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            match unparenthesized(&member.expression) {
                Expression::StringLiteral(literal) => Some(literal.value.as_str()),
                _ => None,
            }
        }
        _ => None,
    }
}

fn assignment_property<'a>(target: &'a AssignmentTarget<'a>) -> Option<(&'a str, Option<&'a str>)> {
    match target {
        AssignmentTarget::StaticMemberExpression(member) if !member.optional => Some((
            member.property.name.as_str(),
            expression_property_name(&member.object),
        )),
        AssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(literal) = unparenthesized(&member.expression) else {
                return None;
            };
            Some((
                literal.value.as_str(),
                expression_property_name(&member.object),
            ))
        }
        _ => None,
    }
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

fn exact_zero(expression: &Expression<'_>) -> bool {
    matches!(unparenthesized(expression), Expression::NumericLiteral(literal) if literal.value == 0.0)
}

fn expression_is_symbol(scoping: &Scoping, expression: &Expression<'_>, symbol: SymbolId) -> bool {
    symbol_of(scoping, expression) == Some(symbol)
}

fn u32_argument_matches_symbol(
    scoping: &Scoping,
    argument: &Argument<'_>,
    symbol: SymbolId,
) -> bool {
    let Some(expression) = argument.as_expression() else {
        return false;
    };
    let expression = unparenthesized(expression);
    if expression_is_symbol(scoping, expression, symbol) {
        return true;
    }
    let Expression::BinaryExpression(binary) = expression else {
        return false;
    };
    binary.operator.as_str() == ">>>"
        && expression_is_symbol(scoping, &binary.left, symbol)
        && exact_zero(&binary.right)
}

fn symbol_binding_is_stable(scoping: &Scoping, symbol: SymbolId) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| !scoping.get_reference(*reference_id).is_write())
}

fn symbol_is_stable(scoping: &Scoping, symbol: SymbolId) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| {
            let reference = scoping.get_reference(*reference_id);
            !reference.is_write() && !reference.flags().is_member_write_target()
        })
}

fn direct_global_name(scoping: &Scoping, expression: &Expression<'_>) -> Option<String> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    let reference = scoping.get_reference(identifier.reference_id.get()?);
    if reference.symbol_id().is_some() {
        return None;
    }
    matches!(identifier.name.as_str(), "window" | "globalThis" | "self")
        .then(|| identifier.name.to_string())
}

struct DynamicScopeProbe<'c> {
    scoping: &'c Scoping,
    found: bool,
}

impl<'a> Visit<'a> for DynamicScopeProbe<'_> {
    fn visit_with_statement(&mut self, _statement: &oxc_ast::ast::WithStatement<'a>) {
        self.found = true;
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if self.found {
            return;
        }
        if let Expression::Identifier(identifier) = unparenthesized(&call.callee) {
            if identifier.name.as_str() == "eval"
                && identifier.reference_id.get().is_some_and(|reference_id| {
                    self.scoping
                        .get_reference(reference_id)
                        .symbol_id()
                        .is_none()
                })
            {
                self.found = true;
                return;
            }
        }
        walk::walk_call_expression(self, call);
    }
}

fn has_dynamic_scope(program: &Program<'_>, scoping: &Scoping) -> bool {
    let mut probe = DynamicScopeProbe {
        scoping,
        found: false,
    };
    probe.visit_program(program);
    probe.found
}

fn collect_global_aliases(program: &Program<'_>, scoping: &Scoping) -> HashMap<SymbolId, String> {
    struct Collector<'c> {
        scoping: &'c Scoping,
        aliases: HashMap<SymbolId, String>,
    }
    impl<'a> Visit<'a> for Collector<'_> {
        fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    continue;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    continue;
                };
                let Some(initializer) = &declarator.init else {
                    continue;
                };
                let Some(global) = direct_global_name(self.scoping, initializer) else {
                    continue;
                };
                if symbol_binding_is_stable(self.scoping, symbol) {
                    self.aliases.insert(symbol, global);
                }
            }
            walk::walk_variable_declaration(self, declaration);
        }
    }
    let mut collector = Collector {
        scoping,
        aliases: HashMap::new(),
    };
    collector.visit_program(program);
    collector.aliases
}

fn global_constructor(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    callee: &Expression<'_>,
    constructor: &str,
) -> Option<String> {
    match unparenthesized(callee) {
        Expression::Identifier(identifier) if identifier.name.as_str() == constructor => {
            let reference = scoping.get_reference(identifier.reference_id.get()?);
            reference
                .symbol_id()
                .is_none()
                .then(|| "globalThis".to_string())
        }
        Expression::StaticMemberExpression(member)
            if !member.optional && member.property.name.as_str() == constructor =>
        {
            global_aliases
                .get(&symbol_of(scoping, &member.object)?)
                .cloned()
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            if property.value.as_str() != constructor {
                return None;
            }
            global_aliases
                .get(&symbol_of(scoping, &member.object)?)
                .cloned()
        }
        _ => None,
    }
}

fn static_member_of_symbol(
    scoping: &Scoping,
    expression: &Expression<'_>,
    symbol: SymbolId,
    property: &str,
) -> bool {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member)
            if !member.optional && member.property.name.as_str() == property =>
        {
            expression_is_symbol(scoping, &member.object, symbol)
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            expression_is_symbol(scoping, &member.object, symbol)
                && matches!(unparenthesized(&member.expression), Expression::StringLiteral(literal) if literal.value.as_str() == property)
        }
        _ => false,
    }
}

fn data_view_binding(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    declaration: &VariableDeclaration<'_>,
    memory_param: SymbolId,
) -> Option<(SymbolId, String)> {
    for declarator in &declaration.declarations {
        let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
            continue;
        };
        let Some(symbol) = identifier.symbol_id.get() else {
            continue;
        };
        let Some(Expression::NewExpression(new_expression)) = &declarator.init else {
            continue;
        };
        let Some(global) =
            global_constructor(scoping, global_aliases, &new_expression.callee, "DataView")
        else {
            continue;
        };
        let [argument] = new_expression.arguments.as_slice() else {
            continue;
        };
        let Some(buffer) = argument.as_expression() else {
            continue;
        };
        if static_member_of_symbol(scoping, buffer, memory_param, "buffer")
            && symbol_is_stable(scoping, symbol)
        {
            return Some((symbol, global));
        }
    }
    None
}

fn sum_of_symbols(
    scoping: &Scoping,
    expression: &Expression<'_>,
    left: SymbolId,
    right: SymbolId,
) -> bool {
    let Expression::BinaryExpression(binary) = unparenthesized(expression) else {
        return false;
    };
    if binary.operator.as_str() != "+" {
        return false;
    }
    (expression_is_symbol(scoping, &binary.left, left)
        && expression_is_symbol(scoping, &binary.right, right))
        || (expression_is_symbol(scoping, &binary.left, right)
            && expression_is_symbol(scoping, &binary.right, left))
}

fn address_binding(
    scoping: &Scoping,
    declaration: &VariableDeclaration<'_>,
    base_param: SymbolId,
    offset_param: SymbolId,
) -> Option<SymbolId> {
    for declarator in &declaration.declarations {
        let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
            continue;
        };
        let Some(symbol) = identifier.symbol_id.get() else {
            continue;
        };
        let Some(initializer) = &declarator.init else {
            continue;
        };
        if sum_of_symbols(scoping, initializer, base_param, offset_param)
            && symbol_is_stable(scoping, symbol)
        {
            return Some(symbol);
        }
    }
    None
}

fn proven_set_u32_call(
    scoping: &Scoping,
    call: &CallExpression<'_>,
    view_symbol: SymbolId,
    address_symbol: SymbolId,
) -> bool {
    if call.optional || call.arguments.len() != 3 || call.arguments.iter().any(Argument::is_spread)
    {
        return false;
    }
    if expression_property_name(&call.callee) != Some("setUint32") {
        return false;
    }
    let receiver = match unparenthesized(&call.callee) {
        Expression::StaticMemberExpression(member) => &member.object,
        Expression::ComputedMemberExpression(member) => &member.object,
        _ => return false,
    };
    let Some(address) = call.arguments[0].as_expression() else {
        return false;
    };
    expression_is_symbol(scoping, receiver, view_symbol)
        && expression_is_symbol(scoping, address, address_symbol)
        && matches!(&call.arguments[2], Argument::BooleanLiteral(literal) if !literal.value)
}

fn numeric_value_for_offset(
    scoping: &Scoping,
    expression: &Expression<'_>,
    offset_symbol: SymbolId,
    offset_value: u32,
) -> Option<f64> {
    match unparenthesized(expression) {
        Expression::NumericLiteral(literal) => Some(literal.value),
        Expression::Identifier(_) if expression_is_symbol(scoping, expression, offset_symbol) => {
            Some(f64::from(offset_value))
        }
        _ => None,
    }
}

fn known_bool_for_offset(
    scoping: &Scoping,
    expression: &Expression<'_>,
    offset_symbol: SymbolId,
    offset_value: u32,
) -> Option<bool> {
    match unparenthesized(expression) {
        Expression::BooleanLiteral(literal) => Some(literal.value),
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "!" => {
            known_bool_for_offset(scoping, &unary.argument, offset_symbol, offset_value)
                .map(|value| !value)
        }
        Expression::BinaryExpression(binary) => {
            let left =
                numeric_value_for_offset(scoping, &binary.left, offset_symbol, offset_value)?;
            let right =
                numeric_value_for_offset(scoping, &binary.right, offset_symbol, offset_value)?;
            match binary.operator.as_str() {
                "==" | "===" => Some(left == right),
                "!=" | "!==" => Some(left != right),
                "<" => Some(left < right),
                "<=" => Some(left <= right),
                ">" => Some(left > right),
                ">=" => Some(left >= right),
                _ => None,
            }
        }
        Expression::LogicalExpression(logical) => {
            let left = known_bool_for_offset(scoping, &logical.left, offset_symbol, offset_value);
            let right =
                || known_bool_for_offset(scoping, &logical.right, offset_symbol, offset_value);
            match logical.operator.as_str() {
                "&&" => match left {
                    Some(false) => Some(false),
                    Some(true) => right(),
                    None if right() == Some(false) => Some(false),
                    None => None,
                },
                "||" => match left {
                    Some(true) => Some(true),
                    Some(false) => right(),
                    None if right() == Some(true) => Some(true),
                    None => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

fn every_normal_result_is_write(
    scoping: &Scoping,
    expression: &Expression<'_>,
    view_symbol: SymbolId,
    address_symbol: SymbolId,
    offset_symbol: SymbolId,
    offset_value: Option<u32>,
) -> bool {
    match unparenthesized(expression) {
        Expression::CallExpression(call) => {
            proven_set_u32_call(scoping, call, view_symbol, address_symbol)
        }
        Expression::ConditionalExpression(conditional) => {
            if let Some(value) = offset_value.and_then(|offset| {
                known_bool_for_offset(scoping, &conditional.test, offset_symbol, offset)
            }) {
                return every_normal_result_is_write(
                    scoping,
                    if value {
                        &conditional.consequent
                    } else {
                        &conditional.alternate
                    },
                    view_symbol,
                    address_symbol,
                    offset_symbol,
                    offset_value,
                );
            }
            every_normal_result_is_write(
                scoping,
                &conditional.consequent,
                view_symbol,
                address_symbol,
                offset_symbol,
                offset_value,
            ) && every_normal_result_is_write(
                scoping,
                &conditional.alternate,
                view_symbol,
                address_symbol,
                offset_symbol,
                offset_value,
            )
        }
        Expression::LogicalExpression(logical) => {
            let Some(offset) = offset_value else {
                return false;
            };
            let left = known_bool_for_offset(scoping, &logical.left, offset_symbol, offset);
            match logical.operator.as_str() {
                "||" if left == Some(false) => every_normal_result_is_write(
                    scoping,
                    &logical.right,
                    view_symbol,
                    address_symbol,
                    offset_symbol,
                    offset_value,
                ),
                "&&" if left == Some(true) => every_normal_result_is_write(
                    scoping,
                    &logical.right,
                    view_symbol,
                    address_symbol,
                    offset_symbol,
                    offset_value,
                ),
                _ => false,
            }
        }
        Expression::SequenceExpression(sequence) => {
            sequence.expressions.last().is_some_and(|last| {
                every_normal_result_is_write(
                    scoping,
                    last,
                    view_symbol,
                    address_symbol,
                    offset_symbol,
                    offset_value,
                )
            })
        }
        _ => false,
    }
}

fn analyze_direct_write_function(
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    offset_value: Option<u32>,
) -> Option<String> {
    if function.r#async || function.generator {
        return None;
    }
    let parameters = parameter_symbols(function)?;
    let [memory_param, base_param, offset_param] = parameters.as_slice() else {
        return None;
    };
    if parameters
        .iter()
        .any(|symbol| !symbol_binding_is_stable(scoping, *symbol))
    {
        return None;
    }
    let body = function.body.as_ref()?;
    let last = body.statements.last()?;
    if !body.statements[..body.statements.len().saturating_sub(1)]
        .iter()
        .all(|statement| {
            matches!(
                statement,
                Statement::FunctionDeclaration(_) | Statement::VariableDeclaration(_)
            )
        })
    {
        return None;
    }

    let mut view = None;
    let mut address = None;
    for statement in &body.statements[..body.statements.len().saturating_sub(1)] {
        let Statement::VariableDeclaration(declaration) = statement else {
            continue;
        };
        if view.is_none() {
            view = data_view_binding(scoping, global_aliases, declaration, *memory_param);
        }
        if address.is_none() {
            address = address_binding(scoping, declaration, *base_param, *offset_param);
        }
    }
    let (view_symbol, global) = view?;
    let address_symbol = address?;
    let final_expression = match last {
        Statement::ExpressionStatement(statement) => &statement.expression,
        Statement::ReturnStatement(statement) => statement.argument.as_ref()?,
        _ => return None,
    };
    every_normal_result_is_write(
        scoping,
        final_expression,
        view_symbol,
        address_symbol,
        *offset_param,
        offset_value,
    )
    .then_some(global)
}

fn unwrap_iife_call<'a>(expression: &'a Expression<'a>) -> Option<&'a CallExpression<'a>> {
    match unparenthesized(expression) {
        Expression::CallExpression(call) => Some(call),
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "!" => {
            let Expression::CallExpression(call) = unparenthesized(&unary.argument) else {
                return None;
            };
            Some(call)
        }
        _ => None,
    }
}

fn analyze_wrapped_write_function(
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    offset_value: Option<u32>,
) -> Option<String> {
    if function.r#async || function.generator {
        return None;
    }
    let outer_params = parameter_symbols(function)?;
    let [memory_param, base_param, offset_param] = outer_params.as_slice() else {
        return None;
    };
    if outer_params
        .iter()
        .any(|symbol| !symbol_binding_is_stable(scoping, *symbol))
    {
        return None;
    }
    let body = function.body.as_ref()?;
    let [Statement::ExpressionStatement(statement)] = body.statements.as_slice() else {
        return None;
    };
    let call = unwrap_iife_call(&statement.expression)?;
    if call.optional || call.arguments.len() != 3 || call.arguments.iter().any(Argument::is_spread)
    {
        return None;
    }
    if !u32_argument_matches_symbol(scoping, &call.arguments[0], *memory_param)
        || !u32_argument_matches_symbol(scoping, &call.arguments[1], *base_param)
        || !u32_argument_matches_symbol(scoping, &call.arguments[2], *offset_param)
    {
        return None;
    }
    let Expression::FunctionExpression(inner) = unparenthesized(&call.callee) else {
        return None;
    };
    analyze_direct_write_function(inner, scoping, global_aliases, offset_value)
}

fn analyze_handler(
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    offset_value: Option<u32>,
) -> Option<String> {
    analyze_direct_write_function(function, scoping, global_aliases, offset_value)
        .or_else(|| analyze_wrapped_write_function(function, scoping, global_aliases, offset_value))
}

struct HandlerCollector<'c, 'g, 'i, 'f> {
    scoping: &'c Scoping,
    global_aliases: &'g HashMap<SymbolId, String>,
    instantiation_sites: &'i HashMap<SymbolId, Vec<WasmInstantiationSite>>,
    module_filter: Option<&'f str>,
    import_filter: Option<&'f str>,
    offset_value: Option<u32>,
    reports: Vec<WasmImportDataViewSetU32Shape>,
    handler_semantics: Vec<WasmImportHandlerShape>,
    import_object_usages: Vec<WasmImportObjectUsage>,
}

impl<'a> Visit<'a> for HandlerCollector<'_, '_, '_, '_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment.operator.as_str() == "=" {
            if let (Some((import_name, import_module)), Expression::FunctionExpression(function)) = (
                assignment_property(&assignment.left),
                unparenthesized(&assignment.right),
            ) {
                if self
                    .import_filter
                    .is_none_or(|wanted| wanted == import_name)
                    && self
                        .module_filter
                        .is_none_or(|wanted| import_module == Some(wanted))
                {
                    if let Some((symbol, import_object, module, name)) =
                        assignment_import_object(self.scoping, &assignment.left)
                    {
                        if module == import_module.unwrap_or_default()
                            && name == import_name
                            && symbol_binding_is_stable(self.scoping, symbol)
                        {
                            if let Some(sites) = self.instantiation_sites.get(&symbol) {
                                let later_sites = sites
                                    .iter()
                                    .filter(|site| site.start > assignment.span.end)
                                    .cloned()
                                    .collect::<Vec<_>>();
                                if !later_sites.is_empty() {
                                    self.import_object_usages.push(WasmImportObjectUsage {
                                        import_module: module,
                                        import_name: name,
                                        assignment_start: assignment.span.start,
                                        assignment_end: assignment.span.end,
                                        import_object,
                                        instantiation_sites: later_sites,
                                    });
                                }
                            }
                        }
                    }
                    if let Some(semantic) =
                        analyze_import_handler(function, self.scoping, self.global_aliases)
                    {
                        self.handler_semantics.push(WasmImportHandlerShape {
                            import_module: import_module.map(str::to_string),
                            import_name: import_name.to_string(),
                            assignment_start: assignment.span.start,
                            assignment_end: assignment.span.end,
                            semantic,
                        });
                    }
                    if let Some(global_object) = analyze_handler(
                        function,
                        self.scoping,
                        self.global_aliases,
                        self.offset_value,
                    ) {
                        self.reports.push(WasmImportDataViewSetU32Shape {
                            import_module: import_module.map(str::to_string),
                            import_name: import_name.to_string(),
                            assignment_start: assignment.span.start,
                            assignment_end: assignment.span.end,
                            memory_param: 0,
                            base_param: 1,
                            offset_param: 2,
                            offset_value: self.offset_value,
                            width_bits: 32,
                            endian: "big",
                            normal_return_set_u32_call_proven: true,
                            standard_builtin_semantics_required: true,
                            global_object,
                            constructor: "DataView",
                            method: "setUint32",
                        });
                    }
                }
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }
}

fn analyze_program(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    module_filter: Option<&str>,
    import_filter: Option<&str>,
    offset_value: Option<u32>,
) -> WasmImportSemanticsAnalysis {
    if has_dynamic_scope(program, scoping) {
        return WasmImportSemanticsAnalysis::default();
    }
    let global_aliases = collect_global_aliases(program, scoping);
    let exact_module_sites = collect_exact_module_sites(source, program, scoping, &global_aliases);
    let instantiation_sites =
        collect_instantiation_sites(program, scoping, &global_aliases, &exact_module_sites);
    let mut collector = HandlerCollector {
        scoping,
        global_aliases: &global_aliases,
        instantiation_sites: &instantiation_sites,
        module_filter,
        import_filter,
        offset_value,
        reports: Vec::new(),
        handler_semantics: Vec::new(),
        import_object_usages: Vec::new(),
    };
    collector.visit_program(program);
    collector.reports.sort_by(|left, right| {
        left.assignment_start
            .cmp(&right.assignment_start)
            .then_with(|| left.import_name.cmp(&right.import_name))
    });
    collector.reports.dedup();
    collector.handler_semantics.sort_by(|left, right| {
        left.assignment_start
            .cmp(&right.assignment_start)
            .then_with(|| left.import_name.cmp(&right.import_name))
    });
    collector.handler_semantics.dedup();
    collector.import_object_usages.sort_by(|left, right| {
        left.assignment_start
            .cmp(&right.assignment_start)
            .then_with(|| left.import_module.cmp(&right.import_module))
            .then_with(|| left.import_name.cmp(&right.import_name))
    });
    collector.import_object_usages.dedup();
    WasmImportSemanticsAnalysis {
        shapes: collector.reports,
        handler_semantics: collector.handler_semantics,
        import_object_usages: collector.import_object_usages,
    }
}

fn analyze_source(
    source: &str,
    module_filter: Option<&str>,
    import_filter: Option<&str>,
    offset_value: Option<u32>,
) -> WasmImportSemanticsAnalysis {
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
        return analyze_program(
            source,
            &parsed.program,
            semantic.semantic.scoping(),
            module_filter,
            import_filter,
            offset_value,
        );
    }
    WasmImportSemanticsAnalysis::default()
}

#[must_use]
pub fn proven_wasm_import_semantics(source: &str) -> WasmImportSemanticsAnalysis {
    analyze_source(source, None, None, None)
}

#[must_use]
pub fn proven_wasm_import_semantics_for(
    source: &str,
    import_module: &str,
    import_name: &str,
    offset: u32,
) -> WasmImportSemanticsAnalysis {
    analyze_source(source, Some(import_module), Some(import_name), Some(offset))
}

#[must_use]
pub fn proven_wasm_import_data_view_set_u32_shapes(
    source: &str,
) -> Vec<WasmImportDataViewSetU32Shape> {
    proven_wasm_import_semantics(source).shapes
}

#[must_use]
pub fn proven_wasm_import_data_view_set_u32_shape_at_offset(
    source: &str,
    import_module: &str,
    import_name: &str,
    offset: u32,
) -> Option<WasmImportDataViewSetU32Shape> {
    let mut reports =
        proven_wasm_import_semantics_for(source, import_module, import_name, offset).shapes;
    (reports.len() == 1).then(|| reports.remove(0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proves_direct_and_wrapped_global_dataview_writes() {
        let source = r#"
            var host = window; var imports = {};
            imports.direct = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer); var address = base + offset;
                flag ? view.setUint32(address, one(), false) : view.setUint32(address, two(), false);
            };
            imports["wrapped"] = function(memory, base, offset) {
                !function(a, b, c) {
                    function value() { return 7; }
                    var view = new host.DataView(a.buffer), address = b + c;
                    cond ? view.setUint32(address, value(), false) : view.setUint32(address, other(), false);
                }(memory, base >>> 0, offset >>> 0);
            };
        "#;
        let reports = proven_wasm_import_data_view_set_u32_shapes(source);
        assert_eq!(reports.len(), 2);
        assert_eq!(reports[0].import_name, "direct");
        assert_eq!(reports[0].global_object, "window");
        assert_eq!(reports[1].import_name, "wrapped");
        assert_eq!(reports[1].global_object, "window");
        assert!(reports
            .iter()
            .all(|report| report.normal_return_set_u32_call_proven));
    }

    #[test]
    fn rejects_missing_or_different_write_semantics() {
        let source = r#"
            var host = window; var imports = {};
            imports.missing = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer); var address = base + offset;
                flag ? view.setUint32(address, 1, false) : sideEffect();
            };
            imports.little = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer); var address = base + offset;
                view.setUint32(address, 1, true);
            };
            imports.wrongBuffer = function(memory, base, offset) {
                var view = new host.DataView(other.buffer); var address = base + offset;
                view.setUint32(address, 1, false);
            };
            imports.wrongAddress = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer); var address = base + offset + 4;
                view.setUint32(address, 1, false);
            };
            imports.control = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer); var address = base + offset;
                if (flag) sideEffect(); view.setUint32(address, 1, false);
            };
        "#;
        assert!(proven_wasm_import_data_view_set_u32_shapes(source).is_empty());
    }

    #[test]
    fn specializes_conditional_write_on_proven_offset() {
        let source = r#"
            var host = window; var imports = { wbg: {} };
            imports.wbg.conditional = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer); var address = base + offset;
                (runtime() || offset !== 7)
                    ? (offset !== 5 || view.setUint32(address, 1, false))
                    : view.setUint32(address, 2, false);
            };
        "#;
        assert!(proven_wasm_import_data_view_set_u32_shapes(source).is_empty());
        assert_eq!(
            proven_wasm_import_data_view_set_u32_shape_at_offset(source, "wbg", "conditional", 5)
                .map(|shape| shape.offset_value),
            Some(Some(5))
        );
        assert!(proven_wasm_import_data_view_set_u32_shape_at_offset(
            source,
            "wbg",
            "conditional",
            7
        )
        .is_none());
    }

    #[test]
    fn rejects_wrong_namespace_and_reassigned_parameters() {
        let source = r#"
            var host = window;
            var imports = { wbg: {}, other: {} };
            imports.other.target = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer), address = base + offset;
                view.setUint32(address, 1, false);
            };
            imports.wbg.target = function(memory, base, offset) {
                base = 99;
                var view = new host.DataView(memory.buffer), address = base + offset;
                view.setUint32(address, 1, false);
            };
        "#;
        assert!(
            proven_wasm_import_data_view_set_u32_shape_at_offset(source, "wbg", "target", 5,)
                .is_none()
        );
    }

    #[test]
    fn rejects_direct_eval_and_with_dynamic_scope() {
        let direct_eval = r#"
            var host = window; var imports = { wbg: {} };
            eval(source);
            imports.wbg.target = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer), address = base + offset;
                view.setUint32(address, 1, false);
            };
        "#;
        assert!(proven_wasm_import_data_view_set_u32_shapes(direct_eval).is_empty());

        let with_scope = r#"
            var host = window; var imports = { wbg: {} };
            with (object) { sideEffect(); }
            imports.wbg.target = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer), address = base + offset;
                view.setUint32(address, 1, false);
            };
        "#;
        assert!(proven_wasm_import_data_view_set_u32_shapes(with_scope).is_empty());
    }

    #[test]
    fn proves_stable_import_object_at_webassembly_instantiation_sites() {
        let source = r#"
            var host = window;
            var imports = { wbg: {} };
            imports.wbg.target = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer), address = base + offset;
                view.setUint32(address, 1, false);
            };
            WebAssembly.instantiate(bytes(), imports);
            new WebAssembly.Instance(module(), imports);
        "#;
        let analysis = proven_wasm_import_semantics_for(source, "wbg", "target", 5);
        assert_eq!(analysis.shapes.len(), 1);
        assert_eq!(analysis.import_object_usages.len(), 1);
        let usage = &analysis.import_object_usages[0];
        assert_eq!(usage.import_object, "imports");
        assert_eq!(usage.import_module, "wbg");
        assert_eq!(usage.import_name, "target");
        assert_eq!(usage.instantiation_sites.len(), 2);
        assert_eq!(
            usage
                .instantiation_sites
                .iter()
                .map(|site| site.kind)
                .collect::<Vec<_>>(),
            vec!["WebAssembly.instantiate", "new WebAssembly.Instance"]
        );
        assert!(usage
            .instantiation_sites
            .iter()
            .all(|site| site.webassembly_builtin_reference_proven));
        assert!(usage
            .instantiation_sites
            .iter()
            .all(|site| site.standard_webassembly_builtin_semantics_required));
    }

    #[test]
    fn requires_instantiation_site_after_import_assignment_in_source() {
        let source = r#"
            var host = window;
            var imports = { wbg: {} };
            WebAssembly.instantiate(bytes(), imports);
            imports.wbg.target = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer), address = base + offset;
                view.setUint32(address, 1, false);
            };
        "#;
        let analysis = proven_wasm_import_semantics_for(source, "wbg", "target", 5);
        assert_eq!(analysis.shapes.len(), 1);
        assert!(analysis.import_object_usages.is_empty());
    }

    #[test]
    fn rejects_shadowed_webassembly_and_reassigned_import_objects() {
        let shadowed = r#"
            var host = window;
            var imports = { wbg: {} };
            imports.wbg.target = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer), address = base + offset;
                view.setUint32(address, 1, false);
            };
            function start(WebAssembly) {
                WebAssembly.instantiate(bytes(), imports);
            }
        "#;
        let analysis = proven_wasm_import_semantics_for(shadowed, "wbg", "target", 5);
        assert_eq!(analysis.shapes.len(), 1);
        assert!(analysis.import_object_usages.is_empty());

        let reassigned = r#"
            var host = window;
            var imports = { wbg: {} };
            imports.wbg.target = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer), address = base + offset;
                view.setUint32(address, 1, false);
            };
            imports = replacement;
            WebAssembly.instantiate(bytes(), imports);
        "#;
        let analysis = proven_wasm_import_semantics_for(reassigned, "wbg", "target", 5);
        assert_eq!(analysis.shapes.len(), 1);
        assert!(analysis.import_object_usages.is_empty());
    }

    #[test]
    fn proves_exact_module_and_returned_import_object_identity() {
        let source = r#"
            var m = window;
            function bA(A) {
                if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false];
                for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) {
                    g[E] = Q.charCodeAt(E);
                }
                return [g.buffer, false];
            }
            function BQ(A, B) {
                return function(A) { if (m.Array.isArray(A)) return A; }(A) || fallback(A, B);
            }
            function tQ() {
                var A = {};
                A.wbg = {};
                A.wbg.target = function() {};
                return A;
            }
            var N = "AGFzbQEAAAA=", e = BQ(bA(N), 2), G = e[0], r = tQ();
            m.WebAssembly.instantiate(G, r);
        "#;
        let analysis = proven_wasm_import_semantics(source);
        let usage = analysis
            .import_object_usages
            .iter()
            .find(|usage| usage.import_name == "target")
            .expect("target usage");
        assert_eq!(usage.import_object, "A");
        let [site] = usage.instantiation_sites.as_slice() else {
            panic!("expected one exact instantiation site");
        };
        assert_eq!(site.kind, "WebAssembly.instantiate");
        assert_eq!(site.global_object, "window");
        assert!(site.webassembly_builtin_reference_proven);
        assert!(site.exact_import_object_identity_proven);
        assert_eq!(site.import_object_identity_kind, "returned_object_call");
        assert!(site.exact_module_identity_proven);
        assert_eq!(
            site.module_sha256.as_deref(),
            Some(crate::sha256_hex(b"\0asm\x01\0\0\0").as_str())
        );
        assert_eq!(site.module_identity_kind, Some("exact_bytes"));
        assert!(site.standard_module_decode_builtins_required);
    }

    #[test]
    fn exact_module_identity_fails_closed_on_conflicting_write_or_shadowed_decoder() {
        let conflicting = r#"
            var m = window;
            function bA(A) {
                if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false];
                for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) {
                    g[E] = Q.charCodeAt(E);
                }
                return [g.buffer, false];
            }
            function BQ(A, B) {
                return function(A) { if (m.Array.isArray(A)) return A; }(A) || fallback(A, B);
            }
            function tQ() { var A = {}; A.wbg = {}; A.wbg.target = function() {}; return A; }
            var N = "AGFzbQEAAAA=", e = BQ(bA(N), 2), G = e[0], r = tQ();
            G = replacement;
            m.WebAssembly.instantiate(G, r);
        "#;
        let analysis = proven_wasm_import_semantics(conflicting);
        let usage = analysis
            .import_object_usages
            .iter()
            .find(|usage| usage.import_name == "target")
            .expect("target usage");
        let [site] = usage.instantiation_sites.as_slice() else {
            panic!("expected one instantiation site");
        };
        assert!(site.exact_import_object_identity_proven);
        assert!(!site.exact_module_identity_proven);
        assert!(site.module_sha256.is_none());

        let shadowed = r#"
            var m = window;
            function bA(A) {
                function atob(A) { return A; }
                if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false];
                for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) {
                    g[E] = Q.charCodeAt(E);
                }
                return [g.buffer, false];
            }
            function BQ(A, B) {
                return function(A) { if (m.Array.isArray(A)) return A; }(A) || fallback(A, B);
            }
            function tQ() { var A = {}; A.wbg = {}; A.wbg.target = function() {}; return A; }
            var N = "AGFzbQEAAAA=", e = BQ(bA(N), 2), G = e[0], r = tQ();
            m.WebAssembly.instantiate(G, r);
        "#;
        let analysis = proven_wasm_import_semantics(shadowed);
        let usage = analysis
            .import_object_usages
            .iter()
            .find(|usage| usage.import_name == "target")
            .expect("target usage");
        assert!(usage
            .instantiation_sites
            .iter()
            .all(|site| !site.exact_module_identity_proven));
    }

    #[test]
    fn proves_bulk_import_handler_semantics() {
        let source = r#"
            var host = window;
            var imports = { wbg: {} };
            imports.wbg.buffer = function(value) { return value.buffer };
            imports.wbg.length = function(value) { return value.length };
            imports.wbg.new_u32 = function(value) { return new host.Uint32Array(value) };
            imports.wbg.set_u32 = function(receiver, source, offset) {
                receiver.set(source, offset >>> 0)
            };
            WebAssembly.instantiate(bytes, imports);
        "#;
        let analysis = proven_wasm_import_semantics(source);
        assert_eq!(analysis.handler_semantics.len(), 4);
        let by_name = analysis
            .handler_semantics
            .iter()
            .map(|shape| (shape.import_name.as_str(), &shape.semantic))
            .collect::<HashMap<_, _>>();
        assert!(matches!(
            by_name["buffer"],
            WasmImportHandlerSemantic::PropertyGetter {
                receiver_param: 0,
                property: "buffer",
                standard_builtin_semantics_required: true,
            }
        ));
        assert!(matches!(
            by_name["length"],
            WasmImportHandlerSemantic::PropertyGetter {
                receiver_param: 0,
                property: "length",
                standard_builtin_semantics_required: true,
            }
        ));
        assert!(matches!(
            by_name["new_u32"],
            WasmImportHandlerSemantic::Uint32ArrayConstructor {
                source_param: 0,
                element_width_bits: 32,
                global_object,
                standard_builtin_semantics_required: true,
            } if global_object == "window"
        ));
        assert!(matches!(
            by_name["set_u32"],
            WasmImportHandlerSemantic::TypedArraySet {
                receiver_param: 0,
                source_param: 1,
                offset_param: 2,
                offset_to_u32_proven: true,
                normal_return_set_call_proven: true,
                standard_builtin_semantics_required: true,
            }
        ));
    }

    #[test]
    fn rejects_ambiguous_bulk_import_handler_semantics() {
        let source = r#"
            var host = window;
            var imports = { wbg: {} };
            imports.wbg.shadowed_ctor = function(value) {
                function Uint32Array(value) { return value; }
                return new Uint32Array(value);
            };
            imports.wbg.reassigned_param = function(value) {
                value = replacement;
                return value.buffer;
            };
            imports.wbg.raw_offset = function(receiver, source, offset) {
                receiver.set(source, offset);
            };
            imports.wbg.extra_effect = function(receiver, source, offset) {
                sideEffect();
                receiver.set(source, offset >>> 0);
            };
        "#;
        assert!(proven_wasm_import_semantics(source)
            .handler_semantics
            .is_empty());
    }

    #[test]
    fn requires_stable_global_alias() {
        let source = r#"
            var host = window; host = fake; var imports = {};
            imports.bad = function(memory, base, offset) {
                var view = new host.DataView(memory.buffer); var address = base + offset;
                view.setUint32(address, 1, false);
            };
        "#;
        assert!(proven_wasm_import_data_view_set_u32_shapes(source).is_empty());
    }
}
