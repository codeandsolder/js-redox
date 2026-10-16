use super::{
    assignment_property,
    module_identity::{webassembly_member_name, ExactModuleSite},
    symbol_of, unparenthesized,
};
use oxc_ast::ast::{
    Argument, AssignmentTarget, BindingPattern, CallExpression, Expression, Function, Program,
    Statement, VariableDeclaration,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::symbol::SymbolId;
use serde::Serialize;
use std::collections::HashMap;

/// A source-level WebAssembly instantiation site using one exact stable local import object.
///
/// `exact_module_identity_proven` is stronger than lexical site identity: when true, the first
/// argument has been statically tied to one exact decoded WASM SHA-256 by the conservative module
/// provenance evaluator. Platform WebAssembly semantics are still an explicit assumption.
#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmInstantiationSite {
    pub start: u32,
    pub end: u32,
    pub kind: &'static str,
    pub module_argument: usize,
    pub import_argument: usize,
    pub global_object: String,
    pub webassembly_builtin_reference_proven: bool,
    pub standard_webassembly_builtin_semantics_required: bool,
    pub exact_import_object_identity_proven: bool,
    pub import_object_identity_kind: &'static str,
    pub exact_module_identity_proven: bool,
    pub module_sha256: Option<String>,
    pub module_identity_kind: Option<&'static str>,
    pub standard_module_decode_builtins_required: bool,
}

/// Links an `imports.<module>.<name>` assignment root to later WebAssembly instantiation sites.
#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmImportObjectUsage {
    pub import_module: String,
    pub import_name: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
    pub import_object: String,
    pub instantiation_sites: Vec<WasmInstantiationSite>,
}

fn identifier_symbol_and_name(
    scoping: &Scoping,
    expression: &Expression<'_>,
) -> Option<(SymbolId, String)> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    let symbol = scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()?;
    Some((symbol, identifier.name.to_string()))
}

fn module_member_root(
    scoping: &Scoping,
    expression: &Expression<'_>,
) -> Option<(SymbolId, String)> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => {
            identifier_symbol_and_name(scoping, &member.object)
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(_) = unparenthesized(&member.expression) else {
                return None;
            };
            identifier_symbol_and_name(scoping, &member.object)
        }
        _ => None,
    }
}

pub(super) fn assignment_import_object(
    scoping: &Scoping,
    target: &AssignmentTarget<'_>,
) -> Option<(SymbolId, String, String, String)> {
    let (import_name, import_module) = assignment_property(target)?;
    let import_module = import_module?;
    let object = match target {
        AssignmentTarget::StaticMemberExpression(member) if !member.optional => &member.object,
        AssignmentTarget::ComputedMemberExpression(member) if !member.optional => &member.object,
        _ => return None,
    };
    let (symbol, name) = module_member_root(scoping, object)?;
    Some((
        symbol,
        name,
        import_module.to_string(),
        import_name.to_string(),
    ))
}

fn second_argument_symbol(scoping: &Scoping, arguments: &[Argument<'_>]) -> Option<SymbolId> {
    let [_, import_object] = arguments else {
        return None;
    };
    symbol_of(scoping, import_object.as_expression()?)
}

fn site_record(
    start: u32,
    end: u32,
    kind: &'static str,
    global_object: String,
    import_object_identity_kind: &'static str,
    exact_sites: &HashMap<(u32, u32), ExactModuleSite>,
) -> WasmInstantiationSite {
    let exact = exact_sites.get(&(start, end));
    WasmInstantiationSite {
        start,
        end,
        kind,
        module_argument: 0,
        import_argument: 1,
        global_object,
        webassembly_builtin_reference_proven: true,
        standard_webassembly_builtin_semantics_required: true,
        exact_import_object_identity_proven: true,
        import_object_identity_kind,
        exact_module_identity_proven: exact.is_some(),
        module_sha256: exact.map(|site| site.sha256.clone()),
        module_identity_kind: exact.map(|site| site.identity_kind),
        standard_module_decode_builtins_required: exact
            .is_some_and(|site| site.standard_decode_builtins_required),
    }
}

struct InstantiationSiteCollector<'c, 'g, 'm> {
    scoping: &'c Scoping,
    global_aliases: &'g HashMap<SymbolId, String>,
    exact_sites: &'m HashMap<(u32, u32), ExactModuleSite>,
    sites: HashMap<SymbolId, Vec<WasmInstantiationSite>>,
}

impl<'a> Visit<'a> for InstantiationSiteCollector<'_, '_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Some((member, global_object)) =
                webassembly_member_name(self.scoping, self.global_aliases, &call.callee)
            {
                if matches!(member, "instantiate" | "instantiateStreaming") {
                    if let Some(symbol) = second_argument_symbol(self.scoping, &call.arguments) {
                        self.sites.entry(symbol).or_default().push(site_record(
                            call.span.start,
                            call.span.end,
                            if member == "instantiate" {
                                "WebAssembly.instantiate"
                            } else {
                                "WebAssembly.instantiateStreaming"
                            },
                            global_object,
                            "same_binding",
                            self.exact_sites,
                        ));
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
        if let Some((member, global_object)) =
            webassembly_member_name(self.scoping, self.global_aliases, &expression.callee)
        {
            if member == "Instance" {
                if let Some(symbol) = second_argument_symbol(self.scoping, &expression.arguments) {
                    self.sites.entry(symbol).or_default().push(site_record(
                        expression.span.start,
                        expression.span.end,
                        "new WebAssembly.Instance",
                        global_object,
                        "same_binding",
                        self.exact_sites,
                    ));
                }
            }
        }
        walk::walk_new_expression(self, expression);
    }
}

fn returned_symbol(expression: &Expression<'_>, scoping: &Scoping) -> Option<SymbolId> {
    match unparenthesized(expression) {
        Expression::Identifier(_) => symbol_of(scoping, expression),
        Expression::SequenceExpression(sequence) => {
            symbol_of(scoping, sequence.expressions.last()?)
        }
        _ => None,
    }
}

fn fresh_returned_object(function: &Function<'_>, scoping: &Scoping) -> Option<SymbolId> {
    let body = function.body.as_ref()?;
    let mut fresh_objects = Vec::new();
    let mut returns = Vec::new();
    for statement in &body.statements {
        match statement {
            Statement::VariableDeclaration(declaration) => {
                for declarator in &declaration.declarations {
                    let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                        continue;
                    };
                    if matches!(
                        declarator.init.as_ref(),
                        Some(Expression::ObjectExpression(_))
                    ) {
                        fresh_objects.push(identifier.symbol_id.get()?);
                    }
                }
            }
            Statement::ReturnStatement(statement) => {
                returns.push(returned_symbol(statement.argument.as_ref()?, scoping)?);
            }
            _ => {}
        }
    }
    let [returned] = returns.as_slice() else {
        return None;
    };
    fresh_objects
        .contains(returned)
        .then_some(*returned)
        .filter(|symbol| super::symbol_binding_is_stable(scoping, *symbol))
}

struct ReturnedObjectFunctionCollector<'c> {
    scoping: &'c Scoping,
    functions: HashMap<SymbolId, SymbolId>,
}

impl<'a> Visit<'a> for ReturnedObjectFunctionCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: oxc_syntax::scope::ScopeFlags) {
        if let Some(identifier) = &function.id {
            if let Some(function_symbol) = identifier.symbol_id.get() {
                if super::symbol_binding_is_stable(self.scoping, function_symbol) {
                    if let Some(object_symbol) = fresh_returned_object(function, self.scoping) {
                        self.functions.insert(function_symbol, object_symbol);
                    }
                }
            }
        }
        walk::walk_function(self, function, flags);
    }
}

fn collect_returned_object_functions(
    program: &Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, SymbolId> {
    let mut collector = ReturnedObjectFunctionCollector {
        scoping,
        functions: HashMap::new(),
    };
    collector.visit_program(program);
    collector.functions
}

struct ReturnedObjectAliasCollector<'c, 'f> {
    scoping: &'c Scoping,
    functions: &'f HashMap<SymbolId, SymbolId>,
    aliases: HashMap<SymbolId, SymbolId>,
}

impl ReturnedObjectAliasCollector<'_, '_> {
    fn returned_object(&self, expression: &Expression<'_>) -> Option<SymbolId> {
        let Expression::CallExpression(call) = unparenthesized(expression) else {
            return None;
        };
        if call.optional || call.arguments.iter().any(Argument::is_spread) {
            return None;
        }
        self.functions
            .get(&symbol_of(self.scoping, &call.callee)?)
            .copied()
    }
}

impl<'a> Visit<'a> for ReturnedObjectAliasCollector<'_, '_> {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                continue;
            };
            let Some(result_symbol) = identifier.symbol_id.get() else {
                continue;
            };
            let Some(initializer) = &declarator.init else {
                continue;
            };
            let Some(object_symbol) = self.returned_object(initializer) else {
                continue;
            };
            if super::symbol_binding_is_stable(self.scoping, result_symbol) {
                self.aliases.insert(result_symbol, object_symbol);
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

fn collect_returned_object_aliases(
    program: &Program<'_>,
    scoping: &Scoping,
    functions: &HashMap<SymbolId, SymbolId>,
) -> HashMap<SymbolId, SymbolId> {
    let mut collector = ReturnedObjectAliasCollector {
        scoping,
        functions,
        aliases: HashMap::new(),
    };
    collector.visit_program(program);
    collector.aliases
}

pub(super) fn collect_instantiation_sites(
    program: &Program<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    exact_sites: &HashMap<(u32, u32), ExactModuleSite>,
) -> HashMap<SymbolId, Vec<WasmInstantiationSite>> {
    let mut collector = InstantiationSiteCollector {
        scoping,
        global_aliases,
        exact_sites,
        sites: HashMap::new(),
    };
    collector.visit_program(program);

    let returned_functions = collect_returned_object_functions(program, scoping);
    let returned_aliases = collect_returned_object_aliases(program, scoping, &returned_functions);
    let bridged = returned_aliases
        .into_iter()
        .filter_map(|(result_symbol, object_symbol)| {
            collector
                .sites
                .get(&result_symbol)
                .cloned()
                .map(|mut sites| {
                    for site in &mut sites {
                        site.import_object_identity_kind = "returned_object_call";
                    }
                    (object_symbol, sites)
                })
        })
        .collect::<Vec<_>>();
    for (object_symbol, sites) in bridged {
        collector
            .sites
            .entry(object_symbol)
            .or_default()
            .extend(sites);
    }

    for sites in collector.sites.values_mut() {
        sites.sort_by(|left, right| {
            left.start
                .cmp(&right.start)
                .then_with(|| left.end.cmp(&right.end))
                .then_with(|| left.kind.cmp(right.kind))
        });
        sites.dedup();
    }
    collector.sites
}
