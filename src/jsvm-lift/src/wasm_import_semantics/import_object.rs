use super::{assignment_property, symbol_of, unparenthesized};
use oxc_ast::ast::{Argument, AssignmentTarget, CallExpression, Expression, Program};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::symbol::SymbolId;
use serde::Serialize;
use std::collections::HashMap;

/// A source-level site where a stable local binding is passed as the import-object argument.
///
/// This proves lexical identity with an unresolved global named `WebAssembly`; it does not prove
/// that the site executes or that the global WebAssembly API has not been monkey-patched.
#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmInstantiationSite {
    pub start: u32,
    pub end: u32,
    pub kind: &'static str,
    pub import_argument: usize,
    pub unshadowed_webassembly_global_proven: bool,
    pub standard_webassembly_builtin_semantics_required: bool,
}

/// Links an `imports.<module>.<name>` assignment root to later WebAssembly instantiation sites.
///
/// This does not prove that the member assignment reaches the site at runtime, nor that the first
/// instantiation argument contains the recovered WASM module bytes. Those remain separate proofs.
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

fn unresolved_global_identifier(
    scoping: &Scoping,
    expression: &Expression<'_>,
    expected: &str,
) -> bool {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return false;
    };
    if identifier.name.as_str() != expected {
        return false;
    }
    identifier
        .reference_id
        .get()
        .is_some_and(|reference_id| scoping.get_reference(reference_id).symbol_id().is_none())
}

fn webassembly_member_name<'a>(
    scoping: &Scoping,
    expression: &'a Expression<'a>,
) -> Option<&'a str> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member)
            if !member.optional
                && unresolved_global_identifier(scoping, &member.object, "WebAssembly") =>
        {
            Some(member.property.name.as_str())
        }
        Expression::ComputedMemberExpression(member)
            if !member.optional
                && unresolved_global_identifier(scoping, &member.object, "WebAssembly") =>
        {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            Some(property.value.as_str())
        }
        _ => None,
    }
}

fn second_argument_symbol(scoping: &Scoping, arguments: &[Argument<'_>]) -> Option<SymbolId> {
    let [_, import_object] = arguments else {
        return None;
    };
    symbol_of(scoping, import_object.as_expression()?)
}

struct InstantiationSiteCollector<'c> {
    scoping: &'c Scoping,
    sites: HashMap<SymbolId, Vec<WasmInstantiationSite>>,
}

impl<'a> Visit<'a> for InstantiationSiteCollector<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Some(kind) = webassembly_member_name(self.scoping, &call.callee) {
                if matches!(kind, "instantiate" | "instantiateStreaming") {
                    if let Some(symbol) = second_argument_symbol(self.scoping, &call.arguments) {
                        self.sites
                            .entry(symbol)
                            .or_default()
                            .push(WasmInstantiationSite {
                                start: call.span.start,
                                end: call.span.end,
                                kind: if kind == "instantiate" {
                                    "WebAssembly.instantiate"
                                } else {
                                    "WebAssembly.instantiateStreaming"
                                },
                                import_argument: 1,
                                unshadowed_webassembly_global_proven: true,
                                standard_webassembly_builtin_semantics_required: true,
                            });
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
        if webassembly_member_name(self.scoping, &expression.callee) == Some("Instance") {
            if let Some(symbol) = second_argument_symbol(self.scoping, &expression.arguments) {
                self.sites
                    .entry(symbol)
                    .or_default()
                    .push(WasmInstantiationSite {
                        start: expression.span.start,
                        end: expression.span.end,
                        kind: "new WebAssembly.Instance",
                        import_argument: 1,
                        unshadowed_webassembly_global_proven: true,
                        standard_webassembly_builtin_semantics_required: true,
                    });
            }
        }
        walk::walk_new_expression(self, expression);
    }
}

pub(super) fn collect_instantiation_sites(
    program: &Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, Vec<WasmInstantiationSite>> {
    let mut collector = InstantiationSiteCollector {
        scoping,
        sites: HashMap::new(),
    };
    collector.visit_program(program);
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
