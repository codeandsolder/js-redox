use jsvm_safe_core::{statically_resolved_symbol, statically_unresolved_global_reference};
use oxc_ast::ast::{BindingPattern, Expression, Program};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::symbol::SymbolId;
use std::collections::HashMap;

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
    statically_resolved_symbol(scoping, identifier.reference_id.get()?)
}

fn stable_binding(scoping: &Scoping, symbol: SymbolId) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| !scoping.get_reference(*reference_id).is_write())
}

fn direct_global_name(scoping: &Scoping, expression: &Expression<'_>) -> Option<String> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    let reference_id = identifier.reference_id.get()?;
    if !statically_unresolved_global_reference(scoping, reference_id) {
        return None;
    }
    matches!(identifier.name.as_str(), "window" | "globalThis" | "self")
        .then(|| identifier.name.to_string())
}

fn global_object_name(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    expression: &Expression<'_>,
) -> Option<String> {
    direct_global_name(scoping, expression).or_else(|| {
        global_aliases
            .get(&symbol_of(scoping, expression)?)
            .cloned()
    })
}

pub(crate) fn collect_global_aliases(
    program: &Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, String> {
    struct Collector<'c, 'm> {
        scoping: &'c Scoping,
        known: &'m HashMap<SymbolId, String>,
        discovered: HashMap<SymbolId, String>,
    }

    impl<'a> Visit<'a> for Collector<'_, '_> {
        fn visit_variable_declaration(
            &mut self,
            declaration: &oxc_ast::ast::VariableDeclaration<'a>,
        ) {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    continue;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    continue;
                };
                if !stable_binding(self.scoping, symbol) {
                    continue;
                }
                let Some(initializer) = &declarator.init else {
                    continue;
                };
                let global = direct_global_name(self.scoping, initializer).or_else(|| {
                    self.known
                        .get(&symbol_of(self.scoping, initializer)?)
                        .cloned()
                });
                if let Some(global) = global {
                    self.discovered.insert(symbol, global);
                }
            }
            walk::walk_variable_declaration(self, declaration);
        }
    }

    let mut aliases = HashMap::new();
    loop {
        let mut collector = Collector {
            scoping,
            known: &aliases,
            discovered: HashMap::new(),
        };
        collector.visit_program(program);
        let before = aliases.len();
        aliases.extend(collector.discovered);
        if aliases.len() == before {
            return aliases;
        }
    }
}

pub(crate) fn global_constructor(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    callee: &Expression<'_>,
    constructor: &str,
) -> Option<String> {
    match unparenthesized(callee) {
        Expression::Identifier(identifier) if identifier.name.as_str() == constructor => {
            let reference_id = identifier.reference_id.get()?;
            statically_unresolved_global_reference(scoping, reference_id)
                .then(|| "globalThis".to_string())
        }
        Expression::StaticMemberExpression(member)
            if !member.optional && member.property.name.as_str() == constructor =>
        {
            global_object_name(scoping, global_aliases, &member.object)
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            if property.value.as_str()? != constructor {
                return None;
            }
            global_object_name(scoping, global_aliases, &member.object)
        }
        _ => None,
    }
}

fn namespace_global(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    expression: &Expression<'_>,
    namespace: &str,
) -> Option<String> {
    if let Expression::Identifier(identifier) = unparenthesized(expression) {
        if identifier.name.as_str() == namespace {
            let reference_id = identifier.reference_id.get()?;
            if statically_unresolved_global_reference(scoping, reference_id) {
                return Some("globalThis".to_string());
            }
        }
    }

    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member)
            if !member.optional && member.property.name.as_str() == namespace =>
        {
            global_object_name(scoping, global_aliases, &member.object)
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            if property.value.as_str()? != namespace {
                return None;
            }
            global_object_name(scoping, global_aliases, &member.object)
        }
        _ => None,
    }
}

pub(crate) fn namespace_member_name<'a>(
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    expression: &'a Expression<'a>,
    namespace: &str,
) -> Option<(&'a str, String)> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => Some((
            member.property.name.as_str(),
            namespace_global(scoping, global_aliases, &member.object, namespace)?,
        )),
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            Some((
                property.value.as_str()?,
                namespace_global(scoping, global_aliases, &member.object, namespace)?,
            ))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    #[test]
    fn resolves_direct_transitive_and_computed_global_builtins() {
        let source = r#"
            var host = window;
            var host2 = host;
            host2["WebAssembly"]["instantiate"](bytes, imports);
            new host2["DataView"](buffer);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let aliases = collect_global_aliases(&parsed.program, scoping);
        assert_eq!(aliases.len(), 2);

        struct Probe<'c, 'g> {
            scoping: &'c Scoping,
            aliases: &'g HashMap<SymbolId, String>,
            wasm: bool,
            data_view: bool,
        }
        impl<'a> Visit<'a> for Probe<'_, '_> {
            fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
                if namespace_member_name(self.scoping, self.aliases, &call.callee, "WebAssembly")
                    .is_some_and(|(member, global)| member == "instantiate" && global == "window")
                {
                    self.wasm = true;
                }
                walk::walk_call_expression(self, call);
            }

            fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
                if global_constructor(self.scoping, self.aliases, &expression.callee, "DataView")
                    .as_deref()
                    == Some("window")
                {
                    self.data_view = true;
                }
                walk::walk_new_expression(self, expression);
            }
        }
        let mut probe = Probe {
            scoping,
            aliases: &aliases,
            wasm: false,
            data_view: false,
        };
        probe.visit_program(&parsed.program);
        assert!(probe.wasm);
        assert!(probe.data_view);
    }

    #[test]
    fn rejects_reassigned_aliases_and_dynamic_global_resolution() {
        let source = r#"
            var host = window;
            host = fake;
            host.WebAssembly.instantiate(bytes, imports);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let aliases = collect_global_aliases(&parsed.program, semantic.semantic.scoping());
        assert!(aliases.is_empty());

        let source = r#"
            function f(scope) {
                with (scope) {
                    return WebAssembly.instantiate(bytes, imports);
                }
            }
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let aliases = collect_global_aliases(&parsed.program, scoping);

        struct Probe<'c, 'g> {
            scoping: &'c Scoping,
            aliases: &'g HashMap<SymbolId, String>,
            resolved: bool,
        }
        impl<'a> Visit<'a> for Probe<'_, '_> {
            fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
                if namespace_member_name(self.scoping, self.aliases, &call.callee, "WebAssembly")
                    .is_some()
                {
                    self.resolved = true;
                }
                walk::walk_call_expression(self, call);
            }
        }
        let mut probe = Probe {
            scoping,
            aliases: &aliases,
            resolved: false,
        };
        probe.visit_program(&parsed.program);
        assert!(!probe.resolved);
    }
}
