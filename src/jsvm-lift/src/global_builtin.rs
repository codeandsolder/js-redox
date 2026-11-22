use jsvm_safe_core::BindingFacts;
use oxc_ast::ast::{BindingPattern, Expression, Program};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::Span;
use oxc_syntax::{scope::ScopeId, symbol::SymbolId};
use std::collections::HashMap;

use work_budget::{BudgetExceeded, BudgetPoller, WorkBudget};
fn unparenthesized<'a>(mut expression: &'a Expression<'a>) -> &'a Expression<'a> {
    while let Expression::ParenthesizedExpression(parenthesized) = expression {
        expression = &parenthesized.expression;
    }
    expression
}

fn direct_global_name(
    scoping: &Scoping,
    facts: &BindingFacts,
    expression: &Expression<'_>,
) -> Option<String> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    let reference_id = identifier.reference_id.get()?;
    if !facts.proves_global_reference(scoping, reference_id) {
        return None;
    }
    matches!(identifier.name.as_str(), "window" | "globalThis" | "self")
        .then(|| identifier.name.to_string())
}

/// A statically identified invocation of a function declaration. Its
/// captured environment is shared with the declaration's lexical owner.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct InvocationSite {
    pub(crate) callee: SymbolId,
    pub(crate) scope: ScopeId,
    pub(crate) span: Span,
}

/// Namespace aliases and the exact lexical proof for the source snapshot.
/// Keep the two together so no consumer can mistake a dynamically shadowed
/// identifier for the global alias whose static symbol it shares.
#[derive(Debug)]
pub struct GlobalAliases {
    facts: BindingFacts,
    aliases: HashMap<SymbolId, String>,
}

impl GlobalAliases {
    pub(crate) const fn facts(&self) -> &BindingFacts {
        &self.facts
    }

    pub(crate) fn alias_symbol(
        &self,
        scoping: &Scoping,
        expression: &Expression<'_>,
    ) -> Option<SymbolId> {
        let symbol = self
            .facts
            .initialized_read(scoping, unparenthesized(expression))?;
        self.aliases.contains_key(&symbol).then_some(symbol)
    }

    fn global_object_name(&self, scoping: &Scoping, expression: &Expression<'_>) -> Option<String> {
        direct_global_name(scoping, &self.facts, expression).or_else(|| {
            self.aliases
                .get(&self.alias_symbol(scoping, expression)?)
                .cloned()
        })
    }

    /// Resolve a captured namespace at a particular known invocation, not
    /// at the textual location of a deferred body. Only bindings outside
    /// the callee's own activation may be proved by this caller context.
    pub(crate) fn captured_namespace_at_invocation(
        &self,
        scoping: &Scoping,
        expression: &Expression<'_>,
        namespace: &str,
        invocation: InvocationSite,
    ) -> Option<(SymbolId, String)> {
        let object = namespace_receiver(expression, namespace)?;
        let Expression::Identifier(identifier) = unparenthesized(object) else {
            return None;
        };
        let reference = identifier.reference_id.get()?;
        let symbol = self.facts.resolved_symbol(scoping, reference)?;
        let flags = scoping.get_reference(reference);
        let owner = scoping.symbol_scope_id(symbol);
        let callee_owner = scoping.symbol_scope_id(invocation.callee);
        if !flags.is_read()
            || flags.is_write()
            || !scoping
                .scope_ancestors(callee_owner)
                .any(|scope| scope == owner)
            || !self.facts.proves_value_initialized(
                scoping,
                symbol,
                invocation.scope,
                invocation.span,
            )
        {
            return None;
        }
        Some((symbol, self.aliases.get(&symbol)?.clone()))
    }

    pub(crate) fn symbols(&self) -> impl Iterator<Item = SymbolId> + '_ {
        self.aliases.keys().copied()
    }
}

pub fn collect_global_aliases(
    program: &Program<'_>,
    scoping: &Scoping,
    budget: &WorkBudget,
) -> Result<GlobalAliases, BudgetExceeded> {
    struct Collector<'c, 'm> {
        scoping: &'c Scoping,
        known: &'m mut GlobalAliases,
        poller: BudgetPoller,
    }

    impl<'a> Visit<'a> for Collector<'_, '_> {
        fn visit_variable_declaration(
            &mut self,
            declaration: &oxc_ast::ast::VariableDeclaration<'a>,
        ) {
            if !self.poller.poll(1) {
                return;
            }
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    continue;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    continue;
                };
                if !self
                    .known
                    .facts
                    .binding_has_stable_value(self.scoping, symbol)
                {
                    continue;
                }
                let Some(initializer) = &declarator.init else {
                    continue;
                };
                let global = self.known.global_object_name(self.scoping, initializer);
                if let Some(global) = global {
                    self.known.aliases.insert(symbol, global);
                }
            }
            walk::walk_variable_declaration(self, declaration);
        }
    }

    budget.checkpoint()?;
    let mut aliases = GlobalAliases {
        facts: BindingFacts::analyze(program, scoping),
        aliases: HashMap::new(),
    };
    // Each admitted alias dependency has a strictly earlier initialized
    // declaration region. Source order is therefore sufficient; additional
    // whole-AST passes cannot establish new initializer dominance.
    let mut collector = Collector {
        scoping,
        known: &mut aliases,
        poller: BudgetPoller::new(budget, 256),
    };
    collector.visit_program(program);
    collector.poller.finish()?;
    Ok(aliases)
}

pub fn global_constructor(
    scoping: &Scoping,
    global_aliases: &GlobalAliases,
    callee: &Expression<'_>,
    constructor: &str,
) -> Option<String> {
    // A constructor reference and a namespace reference have identical
    // exact global-identity requirements. Do not weaken either proof.
    namespace_global(scoping, global_aliases, callee, constructor)
}

fn namespace_global(
    scoping: &Scoping,
    global_aliases: &GlobalAliases,
    expression: &Expression<'_>,
    namespace: &str,
) -> Option<String> {
    if let Expression::Identifier(identifier) = unparenthesized(expression) {
        if identifier.name.as_str() == namespace {
            let reference_id = identifier.reference_id.get()?;
            if global_aliases
                .facts
                .proves_global_reference(scoping, reference_id)
            {
                return Some("globalThis".to_string());
            }
        }
    }

    let receiver = namespace_receiver(expression, namespace)?;
    global_aliases.global_object_name(scoping, receiver)
}

fn namespace_receiver<'a>(
    expression: &'a Expression<'a>,
    namespace: &str,
) -> Option<&'a Expression<'a>> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member)
            if !member.optional && member.property.name.as_str() == namespace =>
        {
            Some(&member.object)
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            (property.value.as_str()? == namespace).then_some(&member.object)
        }
        _ => None,
    }
}

pub fn namespace_member_name<'a>(
    scoping: &Scoping,
    global_aliases: &GlobalAliases,
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

    fn test_budget() -> WorkBudget {
        WorkBudget::unlimited("global-builtin-test")
    }

    struct ResolvedBuiltinsProbe<'c, 'g> {
        scoping: &'c Scoping,
        aliases: &'g GlobalAliases,
        wasm: bool,
        data_view: bool,
        constructor_resolutions: Vec<Option<String>>,
    }
    impl<'a> Visit<'a> for ResolvedBuiltinsProbe<'_, '_> {
        fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
            if namespace_member_name(self.scoping, self.aliases, &call.callee, "WebAssembly")
                .is_some_and(|(member, global)| member == "instantiate" && global == "window")
            {
                self.wasm = true;
            }
            walk::walk_call_expression(self, call);
        }

        fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
            let resolved =
                global_constructor(self.scoping, self.aliases, &expression.callee, "DataView");
            if resolved.as_deref() == Some("window") {
                self.data_view = true;
            }
            self.constructor_resolutions.push(resolved);
            walk::walk_new_expression(self, expression);
        }
    }

    struct DynamicGlobalProbe<'c, 'g> {
        scoping: &'c Scoping,
        aliases: &'g GlobalAliases,
        resolved: bool,
    }
    impl<'a> Visit<'a> for DynamicGlobalProbe<'_, '_> {
        fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
            if namespace_member_name(self.scoping, self.aliases, &call.callee, "WebAssembly")
                .is_some()
            {
                self.resolved = true;
            }
            walk::walk_call_expression(self, call);
        }
    }

    #[test]
    fn resolves_direct_transitive_and_computed_global_builtins() -> Result<(), BudgetExceeded> {
        let source = r#"
            var host = window;
            var host2 = host;
            host2["WebAssembly"]["instantiate"](bytes, imports);
            new host2["DataView"](buffer);
            function local(DataView) { new DataView(buffer); }
            new globalThis["DataView"](buffer);
            new DataView(buffer);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let aliases = collect_global_aliases(&parsed.program, scoping, &test_budget())?;
        assert_eq!(aliases.aliases.len(), 2);

        let mut probe = ResolvedBuiltinsProbe {
            scoping,
            aliases: &aliases,
            wasm: false,
            data_view: false,
            constructor_resolutions: Vec::new(),
        };
        probe.visit_program(&parsed.program);
        assert!(probe.wasm);
        assert!(probe.data_view);
        assert_eq!(
            probe.constructor_resolutions,
            [
                Some("window".to_string()),
                None, // Locally shadowed constructor is not a global.
                Some("globalThis".to_string()),
                Some("globalThis".to_string()),
            ],
        );
        Ok(())
    }

    #[test]
    fn resolves_aliases_only_at_stable_initialized_reference_sites() -> Result<(), BudgetExceeded> {
        let source = r#"
            const host = globalThis;
            function shadow_direct() {
                (eval)("var DataView = Fake");
                new DataView(buffer);
            }
            function shadow_namespace() {
                eval("var globalThis = fake");
                new globalThis.DataView(buffer);
            }
            function shadow_alias() {
                eval("var host = fake");
                new host.DataView(buffer);
            }
            function stable_strict() {
                "use strict";
                eval("var DataView = Fake");
                new DataView(buffer);
            }
            function sibling() {
                new DataView(buffer);
            }
            function local_mutable() {
                let h = globalThis;
                eval("h = fake");
                new h.DataView(buffer);
            }
            function local_constant() {
                const h = globalThis;
                eval("1");
                new h.DataView(buffer);
            }
            let outer = globalThis;
            function parameter(a = eval("outer = fake")) {
                let outer = globalThis;
                new outer.DataView(buffer);
            }
            new outer.DataView(buffer);
            new host.DataView(buffer);
            new later.DataView(buffer);
            const later = globalThis;
            new later.DataView(buffer);
            var redeclared = globalThis;
            var redeclared = fake;
            new redeclared.DataView(buffer);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let aliases = collect_global_aliases(&parsed.program, scoping, &test_budget())?;
        let mut probe = ResolvedBuiltinsProbe {
            scoping,
            aliases: &aliases,
            wasm: false,
            data_view: false,
            constructor_resolutions: Vec::new(),
        };
        probe.visit_program(&parsed.program);
        let expected = [
            None,
            None,
            None,
            Some("globalThis"),
            Some("globalThis"),
            None,
            None,
            None,
            None,
            Some("globalThis"),
            None,
            Some("globalThis"),
            None,
        ];
        assert_eq!(
            probe.constructor_resolutions,
            expected.map(|value| value.map(str::to_owned)),
            "{source}"
        );
        Ok(())
    }

    #[test]
    fn rejects_reassigned_aliases_and_dynamic_global_resolution() -> Result<(), BudgetExceeded> {
        let source = r"
            var host = window;
            host = fake;
            host.WebAssembly.instantiate(bytes, imports);
        ";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let aliases =
            collect_global_aliases(&parsed.program, semantic.semantic.scoping(), &test_budget())?;
        assert!(aliases.aliases.is_empty());

        let source = r"
            function f(scope) {
                with (scope) {
                    return WebAssembly.instantiate(bytes, imports);
                }
            }
        ";
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let aliases = collect_global_aliases(&parsed.program, scoping, &test_budget())?;

        let mut probe = DynamicGlobalProbe {
            scoping,
            aliases: &aliases,
            resolved: false,
        };
        probe.visit_program(&parsed.program);
        assert!(!probe.resolved);
        Ok(())
    }
}
