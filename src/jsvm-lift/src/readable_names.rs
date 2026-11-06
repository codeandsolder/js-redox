//! Restore descriptive lexical names from explicit metadata embedded in bundled
//! JavaScript. This is ONLY a presentation transform for `src/_readable/`.
//! `src/_deobfuscated/` keeps the semantics-preserving original names.
use jsvm_safe_core::{eval_static_primitive, statically_resolved_symbol, StaticPrimitiveValue};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, CallExpression, Expression, IdentifierReference, ObjectProperty,
    ObjectPropertyKind, Program, VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{identifier, symbol::SymbolId};
use rolldown_redox::ecmascript::parse_program;
use std::collections::{BTreeMap, BTreeSet};

fn source_metadata_name(object: &oxc_ast::ast::ObjectExpression<'_>) -> Option<String> {
    for wanted in ["__name", "displayName", "name"] {
        for property in &object.properties {
            let ObjectPropertyKind::ObjectProperty(property) = property else {
                continue;
            };
            if property.computed || !property.key.is_specific_static_name(wanted) {
                continue;
            }
            let StaticPrimitiveValue::String(name) = eval_static_primitive(&property.value)? else {
                continue;
            };
            // PascalCase metadata is usually an actual component/class name;
            // arbitrary human-readable strings are not JavaScript identifiers.
            if name.len() >= 3
                && name.as_bytes()[0].is_ascii_uppercase()
                && identifier::is_identifier_name(&name)
            {
                return Some(name);
            }
        }
    }
    None
}

fn name_from_initializer(expression: &Expression<'_>, remaining_calls: usize) -> Option<String> {
    match expression {
        Expression::ObjectExpression(object) => source_metadata_name(object),
        Expression::ParenthesizedExpression(parenthesized) => {
            name_from_initializer(&parenthesized.expression, remaining_calls)
        }
        Expression::CallExpression(call) if remaining_calls > 0 && !call.optional => {
            name_from_initializer(
                call.arguments.first()?.as_expression()?,
                remaining_calls - 1,
            )
        }
        _ => None,
    }
}

#[derive(Default)]
struct NameCandidates {
    by_symbol: BTreeMap<SymbolId, String>,
}

impl<'a> Visit<'a> for NameCandidates {
    fn visit_variable_declarator(&mut self, declarator: &VariableDeclarator<'a>) {
        if let (BindingPattern::BindingIdentifier(binding), Some(initializer)) =
            (&declarator.id, declarator.init.as_ref())
        {
            if let (Some(symbol), Some(name)) = (
                binding.symbol_id.get(),
                name_from_initializer(initializer, 4),
            ) {
                self.by_symbol.insert(symbol, name);
            }
        }
        walk::walk_variable_declarator(self, declarator);
    }
}

#[derive(Default)]
struct NameUsages {
    used_names: BTreeSet<String>,
    references: BTreeMap<SymbolId, Vec<Span>>,
    forbidden: BTreeSet<SymbolId>,
    dynamic_scope: bool,
}

// Convert the AST's semantic ReferenceIds into binding IDs during a second
// visit, without guessing by identifier spelling (shadowing is common).
struct ScopedReferences<'s> {
    scoping: &'s Scoping,
    usages: NameUsages,
}

impl<'a> Visit<'a> for ScopedReferences<'_> {
    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        self.usages.used_names.insert(id.name.to_string());
        if let Some(symbol) = id
            .reference_id
            .get()
            .and_then(|reference| statically_resolved_symbol(self.scoping, reference))
        {
            self.usages
                .references
                .entry(symbol)
                .or_default()
                .push(id.span);
        }
    }
    fn visit_binding_identifier(&mut self, id: &oxc_ast::ast::BindingIdentifier<'a>) {
        self.usages.used_names.insert(id.name.to_string());
    }
    fn visit_object_property(&mut self, property: &ObjectProperty<'a>) {
        if property.shorthand {
            if let Expression::Identifier(id) = &property.value {
                if let Some(symbol) = id
                    .reference_id
                    .get()
                    .and_then(|r| statically_resolved_symbol(self.scoping, r))
                {
                    self.usages.forbidden.insert(symbol);
                }
            }
        }
        walk::walk_object_property(self, property);
    }
    fn visit_export_specifier(&mut self, specifier: &oxc_ast::ast::ExportSpecifier<'a>) {
        if specifier.local.span() == specifier.exported.span() {
            if let oxc_ast::ast::ModuleExportName::IdentifierReference(id) = &specifier.local {
                if let Some(symbol) = id
                    .reference_id
                    .get()
                    .and_then(|r| statically_resolved_symbol(self.scoping, r))
                {
                    self.usages.forbidden.insert(symbol);
                }
            }
        }
        walk::walk_export_specifier(self, specifier);
    }
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if matches!(&call.callee, Expression::Identifier(id) if id.name == "eval") {
            self.usages.dynamic_scope = true;
        }
        walk::walk_call_expression(self, call);
    }
    fn visit_with_statement(&mut self, with: &oxc_ast::ast::WithStatement<'a>) {
        self.usages.dynamic_scope = true;
        walk::walk_with_statement(self, with);
    }
}

fn rename_in_program(source: &str, program: &Program<'_>) -> Option<(String, usize)> {
    let semantic = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(program);
    if !semantic.diagnostics.is_empty() {
        return None;
    }
    let scoping = semantic.semantic.scoping();
    let mut candidates = NameCandidates::default();
    candidates.visit_program(program);
    if candidates.by_symbol.is_empty() {
        return None;
    }
    let mut visitor = ScopedReferences {
        scoping,
        usages: NameUsages::default(),
    };
    visitor.visit_program(program);
    let mut usages = visitor.usages;
    if usages.dynamic_scope {
        return None;
    }
    let mut edits = Vec::<(usize, usize, String)>::new();
    let mut count = 0;
    for (symbol, name) in candidates.by_symbol {
        if usages.used_names.contains(&name)
            || usages.forbidden.contains(&symbol)
            || !scoping.symbol_redeclarations(symbol).is_empty()
            || scoping.symbol_name(symbol) == name
        {
            continue;
        }
        usages.used_names.insert(name.clone());
        let span = scoping.symbol_span(symbol);
        edits.push((span.start as usize, span.end as usize, name.clone()));
        for reference in usages.references.get(&symbol).into_iter().flatten() {
            edits.push((
                reference.start as usize,
                reference.end as usize,
                name.clone(),
            ));
        }
        count += 1;
    }
    if count == 0 {
        return None;
    }
    edits.sort_by_key(|item| std::cmp::Reverse(item.0));
    let mut result = source.to_string();
    let mut end = source.len();
    for (start, stop, new_name) in edits {
        if start > stop || stop > end || source.get(start..stop).is_none() {
            return None;
        }
        result.replace_range(start..stop, &new_name);
        end = start;
    }
    Some((result, count))
}

/// Readability-only transformation: original executable deobfuscation output
/// remains untouched. Exact parsed lexical bindings, not textual substitution.
pub fn recover_readable_names(source: &str) -> Option<(String, usize)> {
    for source_type in [SourceType::mjs(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, source_type);
        if parsed.is_clean() {
            if let Some((renamed, count)) = rename_in_program(source, &parsed.program) {
                // Reject invalid edits or newly introduced binding collisions.
                // This is a presentation-only view, but its source still needs
                // to parse and resolve consistently for real analysts.
                let verify_allocator = Allocator::default();
                let verified = parse_program(&verify_allocator, &renamed, source_type);
                if verified.is_clean()
                    && SemanticBuilder::new()
                        .with_check_syntax_error(true)
                        .build(&verified.program)
                        .diagnostics
                        .is_empty()
                {
                    return Some((renamed, count));
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::recover_readable_names;

    fn named(source: &str) -> String {
        recover_readable_names(source)
            .map(|(text, _)| text)
            .unwrap_or_else(|| source.to_string())
    }

    #[test]
    fn recovers_component_names_through_nested_factory_wrappers_and_exports() -> anyhow::Result<()>
    {
        let input = r#"
const define = input => input;
const withScope = (input, metadata) => input;
var jr = withScope(define({__name: `VPBackdrop`, setup() {return jr;}}), ["scope"]);
var v = define({__name: "Footer"});
export {jr as t, v as k};
"#;
        let (out, renamed) = recover_readable_names(input)
            .ok_or_else(|| anyhow::anyhow!("no descriptive names recovered"))?;
        assert_eq!(renamed, 2);
        assert!(out.contains("var VPBackdrop = withScope("), "{out}");
        assert!(out.contains("return VPBackdrop;"), "{out}");
        assert!(out.contains("var Footer = define("), "{out}");
        assert!(
            out.contains("export {VPBackdrop as t, Footer as k}"),
            "{out}"
        );
        assert!(out.contains("__name: `VPBackdrop`"));
        assert!(out.contains("__name: \"Footer\""));
        Ok(())
    }

    #[test]
    fn uses_lexical_binding_identity_without_renaming_shadowed_references() {
        let source = r#"
var v = make({__name: "Footer"});
function example(v) {return v;}
export {v as t};
"#;
        let out = named(source);
        assert!(out.contains("var Footer = make"), "{out}");
        assert!(out.contains("function example(v) {return v;}"), "{out}");
        assert!(out.contains("export {Footer as t}"), "{out}");
    }

    #[test]
    fn preserves_shorthand_export_names_and_all_existing_binding_names() {
        for source in [
            "var v = make({__name:'Footer'}); const obj = {v};",
            "var v = make({__name:'Footer'}); export {v};",
            "var v = make({__name:'Footer'}); const Footer = 1;",
            "var v = make({__name:'Footer'}); function f(Footer){ return v + Footer; }",
            "var v = make({__name:'Footer'}); returnMe(Footer);",
            "var v = make({__name:'Footer'}); var v; consume(v);",
        ] {
            assert_eq!(named(source), source, "{source}");
        }
    }

    #[test]
    fn rejects_computed_or_dynamic_metadata_and_dynamic_scope() {
        for source in [
            "var v = make({__name: getName()});",
            "var v = make({['__name']: 'Footer'});",
            "var v = make({__name: 'not an identifier'});",
            "var v = make({__name: 'footer'});",
            "var v = make({__name:'Footer'}); eval('v');",
            "var v = make({__name:'Footer'}); with(obj){v;}",
        ] {
            assert_eq!(named(source), source, "{source}");
        }
    }

    #[test]
    fn source_with_duplicate_descriptive_metadata_names_only_renames_one() {
        let input = "var a = make({__name:'Footer'}), b=make({__name:'Footer'}); consume(a, b);";
        let out = named(input);
        assert!(out.contains("var Footer = make"), "{out}");
        assert!(out.contains("b=make"), "{out}");
        assert!(out.contains("consume(Footer, b)"), "{out}");
    }
}
