//! Restore descriptive lexical names from explicit metadata embedded in bundled
//! JavaScript. This is ONLY a presentation transform for `src/_readable/`.
//! `src/_deobfuscated/` keeps the semantics-preserving original names.
use jsvm_safe_core::{eval_static_primitive, statically_resolved_symbol, StaticPrimitiveValue};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, BindingProperty, CallExpression, Expression, IdentifierReference,
    ImportDeclaration, ImportDeclarationSpecifier, ObjectProperty, ObjectPropertyKind, Program,
    VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{identifier, keyword, symbol::SymbolId};
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

fn meaningful_property_name(name: &str) -> bool {
    // Even short public keys such as `id` and `url` are useful knowledge.
    // JS IdentifierName allows reserved words that cannot be bindings, so
    // exclude those before proposing any source edit.
    name.chars().count() >= 2
        && !name.starts_with('_')
        && name != "eval"
        && name != "arguments"
        && !keyword::is_reserved_keyword(name)
        && identifier::is_identifier_name(name)
}

fn minified_binding(name: &str) -> bool {
    // Keep existing human names. This pass should improve minified lexical
    // aliases, not rename an intentionally descriptive local variable.
    name.len() <= 3
}

/// Recover a descriptive local alias from a property chain already present in
/// the original source, without relying on a builtin whitelist or call traces.
fn member_path(expression: &Expression<'_>) -> Option<Vec<String>> {
    match expression {
        Expression::Identifier(id) => Some(vec![id.name.to_string()]),
        Expression::ParenthesizedExpression(parenthesized) => {
            member_path(&parenthesized.expression)
        }
        Expression::StaticMemberExpression(member) => {
            let mut path = member_path(&member.object)?;
            path.push(member.property.name.to_string());
            Some(path)
        }
        Expression::ComputedMemberExpression(member) => {
            let mut path = member_path(&member.object)?;
            let Expression::StringLiteral(property) = &member.expression else {
                return None;
            };
            path.push(property.value.as_str()?.to_owned());
            Some(path)
        }
        _ => None,
    }
}

fn name_from_member_alias(expression: &Expression<'_>) -> Option<String> {
    let path = member_path(expression)?;
    let (root, properties) = path.split_first()?;
    if properties.is_empty()
        || !identifier::is_identifier_name(root)
        || !(root.len() >= 4 || root.len() >= 2 && root.chars().all(|c| c.is_ascii_uppercase()))
        || !properties
            .iter()
            .all(|name| name.chars().count() >= 2 && identifier::is_identifier_name(name))
    {
        return None;
    }
    let mut name = if root.chars().all(|ch| ch.is_ascii_uppercase()) {
        root.to_ascii_lowercase()
    } else {
        let mut chars = root.chars();
        let first = chars.next()?;
        format!("{}{}", first.to_ascii_lowercase(), chars.as_str())
    };
    for property in properties {
        let mut letters = property.chars();
        let first = letters.next()?;
        name.push(first.to_ascii_uppercase());
        name.extend(letters);
        if name.len() > 80 {
            return None;
        }
    }
    identifier::is_identifier_name(&name).then_some(name)
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
            if let Some(symbol) = binding.symbol_id.get() {
                let metadata = name_from_initializer(initializer, 4);
                let member = minified_binding(&binding.name)
                    .then(|| name_from_member_alias(initializer))
                    .flatten();
                if let Some(name) = metadata.or(member) {
                    self.by_symbol.insert(symbol, name);
                }
            }
        }
        walk::walk_variable_declarator(self, declarator);
    }

    fn visit_binding_property(&mut self, property: &BindingProperty<'a>) {
        if !property.shorthand {
            if let Some(name) = property
                .key
                .static_name()
                .and_then(|key| key.into_cow_str())
            {
                let name = name.into_owned();
                if meaningful_property_name(&name) {
                    let binding = match &property.value {
                        BindingPattern::BindingIdentifier(id) => Some(id.as_ref()),
                        BindingPattern::AssignmentPattern(default) => {
                            if let BindingPattern::BindingIdentifier(id) = &default.left {
                                Some(id.as_ref())
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    if let Some(binding) = binding {
                        if minified_binding(&binding.name)
                            && name.chars().count() > binding.name.chars().count()
                        {
                            if let Some(symbol) = binding.symbol_id.get() {
                                self.by_symbol.insert(symbol, name);
                            }
                        }
                    }
                }
            }
        }
        walk::walk_binding_property(self, property);
    }
}

/// Descriptive ESM names by resolved source specifier and public export name.
/// The public ESM import/export name is never altered by presentation renaming.
pub type ImportedNames = BTreeMap<String, BTreeMap<String, String>>;

struct ImportedNameCandidates<'s> {
    names: &'s ImportedNames,
    candidates: BTreeMap<SymbolId, String>,
}

impl<'a> Visit<'a> for ImportedNameCandidates<'_> {
    fn visit_import_declaration(&mut self, import: &ImportDeclaration<'a>) {
        let Some(source) = import.source.value.as_str() else {
            return;
        };
        let Some(exports) = self.names.get(source) else {
            return;
        };
        for specifier in import.specifiers.iter().flatten() {
            match specifier {
                ImportDeclarationSpecifier::ImportSpecifier(specifier) => {
                    let exported = match &specifier.imported {
                        oxc_ast::ast::ModuleExportName::IdentifierName(id) => id.name.as_str(),
                        oxc_ast::ast::ModuleExportName::StringLiteral(id) => {
                            let Some(value) = id.value.as_str() else {
                                continue;
                            };
                            value
                        }
                        oxc_ast::ast::ModuleExportName::IdentifierReference(id) => id.name.as_str(),
                    };
                    if let (Some(name), Some(symbol)) =
                        (exports.get(exported), specifier.local.symbol_id.get())
                    {
                        self.candidates.insert(symbol, name.clone());
                    }
                }
                ImportDeclarationSpecifier::ImportDefaultSpecifier(specifier) => {
                    if let (Some(name), Some(symbol)) =
                        (exports.get("default"), specifier.local.symbol_id.get())
                    {
                        self.candidates.insert(symbol, name.clone());
                    }
                }
                ImportDeclarationSpecifier::ImportNamespaceSpecifier(_) => {
                    // A namespace represents all exports, not one named binding.
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
enum SyntaxAlias {
    Object(String),
    Export(String),
    Import(String),
}

#[derive(Default)]
struct NameUsages {
    used_names: BTreeSet<String>,
    references: BTreeMap<SymbolId, Vec<Span>>,
    special_references: BTreeMap<(u32, u32), SyntaxAlias>,
    special_bindings: BTreeMap<SymbolId, SyntaxAlias>,
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
                if id.name == "eval" {
                    self.usages.dynamic_scope = true;
                }
                if let Some(symbol) = id
                    .reference_id
                    .get()
                    .and_then(|r| statically_resolved_symbol(self.scoping, r))
                {
                    self.usages.special_references.insert(
                        (id.span.start, id.span.end),
                        SyntaxAlias::Object(id.name.to_string()),
                    );
                    self.usages
                        .references
                        .entry(symbol)
                        .or_default()
                        .push(id.span);
                    self.usages.used_names.insert(id.name.to_string());
                    // The key and value share the same source span. Do not
                    // traverse again: the new text expands `foo` to `foo: Bar`.
                    return;
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
                    self.usages.special_references.insert(
                        (id.span.start, id.span.end),
                        SyntaxAlias::Export(id.name.to_string()),
                    );
                    self.usages
                        .references
                        .entry(symbol)
                        .or_default()
                        .push(id.span);
                    self.usages.used_names.insert(id.name.to_string());
                    return;
                }
            }
        }
        walk::walk_export_specifier(self, specifier);
    }
    fn visit_import_specifier(&mut self, specifier: &oxc_ast::ast::ImportSpecifier<'a>) {
        if specifier.imported.span() == specifier.local.span {
            if let Some(symbol) = specifier.local.symbol_id.get() {
                self.usages.special_bindings.insert(
                    symbol,
                    SyntaxAlias::Import(specifier.local.name.to_string()),
                );
            }
        }
        walk::walk_import_specifier(self, specifier);
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

fn rename_in_program(
    source: &str,
    program: &Program<'_>,
    imports: Option<&ImportedNames>,
) -> Option<(String, usize)> {
    let semantic = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(program);
    if !semantic.diagnostics.is_empty() {
        return None;
    }
    let scoping = semantic.semantic.scoping();
    let mut candidates = NameCandidates::default();
    candidates.visit_program(program);
    if let Some(imports) = imports {
        let mut imported = ImportedNameCandidates {
            names: imports,
            candidates: BTreeMap::new(),
        };
        imported.visit_program(program);
        candidates.by_symbol.extend(imported.candidates);
    }
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
            || !scoping.symbol_redeclarations(symbol).is_empty()
            || scoping.symbol_name(symbol) == name
        {
            continue;
        }
        usages.used_names.insert(name.clone());
        let span = scoping.symbol_span(symbol);
        let binding_text = match usages.special_bindings.get(&symbol) {
            Some(SyntaxAlias::Import(original)) => format!("{original} as {name}"),
            _ => name.clone(),
        };
        edits.push((span.start as usize, span.end as usize, binding_text));
        for reference in usages.references.get(&symbol).into_iter().flatten() {
            let text = match usages
                .special_references
                .get(&(reference.start, reference.end))
            {
                Some(SyntaxAlias::Object(key)) => format!("{key}: {name}"),
                Some(SyntaxAlias::Export(exported)) => {
                    format!("{name} as {exported}")
                }
                _ => name.clone(),
            };
            edits.push((reference.start as usize, reference.end as usize, text));
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
    recover_readable_names_with_imports(source, None)
}

/// Recover component names imported from captured ESM modules. The caller
/// supplies exact specifier-to-export mappings resolved by the project graph.
/// Public ESM export names and import paths remain exactly as captured.
pub fn recover_readable_names_with_imports(
    source: &str,
    imports: Option<&ImportedNames>,
) -> Option<(String, usize)> {
    for source_type in [SourceType::mjs(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, source_type);
        if parsed.is_clean() {
            if let Some((renamed, count)) = rename_in_program(source, &parsed.program, imports) {
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
    fn recovers_descriptive_object_destructuring_aliases() {
        let source = r#"
let {footerBg: v, buttonLink: b = '/guide', internal: {deepValue: x}} = load();
function render({pageTitle: t}) { return [v, b, x, t]; }
export {v as oldFooterBg};
"#;
        let out = named(source);
        assert!(out.contains("footerBg: footerBg"), "{out}");
        assert!(out.contains("buttonLink: buttonLink = '/guide'"), "{out}");
        assert!(out.contains("deepValue: deepValue"), "{out}");
        assert!(out.contains("pageTitle: pageTitle"), "{out}");
        assert!(
            out.contains("return [footerBg, buttonLink, deepValue, pageTitle]"),
            "{out}"
        );
        assert!(out.contains("export {footerBg as oldFooterBg}"), "{out}");
    }

    #[test]
    fn recovers_explicit_member_alias_identifiers() {
        let source = r#"
var R = Object.create, z = Object.defineProperty;
const a = Object.prototype.hasOwnProperty, b = Math.min, c = JSON.parse;
export {R as create, z as define, a as hasOwn};
console.log(R, z, a, b, c);
"#;
        let out = named(source);
        for part in [
            "objectCreate = Object.create",
            "objectDefineProperty = Object.defineProperty",
            "objectPrototypeHasOwnProperty = Object.prototype.hasOwnProperty",
            "mathMin = Math.min",
            "jsonParse = JSON.parse",
            "export {objectCreate as create, objectDefineProperty as define, objectPrototypeHasOwnProperty as hasOwn}",
            "console.log(objectCreate, objectDefineProperty, objectPrototypeHasOwnProperty, mathMin, jsonParse)",
        ] {
            assert!(out.contains(part), "expected {part} in {out}");
        }
    }

    #[test]
    fn preserves_dynamic_computed_accesses_and_existing_descriptive_names() {
        let source = r#"
const {footerBg: originalDescriptiveName, [key]: v} = load();
const a = Object[key], b = obj.render, c = service["createClient"], d = URL.createObjectURL;
const objectCreate = 7;
const e = Object.create;
console.log(a,b,c,d,e);
"#;
        let out = named(source);
        assert!(out.contains("footerBg: originalDescriptiveName"), "{out}");
        assert!(out.contains("[key]: v"), "{out}");
        assert!(out.contains("a = Object[key]"), "{out}");
        assert!(out.contains("b = obj.render"), "{out}");
        assert!(
            out.contains(r#"serviceCreateClient = service["createClient"]"#),
            "{out}"
        );
        assert!(
            out.contains("urlCreateObjectURL = URL.createObjectURL"),
            "{out}"
        );
        assert!(out.contains("e = Object.create"), "{out}");
    }

    #[test]
    fn recovers_short_public_property_keys_and_computed_literal_destructuring() {
        let input = "const {id:i, url:u, ['userName']: n, [dynamicKey]: v, default:d, eval:e, arguments:a} = request; use(i,u,n,v,d,e,a);";
        let out = named(input);
        assert!(out.contains("id:id"), "{out}");
        assert!(out.contains("url:url"), "{out}");
        assert!(out.contains("['userName']: userName"), "{out}");
        assert!(out.contains("[dynamicKey]: v"), "{out}");
        assert!(out.contains("default:d"), "{out}");
        assert!(out.contains("eval:e"), "{out}");
        assert!(out.contains("arguments:a"), "{out}");
        assert!(out.contains("use(id,url,userName,v,d,e,a)"), "{out}");
    }

    #[test]
    fn renames_destructured_object_shorthand_keys_without_changing_them() {
        let source = "const {longProperty: x} = source; const obj={x}; export {x};";
        let out = named(source);
        assert!(out.contains("{longProperty: longProperty}"), "{out}");
        assert!(out.contains("const obj={x: longProperty}"), "{out}");
        assert!(out.contains("export {longProperty as x}"), "{out}");
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
    fn preserves_object_and_export_public_shorthand_names() {
        let object = "var v = make({__name:'Footer'}); const obj = {v};";
        let transformed = named(object);
        assert!(transformed.contains("var Footer = make"), "{transformed}");
        assert!(
            transformed.contains("const obj = {v: Footer}"),
            "{transformed}"
        );
        let reexport = "var v = make({__name:'Footer'}); export {v};";
        let transformed = named(reexport);
        assert!(
            transformed.contains("export {Footer as v}"),
            "{transformed}"
        );
    }

    #[test]
    fn preserves_existing_names_and_redeclared_symbols() {
        for source in [
            "var v = make({__name:'Footer'}); const Footer = 1;",
            "var v = make({__name:'Footer'}); function f(Footer){ return v + Footer; }",
            "var v = make({__name:'Footer'}); returnMe(Footer);",
            "var v = make({__name:'Footer'}); var v; consume(v);",
        ] {
            assert_eq!(named(source), source, "{source}");
        }
    }

    #[test]
    fn recovers_imported_lexical_names_without_changing_esm_public_names() -> anyhow::Result<()> {
        use super::{recover_readable_names_with_imports, ImportedNames};
        let imported = ImportedNames::from([
            (
                "./Footer.js".into(),
                [
                    ("t".into(), "Footer".into()),
                    ("default".into(), "VPHome".into()),
                ]
                .into(),
            ),
            ("./other.js".into(), [("x".into(), "Other".into())].into()),
        ]);
        let source = r#"
import Page, {t as b} from './Footer.js';
import {x} from './other.js';
function f(b) { return b; }
const obj = {b, x};
export {b, x as yy};
console.log(Page, b, x);
"#;
        let (out, count) = recover_readable_names_with_imports(source, Some(&imported))
            .ok_or_else(|| anyhow::anyhow!("expected imported name recovery"))?;
        assert_eq!(count, 3, "{out}");
        assert!(
            out.contains("import VPHome, {t as Footer} from './Footer.js'"),
            "{out}"
        );
        assert!(
            out.contains("import {x as Other} from './other.js'"),
            "{out}"
        );
        assert!(out.contains("function f(b) { return b; }"), "{out}");
        assert!(out.contains("const obj = {b: Footer, x: Other}"), "{out}");
        assert!(out.contains("export {Footer as b, Other as yy}"), "{out}");
        assert!(out.contains("console.log(VPHome, Footer, Other)"), "{out}");
        Ok(())
    }

    #[test]
    fn skips_collisions_and_namespace_imports() {
        use super::{recover_readable_names_with_imports, ImportedNames};
        let imported = ImportedNames::from([(
            "./x.js".into(),
            [("t".into(), "Footer".into()), ("b".into(), "Footer".into())].into(),
        )]);
        let source =
            "import {t as a, b as c} from './x.js'; import * as ns from './x.js'; consume(a,c,ns);";
        let output = recover_readable_names_with_imports(source, Some(&imported))
            .map_or_else(|| source.to_owned(), |(source, _)| source);
        assert!(output.contains("import {t as Footer, b as c}"), "{output}");
        assert!(output.contains("import * as ns"), "{output}");
        assert!(output.contains("consume(Footer,c,ns)"), "{output}");
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
