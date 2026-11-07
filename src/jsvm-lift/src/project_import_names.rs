//! Link exported component identities across the **captured** ESM graph.
//! This only rewrites local bindings in `src/_readable/` and never changes
//! import specifiers, public ESM export names, or exact deobfuscated sources.
use crate::{
    analysis_artifacts::{load_artifact, DEOBFUSCATION, JS_REFERENCES, SOURCE_INDEX},
    readable_names::{recover_readable_names_with_imports, ImportedNames},
};
use anyhow::{Context, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, Declaration, ExportDefaultDeclarationKind, ImportDeclarationSpecifier,
    ModuleExportName, Statement,
};
use oxc_span::SourceType;
use oxc_syntax::{identifier, keyword};
use rolldown_redox::ecmascript::parse_program;
use serde_json::Value;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path},
};

type Exports = BTreeMap<String, String>;

#[derive(Default)]
struct ModuleExports {
    // Public export key -> local lexical binding name.
    local: Vec<(String, String)>,
    // Public export key -> (module specifier, upstream public export key).
    named_reexports: Vec<(String, String, String)>,
    // Ordinary `export * from` statements, excluding default and conflicts.
    star_reexports: Vec<String>,
    // Local imported binding name -> (module specifier, upstream export key).
    imported_bindings: BTreeMap<String, (String, String)>,
}

struct SourceModule {
    readable_path: String,
    source: String,
    refs: BTreeMap<String, Option<String>>,
    exports: ModuleExports,
}

fn field<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

fn exported_key(name: &ModuleExportName<'_>) -> Option<String> {
    match name {
        ModuleExportName::IdentifierName(id) => Some(id.name.to_string()),
        ModuleExportName::IdentifierReference(id) => Some(id.name.to_string()),
        ModuleExportName::StringLiteral(id) => id.value.as_str().map(str::to_owned),
    }
}

fn usable_name(name: &str) -> bool {
    // Names originate from explicit ESM source identifiers and export keys:
    // camelCase, snake_case, PascalCase and __pageData are equally informative.
    // Do not propagate one- or two-letter minifier aliases as semantic names.
    name.chars().filter(|ch| ch.is_alphabetic()).count() >= 4
        && identifier::is_identifier_name(name)
        && !keyword::is_reserved_keyword(name)
}

fn parse_exports(source: &str) -> Option<ModuleExports> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::mjs());
    if !parsed.is_clean() {
        return None;
    }
    let mut exports = ModuleExports::default();
    for stmt in &parsed.program.body {
        match stmt {
            Statement::ImportDeclaration(import) => {
                let source = import.source.value.as_str()?.to_owned();
                for specifier in import.specifiers.iter().flatten() {
                    match specifier {
                        ImportDeclarationSpecifier::ImportSpecifier(named) => {
                            if let Some(key) = exported_key(&named.imported) {
                                exports
                                    .imported_bindings
                                    .insert(named.local.name.to_string(), (source.clone(), key));
                            }
                        }
                        ImportDeclarationSpecifier::ImportDefaultSpecifier(default) => {
                            exports.imported_bindings.insert(
                                default.local.name.to_string(),
                                (source.clone(), "default".to_owned()),
                            );
                        }
                        ImportDeclarationSpecifier::ImportNamespaceSpecifier(_) => {}
                    }
                }
            }
            Statement::ExportNamedDeclaration(named) => {
                for specifier in &named.specifiers {
                    if let (Some(local), Some(public)) = (
                        exported_key(&specifier.local),
                        exported_key(&specifier.exported),
                    ) {
                        exports.local.push((public, local));
                    }
                }
            }
            Statement::ExportFromDeclaration(named) => {
                let source = named.source.value.as_str()?.to_owned();
                for specifier in &named.specifiers {
                    if let (Some(local), Some(public)) = (
                        exported_key(&specifier.local),
                        exported_key(&specifier.exported),
                    ) {
                        exports
                            .named_reexports
                            .push((public, source.clone(), local));
                    }
                }
            }
            Statement::ExportAllDeclaration(star) if star.exported.is_none() => {
                exports
                    .star_reexports
                    .push(star.source.value.as_str()?.to_owned());
            }
            Statement::ExportDeclaration(declaration) => match &declaration.declaration {
                Declaration::VariableDeclaration(vars) => {
                    for declarator in &vars.declarations {
                        if let BindingPattern::BindingIdentifier(id) = &declarator.id {
                            let name = id.name.to_string();
                            exports.local.push((name.clone(), name));
                        }
                    }
                }
                Declaration::FunctionDeclaration(function) => {
                    if let Some(id) = &function.id {
                        let name = id.name.to_string();
                        exports.local.push((name.clone(), name));
                    }
                }
                Declaration::ClassDeclaration(class) => {
                    if let Some(id) = &class.id {
                        let name = id.name.to_string();
                        exports.local.push((name.clone(), name));
                    }
                }
                _ => {}
            },
            Statement::ExportDefaultDeclaration(default) => match &default.declaration {
                ExportDefaultDeclarationKind::Identifier(id) => {
                    exports
                        .local
                        .push(("default".to_owned(), id.name.to_string()));
                }
                ExportDefaultDeclarationKind::FunctionDeclaration(function) => {
                    if let Some(id) = &function.id {
                        exports
                            .local
                            .push(("default".to_owned(), id.name.to_string()));
                    }
                }
                ExportDefaultDeclarationKind::ClassDeclaration(class) => {
                    if let Some(id) = &class.id {
                        exports
                            .local
                            .push(("default".to_owned(), id.name.to_string()));
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
    Some(exports)
}

fn target<'a>(
    modules: &'a BTreeMap<String, SourceModule>,
    module: &'a SourceModule,
    specifier: &str,
) -> Option<&'a str> {
    let url = module.refs.get(specifier)?.as_deref()?;
    modules.contains_key(url).then_some(url)
}

/// Fixed point over captured ESM: follow explicitly named exports, imported
/// aliases, barrels and `export *` without guessing names or module URLs.
/// Named exports override star exports. Ambiguous star names are suppressed.
fn exported_names(modules: &BTreeMap<String, SourceModule>) -> BTreeMap<String, Exports> {
    let mut known = BTreeMap::<String, Exports>::new();
    let mut iterations = 0_usize;
    loop {
        let mut next = BTreeMap::new();
        for (url, module) in modules {
            let mut entries = Exports::new();
            for (public, local) in &module.exports.local {
                // Preserve the original declaration identity across imports
                // and barrels. Only fall back to the public API label when
                // the originating local/forwarded name is minified or unknown.
                // This avoids turning an actual Footer component into a
                // generic name such as forwarded.
                let inferred = if usable_name(local) {
                    Some(local.clone())
                } else {
                    module
                        .exports
                        .imported_bindings
                        .get(local)
                        .and_then(|(spec, public)| {
                            known
                                .get(target(modules, module, spec)?)?
                                .get(public)
                                .cloned()
                        })
                };
                if let Some(name) = inferred.or_else(|| {
                    (public != "default" && usable_name(public)).then(|| public.clone())
                }) {
                    entries.insert(public.clone(), name);
                }
            }
            for (public, spec, imported) in &module.exports.named_reexports {
                if let Some(name) = target(modules, module, spec)
                    .and_then(|upstream| known.get(upstream))
                    .and_then(|exports| exports.get(imported))
                {
                    entries.insert(public.clone(), name.clone());
                }
            }
            // An exported name appearing in multiple star providers is
            // ambiguous even if the two bindings happen to share a label.
            let explicit = module
                .exports
                .local
                .iter()
                .map(|(key, _)| key.as_str())
                .chain(
                    module
                        .exports
                        .named_reexports
                        .iter()
                        .map(|(key, _, _)| key.as_str()),
                )
                .collect::<BTreeSet<_>>();
            let mut stars = BTreeMap::<String, Option<String>>::new();
            for spec in &module.exports.star_reexports {
                let Some(exported) = target(modules, module, spec).and_then(|url| known.get(url))
                else {
                    continue;
                };
                for (key, name) in exported {
                    if key == "default" || explicit.contains(key.as_str()) {
                        continue;
                    }
                    use std::collections::btree_map::Entry;
                    match stars.entry(key.clone()) {
                        Entry::Vacant(entry) => {
                            entry.insert(Some(name.clone()));
                        }
                        Entry::Occupied(mut entry) => {
                            entry.insert(None);
                        }
                    }
                }
            }
            for (key, value) in stars {
                if let Some(name) = value {
                    entries.entry(key).or_insert(name);
                }
            }
            next.insert(url.clone(), entries);
        }
        if next == known {
            return known;
        }
        known = next;
        iterations += 1;
        // There are only finitely many captured modules and exported names;
        // this limit also bounds cyclic re-export graphs and bad captures.
        if iterations > modules.len().saturating_mul(2).saturating_add(2) {
            return known;
        }
    }
}

fn safe_readable_path(path: &str) -> bool {
    let path = Path::new(path);
    path.starts_with("src/_readable")
        && path
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
}

/// Make downstream imports use descriptive component names in the readable
/// view only. The existing module resolution artifact is authoritative.
pub(crate) fn propagate_imported_names(project: &Path) -> Result<usize> {
    let Some(refs) = load_artifact(project, JS_REFERENCES, true)? else {
        return Ok(0);
    };
    let Some(deob) = load_artifact(project, DEOBFUSCATION, true)? else {
        return Ok(0);
    };
    let Some(source_index) = load_artifact(project, SOURCE_INDEX, true)? else {
        return Ok(0);
    };
    let mut urls = BTreeMap::<String, Option<String>>::new();
    for unit in source_index["units"].as_array().into_iter().flatten() {
        if field(unit, "kind") != Some("javascript") {
            continue;
        }
        if let (Some(url), Some(raw)) = (field(unit, "url"), field(unit, "raw_path")) {
            use std::collections::btree_map::Entry;
            match urls.entry(url.to_owned()) {
                Entry::Vacant(entry) => {
                    entry.insert(Some(raw.to_owned()));
                }
                Entry::Occupied(mut entry) => {
                    entry.insert(None);
                }
            }
        }
    }
    let mut by_raw = BTreeMap::<String, (String, String)>::new();
    for unit in deob["units"].as_array().into_iter().flatten() {
        if let (Some(raw), Some(readable)) =
            (field(unit, "raw_path"), field(unit, "readable_output_path"))
        {
            if safe_readable_path(readable) && project.join(readable).is_file() {
                by_raw.insert(
                    raw.to_owned(),
                    (
                        readable.to_owned(),
                        fs::read_to_string(project.join(readable))?,
                    ),
                );
            }
        }
    }
    let mut resolutions = BTreeMap::<String, BTreeMap<String, Option<String>>>::new();
    for unit in refs["code_units"].as_array().into_iter().flatten() {
        let Some(raw) = field(unit, "raw_path") else {
            continue;
        };
        let map = resolutions.entry(raw.to_owned()).or_default();
        for reference in unit["references"].as_array().into_iter().flatten() {
            let (Some(spec), Some(url)) = (
                field(reference, "specifier"),
                field(reference, "resolved_url"),
            ) else {
                continue;
            };
            use std::collections::btree_map::Entry;
            match map.entry(spec.to_owned()) {
                Entry::Vacant(entry) => {
                    entry.insert(Some(url.to_owned()));
                }
                Entry::Occupied(mut entry) => {
                    if entry.get().as_deref() != Some(url) {
                        entry.insert(None);
                    }
                }
            }
        }
    }
    let mut modules = BTreeMap::<String, SourceModule>::new();
    for (url, raw) in urls {
        let Some(raw) = raw else { continue };
        let Some((readable_path, source)) = by_raw.get(&raw) else {
            continue;
        };
        let Some(exports) = parse_exports(source) else {
            continue;
        };
        modules.insert(
            url.clone(),
            SourceModule {
                readable_path: readable_path.clone(),
                source: source.clone(),
                refs: resolutions.remove(&raw).unwrap_or_default(),
                exports,
            },
        );
    }
    let known = exported_names(&modules);
    let mut count = 0;
    for module in modules.values() {
        let mut names = ImportedNames::new();
        for (spec, target_url) in &module.refs {
            let Some(exports) = target_url.as_deref().and_then(|url| known.get(url)) else {
                continue;
            };
            if !exports.is_empty() {
                names.insert(spec.clone(), exports.clone());
            }
        }
        if names.is_empty() {
            continue;
        }
        if let Some((named, renamed)) =
            recover_readable_names_with_imports(&module.source, Some(&names))
        {
            let path = project.join(&module.readable_path);
            let parent = path
                .parent()
                .context("readable source has no parent folder")?;
            let temp = tempfile::NamedTempFile::new_in(parent)?;
            fs::write(temp.path(), named)?;
            // project_deob hard-links identical outputs to a shared cache.
            // Replace just this source file's inode; do not mutate siblings.
            temp.persist(&path)
                .with_context(|| format!("replacing named presentation file {}", path.display()))?;
            count += renamed;
        }
    }
    Ok(count)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis_artifacts::{write_artifact, DEOBFUSCATION, JS_REFERENCES, SOURCE_INDEX};
    use serde_json::json;

    #[test]
    fn propagates_component_names_through_reexports_and_star_barrels() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path();
        let files = [
            (
                "Footer.js",
                "const Footer={label:'Footer'}; export {Footer as t}; export default Footer;",
            ),
            ("Barrel.js", "export {t as u} from './Footer.js';"),
            ("Star.js", "export * from './Barrel.js';"),
            (
                "Aliased.js",
                "import {t as b} from './Footer.js'; export {b as forwarded};",
            ),
            (
                "consumer.js",
                "import {forwarded as z} from './Aliased.js'; use(z);",
            ),
            ("Other.js", "const Different = {}; export {Different as u};"),
            (
                "Conflicted.js",
                "export * from './Star.js'; export * from './Other.js';",
            ),
            (
                "index.js",
                "import {u as b} from './Star.js'; const obj={b}; export {b}; console.log(b);",
            ),
            ("shorthand.js", "import {t} from './Footer.js'; use(t);"),
            ("default.js", "import x from './Footer.js'; use(x);"),
            (
                "conflict.js",
                "import {u as b} from './Conflicted.js'; consume(b);",
            ),
            (
                "collision.js",
                "import {u as b} from './Star.js'; const Footer = 1; consume(b);",
            ),
            (
                "PublicApi.js",
                "const z=()=>7; export {z as createApp};",
            ),
            (
                "ApiBarrel.js",
                "export {createApp as createApplication} from './PublicApi.js';",
            ),
            (
                "ApiConsumer.js",
                "import {createApplication as q} from './ApiBarrel.js'; console.log(q());",
            ),
            (
                "DirectApiConsumer.js",
                "import {createApp as q} from './PublicApi.js'; console.log(q());",
            ),
            (
                "ApiCollision.js",
                "import {createApplication as q} from './ApiBarrel.js'; const createApp=1; console.log(q());",
            ),
            (
                "DescriptiveLocal.js",
                "const decodeResponse=(data)=>data; export {decodeResponse as r};",
            ),
            (
                "LocalConsumer.js",
                "import {r as q} from './DescriptiveLocal.js'; use(q);",
            ),
        ];
        let refs = [
            ("Barrel.js", "./Footer.js", "reexport_named", "Footer.js"),
            ("Star.js", "./Barrel.js", "reexport_all", "Barrel.js"),
            ("Aliased.js", "./Footer.js", "import_static", "Footer.js"),
            ("consumer.js", "./Aliased.js", "import_static", "Aliased.js"),
            ("Conflicted.js", "./Star.js", "reexport_all", "Star.js"),
            ("Conflicted.js", "./Other.js", "reexport_all", "Other.js"),
            ("index.js", "./Star.js", "import_static", "Star.js"),
            ("shorthand.js", "./Footer.js", "import_static", "Footer.js"),
            ("default.js", "./Footer.js", "import_static", "Footer.js"),
            (
                "conflict.js",
                "./Conflicted.js",
                "import_static",
                "Conflicted.js",
            ),
            ("collision.js", "./Star.js", "import_static", "Star.js"),
            (
                "ApiBarrel.js",
                "./PublicApi.js",
                "reexport_named",
                "PublicApi.js",
            ),
            (
                "ApiConsumer.js",
                "./ApiBarrel.js",
                "import_static",
                "ApiBarrel.js",
            ),
            (
                "DirectApiConsumer.js",
                "./PublicApi.js",
                "import_static",
                "PublicApi.js",
            ),
            (
                "ApiCollision.js",
                "./ApiBarrel.js",
                "import_static",
                "ApiBarrel.js",
            ),
            (
                "LocalConsumer.js",
                "./DescriptiveLocal.js",
                "import_static",
                "DescriptiveLocal.js",
            ),
        ];
        let mut source_units = Vec::new();
        let mut deob_units = Vec::new();
        let mut ref_units = Vec::new();
        for (name, source) in files {
            let raw = format!("resources/{name}");
            let readable = format!("src/_readable/{name}");
            let deob = format!("src/_deobfuscated/{name}");
            fs::create_dir_all(project.join("src/_readable"))?;
            fs::create_dir_all(project.join("src/_deobfuscated"))?;
            fs::write(project.join(&readable), source)?;
            fs::write(project.join(&deob), source)?;
            source_units.push(json!({
                "kind":"javascript", "raw_path":raw, "url":format!("https://fixture.test/{name}"),
                "source_path":format!("src/{name}"),
            }));
            deob_units
                .push(json!({"raw_path":raw,"readable_output_path":readable,"output_path":deob}));
            ref_units.push(json!({
                "raw_path":raw,
                "references":refs.iter().filter(|(unit,_,_,_)| *unit==name).map(|(_,specifier,kind,to)| json!({
                    "specifier":specifier,"kind":kind,
                    "resolved_url":format!("https://fixture.test/{to}"),
                })).collect::<Vec<_>>(),
            }));
        }
        // Capture deob's real shared-formatting-cache hardlink semantics.
        let shared_cache = project.join("shared-readable-cache.js");
        fs::hard_link(project.join("src/_readable/index.js"), &shared_cache)?;
        write_artifact(
            project,
            SOURCE_INDEX,
            &json!({
                "schema":SOURCE_INDEX.schema,"units":source_units,"summary":{}
            }),
        )?;
        write_artifact(
            project,
            DEOBFUSCATION,
            &json!({
                "schema":DEOBFUSCATION.schema,"units":deob_units,"summary":{}
            }),
        )?;
        write_artifact(
            project,
            JS_REFERENCES,
            &json!({
                "schema":JS_REFERENCES.schema,"code_units":ref_units,"summary":{}
            }),
        )?;
        assert_eq!(propagate_imported_names(project)?, 8);
        let index = fs::read_to_string(project.join("src/_readable/index.js"))?;
        assert!(index.contains("import {u as Footer}"), "{index}");
        assert!(index.contains("const obj={b: Footer}"), "{index}");
        assert!(index.contains("export {Footer as b}"), "{index}");
        assert!(index.contains("console.log(Footer)"), "{index}");
        let direct = fs::read_to_string(project.join("src/_readable/shorthand.js"))?;
        assert!(direct.contains("import {t as Footer}"), "{direct}");
        let default = fs::read_to_string(project.join("src/_readable/default.js"))?;
        assert!(default.contains("import Footer from"), "{default}");
        let aliased = fs::read_to_string(project.join("src/_readable/Aliased.js"))?;
        assert!(aliased.contains("import {t as Footer}"), "{aliased}");
        assert!(
            aliased.contains("export {Footer as forwarded}"),
            "{aliased}"
        );
        let consumer = fs::read_to_string(project.join("src/_readable/consumer.js"))?;
        assert!(
            consumer.contains("import {forwarded as Footer}"),
            "{consumer}"
        );
        assert!(consumer.contains("use(Footer)"), "{consumer}");
        let ambiguous = fs::read_to_string(project.join("src/_readable/conflict.js"))?;
        assert!(ambiguous.contains("import {u as b}"), "{ambiguous}");
        let collision = fs::read_to_string(project.join("src/_readable/collision.js"))?;
        assert!(collision.contains("import {u as b}"), "{collision}");
        assert_eq!(
            fs::read_to_string(&shared_cache)?,
            files[7].1,
            "cross-module naming mutated the deduplicated formatter cache"
        );
        let consumer = fs::read_to_string(project.join("src/_readable/ApiConsumer.js"))?;
        assert!(
            consumer.contains("import {createApplication as createApp}"),
            "{consumer}"
        );
        assert!(consumer.contains("console.log(createApp())"), "{consumer}");
        let direct = fs::read_to_string(project.join("src/_readable/DirectApiConsumer.js"))?;
        assert!(
            direct.contains("import {createApp as createApp}"),
            "{direct}"
        );
        assert!(direct.contains("console.log(createApp())"), "{direct}");
        let local = fs::read_to_string(project.join("src/_readable/LocalConsumer.js"))?;
        assert!(local.contains("import {r as decodeResponse}"), "{local}");
        assert!(local.contains("use(decodeResponse)"), "{local}");
        let collision = fs::read_to_string(project.join("src/_readable/ApiCollision.js"))?;
        assert!(
            collision.contains("import {createApplication as q}"),
            "{collision}"
        );
        assert!(collision.contains("console.log(q())"), "{collision}");
        // Only `_readable` is rewritten; source bytes used for safe analysis are not.
        let exact = fs::read_to_string(project.join("src/_deobfuscated/index.js"))?;
        assert_eq!(exact, files[7].1);
        // Idempotence of the presentation pass, even for import shorthand.
        assert_eq!(propagate_imported_names(project)?, 0);
        Ok(())
    }
}
