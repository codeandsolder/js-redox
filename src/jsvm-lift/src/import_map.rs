//! Shared WHATWG-style import-map parsing and module specifier resolution.
//!
//! Used by both HTTP capture and captured-project reference analysis.
//! Keep import-map matching semantics independent of either pipeline.

use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::BTreeMap;
use url::Url;

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct ImportMap {
    #[serde(default)]
    pub(crate) imports: BTreeMap<String, Option<String>>,
    #[serde(default)]
    pub(crate) scopes: BTreeMap<String, BTreeMap<String, Option<String>>>,
    #[serde(default)]
    pub(crate) integrity: BTreeMap<String, String>,
}

fn absolute_url(value: &str) -> bool {
    Url::parse(value).is_ok_and(|url| !url.scheme().is_empty())
}

pub fn join_url(base: &str, value: &str) -> Option<String> {
    Url::parse(base)
        .ok()?
        .join(value)
        .ok()
        .map(|url| url.to_string())
}

fn url_like(base_url: Option<&str>, specifier: &str) -> Option<String> {
    if specifier.is_empty() {
        return None;
    }
    if let Ok(url) = Url::parse(specifier) {
        return Some(url.to_string());
    }
    if specifier.starts_with("//")
        || specifier.starts_with("./")
        || specifier.starts_with("../")
        || specifier.starts_with('/')
    {
        return join_url(base_url?, specifier);
    }
    None
}

fn normalize_map_key(base_url: &str, key: &str) -> Option<String> {
    (!key.is_empty()).then(|| url_like(Some(base_url), key).unwrap_or_else(|| key.to_owned()))
}

fn normalize_map_address(base_url: &str, value: Option<&Value>) -> Option<String> {
    let value = value?.as_str()?;
    if !(absolute_url(value)
        || value.starts_with("./")
        || value.starts_with("../")
        || value.starts_with('/')
        || value.starts_with("//"))
    {
        return None;
    }
    url_like(Some(base_url), value)
}

fn parse_specifier_map(
    base_url: &str,
    value: Option<&Value>,
    warnings: &mut Vec<String>,
    label: &str,
) -> BTreeMap<String, Option<String>> {
    let Some(object) = value.and_then(Value::as_object) else {
        warnings.push(format!("{label} is not an object"));
        return BTreeMap::new();
    };
    let mut out = BTreeMap::new();
    for (raw_key, raw_value) in object {
        let Some(key) = normalize_map_key(base_url, raw_key) else {
            warnings.push(format!("{label}: ignored empty/invalid key {raw_key:?}"));
            continue;
        };
        let mut address = normalize_map_address(base_url, Some(raw_value));
        if !raw_value.is_null() && address.is_none() {
            warnings.push(format!("{label}: {raw_key:?} has invalid non-URL address"));
        }
        if key.ends_with('/') && address.as_ref().is_some_and(|value| !value.ends_with('/')) {
            warnings.push(format!(
                "{label}: prefix key {raw_key:?} maps to non-prefix address {raw_value:?}"
            ));
            address = None;
        }
        out.insert(key, address);
    }
    out
}

pub fn parse_import_map(base_url: &str, payload: &Value, warnings: &mut Vec<String>) -> ImportMap {
    let Some(object) = payload.as_object() else {
        warnings.push("import map root is not an object".into());
        return ImportMap::default();
    };
    let imports = object.get("imports").map_or_else(BTreeMap::new, |imports| {
        parse_specifier_map(base_url, Some(imports), warnings, "imports")
    });
    let mut scopes = BTreeMap::new();
    match object.get("scopes") {
        None | Some(Value::Null) => {}
        Some(Value::Object(raw_scopes)) => {
            for (raw_scope, specifier_map) in raw_scopes {
                if raw_scope.is_empty() {
                    warnings.push("ignored invalid empty scope key".into());
                    continue;
                }
                let Some(scope) = join_url(base_url, raw_scope) else {
                    warnings.push(format!("ignored invalid scope key {raw_scope:?}"));
                    continue;
                };
                scopes.insert(
                    scope,
                    parse_specifier_map(
                        base_url,
                        Some(specifier_map),
                        warnings,
                        &format!("scope {raw_scope:?}"),
                    ),
                );
            }
        }
        Some(_) => warnings.push("scopes is not an object".into()),
    }
    let mut integrity = BTreeMap::new();
    if let Some(raw) = object.get("integrity").and_then(Value::as_object) {
        for (raw_url, metadata) in raw {
            if let Some(metadata) = metadata.as_str() {
                if let Some(resolved) = url_like(Some(base_url), raw_url) {
                    integrity.insert(resolved, metadata.to_owned());
                }
            }
        }
    }
    ImportMap {
        imports,
        scopes,
        integrity,
    }
}

fn merge_specifier_map(
    existing: &BTreeMap<String, Option<String>>,
    new: &BTreeMap<String, Option<String>>,
) -> BTreeMap<String, Option<String>> {
    let mut merged = existing.clone();
    for (key, value) in new {
        merged.entry(key.clone()).or_insert_with(|| value.clone());
    }
    merged
}

pub fn merge_import_map(existing: &ImportMap, new: &ImportMap) -> ImportMap {
    let mut merged = ImportMap {
        imports: merge_specifier_map(&existing.imports, &new.imports),
        scopes: existing.scopes.clone(),
        integrity: existing.integrity.clone(),
    };
    for (scope, entries) in &new.scopes {
        let current = merged.scopes.entry(scope.clone()).or_default();
        for (key, value) in entries {
            current.entry(key.clone()).or_insert_with(|| value.clone());
        }
    }
    for (url, integrity) in &new.integrity {
        merged
            .integrity
            .entry(url.clone())
            .or_insert_with(|| integrity.clone());
    }
    merged
}

fn resolve_in_specifier_map(
    normalized: &str,
    specifier_map: &BTreeMap<String, Option<String>>,
) -> Option<(Option<String>, String)> {
    if let Some(value) = specifier_map.get(normalized) {
        return Some((value.clone(), normalized.to_owned()));
    }
    let key = specifier_map
        .keys()
        .filter(|key| key.ends_with('/') && normalized.starts_with(key.as_str()))
        .max_by_key(|key| key.len())?;
    let Some(base) = specifier_map.get(key)?.as_deref() else {
        return Some((None, key.clone()));
    };
    let suffix = &normalized[key.len()..];
    let resolved = join_url(base, suffix);
    let resolved = resolved.filter(|value| value.starts_with(base));
    Some((resolved, key.clone()))
}

fn resolution_value(
    resolved_url: Option<String>,
    bare: bool,
    resolution: &str,
    key: Option<String>,
    scope: Option<String>,
) -> Value {
    Value::Object(Map::from_iter([
        (
            "resolved_url".to_owned(),
            resolved_url.map_or(Value::Null, Value::String),
        ),
        ("bare_specifier".to_owned(), Value::Bool(bare)),
        (
            "resolution".to_owned(),
            Value::String(resolution.to_owned()),
        ),
        (
            "import_map_key".to_owned(),
            key.map_or(Value::Null, Value::String),
        ),
        ("scope".to_owned(), scope.map_or(Value::Null, Value::String)),
    ]))
}

fn resolve_from_map(
    normalized: &str,
    bare: bool,
    entries: &BTreeMap<String, Option<String>>,
    matched_resolution: &str,
    scope: Option<&String>,
) -> Option<Value> {
    let (resolved, key) = resolve_in_specifier_map(normalized, entries)?;
    let resolution = if resolved.is_some() {
        matched_resolution
    } else {
        "import_map_blocked"
    };
    Some(resolution_value(
        resolved,
        bare,
        resolution,
        Some(key),
        scope.cloned(),
    ))
}

pub fn resolve_with_import_map(
    base_url: Option<&str>,
    specifier: &str,
    import_map: Option<&ImportMap>,
) -> Value {
    let normalized_url = url_like(base_url, specifier);
    let normalized = normalized_url.as_deref().unwrap_or(specifier);
    if let (Some(import_map), Some(base_url)) = (import_map, base_url) {
        let mut scopes = import_map
            .scopes
            .keys()
            .filter(|scope| base_url.starts_with(scope.as_str()))
            .collect::<Vec<_>>();
        scopes.sort_by_key(|scope| std::cmp::Reverse(scope.len()));
        for scope in scopes {
            if let Some(result) = resolve_from_map(
                normalized,
                normalized_url.is_none(),
                &import_map.scopes[scope],
                "import_map_scope",
                Some(scope),
            ) {
                return result;
            }
        }
        if let Some(result) = resolve_from_map(
            normalized,
            normalized_url.is_none(),
            &import_map.imports,
            "import_map",
            None,
        ) {
            return result;
        }
    }
    if let Some(url) = normalized_url {
        return resolution_value(Some(url), false, "url", None, None);
    }
    resolution_value(None, true, "unresolved_bare", None, None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bare_specifiers_preserve_whitespace_and_absolute_urls_are_canonical() {
        let mut warnings = Vec::new();
        let map = parse_import_map(
            "https://app.test/index.html",
            &serde_json::json!({
                "imports": {
                    " pkg ": "/spaced.js",
                    "pkg": "/plain.js",
                    "https://APP.TEST:443/CAPS.js": "/canonical.js"
                }
            }),
            &mut warnings,
        );
        assert!(warnings.is_empty(), "{warnings:?}");
        let spaced = resolve_with_import_map(Some("https://app.test/main.js"), " pkg ", Some(&map));
        assert_eq!(spaced["resolved_url"], "https://app.test/spaced.js");
        assert_eq!(spaced["bare_specifier"], true);
        let plain = resolve_with_import_map(Some("https://app.test/main.js"), "pkg", Some(&map));
        assert_eq!(plain["resolved_url"], "https://app.test/plain.js");
        let canonical = resolve_with_import_map(
            Some("https://app.test/main.js"),
            "https://app.test/CAPS.js",
            Some(&map),
        );
        assert_eq!(canonical["resolved_url"], "https://app.test/canonical.js");
        let missing =
            resolve_with_import_map(Some("https://app.test/main.js"), " missing ", Some(&map));
        assert_eq!(missing["resolution"], "unresolved_bare");
    }

    #[test]
    fn import_map_normalizes_url_keys_and_addresses() {
        let mut warnings = Vec::new();
        let map = parse_import_map(
            "https://app.test/site/page.html",
            &serde_json::json!({
                "imports": {
                    "/modules/a.js": "../cdn/a.js",
                    "pkg/": "./vendor/pkg/"
                },
                "scopes": {
                    "/site/feature/": {
                        "pkg/": "/scoped/"
                    }
                }
            }),
            &mut warnings,
        );
        assert!(warnings.is_empty(), "{warnings:?}");
        let exact = resolve_with_import_map(
            Some("https://app.test/site/page.html"),
            "/modules/a.js",
            Some(&map),
        );
        assert_eq!(exact["resolved_url"], "https://app.test/cdn/a.js");
        assert_eq!(exact["resolution"], "import_map");
        let scoped = resolve_with_import_map(
            Some("https://app.test/site/feature/main.js"),
            "pkg/util.js",
            Some(&map),
        );
        assert_eq!(scoped["resolved_url"], "https://app.test/scoped/util.js");
        assert_eq!(scoped["resolution"], "import_map_scope");
        let global = resolve_with_import_map(
            Some("https://app.test/site/other/main.js"),
            "pkg/util.js",
            Some(&map),
        );
        assert_eq!(
            global["resolved_url"],
            "https://app.test/site/vendor/pkg/util.js"
        );
    }

    #[test]
    fn invalid_map_addresses_block_resolution_and_later_definitions() {
        let mut warnings = Vec::new();
        let blocked = parse_import_map(
            "https://app.test/index.html",
            &serde_json::json!({"imports": {"pkg/": "./not-a-prefix", "bare": "relative-address"}}),
            &mut warnings,
        );
        assert_eq!(blocked.imports["pkg/"], None);
        assert_eq!(blocked.imports["bare"], None);
        assert_eq!(warnings.len(), 2);
        let followup = parse_import_map(
            "https://app.test/index.html",
            &serde_json::json!({"imports": {"pkg/": "./valid/", "bare": "/valid.js"}}),
            &mut Vec::new(),
        );
        let merged = merge_import_map(&blocked, &followup);
        for specifier in ["pkg/module.js", "bare"] {
            let result = resolve_with_import_map(
                Some("https://app.test/index.html"),
                specifier,
                Some(&merged),
            );
            assert_eq!(result["resolution"], "import_map_blocked");
            assert!(result["resolved_url"].is_null());
        }
    }

    #[test]
    fn prefix_mappings_cannot_escape_mapped_base() {
        let mut map = ImportMap::default();
        map.imports
            .insert("pkg/".into(), Some("https://cdn.test/prefix/".into()));
        let result = resolve_with_import_map(
            Some("https://app.test/main.js"),
            "pkg/../escape.js",
            Some(&map),
        );
        assert_eq!(result["resolution"], "import_map_blocked");
        assert!(result["resolved_url"].is_null());
        assert_eq!(result["import_map_key"], "pkg/");
    }

    #[test]
    fn import_map_resolution_prefers_longest_scope_and_prefix() {
        let mut map = ImportMap::default();
        map.imports
            .insert("pkg/".into(), Some("https://cdn.test/pkg/".into()));
        map.scopes.insert(
            "https://app.test/feature/".into(),
            BTreeMap::from([("pkg/".into(), Some("https://scope.test/pkg/".into()))]),
        );
        let result = resolve_with_import_map(
            Some("https://app.test/feature/main.js"),
            "pkg/util.js",
            Some(&map),
        );
        assert_eq!(result["resolved_url"], "https://scope.test/pkg/util.js");
        assert_eq!(result["resolution"], "import_map_scope");
    }

    #[test]
    fn import_map_merge_preserves_existing_scope_entries_and_explicit_blocks() {
        let scope = "https://app.test/feature/";
        let mut existing = ImportMap::default();
        existing.scopes.insert(
            scope.to_owned(),
            BTreeMap::from([
                ("pkg/".into(), Some("https://old.test/pkg/".into())),
                ("blocked".into(), None),
            ]),
        );
        let mut update = ImportMap::default();
        update.scopes.insert(
            scope.to_owned(),
            BTreeMap::from([
                ("pkg/".into(), Some("https://new.test/pkg/".into())),
                ("blocked".into(), Some("https://new.test/blocked".into())),
                ("extra".into(), Some("https://new.test/extra.js".into())),
            ]),
        );
        let merged = merge_import_map(&existing, &update);
        assert_eq!(
            merged.scopes[scope]["pkg/"].as_deref(),
            Some("https://old.test/pkg/")
        );
        assert_eq!(merged.scopes[scope]["blocked"], None);
        let package = resolve_with_import_map(
            Some("https://app.test/feature/main.js"),
            "pkg/util.js",
            Some(&merged),
        );
        assert_eq!(package["resolved_url"], "https://old.test/pkg/util.js");
        assert_eq!(package["resolution"], "import_map_scope");
        assert_eq!(package["bare_specifier"], true);
        assert_eq!(package["import_map_key"], "pkg/");
        assert_eq!(package["scope"], scope);

        let blocked = resolve_with_import_map(
            Some("https://app.test/feature/main.js"),
            "blocked",
            Some(&merged),
        );
        assert_eq!(blocked["resolved_url"], Value::Null);
        assert_eq!(blocked["resolution"], "import_map_blocked");
        assert_eq!(blocked["import_map_key"], "blocked");

        let added = resolve_with_import_map(
            Some("https://app.test/feature/main.js"),
            "extra",
            Some(&merged),
        );
        assert_eq!(added["resolved_url"], "https://new.test/extra.js");
        assert_eq!(added["resolution"], "import_map_scope");
        assert_eq!(existing.scopes[scope].len(), 2);
    }
}
