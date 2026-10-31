use crate::{
    analysis_artifacts::{load_artifact, write_artifact, IMPORT_MAPS, JS_REFERENCES, SOURCE_INDEX},
    browser_script_types::is_executable_script,
    capture_project::load_manifest,
    content_dedup::{default_jobs, sha256_path},
    js_refs::extract_js_references,
};
use anyhow::{Context, Result};
use rayon::{prelude::*, ThreadPoolBuilder};
use regex::Regex;
use serde::{Deserialize, Serialize};
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    path::{Path, PathBuf},
};
use url::Url;

const IMPORT_KINDS: &[&str] = &["import_static", "import_dynamic"];
const DYNAMIC_GLOB_KIND: &str = "import_dynamic_glob";

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
struct ImportMap {
    #[serde(default)]
    imports: BTreeMap<String, Option<String>>,
    #[serde(default)]
    scopes: BTreeMap<String, BTreeMap<String, Option<String>>>,
    #[serde(default)]
    integrity: BTreeMap<String, String>,
}

#[derive(Debug, Clone)]
struct JsUnit {
    unit: Value,
    source: PathBuf,
    source_path: String,
    digest: String,
}

#[derive(Debug, Clone)]
struct ExtractionResult {
    canonical_source_path: String,
    group_size: usize,
    references: Vec<Value>,
    error: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReferenceScanSummary {
    pub javascript_units: usize,
    pub references: usize,
    pub failures: usize,
    pub resolved_by_import_map: usize,
    pub unresolved_bare_specifiers: usize,
    pub ambiguous_document_contexts: usize,
    pub jobs: usize,
}

fn absolute_url(value: &str) -> bool {
    Url::parse(value).is_ok_and(|url| !url.scheme().is_empty())
}

fn join_url(base: &str, value: &str) -> Option<String> {
    Url::parse(base)
        .ok()?
        .join(value)
        .ok()
        .map(|url| url.to_string())
}

fn url_like(base_url: Option<&str>, specifier: &str) -> Option<String> {
    let specifier = specifier.trim();
    if specifier.is_empty() {
        return None;
    }
    if absolute_url(specifier) {
        return Some(specifier.to_owned());
    }
    if specifier.starts_with("//") {
        let base = Url::parse(base_url?).ok()?;
        return Some(format!("{}:{specifier}", base.scheme()));
    }
    if specifier.starts_with("./") || specifier.starts_with("../") || specifier.starts_with('/') {
        return join_url(base_url?, specifier);
    }
    None
}

fn decode_dynamic_glob_literals(pattern: &str) -> String {
    pattern
        .replace("[[]", "[")
        .replace("[]]", "]")
        .replace("[{]", "{")
        .replace("[}]", "}")
        .replace("[?]", "?")
}

fn dynamic_glob_regex(pattern: &str) -> Result<Regex> {
    let mut regex = String::from("^");
    for character in pattern.chars() {
        if character == '*' {
            regex.push_str("[^/]*");
        } else {
            regex.push_str(&regex::escape(&character.to_string()));
        }
    }
    regex.push('$');
    Ok(Regex::new(&regex)?)
}

fn captured_dynamic_glob_matches(
    base_url: Option<&str>,
    pattern: &str,
    captured_urls: impl Iterator<Item = String>,
) -> Result<(Option<String>, Vec<String>)> {
    let Some(base_url) = base_url else {
        return Ok((None, Vec::new()));
    };
    let decoded = decode_dynamic_glob_literals(pattern);
    let Some(absolute_pattern) = join_url(base_url, &decoded) else {
        return Ok((None, Vec::new()));
    };
    let matcher = dynamic_glob_regex(&absolute_pattern)?;
    let mut matches = captured_urls
        .filter(|url| matcher.is_match(url))
        .collect::<Vec<_>>();
    matches.sort();
    Ok((Some(absolute_pattern), matches))
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

fn parse_import_map(base_url: &str, payload: &Value, warnings: &mut Vec<String>) -> ImportMap {
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

fn merge_import_map(existing: &ImportMap, new: &ImportMap) -> ImportMap {
    let mut merged = ImportMap {
        imports: merge_specifier_map(&existing.imports, &new.imports),
        scopes: existing.scopes.clone(),
        integrity: existing.integrity.clone(),
    };
    for (scope, entries) in &new.scopes {
        let current = merged.scopes.get(scope).cloned().unwrap_or_default();
        merged
            .scopes
            .insert(scope.clone(), merge_specifier_map(&current, entries));
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
    let base = specifier_map.get(key)?.clone();
    let Some(base) = base else {
        return Some((None, key.clone()));
    };
    let suffix = &normalized[key.len()..];
    let resolved = join_url(&base, suffix);
    let resolved = resolved.filter(|value| value.starts_with(&base));
    Some((resolved, key.clone()))
}

fn resolution_value(
    resolved_url: Option<String>,
    bare: bool,
    resolution: &str,
    key: Option<String>,
    scope: Option<String>,
) -> Value {
    json!({
        "resolved_url": resolved_url,
        "bare_specifier": bare,
        "resolution": resolution,
        "import_map_key": key,
        "scope": scope,
    })
}

fn resolve_with_import_map(
    base_url: Option<&str>,
    specifier: &str,
    import_map: Option<&ImportMap>,
) -> Value {
    let specifier = specifier.trim();
    let normalized_url = url_like(base_url, specifier);
    let normalized = normalized_url
        .clone()
        .unwrap_or_else(|| specifier.to_owned());
    if let (Some(import_map), Some(base_url)) = (import_map, base_url) {
        let mut scopes = import_map
            .scopes
            .keys()
            .filter(|scope| base_url.starts_with(scope.as_str()))
            .collect::<Vec<_>>();
        scopes.sort_by_key(|scope| std::cmp::Reverse(scope.len()));
        for scope in scopes {
            if let Some((resolved, key)) =
                resolve_in_specifier_map(&normalized, &import_map.scopes[scope])
            {
                return resolution_value(
                    resolved.clone(),
                    normalized_url.is_none(),
                    if resolved.is_some() {
                        "import_map_scope"
                    } else {
                        "import_map_blocked"
                    },
                    Some(key),
                    Some(scope.clone()),
                );
            }
        }
        if let Some((resolved, key)) = resolve_in_specifier_map(&normalized, &import_map.imports) {
            return resolution_value(
                resolved.clone(),
                normalized_url.is_none(),
                if resolved.is_some() {
                    "import_map"
                } else {
                    "import_map_blocked"
                },
                Some(key),
                None,
            );
        }
    }
    if let Some(url) = normalized_url {
        return resolution_value(Some(url), false, "url", None, None);
    }
    resolution_value(None, true, "unresolved_bare", None, None)
}

fn is_import_map(script: &Value) -> bool {
    script
        .get("script_type")
        .and_then(Value::as_str)
        .is_some_and(|value| value.trim().eq_ignore_ascii_case("importmap"))
}

fn load_import_maps(
    project: &Path,
    manifest: &crate::capture_project::CaptureManifest,
) -> Result<(BTreeMap<u64, ImportMap>, Value)> {
    let resources = manifest
        .resources
        .iter()
        .filter_map(|resource| {
            resource
                .get("id")
                .and_then(Value::as_u64)
                .map(|id| (id, resource))
        })
        .collect::<BTreeMap<_, _>>();
    let mut by_document = BTreeMap::<u64, Vec<&Value>>::new();
    for script in &manifest.inline_scripts {
        if is_import_map(script) && script.get("output_path").and_then(Value::as_str).is_some() {
            let document_id = script
                .get("parent_resource_id")
                .and_then(Value::as_u64)
                .context("import map parent_resource_id must be a non-negative integer")?;
            by_document.entry(document_id).or_default().push(script);
        }
    }
    for scripts in by_document.values_mut() {
        scripts.sort_by_key(|script| script.get("ordinal").and_then(Value::as_u64).unwrap_or(0));
    }

    let mut maps_by_document = BTreeMap::new();
    let mut records = Vec::new();
    let mut parse_failures = 0_usize;
    for (document_id, scripts) in by_document {
        let resource = resources.get(&document_id).copied();
        let base_url = resource
            .and_then(|value| value.get("url"))
            .and_then(Value::as_str)
            .unwrap_or_default();
        let mut merged = ImportMap::default();
        for script in scripts {
            let mut warnings = Vec::new();
            let raw_path = script
                .get("output_path")
                .and_then(Value::as_str)
                .context("import map output_path missing")?;
            let path = project.join(raw_path);
            let (parsed, status) = match fs::read_to_string(&path)
                .with_context(|| format!("reading {}", path.display()))
                .and_then(|text| {
                    serde_json::from_str::<Value>(&text).context("parsing import map JSON")
                }) {
                Ok(payload) => {
                    let parsed = parse_import_map(base_url, &payload, &mut warnings);
                    merged = merge_import_map(&merged, &parsed);
                    (parsed, "parsed")
                }
                Err(error) => {
                    warnings.push(error.to_string());
                    parse_failures += 1;
                    (ImportMap::default(), "error")
                }
            };
            records.push(json!({
                "document_resource_id": document_id,
                "pageref": resource.and_then(|value| value.get("pageref")).cloned().unwrap_or(Value::Null),
                "base_url": base_url,
                "ordinal": script.get("ordinal").cloned().unwrap_or(Value::Null),
                "raw_path": raw_path,
                "status": status,
                "warnings": warnings,
                "imports": parsed.imports,
                "scopes": parsed.scopes,
                "integrity": parsed.integrity,
            }));
        }
        maps_by_document.insert(document_id, merged);
    }
    let documents = maps_by_document
        .iter()
        .map(|(id, map)| Ok((id.to_string(), serde_json::to_value(map)?)))
        .collect::<Result<Map<String, Value>>>()?;
    let analysis = json!({
        "schema": IMPORT_MAPS.schema,
        "maps": records,
        "documents": documents,
        "summary": {
            "import_map_scripts": records.len(),
            "documents_with_import_maps": maps_by_document.len(),
            "parse_failures": parse_failures,
            "imports": maps_by_document.values().map(|map| map.imports.len()).sum::<usize>(),
            "scopes": maps_by_document.values().map(|map| map.scopes.len()).sum::<usize>(),
        },
        "limitation": "Multiple import maps are merged with standard first-definition-wins conflict semantics, but runtime resolved-module-set timing is not reconstructed."
    });
    write_artifact(project, IMPORT_MAPS, &analysis)?;
    Ok((maps_by_document, analysis))
}

fn candidate_key(candidate: &Value) -> String {
    serde_json::to_string(candidate).unwrap_or_default()
}

fn push_candidate(
    store: &mut BTreeMap<(usize, usize), BTreeMap<String, Value>>,
    key: (usize, usize),
    candidate: Value,
) {
    store
        .entry(key)
        .or_default()
        .insert(candidate_key(&candidate), candidate);
}

fn set_resolution_fields(target: &mut Map<String, Value>, source: &Value) {
    for key in [
        "resolved_url",
        "bare_specifier",
        "resolution",
        "import_map_key",
        "scope",
    ] {
        target.insert(key.into(), source.get(key).cloned().unwrap_or(Value::Null));
    }
}

pub fn scan_project_references(
    project: &Path,
    jobs: Option<usize>,
) -> Result<ReferenceScanSummary> {
    let jobs = jobs.unwrap_or_else(|| default_jobs(8)).max(1);
    let manifest = load_manifest(project)?;
    let source_index =
        load_artifact(project, SOURCE_INDEX, false)?.context("source index missing")?;
    let (import_maps, import_map_analysis) = load_import_maps(project, &manifest)?;

    let mut javascript_units = Vec::<JsUnit>::new();
    let mut extraction_groups = BTreeMap::<String, Vec<usize>>::new();
    for unit in source_index
        .get("units")
        .and_then(Value::as_array)
        .context("source index units missing")?
    {
        if unit.get("kind").and_then(Value::as_str) != Some("javascript") {
            continue;
        }
        let Some(source_path) = unit.get("source_path").and_then(Value::as_str) else {
            continue;
        };
        let source = project.join(source_path);
        let digest = sha256_path(&source)?;
        let index = javascript_units.len();
        javascript_units.push(JsUnit {
            unit: unit.clone(),
            source,
            source_path: source_path.to_owned(),
            digest: digest.clone(),
        });
        extraction_groups.entry(digest).or_default().push(index);
    }

    let pool = ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .context("building JS-reference thread pool")?;
    let group_refs = extraction_groups.iter().collect::<Vec<_>>();
    let extracted = pool.install(|| {
        group_refs
            .par_iter()
            .map(|(digest, group)| {
                let canonical_index = *group.first().context("empty JS-reference group")?;
                let canonical = &javascript_units[canonical_index];
                let source = fs::read_to_string(&canonical.source)
                    .with_context(|| format!("reading {}", canonical.source.display()))?;
                let result = extract_js_references(&source);
                let (references, error) = match result {
                    Ok(references) => (
                        serde_json::to_value(references)?
                            .as_array()
                            .cloned()
                            .unwrap_or_default(),
                        None,
                    ),
                    Err(error) => (Vec::new(), Some(error.to_string())),
                };
                Ok::<_, anyhow::Error>((
                    (*digest).clone(),
                    ExtractionResult {
                        canonical_source_path: canonical.source_path.clone(),
                        group_size: group.len(),
                        references,
                        error,
                    },
                ))
            })
            .collect::<Vec<_>>()
    });
    let extraction_results = extracted
        .into_iter()
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .collect::<BTreeMap<_, _>>();

    let mut rows = Vec::<Value>::new();
    let mut failures = 0_usize;
    let mut total_refs = 0_usize;
    let mut units_by_url = BTreeMap::<String, Vec<usize>>::new();
    let mut units_by_raw = BTreeMap::<String, usize>::new();
    let mut seen_per_digest = BTreeMap::<String, usize>::new();
    for item in &javascript_units {
        let result = extraction_results
            .get(&item.digest)
            .context("missing extraction result")?;
        let occurrence = *seen_per_digest.get(&item.digest).unwrap_or(&0);
        seen_per_digest.insert(item.digest.clone(), occurrence + 1);
        let mut row = json!({
            "resource_id": item.unit.get("resource_id").cloned().unwrap_or(Value::Null),
            "url": item.unit.get("url").cloned().unwrap_or(Value::Null),
            "raw_path": item.unit.get("raw_path").cloned().unwrap_or(Value::Null),
            "source_path": item.source_path,
            "content_sha256": item.digest,
            "content_group_size": result.group_size,
            "deduplicated": occurrence > 0,
            "deduplicated_from": if occurrence > 0 { Value::String(result.canonical_source_path.clone()) } else { Value::Null },
            "extractor_exit": if result.error.is_some() { 1 } else { 0 },
            "document_resource_ids": [],
            "references": result.references,
        });
        if let Some(error) = &result.error {
            failures += 1;
            row.as_object_mut()
                .context("reference row must be object")?
                .insert("error".into(), Value::String(error.clone()));
        } else {
            total_refs += result.references.len();
        }
        let row_id = rows.len();
        if let Some(url) = row.get("url").and_then(Value::as_str) {
            if !url.is_empty() {
                units_by_url.entry(url.to_owned()).or_default().push(row_id);
            }
        }
        if let Some(raw) = row.get("raw_path").and_then(Value::as_str) {
            if !raw.is_empty() {
                units_by_raw.insert(raw.to_owned(), row_id);
            }
        }
        rows.push(row);
    }

    let captured_urls = units_by_url.keys().cloned().collect::<Vec<_>>();
    let mut dynamic_glob_matches = BTreeMap::<(usize, usize), Vec<String>>::new();
    let mut dynamic_glob_patterns = 0_usize;
    for (row_id, row) in rows.iter_mut().enumerate() {
        let base_url = row
            .get("url")
            .and_then(Value::as_str)
            .map(ToOwned::to_owned);
        let refs = row
            .get_mut("references")
            .and_then(Value::as_array_mut)
            .context("references must be array")?;
        for (ref_index, reference) in refs.iter_mut().enumerate() {
            if reference.get("kind").and_then(Value::as_str) != Some(DYNAMIC_GLOB_KIND) {
                continue;
            }
            dynamic_glob_patterns += 1;
            let glob = reference
                .get("glob")
                .and_then(Value::as_str)
                .unwrap_or_default();
            let (absolute, matches) = captured_dynamic_glob_matches(
                base_url.as_deref(),
                glob,
                captured_urls.clone().into_iter(),
            )?;
            reference
                .as_object_mut()
                .context("reference must be object")?
                .insert(
                    "absolute_glob".into(),
                    absolute.map_or(Value::Null, Value::String),
                );
            dynamic_glob_matches.insert((row_id, ref_index), matches);
        }
    }

    let mut queue = VecDeque::new();
    let mut contexts = vec![BTreeSet::<u64>::new(); rows.len()];
    for script in &manifest.inline_scripts {
        if is_import_map(script)
            || !is_executable_script(script.get("script_type").and_then(Value::as_str))
        {
            continue;
        }
        let document_id = script
            .get("parent_resource_id")
            .and_then(Value::as_u64)
            .context("script parent_resource_id must be integer")?;
        if !import_maps.contains_key(&document_id) {
            continue;
        }
        if let Some(path) = script.get("output_path").and_then(Value::as_str) {
            if let Some(&row_id) = units_by_raw.get(path) {
                if contexts[row_id].insert(document_id) {
                    queue.push_back((row_id, document_id));
                }
            }
        }
        if let Some(src) = script.get("resolved_src").and_then(Value::as_str) {
            for &row_id in units_by_url.get(src).into_iter().flatten() {
                if contexts[row_id].insert(document_id) {
                    queue.push_back((row_id, document_id));
                }
            }
        }
    }

    let mut candidates = BTreeMap::<(usize, usize), BTreeMap<String, Value>>::new();
    let mut seen_context = BTreeSet::<(usize, u64)>::new();
    while let Some((row_id, document_id)) = queue.pop_front() {
        if !seen_context.insert((row_id, document_id)) {
            continue;
        }
        let row_url = rows[row_id]
            .get("url")
            .and_then(Value::as_str)
            .map(ToOwned::to_owned);
        let references = rows[row_id]
            .get("references")
            .and_then(Value::as_array)
            .cloned()
            .unwrap_or_default();
        let import_map = import_maps.get(&document_id);
        for (ref_index, reference) in references.iter().enumerate() {
            let kind = reference
                .get("kind")
                .and_then(Value::as_str)
                .unwrap_or_default();
            if kind == DYNAMIC_GLOB_KIND {
                for matched_url in dynamic_glob_matches
                    .get(&(row_id, ref_index))
                    .cloned()
                    .unwrap_or_default()
                {
                    let mut result =
                        resolve_with_import_map(row_url.as_deref(), &matched_url, import_map);
                    if let Some(resolution) = result
                        .get("resolution")
                        .and_then(Value::as_str)
                        .map(ToOwned::to_owned)
                    {
                        let updated = if resolution == "url" {
                            "captured_dynamic_glob".to_owned()
                        } else {
                            format!("captured_dynamic_glob_{resolution}")
                        };
                        result
                            .as_object_mut()
                            .context("resolution must be object")?
                            .insert("resolution".into(), Value::String(updated));
                    }
                    let mut candidate = result
                        .as_object()
                        .cloned()
                        .context("resolution must be object")?;
                    candidate.insert("document_resource_id".into(), Value::from(document_id));
                    candidate.insert("glob_match_url".into(), Value::String(matched_url));
                    let candidate = Value::Object(candidate);
                    let resolved = candidate
                        .get("resolved_url")
                        .and_then(Value::as_str)
                        .map(ToOwned::to_owned);
                    push_candidate(&mut candidates, (row_id, ref_index), candidate);
                    if let Some(resolved) = resolved {
                        for &target in units_by_url.get(&resolved).into_iter().flatten() {
                            if contexts[target].insert(document_id) {
                                queue.push_back((target, document_id));
                            }
                        }
                    }
                }
                continue;
            }
            if !IMPORT_KINDS.contains(&kind) {
                continue;
            }
            let specifier = reference
                .get("specifier")
                .and_then(Value::as_str)
                .unwrap_or_default();
            let result = resolve_with_import_map(row_url.as_deref(), specifier, import_map);
            let mut candidate = result
                .as_object()
                .cloned()
                .context("resolution must be object")?;
            candidate.insert("document_resource_id".into(), Value::from(document_id));
            let candidate = Value::Object(candidate);
            let resolved = candidate
                .get("resolved_url")
                .and_then(Value::as_str)
                .map(ToOwned::to_owned);
            push_candidate(&mut candidates, (row_id, ref_index), candidate);
            if let Some(resolved) = resolved {
                for &target in units_by_url.get(&resolved).into_iter().flatten() {
                    if contexts[target].insert(document_id) {
                        queue.push_back((target, document_id));
                    }
                }
            }
        }
    }

    let mut resolved_by_import_map = 0_usize;
    let mut unresolved_bare = 0_usize;
    let mut ambiguous = 0_usize;
    for (row_id, row) in rows.iter_mut().enumerate() {
        row.as_object_mut()
            .context("reference row must be object")?
            .insert(
                "document_resource_ids".into(),
                Value::Array(contexts[row_id].iter().copied().map(Value::from).collect()),
            );
        let base_url = row
            .get("url")
            .and_then(Value::as_str)
            .map(ToOwned::to_owned);
        let refs = row
            .get_mut("references")
            .and_then(Value::as_array_mut)
            .context("references must be array")?;
        for (ref_index, reference) in refs.iter_mut().enumerate() {
            let kind = reference
                .get("kind")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_owned();
            let mut choices = candidates
                .get(&(row_id, ref_index))
                .map(|map| map.values().cloned().collect::<Vec<_>>())
                .unwrap_or_default();
            if kind == DYNAMIC_GLOB_KIND {
                let raw_matches = dynamic_glob_matches
                    .get(&(row_id, ref_index))
                    .cloned()
                    .unwrap_or_default();
                if choices.is_empty() {
                    choices = raw_matches.iter().map(|matched| json!({
                        "document_resource_id": Value::Null, "glob_match_url": matched,
                        "resolved_url": matched, "bare_specifier": false,
                        "resolution": "captured_dynamic_glob", "import_map_key": Value::Null, "scope": Value::Null,
                    })).collect();
                }
                choices.sort_by_key(|choice| {
                    (
                        choice
                            .get("document_resource_id")
                            .and_then(Value::as_u64)
                            .is_some(),
                        choice
                            .get("document_resource_id")
                            .and_then(Value::as_u64)
                            .unwrap_or(0),
                        choice
                            .get("resolved_url")
                            .and_then(Value::as_str)
                            .unwrap_or_default()
                            .to_owned(),
                    )
                });
                let mut resolved = choices
                    .iter()
                    .filter_map(|choice| {
                        choice
                            .get("resolved_url")
                            .and_then(Value::as_str)
                            .map(ToOwned::to_owned)
                    })
                    .collect::<BTreeSet<_>>();
                let candidate_count = resolved.len();
                let resolved_url = if candidate_count == 1 {
                    resolved
                        .pop_first()
                        .map(Value::String)
                        .unwrap_or(Value::Null)
                } else {
                    Value::Null
                };
                let object = reference
                    .as_object_mut()
                    .context("reference must be object")?;
                object.insert("resolution_candidates".into(), Value::Array(choices));
                object.insert("candidate_count".into(), Value::from(candidate_count));
                object.insert("resolved_url".into(), resolved_url);
                object.insert("bare_specifier".into(), Value::Bool(false));
                object.insert(
                    "resolution".into(),
                    Value::String(
                        if raw_matches.is_empty() {
                            "captured_dynamic_glob_unmatched"
                        } else {
                            "captured_dynamic_glob"
                        }
                        .into(),
                    ),
                );
                object.insert("import_map_key".into(), Value::Null);
                object.insert("scope".into(), Value::Null);
                continue;
            }
            if !IMPORT_KINDS.contains(&kind.as_str()) || choices.is_empty() {
                let specifier = reference
                    .get("specifier")
                    .and_then(Value::as_str)
                    .unwrap_or_default()
                    .to_owned();
                let result = resolve_with_import_map(base_url.as_deref(), &specifier, None);
                let object = reference
                    .as_object_mut()
                    .context("reference must be object")?;
                set_resolution_fields(object, &result);
                if result.get("resolution").and_then(Value::as_str) == Some("unresolved_bare") {
                    unresolved_bare += 1;
                }
                continue;
            }
            choices.sort_by_key(|choice| {
                choice
                    .get("document_resource_id")
                    .and_then(Value::as_u64)
                    .unwrap_or(0)
            });
            let signatures = choices
                .iter()
                .map(|choice| {
                    (
                        choice
                            .get("resolved_url")
                            .cloned()
                            .unwrap_or(Value::Null)
                            .to_string(),
                        choice
                            .get("resolution")
                            .cloned()
                            .unwrap_or(Value::Null)
                            .to_string(),
                        choice
                            .get("import_map_key")
                            .cloned()
                            .unwrap_or(Value::Null)
                            .to_string(),
                        choice
                            .get("scope")
                            .cloned()
                            .unwrap_or(Value::Null)
                            .to_string(),
                    )
                })
                .collect::<BTreeSet<_>>();
            let object = reference
                .as_object_mut()
                .context("reference must be object")?;
            object.insert(
                "resolution_candidates".into(),
                Value::Array(choices.clone()),
            );
            if signatures.len() == 1 {
                let only = choices.first().context("resolution choices disappeared")?;
                set_resolution_fields(object, only);
                if only
                    .get("resolution")
                    .and_then(Value::as_str)
                    .is_some_and(|value| value.starts_with("import_map"))
                    && only
                        .get("resolved_url")
                        .is_some_and(|value| !value.is_null())
                {
                    resolved_by_import_map += 1;
                }
                if only.get("resolution").and_then(Value::as_str) == Some("unresolved_bare") {
                    unresolved_bare += 1;
                }
            } else {
                object.insert("resolved_url".into(), Value::Null);
                object.insert(
                    "bare_specifier".into(),
                    Value::Bool(choices.iter().all(|choice| {
                        choice
                            .get("bare_specifier")
                            .and_then(Value::as_bool)
                            .unwrap_or(false)
                    })),
                );
                object.insert(
                    "resolution".into(),
                    Value::String("ambiguous_document_context".into()),
                );
                object.insert("import_map_key".into(), Value::Null);
                object.insert("scope".into(), Value::Null);
                ambiguous += 1;
            }
        }
    }

    let dynamic_candidates = dynamic_glob_matches
        .values()
        .map(|matches| matches.iter().collect::<BTreeSet<_>>().len())
        .sum::<usize>();
    let dynamic_unmatched = dynamic_glob_matches
        .values()
        .filter(|matches| matches.is_empty())
        .count();
    let import_map_scripts = import_map_analysis
        .get("summary")
        .and_then(|summary| summary.get("import_map_scripts"))
        .cloned()
        .unwrap_or(Value::from(0));
    let document = json!({
        "schema": JS_REFERENCES.schema,
        "extractor": "jsvm_lift::js_refs",
        "import_maps": IMPORT_MAPS.relative_path,
        "code_units": rows,
        "summary": {
            "javascript_units": javascript_units.len(), "unique_input_bodies": extraction_groups.len(),
            "deduplicated_units": javascript_units.len().saturating_sub(extraction_groups.len()),
            "extractor_invocations": extraction_groups.len(), "jobs": jobs, "references": total_refs,
            "failures": failures, "import_map_scripts": import_map_scripts,
            "resolved_by_import_map": resolved_by_import_map, "unresolved_bare_specifiers": unresolved_bare,
            "ambiguous_document_contexts": ambiguous, "dynamic_import_globs": dynamic_glob_patterns,
            "dynamic_import_candidate_urls": dynamic_candidates, "dynamic_import_unmatched": dynamic_unmatched,
        }
    });
    write_artifact(project, JS_REFERENCES, &document)?;
    Ok(ReferenceScanSummary {
        javascript_units: javascript_units.len(),
        references: total_refs,
        failures,
        resolved_by_import_map,
        unresolved_bare_specifiers: unresolved_bare,
        ambiguous_document_contexts: ambiguous,
        jobs,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn dynamic_glob_matches_only_one_path_segment() -> Result<()> {
        let (_, matches) = captured_dynamic_glob_matches(
            Some("https://app.test/src/main.js"),
            "./pages/*.js",
            [
                "https://app.test/src/pages/a.js".to_owned(),
                "https://app.test/src/pages/deep/b.js".to_owned(),
            ]
            .into_iter(),
        )?;
        assert_eq!(matches, ["https://app.test/src/pages/a.js"]);
        Ok(())
    }
}
