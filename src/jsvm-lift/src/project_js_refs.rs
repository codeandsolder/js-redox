mod context;

use crate::{
    analysis_artifacts::{load_artifact, write_artifact, IMPORT_MAPS, JS_REFERENCES, SOURCE_INDEX},
    analysis_budget::{recoverable_unit_error, AnalysisBudgets, AnalysisOperation},
    capture_project::load_manifest,
    content_dedup::{default_jobs, sha256_path},
    import_map::{join_url, merge_import_map, parse_import_map, ImportMap},
    js_refs::extract_js_references,
};
use anyhow::{Context, Result};
use rayon::{prelude::*, ThreadPoolBuilder};
use regex::Regex;
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

const DYNAMIC_GLOB_KIND: &str = "import_dynamic_glob";

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

fn captured_dynamic_glob_matches<'a>(
    base_url: Option<&str>,
    pattern: &str,
    captured_urls: impl Iterator<Item = &'a str>,
) -> Result<(Option<String>, Vec<String>)> {
    let Some(base_url) = base_url else {
        return Ok((None, Vec::new()));
    };
    let decoded = decode_dynamic_glob_literals(pattern);
    let Some(absolute_pattern) = join_url(base_url, &decoded) else {
        return Ok((None, Vec::new()));
    };
    let glob_regex = dynamic_glob_regex(&absolute_pattern)?;
    let mut matching_urls = captured_urls
        .filter(|url| glob_regex.is_match(url))
        .map(str::to_owned)
        .collect::<Vec<_>>();
    matching_urls.sort();
    Ok((Some(absolute_pattern), matching_urls))
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
            .and_then(|value| value.get("document_base_url").or_else(|| value.get("url")))
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

/// Scan project JavaScript references under the recorded capture/module context.
///
/// # Errors
///
/// Fails on exhausted analysis budget, missing or invalid manifest/source-index artifacts,
/// unreadable source files, or errors writing the reference inventory.
pub fn scan_project_references(
    project: &Path,
    jobs: Option<usize>,
    budgets: &AnalysisBudgets,
) -> Result<ReferenceScanSummary> {
    let jobs = jobs.unwrap_or_else(|| default_jobs(8)).max(1);
    let stage_budget = budgets.operation(
        AnalysisOperation::ReferenceScan,
        project.display().to_string(),
    );
    stage_budget.checkpoint()?;
    let manifest = load_manifest(project)?;
    let source_index = load_artifact(project, SOURCE_INDEX).context("source index missing")?;
    let (import_maps, import_map_analysis) = load_import_maps(project, &manifest)?;
    stage_budget.checkpoint()?;

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
                let budget = budgets.operation_under(
                    &stage_budget,
                    AnalysisOperation::ReferenceScan,
                    canonical.source.display().to_string(),
                );
                if let Err(error) = budget.checkpoint() {
                    let error = recoverable_unit_error(anyhow::Error::new(error))?;
                    return Ok::<_, anyhow::Error>((
                        (*digest).clone(),
                        ExtractionResult {
                            canonical_source_path: canonical.source_path.clone(),
                            group_size: group.len(),
                            references: Vec::new(),
                            error: Some(error.to_string()),
                        },
                    ));
                }
                let source = fs::read_to_string(&canonical.source)
                    .with_context(|| format!("reading {}", canonical.source.display()))?;
                let result = extract_js_references(&source, &budget);
                let (references, error) = match result {
                    Ok(references) => (
                        serde_json::to_value(references)?
                            .as_array()
                            .cloned()
                            .unwrap_or_default(),
                        None,
                    ),
                    Err(error) => {
                        let error = recoverable_unit_error(error)?;
                        (Vec::new(), Some(error.to_string()))
                    }
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
    stage_budget.checkpoint()?;

    let mut rows = Vec::<Value>::new();
    let mut failures = 0_usize;
    let mut total_refs = 0_usize;
    let mut units_by_url = BTreeMap::<String, Vec<usize>>::new();
    let mut units_by_raw = BTreeMap::<String, Vec<usize>>::new();
    let mut seen_per_digest = BTreeMap::<String, usize>::new();
    for item in &javascript_units {
        stage_budget.checkpoint()?;
        let result = extraction_results
            .get(&item.digest)
            .context("missing extraction result")?;
        let occurrence = *seen_per_digest.get(&item.digest).unwrap_or(&0);
        seen_per_digest.insert(item.digest.clone(), occurrence + 1);
        let mut row = json!({
            "resource_id": item.unit.get("resource_id").cloned().unwrap_or(Value::Null),
            "origin": item.unit.get("origin").cloned().unwrap_or(Value::Null),
            "ordinal": item.unit.get("ordinal").cloned().unwrap_or(Value::Null),
            "url": item.unit.get("url").cloned().unwrap_or(Value::Null),
            "raw_path": item.unit.get("raw_path").cloned().unwrap_or(Value::Null),
            "source_path": item.source_path,
            "content_sha256": item.digest,
            "content_group_size": result.group_size,
            "deduplicated": occurrence > 0,
            "deduplicated_from": if occurrence > 0 { Value::String(result.canonical_source_path.clone()) } else { Value::Null },
            "extractor_exit": i32::from(result.error.is_some()),
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
        // Inline scripts share the parent document URL; runtime scripts can
        // advertise a URL without being captured network response instances.
        if row.get("origin").and_then(Value::as_str) == Some("resource") {
            if let Some(url) = row
                .get("url")
                .and_then(Value::as_str)
                .filter(|url| !url.is_empty())
            {
                units_by_url.entry(url.to_owned()).or_default().push(row_id);
            }
        }
        if let Some(raw) = row.get("raw_path").and_then(Value::as_str) {
            if !raw.is_empty() {
                units_by_raw.entry(raw.to_owned()).or_default().push(row_id);
            }
        }
        rows.push(row);
    }

    let document_bases = manifest
        .resources
        .iter()
        .filter_map(|resource| {
            Some((
                resource.get("id")?.as_u64()?,
                resource.get("document_base_url")?.as_str()?.to_owned(),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    for row in &mut rows {
        let base_url = if row.get("origin").and_then(Value::as_str) == Some("inline_script") {
            row.get("resource_id")
                .and_then(Value::as_u64)
                .and_then(|id| document_bases.get(&id))
                .cloned()
        } else {
            None
        };
        if let Some(base_url) = base_url {
            row.as_object_mut()
                .context("reference row must be object")?
                .insert("resolution_base_url".into(), Value::String(base_url));
        }
    }
    let mut dynamic_glob_matches = BTreeMap::<(usize, usize), Vec<String>>::new();
    let mut dynamic_glob_patterns = 0_usize;
    for (row_id, row) in rows.iter_mut().enumerate() {
        stage_budget.checkpoint()?;
        let base_url = row
            .get("resolution_base_url")
            .or_else(|| row.get("url"))
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
                units_by_url.keys().map(String::as_str),
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

    let context_evidence = context::propagate_context_evidence(
        &rows,
        &manifest.inline_scripts,
        &units_by_url,
        &units_by_raw,
        &import_maps,
        &dynamic_glob_matches,
        &stage_budget,
    )?;
    let resolution =
        context::apply_reference_resolutions(&mut rows, &context_evidence, &dynamic_glob_matches)?;
    let resolved_by_import_map = resolution.resolved_by_import_map;
    let unresolved_bare = resolution.unresolved_bare;
    let ambiguous = resolution.ambiguous;

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
        .unwrap_or_else(|| Value::from(0));
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
    fn dynamic_glob_matches_only_one_path_segment() -> Result<()> {
        let (_, matches) = captured_dynamic_glob_matches(
            Some("https://app.test/src/main.js"),
            "./pages/*.js",
            [
                "https://app.test/src/pages/a.js",
                "https://app.test/src/pages/deep/b.js",
            ]
            .into_iter(),
        )?;
        assert_eq!(matches, ["https://app.test/src/pages/a.js"]);
        Ok(())
    }
}
