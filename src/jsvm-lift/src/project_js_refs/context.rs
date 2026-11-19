//! Captured-project module reference evidence and document-context routing.
//!
//! Propagates the captured document identities through imported modules,
//! retains distinct per-context candidates, and only then resolves the
//! evidence into reference rows. The owning scan stage writes the artifact.

use super::{is_import_map, DYNAMIC_GLOB_KIND};
use crate::{
    browser_script_types::is_executable_script,
    import_map::{resolve_with_import_map, ImportMap},
};
use anyhow::{Context, Result};
use serde_json::{json, Map, Value};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use work_budget::WorkBudget;

// ECMAScript re-exports are module dependencies, just like static imports.
const IMPORT_KINDS: &[&str] = &[
    "import_static",
    "import_dynamic",
    "reexport_named",
    "reexport_all",
];

type ReferenceKey = (usize, usize);
type CandidateStore = BTreeMap<ReferenceKey, BTreeMap<String, Value>>;

pub(super) struct ContextEvidence {
    document_ids: Vec<BTreeSet<u64>>,
    candidates: CandidateStore,
}

pub(super) struct ResolutionStatistics {
    pub(super) resolved_by_import_map: usize,
    pub(super) unresolved_bare: usize,
    pub(super) ambiguous: usize,
}

fn candidate_key(candidate: &Value) -> Result<String> {
    Ok(serde_json::to_string(candidate)?)
}

fn push_candidate(
    store: &mut BTreeMap<(usize, usize), BTreeMap<String, Value>>,
    key: (usize, usize),
    candidate: Value,
) -> Result<()> {
    store
        .entry(key)
        .or_default()
        .insert(candidate_key(&candidate)?, candidate);
    Ok(())
}

// The document-specific module graph state is shared by all reference kinds
// within a source unit. Keep it borrowed only for this unit's reference pass.
struct ContextRouting<'a> {
    units_by_url: &'a BTreeMap<String, Vec<usize>>,
    contexts: &'a mut [BTreeSet<u64>],
    queue: &'a mut VecDeque<(usize, u64)>,
}

// Normal imports and captured dynamic globs must use precisely the same
// document-context propagation and candidate deduplication. Only glob
// metadata and its resolution classification are specific to the caller.
fn push_contextual_resolution(
    store: &mut BTreeMap<(usize, usize), BTreeMap<String, Value>>,
    key: (usize, usize),
    document_id: u64,
    mut resolution: Value,
    glob_match_url: Option<&str>,
    routing: &mut ContextRouting<'_>,
) -> Result<()> {
    let candidate = resolution
        .as_object_mut()
        .context("resolution must be object")?;
    candidate.insert("document_resource_id".into(), Value::from(document_id));
    if let Some(url) = glob_match_url {
        candidate.insert("glob_match_url".into(), Value::String(url.to_owned()));
    }
    let resolved = candidate
        .get("resolved_url")
        .and_then(Value::as_str)
        .map(ToOwned::to_owned);
    push_candidate(store, key, resolution)?;
    if let Some(resolved) = resolved {
        for &target in routing.units_by_url.get(&resolved).into_iter().flatten() {
            if routing.contexts[target].insert(document_id) {
                routing.queue.push_back((target, document_id));
            }
        }
    }
    Ok(())
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

/// Collect document-context evidence for every reachable captured module.
///
/// No JSON artifact is emitted; candidates carry their proven document IDs.
pub(super) fn propagate_context_evidence(
    rows: &[Value],
    inline_scripts: &[Value],
    units_by_url: &BTreeMap<String, Vec<usize>>,
    units_by_raw: &BTreeMap<String, Vec<usize>>,
    import_maps: &BTreeMap<u64, ImportMap>,
    dynamic_glob_matches: &BTreeMap<ReferenceKey, Vec<String>>,
    stage_budget: &WorkBudget,
) -> Result<ContextEvidence> {
    let mut queue = VecDeque::new();
    let mut contexts = vec![BTreeSet::<u64>::new(); rows.len()];
    for script in inline_scripts {
        if is_import_map(script)
            || !is_executable_script(script.get("script_type").and_then(Value::as_str))
        {
            continue;
        }
        let document_id = script
            .get("parent_resource_id")
            .and_then(Value::as_u64)
            .context("script parent_resource_id must be integer")?;
        // Every executable script seeds its document context, even without
        // an import map: a shared module must retain both mapped and unmapped
        // resolution outcomes rather than inheriting only the mapped one.
        if let Some(path) = script.get("output_path").and_then(Value::as_str) {
            let script_ordinal = script.get("ordinal").and_then(Value::as_u64);
            for &row_id in units_by_raw.get(path).into_iter().flatten() {
                let unit = &rows[row_id];
                if unit.get("origin").and_then(Value::as_str) != Some("inline_script")
                    || unit.get("resource_id").and_then(Value::as_u64) != Some(document_id)
                    || unit.get("ordinal").and_then(Value::as_u64) != script_ordinal
                {
                    continue;
                }
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
        stage_budget.checkpoint()?;
        if !seen_context.insert((row_id, document_id)) {
            continue;
        }
        let row_url = rows[row_id]
            .get("resolution_base_url")
            .or_else(|| rows[row_id].get("url"))
            .and_then(Value::as_str)
            .map(ToOwned::to_owned);
        let references = rows[row_id]
            .get("references")
            .and_then(Value::as_array)
            .map_or(&[][..], Vec::as_slice);
        let import_map = import_maps.get(&document_id);
        let mut routing = ContextRouting {
            units_by_url,
            contexts: &mut contexts,
            queue: &mut queue,
        };
        for (ref_index, reference) in references.iter().enumerate() {
            let kind = reference
                .get("kind")
                .and_then(Value::as_str)
                .unwrap_or_default();
            if kind == DYNAMIC_GLOB_KIND {
                for matched_url in dynamic_glob_matches
                    .get(&(row_id, ref_index))
                    .into_iter()
                    .flatten()
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
                    push_contextual_resolution(
                        &mut candidates,
                        (row_id, ref_index),
                        document_id,
                        result,
                        Some(matched_url.as_str()),
                        &mut routing,
                    )?;
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
            push_contextual_resolution(
                &mut candidates,
                (row_id, ref_index),
                document_id,
                result,
                None,
                &mut routing,
            )?;
        }
    }

    Ok(ContextEvidence {
        document_ids: contexts,
        candidates,
    })
}

/// Project contextual candidates to the existing JSON reference schema.
///
/// A reference is unambiguous only when every recorded document context
/// agrees on the *full* resolution signature, not just its URL.
pub(super) fn apply_reference_resolutions(
    rows: &mut [Value],
    evidence: &ContextEvidence,
    dynamic_glob_matches: &BTreeMap<ReferenceKey, Vec<String>>,
) -> Result<ResolutionStatistics> {
    let mut resolved_by_import_map = 0_usize;
    let mut unresolved_bare = 0_usize;
    let mut ambiguous = 0_usize;
    for (row_id, row) in rows.iter_mut().enumerate() {
        row.as_object_mut()
            .context("reference row must be object")?
            .insert(
                "document_resource_ids".into(),
                Value::Array(
                    evidence.document_ids[row_id]
                        .iter()
                        .copied()
                        .map(Value::from)
                        .collect(),
                ),
            );
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
            let kind = reference
                .get("kind")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_owned();
            let mut choices = evidence
                .candidates
                .get(&(row_id, ref_index))
                .map_or_default(|map| map.values().cloned().collect::<Vec<_>>());
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
                    resolved.pop_first().map_or(Value::Null, Value::String)
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

    Ok(ResolutionStatistics {
        resolved_by_import_map,
        unresolved_bare,
        ambiguous,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conflicting_document_maps_preserve_both_provenances() -> Result<()> {
        use crate::analysis_budget::{AnalysisBudgets, AnalysisOperation};

        let mut rows = vec![
            json!({
                "origin": "resource",
                "url": "https://app.test/shared.js",
                "references": [{"kind": "import_static", "specifier": "pkg"}]
            }),
            json!({
                "origin": "resource",
                "url": "https://app.test/mapped.js",
                "references": []
            }),
        ];
        let scripts = vec![
            json!({"script_type": "module", "parent_resource_id": 7,
                "resolved_src": "https://app.test/shared.js"}),
            json!({"script_type": "module", "parent_resource_id": 9,
                "resolved_src": "https://app.test/shared.js"}),
        ];
        let urls = BTreeMap::from([
            ("https://app.test/shared.js".to_owned(), vec![0]),
            ("https://app.test/mapped.js".to_owned(), vec![1]),
        ]);
        let mut mapped = ImportMap::default();
        mapped
            .imports
            .insert("pkg".into(), Some("https://app.test/mapped.js".into()));
        let maps = BTreeMap::from([(7, mapped)]);
        let budget = AnalysisBudgets::standard("context-fixture")
            .operation(AnalysisOperation::ReferenceScan, "two-documents");
        let evidence = propagate_context_evidence(
            &rows,
            &scripts,
            &urls,
            &BTreeMap::new(),
            &maps,
            &BTreeMap::new(),
            &budget,
        )?;
        assert_eq!(
            evidence.document_ids,
            vec![BTreeSet::from([7, 9]), BTreeSet::from([7])]
        );
        let stats = apply_reference_resolutions(&mut rows, &evidence, &BTreeMap::new())?;
        assert_eq!(stats.ambiguous, 1);
        let reference = &rows[0]["references"][0];
        assert_eq!(reference["resolution"], "ambiguous_document_context");
        assert!(reference["resolved_url"].is_null());
        assert!(reference["bare_specifier"].as_bool().unwrap_or(false));
        let choices = reference["resolution_candidates"]
            .as_array()
            .context("missing provenance candidates")?;
        assert_eq!(choices.len(), 2);
        assert!(choices
            .iter()
            .any(|candidate| candidate["document_resource_id"] == 7
                && candidate["resolution"] == "import_map"
                && candidate["resolved_url"] == "https://app.test/mapped.js"));
        assert!(choices
            .iter()
            .any(|candidate| candidate["document_resource_id"] == 9
                && candidate["resolution"] == "unresolved_bare"
                && candidate["resolved_url"].is_null()));
        Ok(())
    }

    #[test]
    fn identical_resolutions_keep_each_document_witness() -> Result<()> {
        let mut rows = vec![json!({"references": [
            {"kind": "import_static", "specifier": "pkg"}
        ]})];
        let target = json!({
            "resolved_url": "https://app.test/pkg.js",
            "bare_specifier": true,
            "resolution": "import_map",
            "import_map_key": "pkg",
            "scope": null
        });
        let mut candidate_a = target.clone();
        candidate_a["document_resource_id"] = json!(7);
        let mut candidate_b = target;
        candidate_b["document_resource_id"] = json!(9);
        let mut choices = BTreeMap::new();
        choices.insert(candidate_key(&candidate_a)?, candidate_a);
        choices.insert(candidate_key(&candidate_b)?, candidate_b);
        let evidence = ContextEvidence {
            document_ids: vec![BTreeSet::from([7, 9])],
            candidates: BTreeMap::from([((0, 0), choices)]),
        };
        let stats = apply_reference_resolutions(&mut rows, &evidence, &BTreeMap::new())?;
        assert_eq!(stats.resolved_by_import_map, 1);
        assert_eq!(stats.ambiguous, 0);
        let reference = &rows[0]["references"][0];
        assert_eq!(reference["resolution"], "import_map");
        assert_eq!(reference["resolved_url"], "https://app.test/pkg.js");
        assert_eq!(
            reference["resolution_candidates"].as_array().map(Vec::len),
            Some(2)
        );
        assert_eq!(rows[0]["document_resource_ids"], json!([7, 9]));
        Ok(())
    }

    #[test]
    fn equivalent_urls_with_different_resolution_proofs_remain_ambiguous() -> Result<()> {
        let mut rows = vec![json!({"references": [
            {"kind": "import_static", "specifier": "./pkg.js"}
        ]})];
        let mut choices = BTreeMap::new();
        for (document_id, resolution, map_key) in [
            (7, "url", Value::Null),
            (9, "import_map", json!("./pkg.js")),
        ] {
            let candidate = json!({
                "document_resource_id": document_id,
                "resolved_url": "https://app.test/pkg.js",
                "bare_specifier": false,
                "resolution": resolution,
                "import_map_key": map_key,
                "scope": null
            });
            choices.insert(candidate_key(&candidate)?, candidate);
        }
        let evidence = ContextEvidence {
            document_ids: vec![BTreeSet::from([7, 9])],
            candidates: BTreeMap::from([((0, 0), choices)]),
        };
        let stats = apply_reference_resolutions(&mut rows, &evidence, &BTreeMap::new())?;
        assert_eq!(stats.ambiguous, 1);
        assert!(rows[0]["references"][0]["resolved_url"].is_null());
        assert_eq!(
            rows[0]["references"][0]["resolution"],
            "ambiguous_document_context"
        );
        Ok(())
    }

    #[test]
    fn uncontextualized_globs_retain_all_captured_candidates() -> Result<()> {
        let mut rows = vec![json!({"references": [
            {"kind": "import_dynamic_glob", "glob": "./pages/*.js"},
            {"kind": "import_dynamic_glob", "glob": "./missing/*.js"}
        ]})];
        let matches = BTreeMap::from([
            (
                (0, 0),
                vec![
                    "https://app.test/pages/a.js".to_owned(),
                    "https://app.test/pages/b.js".to_owned(),
                ],
            ),
            ((0, 1), Vec::new()),
        ]);
        let evidence = ContextEvidence {
            document_ids: vec![BTreeSet::new()],
            candidates: BTreeMap::new(),
        };
        let stats = apply_reference_resolutions(&mut rows, &evidence, &matches)?;
        assert_eq!(stats.ambiguous, 0);
        let glob = &rows[0]["references"][0];
        assert_eq!(glob["candidate_count"], 2);
        assert_eq!(glob["resolution"], "captured_dynamic_glob");
        assert!(glob["resolved_url"].is_null());
        assert_eq!(
            glob["resolution_candidates"].as_array().map(Vec::len),
            Some(2)
        );
        assert_eq!(
            glob["resolution_candidates"][0]["document_resource_id"],
            Value::Null
        );
        let unmatched = &rows[0]["references"][1];
        assert_eq!(unmatched["candidate_count"], 0);
        assert_eq!(unmatched["resolution"], "captured_dynamic_glob_unmatched");
        assert!(unmatched["resolved_url"].is_null());
        Ok(())
    }

    #[test]
    fn import_and_glob_candidates_propagate_context_once_per_document() -> Result<()> {
        let units_by_url =
            BTreeMap::from([("https://example.test/dependency.js".to_owned(), vec![1, 2])]);
        let mut store = BTreeMap::new();
        let mut contexts = vec![BTreeSet::new(); 3];
        let mut queue = VecDeque::new();
        let mut routing = ContextRouting {
            units_by_url: &units_by_url,
            contexts: &mut contexts,
            queue: &mut queue,
        };
        let resolution = json!({
            "resolution": "url",
            "resolved_url": "https://example.test/dependency.js",
        });
        push_contextual_resolution(
            &mut store,
            (0, 0),
            7,
            resolution.clone(),
            None,
            &mut routing,
        )?;
        push_contextual_resolution(
            &mut store,
            (0, 0),
            7,
            resolution.clone(),
            None,
            &mut routing,
        )?;
        assert_eq!(store[&(0, 0)].len(), 1);
        assert_eq!(
            store[&(0, 0)]
                .values()
                .next()
                .context("import candidate missing")?["document_resource_id"],
            7
        );
        assert_eq!(routing.queue.len(), 2);
        assert_eq!(routing.contexts[1], BTreeSet::from([7]));
        assert_eq!(routing.contexts[2], BTreeSet::from([7]));

        push_contextual_resolution(
            &mut store,
            (0, 1),
            9,
            resolution,
            Some("https://example.test/dependency.js"),
            &mut routing,
        )?;
        let glob = store[&(0, 1)]
            .values()
            .next()
            .context("glob candidate missing")?;
        assert_eq!(glob["document_resource_id"], 9);
        assert_eq!(glob["glob_match_url"], "https://example.test/dependency.js");
        assert_eq!(routing.contexts[1], BTreeSet::from([7, 9]));
        assert_eq!(routing.contexts[2], BTreeSet::from([7, 9]));
        assert_eq!(routing.queue.len(), 4);
        Ok(())
    }
}
