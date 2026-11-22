mod builder;
mod bundle_evidence;
mod capture_evidence;
mod generated_evidence;
mod reference_evidence;
mod runtime_evidence;
mod runtime_wasm_evidence;
mod sourcemap_evidence;
mod static_evidence;
mod trace_evidence;
mod wasm_evidence;

use crate::{
    analysis_artifacts::{
        load_artifact, API_SURFACE, BUNDLES, DEOBFUSCATION, IMPORT_MAPS, JSVM_INDEX, JS_REFERENCES,
        RUNTIME_SCRIPTS, SELECTIVE_TRACE, SOURCEMAPS, SOURCE_INDEX, WASM_INDEX,
        WASM_RESOURCE_PROVENANCE,
    },
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    capture_project::load_manifest,
    sha256_hex,
};
use anyhow::{Context, Result};
use builder::GraphBuilder;
use capture_evidence::InlineSourceIndex;
use runtime_evidence::seed_runtime_script_evidence;
use serde_json::{json, Map, Value};
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceGraphSummary {
    pub nodes: usize,
    pub edges: usize,
    pub unresolved_edges: usize,
    pub external_urls: usize,
}

fn field(value: &Value, key: &str) -> Value {
    value.get(key).cloned().unwrap_or(Value::Null)
}

fn array_field<'a>(value: &'a Value, key: &str) -> &'a [Value] {
    value
        .get(key)
        .and_then(Value::as_array)
        .map_or_default(Vec::as_slice)
}

fn object_field<'a>(value: &'a Value, key: &str) -> Option<&'a Map<String, Value>> {
    value.get(key).and_then(Value::as_object)
}

fn string_field<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

fn nonempty_string_field<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    string_field(value, key).filter(|value| !value.is_empty())
}

fn u64_field(value: &Value, key: &str) -> Option<u64> {
    value.get(key).and_then(Value::as_u64)
}

fn required_u64(value: &Value, key: &str, label: &str) -> Result<u64> {
    u64_field(value, key).with_context(|| format!("{label}.{key} must be a non-negative integer"))
}

fn bool_field(value: &Value, key: &str) -> bool {
    value.get(key).and_then(Value::as_bool).unwrap_or(false)
}

fn compact_key(parts: impl serde::Serialize) -> Result<String> {
    Ok(serde_json::to_string(&parts)?)
}

fn digest_id(prefix: &str, text: &str) -> String {
    format!("{prefix}{}", &sha256_hex(text.as_bytes())[..20])
}

fn optional_artifact(
    project: &Path,
    spec: crate::analysis_artifacts::ArtifactSpec,
    fallback: Value,
) -> Result<Value> {
    Ok(load_artifact(project, spec, true)?.unwrap_or(fallback))
}

/// Build the project source/provenance graph from indexed capture evidence.
///
/// # Errors
///
/// Fails when the project path cannot be resolved, its manifest or linked artifacts cannot be
/// read or persisted, or the graph traversal exhausts its analysis budget.
pub fn build_source_graph(project: &Path, budgets: &AnalysisBudgets) -> Result<SourceGraphSummary> {
    let budget = budgets.operation(
        AnalysisOperation::SourceGraph,
        project.display().to_string(),
    );
    budget.checkpoint()?;
    let project = project
        .canonicalize()
        .with_context(|| format!("capture project does not exist: {}", project.display()))?;
    let manifest = load_manifest(&project)?;
    let source_index = optional_artifact(&project, SOURCE_INDEX, json!({"units":[]}))?;
    let sourcemaps = optional_artifact(&project, SOURCEMAPS, json!({"source_maps":[]}))?;
    let jsvm = optional_artifact(
        &project,
        JSVM_INDEX,
        json!({"code_units":[], "dynamic_code_units":[], "devirtualized_units":[]}),
    )?;
    let jsrefs = optional_artifact(&project, JS_REFERENCES, json!({"code_units":[]}))?;
    let deobfuscation = optional_artifact(&project, DEOBFUSCATION, json!({"units":[]}))?;
    let api_surface = optional_artifact(&project, API_SURFACE, json!({"callsites":[]}))?;
    let bundles = optional_artifact(&project, BUNDLES, json!({"bundles":[], "modules":[]}))?;
    let wasm = optional_artifact(&project, WASM_INDEX, json!({"modules":[]}))?;
    let wasm_resource_provenance = optional_artifact(
        &project,
        WASM_RESOURCE_PROVENANCE,
        json!({"observations":[], "unmatched":[], "summary":{}}),
    )?;
    let runtime = optional_artifact(
        &project,
        RUNTIME_SCRIPTS,
        json!({"sources":[], "alpine_families":[], "gtm_families":[], "script_identity_conflicts":[]}),
    )?;
    let selective_trace = optional_artifact(
        &project,
        SELECTIVE_TRACE,
        json!({"hits":[], "errors":[], "summary":{}}),
    )?;
    let import_maps = optional_artifact(
        &project,
        IMPORT_MAPS,
        json!({"maps":[], "documents":{}, "summary":{}}),
    )?;

    let mut graph = GraphBuilder::default();
    let capture_evidence::CapturedSourceIndex {
        resource_nodes_by_sha,
        inline_nodes,
        inline_nodes_by_sha,
    } = capture_evidence::seed_capture_evidence(&mut graph, &manifest, &source_index, &budget)?;

    let runtime_instances = seed_runtime_script_evidence(
        &mut graph,
        &runtime,
        &source_index,
        &deobfuscation,
        &resource_nodes_by_sha,
        &inline_nodes_by_sha,
        &budget,
    )?;
    trace_evidence::seed_selective_trace_witnesses(
        &mut graph,
        &selective_trace,
        &runtime_instances,
        &budget,
    )?;

    runtime_wasm_evidence::seed_runtime_wasm_observations(
        &mut graph,
        &wasm_resource_provenance,
        &runtime_instances,
        &budget,
    )?;

    let deob_nodes = static_evidence::seed_safe_deobfuscation_sources(
        &mut graph,
        &deobfuscation,
        &inline_nodes,
        &budget,
    )?;
    static_evidence::seed_browser_api_callsites(
        &mut graph,
        &api_surface,
        &deob_nodes,
        &inline_nodes,
        &budget,
    )?;

    bundle_evidence::seed_bundle_evidence(&mut graph, &bundles, &deob_nodes, &budget)?;

    sourcemap_evidence::seed_sourcemap_evidence(&mut graph, &sourcemaps, &budget)?;

    generated_evidence::seed_generated_and_vm_evidence(&mut graph, &jsvm, &deob_nodes, &budget)?;

    reference_evidence::seed_import_map_definitions(
        &mut graph,
        &import_maps,
        &inline_nodes,
        &budget,
    )?;
    reference_evidence::seed_js_reference_edges(&mut graph, &jsrefs, &inline_nodes, &budget)?;

    wasm_evidence::seed_static_wasm_modules(&mut graph, &wasm, &budget)?;

    graph.finish(&project, &manifest, &budget)
}

#[cfg(test)]
mod tests {
    use super::capture_evidence::{
        seed_captured_inline_scripts, seed_captured_reference_edges, seed_captured_resources,
        seed_navigation_roots,
    };
    use super::runtime_evidence::add_runtime_network_source_edges;
    use super::*;
    use crate::runtime_coverage::RuntimeCoverageIndex;
    use crate::{
        analysis_artifacts::{load_artifact, write_artifact, JS_REFERENCES, SOURCE_GRAPH},
        capture_project::{write_manifest, CaptureManifest, CaptureSource, MANIFEST_NAME},
    };
    use std::collections::{BTreeMap, BTreeSet};

    fn seeded_capture_fixture() -> CaptureManifest {
        let shared = "https://fixture.invalid/shared.js";
        CaptureManifest {
            schema: "capture-project/v1".into(),
            source: CaptureSource {
                kind: "har".into(),
                input: "shared-resource-fixture".into(),
                salvaged: false,
                extra: Map::new(),
            },
            pages: vec![json!({
                "kind":"recorder_navigation",
                "requested_url":"https://fixture.invalid/entry",
                "final_url":shared,
            })],
            resources: vec![
                json!({"id":3,"url":shared,"sha256":"same-digest",
                    "kind":"javascript","output_path":"resources/a.js"}),
                json!({"id":9,"url":shared,"sha256":"same-digest",
                    "kind":"javascript","output_path":"resources/b.bin",
                    "saved_page_reference_roles":["css","javascript"]}),
                json!({"id":12,"url":"https://fixture.invalid/redirect",
                    "references":[{"kind":"script_src","raw":"shared.js","resolved_url":shared}],
                    "response_headers":[{"name":"LoCaTiOn","value":"./shared.js"}]}),
            ],
            inline_scripts: vec![
                json!({"parent_resource_id":3,"ordinal":1,
                    "output_path":"resources/inline.js","sha256":"inline-digest"}),
                json!({"parent_resource_id":3,"ordinal":2,
                    "output_path":"resources/inline.js","sha256":"inline-digest"}),
            ],
            counts: BTreeMap::new(),
            extra: Map::new(),
        }
    }

    #[test]
    fn captured_graph_seed_preserves_shared_response_and_inline_identities() -> Result<()> {
        let manifest = seeded_capture_fixture();
        let source_index = json!({"units":[
            {"resource_id":3,"source_path":"src/a.js"},
            {"resource_id":9,"source_path":"src/b.js"},
        ]});
        let budget = work_budget::WorkBudget::new(
            "captured-graph-seed",
            work_budget::BudgetLimits::unlimited(),
        );
        let mut graph = GraphBuilder::default();
        let resources = seed_captured_resources(&mut graph, &manifest, &source_index, &budget)?;
        seed_navigation_roots(&mut graph, &manifest, &budget)?;
        seed_captured_reference_edges(&mut graph, &manifest, &budget)?;
        let (inline, inline_by_sha) = seed_captured_inline_scripts(&mut graph, &manifest, &budget)?;

        assert_eq!(resources["same-digest"], ["resource:3", "resource:9"]);
        assert_eq!(
            graph.captured_targets("https://fixture.invalid/shared.js"),
            Some(&BTreeSet::from(["resource:3".into(), "resource:9".into()]))
        );
        assert_eq!(
            graph.node_value("resource:3")["source_paths"],
            json!(["src/a.js"])
        );
        assert_eq!(
            graph.node_value("resource:9")["source_paths"],
            json!(["src/b.js"])
        );
        assert_eq!(
            graph.node_value("resource:9")["saved_page_reference_roles"],
            json!(["css", "javascript"])
        );
        for kind in ["observed_navigation", "script_src", "redirect"] {
            let matching = graph
                .edges()
                .values()
                .filter(|edge| {
                    edge["kind"] == kind
                        && matches!(edge["to"].as_str(), Some("resource:3" | "resource:9"))
                })
                .count();
            assert_eq!(matching, 2, "shared URL must retain both {kind} candidates");
        }
        assert_eq!(
            graph
                .edges()
                .values()
                .filter(|edge| edge["kind"] == "requested_navigation")
                .count(),
            1,
            "unmatched navigation must remain an explicit external URL"
        );
        assert_eq!(inline_by_sha["inline-digest"], ["inline:3:1", "inline:3:2"]);
        for ordinal in [1, 2] {
            assert_eq!(
                inline.exact("resources/inline.js", 3, ordinal),
                Some(format!("inline:3:{ordinal}"))
            );
        }
        assert!(inline
            .for_record(&json!({"raw_path":"resources/inline.js"}))
            .is_none());
        let destination = tempfile::tempdir()?;
        let summary = graph.finish(destination.path(), &manifest, &budget)?;
        assert_eq!(summary.external_urls, 1);
        let artifact = load_artifact(destination.path(), SOURCE_GRAPH, false)?
            .context("finalized graph artifact missing")?;
        assert_eq!(artifact["summary"]["edge_kinds"]["redirect"], 2);
        assert_eq!(artifact["summary"]["edge_kinds"]["script_src"], 2);
        assert_eq!(artifact["summary"]["edge_kinds"]["inline_script"], 2);
        assert_eq!(artifact["summary"]["node_types"]["external_url"], 1);
        Ok(())
    }

    fn runtime_match_test_graph() -> Result<(GraphBuilder, BTreeMap<String, Vec<String>>)> {
        let mut graph = GraphBuilder::default();
        let mut hashes = BTreeMap::<String, Vec<String>>::new();
        for (id, url, digest) in [
            ("resource:1", "https://fixture.invalid/app.js", "alpha"),
            ("resource:2", "https://fixture.invalid/app.js", "beta"),
            ("resource:3", "https://fixture.invalid/copy.js", "alpha"),
        ] {
            graph.insert_node(
                id,
                json!({
                    "type":"resource","kind":"javascript","url":url,"sha256":digest
                }),
            )?;
            graph.register_resource_url(url, id);
            hashes
                .entry(digest.to_owned())
                .or_default()
                .push(id.to_owned());
        }
        Ok((graph, hashes))
    }

    #[test]
    fn runtime_network_execution_requires_unique_hash_url_and_positive_matching_instance(
    ) -> Result<()> {
        let (mut graph, hashes) = runtime_match_test_graph()?;
        let runtime = json!({
            "sha256":"alpha","urls":["https://fixture.invalid/app.js"],
            "observed_executed":true,
            "coverage_mode":"best-effort",
            "script_instances":[{
                "cdp_session":"main","script_id":"1","script_url":"https://fixture.invalid/copy.js",
                "execution":{"status":"positive","positive_functions":1,"positive_ranges":1}
            }]
        });
        let budget = work_budget::WorkBudget::unlimited("runtime-network-test");
        let coverage = RuntimeCoverageIndex::build(&json!({"sources":[runtime]}), &budget)?;
        add_runtime_network_source_edges(
            &mut graph,
            &runtime,
            "runtime:parsed",
            &hashes,
            coverage.witnesses(runtime["sha256"].as_str().unwrap_or_default()),
            &budget,
        )?;
        let parsed = graph
            .edges()
            .values()
            .filter(|edge| edge["to"] == "runtime:parsed")
            .collect::<Vec<_>>();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0]["from"], "resource:1");
        assert_eq!(parsed[0]["kind"], "runtime_source_match");
        assert_eq!(parsed[0]["identity_basis"], "sha256_and_url");
        assert_eq!(parsed[0]["exact_response_identity"], true);
        assert_eq!(parsed[0]["runtime_execution_observed"], false);
        assert_eq!(parsed[0]["coverage_mode"], "best-effort");

        let mut confirmed = runtime;
        confirmed["script_instances"][0]["script_url"] = json!("https://fixture.invalid/app.js");
        let budget = work_budget::WorkBudget::unlimited("runtime-network-test");
        let coverage = RuntimeCoverageIndex::build(&json!({"sources":[confirmed]}), &budget)?;
        add_runtime_network_source_edges(
            &mut graph,
            &confirmed,
            "runtime:executed",
            &hashes,
            coverage.witnesses(confirmed["sha256"].as_str().unwrap_or_default()),
            &budget,
        )?;
        let executed = graph
            .edges()
            .values()
            .filter(|edge| edge["to"] == "runtime:executed")
            .collect::<Vec<_>>();
        assert_eq!(executed.len(), 1);
        assert_eq!(executed[0]["from"], "resource:1");
        assert_eq!(executed[0]["kind"], "runtime_execution");
        assert_eq!(executed[0]["runtime_execution_observed"], true);
        assert_eq!(executed[0]["coverage_mode"], "best-effort");
        Ok(())
    }

    #[test]
    fn runtime_url_and_hash_only_matches_remain_ambiguous_candidates() -> Result<()> {
        let (mut graph, hashes) = runtime_match_test_graph()?;
        let runtime = json!({
            "sha256":"missing","urls":["https://fixture.invalid/app.js"],
            "observed_executed":true,
            "script_instances":[{
                "cdp_session":"main","script_id":"1","script_url":"https://fixture.invalid/app.js",
                "execution":{"status":"positive","positive_functions":1,"positive_ranges":1}
            }]
        });
        let budget = work_budget::WorkBudget::unlimited("runtime-network-test");
        let coverage = RuntimeCoverageIndex::build(&json!({"sources":[runtime]}), &budget)?;
        add_runtime_network_source_edges(
            &mut graph,
            &runtime,
            "runtime:url-only",
            &hashes,
            coverage.witnesses(runtime["sha256"].as_str().unwrap_or_default()),
            &budget,
        )?;
        let url_edges = graph
            .edges()
            .values()
            .filter(|edge| edge["to"] == "runtime:url-only")
            .collect::<Vec<_>>();
        assert_eq!(url_edges.len(), 2);
        assert_eq!(
            url_edges
                .iter()
                .map(|edge| edge["from"].as_str().unwrap_or(""))
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["resource:1", "resource:2"])
        );
        for edge in url_edges {
            assert_eq!(edge["kind"], "runtime_source_candidate");
            assert_eq!(edge["identity_basis"], "url_only");
            assert_eq!(edge["candidate_count"], 2);
            assert_eq!(edge["exact_response_identity"], false);
        }
        let sha_only = json!({"sha256":"alpha","urls":[],"observed_executed":true});
        let budget = work_budget::WorkBudget::unlimited("runtime-network-test");
        let coverage = RuntimeCoverageIndex::build(&json!({"sources":[sha_only]}), &budget)?;
        add_runtime_network_source_edges(
            &mut graph,
            &sha_only,
            "runtime:sha-only",
            &hashes,
            coverage.witnesses(sha_only["sha256"].as_str().unwrap_or_default()),
            &budget,
        )?;
        let hash_edges = graph
            .edges()
            .values()
            .filter(|edge| edge["to"] == "runtime:sha-only")
            .collect::<Vec<_>>();
        assert_eq!(hash_edges.len(), 2);
        assert_eq!(
            hash_edges
                .iter()
                .map(|edge| edge["from"].as_str().unwrap_or(""))
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["resource:1", "resource:3"])
        );
        for edge in hash_edges {
            assert_eq!(edge["kind"], "runtime_source_candidate");
            assert_eq!(edge["identity_basis"], "sha256_only");
            assert_eq!(edge["exact_response_identity"], false);
        }
        Ok(())
    }

    #[test]
    fn shared_inline_bytes_require_exact_parent_and_ordinal() -> Result<()> {
        let mut sources = InlineSourceIndex::default();
        sources.insert("resources/shared.js", 7, 2, "inline:7:2".into())?;
        sources.insert("resources/shared.js", 7, 3, "inline:7:3".into())?;
        sources.insert("resources/shared.js", 8, 2, "inline:8:2".into())?;
        for (parent, ordinal) in [(7, 2), (7, 3), (8, 2)] {
            assert_eq!(
                sources.exact("resources/shared.js", parent, ordinal),
                Some(format!("inline:{parent}:{ordinal}"))
            );
            assert_eq!(
                sources.for_record(&json!({
                    "raw_path":"resources/shared.js",
                    "resource_id":parent,"ordinal":ordinal
                })),
                Some(format!("inline:{parent}:{ordinal}"))
            );
        }
        assert_eq!(
            sources.for_record(&json!({"raw_path":"resources/shared.js"})),
            None
        );
        assert!(sources
            .insert("resources/shared.js", 7, 2, "other".into())
            .is_err());
        Ok(())
    }

    // Reusable captured-resource/reference inventory for document-context proof regressions.
    fn write_contextual_reference_fixture(project: &Path) -> Result<()> {
        let source_url = "https://example.test/entry.js";
        let exact_url = "https://example.test/exact.js";
        let stale_url = "https://example.test/stale.js";
        let manifest = CaptureManifest {
            schema: "capture-project/v1".into(),
            source: CaptureSource {
                kind: "har".into(),
                input: "context-fixture".into(),
                salvaged: false,
                extra: Map::new(),
            },
            pages: vec![],
            resources: vec![
                json!({"id":7,"url":source_url,"kind":"javascript"}),
                json!({"id":42,"url":exact_url,"kind":"javascript"}),
                json!({"id":99,"url":stale_url,"kind":"javascript"}),
            ],
            inline_scripts: vec![],
            counts: BTreeMap::new(),
            extra: Map::new(),
        };
        write_manifest(&project.join(MANIFEST_NAME), &manifest)?;
        write_artifact(
            project,
            JS_REFERENCES,
            &json!({
                "schema":JS_REFERENCES.schema,
                "summary":{},
                "code_units":[{
                    "resource_id":7,"raw_path":"resources/entry.js",
                    "references":[
                        {
                            "kind":"import_static","specifier":"per_document",
                            "resolved_url":stale_url,"resolution":"url",
                            "resolution_candidates":[
                                {"document_resource_id":3,"resolved_url":exact_url,
                                 "resolution":"import_map","import_map_key":"per_document"},
                                {"document_resource_id":4,"resolved_url":stale_url,
                                 "resolution":"import_map_blocked"}
                            ]
                        },
                        {
                            "kind":"import_static","specifier":"empty_inventory",
                            "resolved_url":stale_url,"resolution":"url",
                            "resolution_candidates":[]
                        },
                        {
                            "kind":"import_static","specifier":"malformed_inventory",
                            "resolved_url":stale_url,"resolution":"url",
                            "resolution_candidates":"malformed"
                        },
                        {
                            "kind":"import_dynamic","specifier":"dynamic_blocked",
                            "resolved_url":stale_url,"resolution":"url",
                            "resolution_candidates":[{
                                "document_resource_id":3,"resolved_url":stale_url,
                                "resolution":"captured_dynamic_glob_import_map_blocked"
                            }]
                        },
                        {
                            "kind":"import_static","specifier":"legacy",
                            "resolved_url":stale_url,"resolution":"url"
                        }
                    ]
                }]
            }),
        )?;
        build_source_graph(
            project,
            &AnalysisBudgets::standard("source-graph-contextual-proof-test"),
        )?;
        Ok(())
    }

    #[test]
    fn source_graph_never_upgrades_contextual_summaries_or_blocked_imports() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path().join("project");
        std::fs::create_dir_all(&project)?;
        write_contextual_reference_fixture(&project)?;
        let graph = load_artifact(&project, SOURCE_GRAPH, false)?.context("missing graph")?;
        let edges = graph["edges"].as_array().context("missing graph edges")?;
        let refs = edges
            .iter()
            .filter(|edge| {
                edge["from"] == "resource:7"
                    && edge["kind"]
                        .as_str()
                        .is_some_and(|kind| kind.starts_with("js_"))
            })
            .collect::<Vec<_>>();
        let at = |specifier: &str| {
            refs.iter()
                .copied()
                .filter(|edge| edge["specifier"] == specifier)
                .collect::<Vec<_>>()
        };
        let exact = at("per_document");
        assert_eq!(exact.len(), 2);
        assert!(exact.iter().any(|edge| {
            edge["to"] == "resource:42"
                && edge["document_resource_id"] == 3
                && edge["resolution"] == "import_map"
                && edge["import_map_key"] == "per_document"
        }));
        assert!(exact.iter().any(|edge| {
            edge["to"]
                .as_str()
                .is_some_and(|id| id.starts_with("specifier:"))
                && edge["document_resource_id"] == 4
                && edge["resolution"] == "import_map_blocked"
                && edge["blocked"] == true
                && edge["resolved_url"].is_null()
        }));
        for specifier in ["empty_inventory", "malformed_inventory"] {
            let unresolved = at(specifier);
            assert_eq!(unresolved.len(), 1);
            assert_eq!(
                unresolved[0]["resolution"],
                "no_matching_contextual_resolution"
            );
            assert!(unresolved[0]["resolved_url"].is_null());
            assert!(unresolved[0]["to"]
                .as_str()
                .is_some_and(|id| id.starts_with("specifier:")));
        }
        let blocked = at("dynamic_blocked");
        assert_eq!(blocked.len(), 1);
        assert_eq!(blocked[0]["blocked"], true);
        assert_eq!(
            blocked[0]["resolution"],
            "captured_dynamic_glob_import_map_blocked"
        );
        assert_eq!(blocked[0]["document_resource_id"], 3);
        assert!(blocked[0]["resolved_url"].is_null());
        let legacy = at("legacy");
        assert_eq!(legacy.len(), 1);
        assert_eq!(legacy[0]["to"], "resource:99");
        assert!(legacy[0]["document_resource_id"].is_null());
        assert!(refs
            .iter()
            .all(|edge| { edge["to"] != "resource:99" || edge["specifier"] == "legacy" }));
        Ok(())
    }

    #[test]
    fn runtime_script_exact_source_identity_connects_to_safe_deob_result() -> Result<()> {
        use crate::analysis_artifacts::{
            write_artifact, DEOBFUSCATION, RUNTIME_SCRIPTS, SOURCE_INDEX,
        };

        let temp = tempfile::tempdir()?;
        let project = temp.path().join("project");
        std::fs::create_dir_all(&project)?;
        let digest = "c".repeat(64);
        let raw_path = format!("resources/runtime-scripts/{digest}.js");
        let view = format!("src/runtime-scripts/{digest}.js");
        let readable = format!("src/_readable/runtime-scripts/{digest}.js");
        let manifest = CaptureManifest {
            schema: "capture-project/v1".into(),
            source: CaptureSource {
                kind: "recorder".into(),
                input: "fixture-recorder".into(),
                salvaged: false,
                extra: Map::new(),
            },
            pages: vec![],
            resources: vec![],
            inline_scripts: vec![],
            counts: BTreeMap::new(),
            extra: Map::new(),
        };
        write_manifest(&project.join(MANIFEST_NAME), &manifest)?;
        write_artifact(
            &project,
            RUNTIME_SCRIPTS,
            &json!({
                "schema": RUNTIME_SCRIPTS.schema,
                "script_identity_conflicts":[],
                "sources": [{
                    "sha256": digest, "path": format!("runtime-scripts/{digest}.js"),
                    "classification":"generated_runtime",
                }],
                "alpine_families":[], "gtm_families":[], "summary":{},
            }),
        )?;
        write_artifact(
            &project,
            SOURCE_INDEX,
            &json!({
                "schema": SOURCE_INDEX.schema,
                "units": [{
                    "origin":"runtime_script", "kind":"javascript",
                    "raw_path":raw_path, "source_path":view,
                    "input_sha256":digest, "resource_id":Value::Null,
                }],
                "summary":{},
            }),
        )?;
        write_artifact(
            &project,
            DEOBFUSCATION,
            &json!({
                "schema": DEOBFUSCATION.schema,
                "units": [{
                    "ordinal":0, "raw_path":raw_path,
                    "input_sha256":digest, "readable_output_path":readable,
                    "output_path":format!("src/_deobfuscated/runtime-scripts/{digest}.js"),
                    "exit":0, "changed":true,
                }],
                "summary":{},
            }),
        )?;
        build_source_graph(
            &project,
            &AnalysisBudgets::standard("runtime-origin-graph-test"),
        )?;
        let graph = load_artifact(&project, SOURCE_GRAPH, false)?.context("missing graph")?;
        assert!(graph["edges"]
            .as_array()
            .is_some_and(|edges| edges
                .iter()
                .any(|edge| edge["from"] == format!("runtime:{}", &digest[..20])
                    && edge["to"] == "deobfuscated:0"
                    && edge["kind"] == "safe_deobfuscation")));
        let runtime = graph["nodes"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|node| node["id"] == format!("runtime:{}", &digest[..20]))
            .context("missing runtime node")?;
        assert_eq!(runtime["general_source_path"], view);
        assert_eq!(runtime["safe_readable_source_path"], readable);
        Ok(())
    }

    #[test]
    fn sparse_resource_ids_and_redirects_remain_first_class_graph_edges() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path().join("project");
        std::fs::create_dir_all(&project)?;
        let manifest = CaptureManifest {
            schema: "capture-project/v1".into(),
            source: CaptureSource {
                kind: "har".into(),
                input: "/tmp/input.har".into(),
                salvaged: false,
                extra: Map::new(),
            },
            pages: Vec::new(),
            resources: vec![
                json!({
                    "id":7,
                    "url":"https://example.test/a.js",
                    "kind":"javascript",
                    "status":302,
                    "body_present":false,
                    "output_path":Value::Null,
                    "response_headers":[{"name":"Location","value":"/b.js"}],
                    "references":[]
                }),
                json!({
                    "id":42,
                    "url":"https://example.test/b.js",
                    "kind":"javascript",
                    "status":200,
                    "body_present":true,
                    "output_path":"resources/b.js",
                    "sha256":"0123456789012345678901234567890123456789012345678901234567890123",
                    "response_headers":[],
                    "references":[]
                }),
            ],
            inline_scripts: Vec::new(),
            counts: BTreeMap::new(),
            extra: Map::new(),
        };
        write_manifest(&project.join(MANIFEST_NAME), &manifest)?;
        let summary =
            build_source_graph(&project, &AnalysisBudgets::standard("source-graph-test"))?;
        assert_eq!(summary.nodes, 2);
        assert_eq!(summary.edges, 1);
        assert_eq!(summary.external_urls, 0);
        let artifact = load_artifact(&project, SOURCE_GRAPH, false)?.context("missing graph")?;
        assert!(artifact["nodes"]
            .as_array()
            .is_some_and(|nodes| nodes.iter().any(|node| node["id"] == "resource:42")));
        assert!(artifact["edges"]
            .as_array()
            .is_some_and(|edges| edges.iter().any(|edge| {
                edge["from"] == "resource:7"
                    && edge["to"] == "resource:42"
                    && edge["kind"] == "redirect"
            })));
        Ok(())
    }
    #[test]
    fn graph_publication_separates_links_from_incomplete_endpoint_claims() -> Result<()> {
        let destination = tempfile::tempdir()?;
        let manifest = seeded_capture_fixture();
        let mut graph = GraphBuilder::default();
        let budget = work_budget::WorkBudget::unlimited("graph-endpoint-closure");
        graph.insert_node("a", json!({"type":"resource"}))?;
        graph.add_edge("a", "b", "forward", json!({"witness":1}))?;
        graph.add_edge("a", "missing", "claim", json!({"witness":2}))?;
        graph.add_edge("other", "b", "claim", json!({"witness":3}))?;
        graph.add_edge("other", "missing", "claim", json!({"witness":4}))?;
        graph.add_edge("missing", "missing", "self", json!({"witness":5}))?;
        graph.insert_node("b", json!({"type":"resource"}))?;
        let summary = graph.finish(destination.path(), &manifest, &budget)?;
        assert_eq!(summary.nodes, 2);
        assert_eq!(summary.edges, 1);
        assert_eq!(summary.unresolved_edges, 4);
        let artifact =
            load_artifact(destination.path(), SOURCE_GRAPH, false)?.context("missing graph")?;
        assert_eq!(artifact["schema"], "source-graph/v2");
        assert_eq!(
            artifact["edges"],
            json!([{"from":"a","to":"b","kind":"forward","witness":1}])
        );
        let claims = artifact["unresolved_edges"]
            .as_array()
            .context("missing claims")?;
        for (witness, missing) in [
            (2, json!(["to"])),
            (3, json!(["from"])),
            (4, json!(["from", "to"])),
            (5, json!(["from", "to"])),
        ] {
            let claim = claims
                .iter()
                .find(|claim| claim["edge"]["witness"] == witness)
                .context("missing original edge claim")?;
            assert_eq!(claim["missing_endpoints"], missing);
        }
        assert_eq!(artifact["summary"]["edge_kinds"], json!({"forward":1}));
        assert_eq!(
            artifact["summary"]["unresolved_edge_kinds"],
            json!({"claim":3,"self":1})
        );
        Ok(())
    }
}
