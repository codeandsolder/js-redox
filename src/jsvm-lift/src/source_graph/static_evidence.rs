//! Static evidence stages: safe-deobfuscation derivatives and browser API callsites.
//!
//! Source identity is resolved before graph edges are emitted. A source
//! derivative is not runtime execution proof, and a callsite's selected
//! derivative takes precedence over its original captured source.

use super::{
    array_field, bool_field, field, required_u64, string_field, u64_field, GraphBuilder,
    InlineSourceIndex, RuntimeSourceGraphIndex,
};
use anyhow::{bail, Result};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use work_budget::WorkBudget;

/// Add provenance-preserving safe static deobfuscation results.
///
/// The ordinal index is subsequently used to associate API callsites and
/// bundle payloads with their exact selected source derivative.
pub(super) fn seed_safe_deobfuscation_sources(
    graph: &mut GraphBuilder,
    deobfuscation: &Value,
    inline_nodes: &InlineSourceIndex,
    runtime_index: &RuntimeSourceGraphIndex,
    budget: &WorkBudget,
) -> Result<BTreeMap<u64, String>> {
    // Safe static deobfuscation is a provenance-preserving source transform.
    let mut deob_nodes = BTreeMap::<u64, String>::new();
    for unit in array_field(deobfuscation, "units") {
        budget.checkpoint()?;
        if unit.get("exit").and_then(Value::as_i64).unwrap_or(0) != 0 {
            continue;
        }
        let ordinal = u64_field(unit, "ordinal").unwrap_or(0);
        let node_id = format!("deobfuscated:{ordinal}");
        deob_nodes.insert(ordinal, node_id.clone());
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"deobfuscated_source",
                "resource_id":field(unit,"resource_id"),
                "input_path":field(unit,"input_path"),
                "source_path":field(unit,"output_path"),
                "readable_source_path":field(unit,"readable_output_path"),
                "readable_formatted":bool_field(unit,"readable_formatted"),
                "input_sha256":field(unit,"input_sha256"),
                "output_sha256":field(unit,"output_sha256"),
                "changed":bool_field(unit,"changed"),
                "iterations":field(unit,"iterations"),
                "transforms":unit.get("transforms").cloned().unwrap_or_else(|| json!({})),
                "arithmetic_state_proofs":unit.get("arithmetic_state_proofs").cloned().unwrap_or_else(|| json!([])),
                "string_recovery_report_path":field(unit,"string_recovery_report_path"),
                "string_recovery_changed":bool_field(unit,"string_recovery_changed"),
                "string_recovery_replacements":unit.get("string_recovery_replacements").cloned().unwrap_or_else(|| json!(0)),
                "pre_deob_sha256":field(unit,"pre_deob_sha256"),
                "safe_static_only":true,
                "presentation_formatted":bool_field(unit,"presentation_formatted"),
                "runtime_semantics_preserved_by_design":unit.get("runtime_semantics_preserved_by_design").and_then(Value::as_bool).unwrap_or(true),
            }),
        )?;
        let parent = string_field(unit, "raw_path")
            .and_then(|raw| {
                inline_nodes.for_record(unit).or_else(|| {
                    // CDP runtime source bodies are not synthetic HTTP
                    // resources. Connect their deobfuscation result to the
                    // independently captured runtime-script node by exact
                    // content-addressed identity, not a guessed URL.
                    let digest = raw
                        .strip_prefix("resources/runtime-scripts/")?
                        .strip_suffix(".js")?;
                    if string_field(unit, "input_sha256") != Some(digest)
                        || !runtime_index.general_paths.contains_key(digest)
                    {
                        return None;
                    }
                    Some(format!("runtime:{}", &digest[..digest.len().min(20)]))
                })
            })
            .or_else(|| {
                u64_field(unit, "resource_id").map(|resource_id| format!("resource:{resource_id}"))
            });
        if let Some(parent) = parent {
            graph.add_edge(
                &parent,
                &node_id,
                "safe_deobfuscation",
                json!({
                    "changed":bool_field(unit,"changed"),
                    "transforms":unit.get("transforms").cloned().unwrap_or_else(|| json!({})),
                    "string_recovery_replacements":unit.get("string_recovery_replacements").cloned().unwrap_or_else(|| json!(0)),
                }),
            )?;
        }
    }

    Ok(deob_nodes)
}

/// Resolve the exact chosen source derivative for an API mutation or call.
/// Both kinds of observation must attach to the same selected source.
fn api_source_parent(
    row: &Value,
    deob_nodes: &BTreeMap<u64, String>,
    inline_nodes: &InlineSourceIndex,
) -> Option<String> {
    u64_field(row, "deobfuscation_ordinal")
        .and_then(|ordinal| deob_nodes.get(&ordinal).cloned())
        .or_else(|| inline_nodes.for_record(row))
        .or_else(|| {
            u64_field(row, "resource_id").map(|resource_id| format!("resource:{resource_id}"))
        })
}

/// Attach browser API callsites and exact local mutation-site provenance to
/// the selected source derivative. Static graph edges do not prove execution.
pub(super) fn seed_browser_api_callsites(
    graph: &mut GraphBuilder,
    api_surface: &Value,
    deob_nodes: &BTreeMap<u64, String>,
    inline_nodes: &InlineSourceIndex,
    budget: &WorkBudget,
) -> Result<()> {
    let mut mutation_nodes = BTreeMap::<(u64, u64), (String, &Value)>::new();
    for row in array_field(api_surface, "mutation_sites") {
        budget.checkpoint()?;
        let source_index_ordinal = required_u64(row, "source_index_ordinal", "api mutation site")?;
        let site_ordinal = required_u64(row, "mutation_site_ordinal", "api mutation site")?;
        let node_id = format!("api-mutation:{source_index_ordinal}:{site_ordinal}");
        if mutation_nodes
            .insert((source_index_ordinal, site_ordinal), (node_id.clone(), row))
            .is_some()
        {
            bail!("duplicate API mutation site: {node_id}");
        }
        graph.add_node(
            node_id.clone(),
            json!({
                "type": "api_mutation",
                "resource_id": field(row, "resource_id"),
                "source_index_ordinal": source_index_ordinal,
                "source_path": field(row, "analysis_path"),
                "raw_path": field(row, "raw_path"),
                "start": field(row, "start"),
                "end": field(row, "end"),
                "line": field(row, "line"),
                "column": field(row, "column"),
                "operation": field(row, "operation"),
                "certainty": field(row, "certainty"),
                "target_pattern": field(row, "target_pattern"),
                "bound_function_span": field(row, "bound_function_span"),
                "affected_families": field(row, "affected_families"),
                "expression": field(row, "expression"),
            }),
        )?;
        if let Some(parent) = api_source_parent(row, deob_nodes, inline_nodes) {
            graph.add_edge(&parent, &node_id, "api_mutation_site", json!({}))?;
        }
    }
    // An original sink expression can have many specializing wrapper
    // invocations. Join by source identity, span and native API origin, never
    // by URL or text. Higher-order wrappers may have no direct sink row.
    type SinkKey = (u64, u64, u64, String);
    let mut direct_sites = BTreeMap::<SinkKey, Vec<String>>::new();
    let mut forwarded_sites = Vec::<(SinkKey, String)>::new();
    // Static browser API callsites hang off the exact selected source derivative.
    for row in array_field(api_surface, "callsites") {
        budget.checkpoint()?;
        let source_index_ordinal = required_u64(row, "source_index_ordinal", "api callsite")?;
        let callsite_ordinal = required_u64(row, "callsite_ordinal", "api callsite")?;
        let node_id = format!("api-call:{source_index_ordinal}:{callsite_ordinal}");
        if let Some(origin) = string_field(row, "api_origin") {
            if let Some(span) = row.get("forwarded_sink_span") {
                let Some((start, end)) = span.as_array().and_then(|values| {
                    let [start, end] = values.as_slice() else {
                        return None;
                    };
                    Some((start.as_u64()?, end.as_u64()?))
                }) else {
                    bail!("invalid forwarded sink span for {node_id}");
                };
                forwarded_sites.push((
                    (source_index_ordinal, start, end, origin.to_owned()),
                    node_id.clone(),
                ));
            } else if let Some((start, end)) = u64_field(row, "start").zip(u64_field(row, "end")) {
                direct_sites
                    .entry((source_index_ordinal, start, end, origin.to_owned()))
                    .or_default()
                    .push(node_id.clone());
            }
        }
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"api_callsite",
                "sink_kind":field(row,"kind"),
                "resource_id":field(row,"resource_id"),
                "source_index_ordinal":source_index_ordinal,
                "source_path":field(row,"analysis_path"),
                "raw_path":field(row,"raw_path"),
                "start":field(row,"start"),
                "end":field(row,"end"),
                "line":field(row,"line"),
                "column":field(row,"column"),
                "callee":field(row,"callee"),
                "api_origin":field(row,"api_origin"),
                "invocation_form":field(row,"invocation_form"),
                "forwarded_sink_span":field(row,"forwarded_sink_span"),
                "binding_witnesses":field(row,"binding_witnesses"),
                "proof":field(row,"proof"),
                "binding_status":field(row,"binding_status"),
                "mutation_site_ordinals":field(row,"mutation_site_ordinals"),
                "method":field(row,"method"),
                "method_expression":field(row,"method_expression"),
                "method_status":field(row,"method_status"),
                "url":field(row,"url"),
                "url_expression":field(row,"url_expression"),
                "standard_browser_api_semantics_required":bool_field(row,"standard_browser_api_semantics_required"),
            }),
        )?;
        if let Some(parent) = api_source_parent(row, deob_nodes, inline_nodes) {
            graph.add_edge(&parent, &node_id, "api_callsite", json!({}))?;
        }
        if let Some(ordinals) = row.get("mutation_site_ordinals") {
            let Some(ordinals) = ordinals.as_array() else {
                bail!("API callsite {node_id} has non-array mutation site ordinals");
            };
            for ordinal in ordinals {
                budget.checkpoint()?;
                let Some(site_ordinal) = ordinal.as_u64() else {
                    bail!("API callsite {node_id} has non-integer mutation site ordinal");
                };
                let Some((mutation_node, site)) =
                    mutation_nodes.get(&(source_index_ordinal, site_ordinal))
                else {
                    bail!("API callsite {node_id} references missing mutation site {site_ordinal}");
                };
                graph.add_edge(
                    mutation_node,
                    &node_id,
                    "api_mutation_evidence",
                    json!({
                        "operation": field(site, "operation"),
                        "certainty": field(site, "certainty"),
                        "affected_families": field(site, "affected_families"),
                        "source_mutation_span": [field(site, "start"), field(site, "end")],
                    }),
                )?;
            }
        }
        if bool_field(row, "absolute_network_url")
            && !string_field(row, "kind").is_some_and(|kind| kind.ends_with("_candidate"))
            && string_field(row, "binding_status") != Some("candidate")
            && !matches!(
                string_field(row, "method_status"),
                Some("invalid" | "conditional")
            )
        {
            if let Some(url) = string_field(row, "url") {
                for target in graph.targets_for(url)? {
                    graph.add_edge(
                        &node_id,
                        &target,
                        "api_target",
                        json!({
                            "sink_kind":field(row,"kind"),
                            "method":field(row,"method"),
                            "method_status":field(row,"method_status"),
                            "standard_browser_api_semantics_required":bool_field(row,"standard_browser_api_semantics_required"),
                        }),
                    )?;
                }
            }
        }
    }

    for (key, node_id) in forwarded_sites {
        budget.checkpoint()?;
        if let Some(targets) = direct_sites.get(&key) {
            if let [target] = targets.as_slice() {
                graph.add_edge(&node_id, target, "api_forwarded_invocation", json!({}))?;
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis_budget::{AnalysisBudgets, AnalysisOperation};
    use anyhow::Context;

    #[test]
    fn deobfuscation_parent_identity_prefers_inline_then_exact_runtime() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let mut inline = InlineSourceIndex::default();
        inline.insert("resources/inline.js", 7, 4, "inline:7:4".into())?;
        let runtime_sha = "a".repeat(64);
        let runtime_path = format!("resources/runtime-scripts/{runtime_sha}.js");
        let runtime_index = RuntimeSourceGraphIndex {
            instances: BTreeMap::new(),
            general_paths: BTreeMap::from([(runtime_sha.clone(), runtime_path.clone())]),
        };
        let units = json!({
            "units": [
                {
                    "ordinal": 4, "exit": 0, "resource_id": 7,
                    "raw_path": "resources/inline.js", "input_sha256": "inline-sha"
                },
                {
                    "ordinal": 6, "exit": 0, "resource_id": 12,
                    "raw_path": runtime_path, "input_sha256": runtime_sha
                },
                {
                    "ordinal": 8, "exit": 0, "resource_id": 13,
                    "raw_path": "resources/runtime-scripts/wrong.js",
                    "input_sha256": "different"
                },
                {
                    "ordinal": 9, "exit": 1, "resource_id": 14,
                    "raw_path": "resources/failure.js"
                }
            ]
        });
        let budget = AnalysisBudgets::standard("static-evidence-test")
            .operation(AnalysisOperation::SourceGraph, "parents");
        let nodes =
            seed_safe_deobfuscation_sources(&mut graph, &units, &inline, &runtime_index, &budget)?;
        assert_eq!(nodes.len(), 3);
        assert!(!nodes.contains_key(&9));
        let edges = graph
            .edges
            .iter()
            .filter(|edge| edge["kind"] == "safe_deobfuscation")
            .collect::<Vec<_>>();
        assert_eq!(edges.len(), 3);
        assert!(edges
            .iter()
            .any(|edge| { edge["from"] == "inline:7:4" && edge["to"] == "deobfuscated:4" }));
        assert!(edges.iter().any(|edge| {
            edge["from"] == "runtime:aaaaaaaaaaaaaaaaaaaa" && edge["to"] == "deobfuscated:6"
        }));
        assert!(edges
            .iter()
            .any(|edge| { edge["from"] == "resource:13" && edge["to"] == "deobfuscated:8" }));
        assert_eq!(
            graph
                .nodes
                .get("deobfuscated:4")
                .context("missing deob node")?["safe_static_only"],
            Value::Bool(true)
        );
        Ok(())
    }

    #[test]
    fn reflective_mutation_sites_attach_to_exact_derivative_and_candidate_calls() -> Result<()> {
        let mut graph = GraphBuilder::default();
        graph.register_resource_url("https://api.test/data", "resource:99");
        let deob_nodes = BTreeMap::from([(3, "deobfuscated:3".to_owned())]);
        let document = json!({
            "mutation_sites": [
                {
                    "source_index_ordinal": 2, "mutation_site_ordinal": 0,
                    "resource_id": 7, "deobfuscation_ordinal": 3,
                    "analysis_path": "src/_deobfuscated/app.js",
                    "start": 9, "end": 65,
                    "line": 1, "column": 9,
                    "operation": "Object.defineProperty",
                    "certainty": "possible",
                    "target_pattern": ["window","fetch"],
                    "affected_families": ["fetch"],
                    "expression": "Object.defineProperty(window, 'fetch', descriptor)"
                }
            ],
            "callsites": [
                {
                    "source_index_ordinal": 2, "callsite_ordinal": 0,
                    "resource_id": 7, "deobfuscation_ordinal": 3,
                    "analysis_path": "src/_deobfuscated/app.js",
                    "kind": "fetch_candidate", "binding_status": "candidate",
                    "api_origin": "fetch", "invocation_form": "bound",
                    "binding_witnesses": [{"kind":"bind","start":0,"end":8}],
                    "method": "GET", "method_status": "conditional",
                    "mutation_site_ordinals": [0],
                    "url": "https://api.test/data", "absolute_network_url": true
                }
            ]
        });
        let budget = AnalysisBudgets::standard("api-mutation-provenance-graph")
            .operation(AnalysisOperation::SourceGraph, "reflective");
        seed_browser_api_callsites(
            &mut graph,
            &document,
            &deob_nodes,
            &InlineSourceIndex::default(),
            &budget,
        )?;
        let mutation = graph
            .nodes
            .get("api-mutation:2:0")
            .context("missing mutation")?;
        assert_eq!(mutation["operation"], "Object.defineProperty");
        assert_eq!(mutation["certainty"], "possible");
        assert_eq!(mutation["target_pattern"], json!(["window", "fetch"]));
        let call = graph
            .nodes
            .get("api-call:2:0")
            .context("missing candidate")?;
        assert_eq!(call["mutation_site_ordinals"], json!([0]));
        assert_eq!(call["api_origin"], "fetch");
        assert_eq!(call["invocation_form"], "bound");
        assert_eq!(call["binding_witnesses"][0]["kind"], "bind");
        assert!(graph.edges.iter().any(|edge| {
            edge["from"] == "deobfuscated:3"
                && edge["to"] == "api-mutation:2:0"
                && edge["kind"] == "api_mutation_site"
        }));
        assert!(graph.edges.iter().any(|edge| {
            edge["from"] == "api-mutation:2:0"
                && edge["to"] == "api-call:2:0"
                && edge["kind"] == "api_mutation_evidence"
        }));
        assert!(!graph.edges.iter().any(|edge| edge["kind"] == "api_target"));
        Ok(())
    }

    #[test]
    fn wrapper_provenance_links_only_exact_original_source_sink() -> Result<()> {
        let mut graph = GraphBuilder::default();
        graph.register_resource_url("https://api.test/data", "resource:99");
        let doc = json!({"callsites": [
            {"source_index_ordinal":2,"callsite_ordinal":0,"start":10,"end":30,"api_origin":"fetch","kind":"fetch","invocation_form":"direct"},
            {"source_index_ordinal":3,"callsite_ordinal":0,"start":10,"end":30,"api_origin":"fetch","kind":"fetch","invocation_form":"direct"},
            {"source_index_ordinal":2,"callsite_ordinal":1,"start":40,"end":80,"api_origin":"fetch","kind":"fetch","invocation_form":"wrapper","forwarded_sink_span":[10,30],"url":"https://api.test/data","absolute_network_url":true,"method":"GET","method_status":"exact","binding_status":"standard"},
            {"source_index_ordinal":2,"callsite_ordinal":2,"start":90,"end":120,"api_origin":"fetch","kind":"fetch_candidate","invocation_form":"wrapper","forwarded_sink_span":[10,30],"url":"https://api.test/data","absolute_network_url":true,"binding_status":"candidate"},
            {"source_index_ordinal":4,"callsite_ordinal":0,"start":40,"end":80,"api_origin":"fetch","kind":"fetch","invocation_form":"wrapper","forwarded_sink_span":[10,30]}
        ]});
        let budget = AnalysisBudgets::standard("wrapper-graph")
            .operation(AnalysisOperation::SourceGraph, "forwarded");
        seed_browser_api_callsites(
            &mut graph,
            &doc,
            &BTreeMap::new(),
            &InlineSourceIndex::default(),
            &budget,
        )?;
        let forwarding = graph
            .edges
            .iter()
            .filter(|edge| edge["kind"] == "api_forwarded_invocation")
            .collect::<Vec<_>>();
        assert_eq!(forwarding.len(), 2);
        assert!(forwarding.iter().all(|edge| edge["to"] == "api-call:2:0"));
        assert!(graph
            .edges
            .iter()
            .any(|edge| edge["kind"] == "api_target" && edge["from"] == "api-call:2:1"));
        assert!(!graph
            .edges
            .iter()
            .any(|edge| edge["kind"] == "api_target" && edge["from"] == "api-call:2:2"));
        Ok(())
    }

    #[test]
    fn api_mutation_references_cannot_cross_source_units_or_dangle() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let document = json!({
            "mutation_sites": [
                {"source_index_ordinal": 1, "mutation_site_ordinal": 0,
                 "resource_id": 3, "operation": "Reflect.set",
                 "certainty": "possible", "affected_families": ["fetch"]}
            ],
            "callsites": [
                {"source_index_ordinal": 2, "callsite_ordinal": 0,
                 "resource_id": 4, "kind": "fetch_candidate",
                 "mutation_site_ordinals": [0]}
            ]
        });
        let budget = AnalysisBudgets::standard("api-mutation-identity-guard")
            .operation(AnalysisOperation::SourceGraph, "cross-unit");
        assert!(seed_browser_api_callsites(
            &mut graph,
            &document,
            &BTreeMap::new(),
            &InlineSourceIndex::default(),
            &budget,
        )
        .is_err());
        Ok(())
    }

    #[test]
    fn candidate_api_sites_keep_source_provenance_without_verified_network_target() -> Result<()> {
        let mut graph = GraphBuilder::default();
        graph.register_resource_url("https://app.test/api", "resource:99");
        let rows = json!({"callsites": [
            {
                "source_index_ordinal": 7, "callsite_ordinal": 0,
                "resource_id": 5, "kind": "fetch_candidate",
                "binding_status": "candidate",
                "proof": "unresolved_global_member_mutation_may_replace_fetch",
                "method": "POST", "method_status": "conditional",
                "url": "https://app.test/api", "absolute_network_url": true
            },
            {
                "source_index_ordinal": 7, "callsite_ordinal": 1,
                "resource_id": 5, "kind": "fetch",
                "binding_status": "candidate",
                "proof": "candidate_marker_is_authoritative",
                "method_status": "exact",
                "url": "https://app.test/api", "absolute_network_url": true
            },
            {
                "source_index_ordinal": 7, "callsite_ordinal": 2,
                "resource_id": 5, "kind": "fetch",
                "binding_status": "standard",
                "method_status": "exact",
                "url": "https://app.test/api", "absolute_network_url": true
            }
        ]});
        let budget = AnalysisBudgets::standard("candidate-api-graph-test")
            .operation(AnalysisOperation::SourceGraph, "candidate");
        seed_browser_api_callsites(
            &mut graph,
            &rows,
            &BTreeMap::new(),
            &InlineSourceIndex::default(),
            &budget,
        )?;
        let target_edges = graph
            .edges
            .iter()
            .filter(|edge| edge["kind"] == "api_target")
            .collect::<Vec<_>>();
        assert_eq!(target_edges.len(), 1, "{target_edges:#?}");
        assert_eq!(target_edges[0]["from"], "api-call:7:2");
        for ordinal in 0..2 {
            let id = format!("api-call:7:{ordinal}");
            let node = graph.nodes.get(&id).context("candidate node missing")?;
            assert_eq!(node["binding_status"], "candidate");
            assert_eq!(node["url"], "https://app.test/api");
            assert!(graph
                .edges
                .iter()
                .any(|edge| { edge["to"] == id && edge["kind"] == "api_callsite" }));
        }
        Ok(())
    }

    #[test]
    fn callsites_select_source_derivatives_and_guard_url_targets() -> Result<()> {
        let mut graph = GraphBuilder::default();
        graph.register_resource_url("https://app.test/api", "resource:99");
        let mut inline = InlineSourceIndex::default();
        inline.insert("resources/inline.js", 7, 4, "inline:7:4".into())?;
        let deob_nodes = BTreeMap::from([(3, "deobfuscated:3".into())]);
        let calls = json!({
            "callsites": [
                {
                    "source_index_ordinal": 1, "callsite_ordinal": 1,
                    "deobfuscation_ordinal": 3, "resource_id": 7,
                    "raw_path": "resources/inline.js", "ordinal": 4,
                    "kind": "fetch", "absolute_network_url": true,
                    "url": "https://app.test/api", "method_status": "static"
                },
                {
                    "source_index_ordinal": 1, "callsite_ordinal": 2,
                    "resource_id": 7, "raw_path": "resources/inline.js",
                    "ordinal": 4, "kind": "fetch", "method_status": "invalid",
                    "absolute_network_url": true, "url": "https://app.test/api"
                },
                {
                    "source_index_ordinal": 1, "callsite_ordinal": 3,
                    "resource_id": 8, "kind": "xhr_open_candidate",
                    "absolute_network_url": true, "url": "https://app.test/api"
                },
                {
                    "source_index_ordinal": 1, "callsite_ordinal": 4,
                    "resource_id": 8, "kind": "fetch",
                    "absolute_network_url": false, "url": "https://app.test/api"
                }
            ]
        });
        let budget = AnalysisBudgets::standard("static-evidence-test")
            .operation(AnalysisOperation::SourceGraph, "callsites");
        seed_browser_api_callsites(&mut graph, &calls, &deob_nodes, &inline, &budget)?;
        let parents = graph
            .edges
            .iter()
            .filter(|edge| edge["kind"] == "api_callsite")
            .map(|edge| (edge["from"].as_str(), edge["to"].as_str()))
            .collect::<Vec<_>>();
        assert_eq!(
            parents,
            vec![
                (Some("deobfuscated:3"), Some("api-call:1:1")),
                (Some("inline:7:4"), Some("api-call:1:2")),
                (Some("resource:8"), Some("api-call:1:3")),
                (Some("resource:8"), Some("api-call:1:4")),
            ]
        );
        let targets = graph
            .edges
            .iter()
            .filter(|edge| edge["kind"] == "api_target")
            .collect::<Vec<_>>();
        assert_eq!(targets.len(), 1);
        assert_eq!(targets[0]["from"], "api-call:1:1");
        assert_eq!(targets[0]["to"], "resource:99");
        assert_eq!(
            graph
                .nodes
                .get("api-call:1:1")
                .context("missing callsite")?["source_index_ordinal"],
            1
        );
        Ok(())
    }
}
