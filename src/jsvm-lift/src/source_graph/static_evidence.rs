//! Static evidence stages: safe-deobfuscation derivatives and browser API callsites.
//!
//! Source identity is resolved before graph edges are emitted. A source
//! derivative is not runtime execution proof, and a callsite's selected
//! derivative takes precedence over its original captured source.

use super::{
    array_field, bool_field, field, required_u64, string_field, u64_field, GraphBuilder,
    InlineSourceIndex, RuntimeSourceGraphIndex,
};
use anyhow::Result;
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

/// Attach browser API observations to the selected source derivative.
///
/// Callsite URL targets are candidates, not evidence that a network request
/// executed; the api_target edge retains the source proof requirements.
pub(super) fn seed_browser_api_callsites(
    graph: &mut GraphBuilder,
    api_surface: &Value,
    deob_nodes: &BTreeMap<u64, String>,
    inline_nodes: &InlineSourceIndex,
    budget: &WorkBudget,
) -> Result<()> {
    // Static browser API callsites hang off the exact selected source derivative.
    for row in array_field(api_surface, "callsites") {
        budget.checkpoint()?;
        let source_index_ordinal = required_u64(row, "source_index_ordinal", "api callsite")?;
        let callsite_ordinal = required_u64(row, "callsite_ordinal", "api callsite")?;
        let node_id = format!("api-call:{source_index_ordinal}:{callsite_ordinal}");
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
                "proof":field(row,"proof"),
                "method":field(row,"method"),
                "method_expression":field(row,"method_expression"),
                "method_status":field(row,"method_status"),
                "url":field(row,"url"),
                "url_expression":field(row,"url_expression"),
                "standard_browser_api_semantics_required":bool_field(row,"standard_browser_api_semantics_required"),
            }),
        )?;
        let mut parent = u64_field(row, "deobfuscation_ordinal")
            .and_then(|ordinal| deob_nodes.get(&ordinal).cloned());
        if parent.is_none() {
            parent = inline_nodes.for_record(row);
        }
        if parent.is_none() {
            parent =
                u64_field(row, "resource_id").map(|resource_id| format!("resource:{resource_id}"));
        }
        if let Some(parent) = parent {
            graph.add_edge(&parent, &node_id, "api_callsite", json!({}))?;
        }
        if bool_field(row, "absolute_network_url")
            && string_field(row, "kind") != Some("xhr_open_candidate")
            && string_field(row, "method_status") != Some("invalid")
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
