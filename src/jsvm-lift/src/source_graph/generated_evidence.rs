//! Static generated-code provenance and derived VM source graph stages.
//!
//! The exact (parent scan, dynamic ordinal) site plus its linked child scan
//! determine generated code source identity. A claimed scan ID, raw URL or
//! digest coincidence alone never establishes a code parent.

use super::{
    array_field, field, nonempty_string_field, required_u64, string_field, u64_field, GraphBuilder,
};
use anyhow::Result;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use work_budget::WorkBudget;

struct DynamicSource {
    analysis_parent: String,
    child_scan_id: Option<u64>,
}

/// Add generated source and recovered source nodes, then attach proven
/// generated-code and devirtualization edges by exact scan identity.
pub(super) fn seed_generated_and_vm_evidence(
    graph: &mut GraphBuilder,
    jsvm: &Value,
    deob_nodes: &BTreeMap<u64, String>,
    budget: &WorkBudget,
) -> Result<()> {
    // Static Function(...) recovery is a generated-code provenance edge.
    let mut sources = BTreeMap::<(u64, u64), DynamicSource>::new();
    let mut child_claims = BTreeMap::<u64, (u64, u64)>::new();
    for dynamic in array_field(jsvm, "dynamic_code_units") {
        budget.checkpoint()?;
        let parent_scan_id = required_u64(dynamic, "parent_scan_id", "dynamic code unit")?;
        let ordinal = required_u64(dynamic, "ordinal", "dynamic code unit")?;
        let node_id = format!("dynamic:{parent_scan_id}:{ordinal}");
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"generated_dynamic_code",
                "parent_scan_id":parent_scan_id,
                "ordinal":ordinal,
                "depth":field(dynamic,"depth"),
                "generated_kind":field(dynamic,"kind"),
                "outer_start":field(dynamic,"outer_start"),
                "outer_end":field(dynamic,"outer_end"),
                "body_bytes":field(dynamic,"body_bytes"),
                "raw_dump":field(dynamic,"raw_dump"),
                "source_path":field(dynamic,"source_path"),
                "analysis_path":field(dynamic,"analysis_path"),
                "analysis_stage":field(dynamic,"analysis_stage"),
                "recovery_report":field(dynamic,"recovery_report"),
                "formatted":field(dynamic,"formatted"),
                "child_scan_id":field(dynamic,"child_scan_id"),
            }),
        )?;
        let mut analysis_parent = node_id.clone();
        if let Some(analysis_path) = nonempty_string_field(dynamic, "analysis_path") {
            if string_field(dynamic, "raw_dump") != Some(analysis_path) {
                let recovery_node = format!("generated-recovery:{parent_scan_id}:{ordinal}");
                graph.add_node(
                    recovery_node.clone(),
                    json!({
                        "type":"generated_recovered_source",
                        "parent_scan_id":parent_scan_id,
                        "ordinal":ordinal,
                        "recovery_stage":field(dynamic,"analysis_stage"),
                        "source_path":analysis_path,
                        "readable_source_path":field(dynamic,"source_path"),
                        "recovery_report":field(dynamic,"recovery_report"),
                    }),
                )?;
                graph.add_edge(
                    &node_id,
                    &recovery_node,
                    "generated_safe_recovery",
                    json!({"recovery_stage":field(dynamic,"analysis_stage")}),
                )?;
                analysis_parent = recovery_node;
            }
        }
        let child_scan_id = u64_field(dynamic, "child_scan_id");
        if let Some(child_scan_id) = child_scan_id {
            anyhow::ensure!(
                child_claims
                    .insert(child_scan_id, (parent_scan_id, ordinal))
                    .is_none(),
                "multiple generated sources claim child scan id {child_scan_id}"
            );
        }
        anyhow::ensure!(
            sources
                .insert(
                    (parent_scan_id, ordinal),
                    DynamicSource {
                        analysis_parent,
                        child_scan_id,
                    }
                )
                .is_none(),
            "duplicate dynamic source identity ({parent_scan_id}, {ordinal})"
        );
    }

    let mut scan_to_parent = BTreeMap::<u64, String>::new();
    let mut scan_ids = BTreeSet::<u64>::new();
    for unit in array_field(jsvm, "code_units") {
        budget.checkpoint()?;
        let Some(scan_id) = u64_field(unit, "scan_id") else {
            continue;
        };
        anyhow::ensure!(
            scan_ids.insert(scan_id),
            "duplicate code unit scan id {scan_id}"
        );
        // A generated site can claim a child scan ID only for that exact
        // generated code-unit row. An inconsistent capture must not allow a
        // resource-root row with that ID to parent nested generated evidence.
        if let Some(&claimed_identity) = child_claims.get(&scan_id) {
            let actual_identity =
                u64_field(unit, "parent_scan_id").zip(u64_field(unit, "parent_dynamic_ordinal"));
            if string_field(unit, "origin") != Some("generated_dynamic_code")
                || actual_identity != Some(claimed_identity)
            {
                continue;
            }
        }
        let parent = if string_field(unit, "origin") == Some("generated_dynamic_code") {
            // Both sides must agree on the exact generated-site identity and
            // scan linkage. Never synthesize a parent node for missing or stale
            // evidence, nor accept the last claimant of a shared scan ID.
            let identity =
                u64_field(unit, "parent_scan_id").zip(u64_field(unit, "parent_dynamic_ordinal"));
            identity
                .and_then(|identity| sources.get(&identity))
                .filter(|source| source.child_scan_id == Some(scan_id))
                .map(|source| source.analysis_parent.clone())
        } else if let Some(deob_ordinal) = u64_field(unit, "deobfuscation_ordinal") {
            deob_nodes.get(&deob_ordinal).cloned()
        } else {
            u64_field(unit, "resource_id").map(|resource_id| format!("resource:{resource_id}"))
        };
        if let Some(parent) = parent {
            scan_to_parent.insert(scan_id, parent);
        }
    }

    for dynamic in array_field(jsvm, "dynamic_code_units") {
        budget.checkpoint()?;
        let parent_scan_id = required_u64(dynamic, "parent_scan_id", "dynamic code unit")?;
        let ordinal = required_u64(dynamic, "ordinal", "dynamic code unit")?;
        let node_id = format!("dynamic:{parent_scan_id}:{ordinal}");
        if let Some(parent) = scan_to_parent.get(&parent_scan_id) {
            graph.add_edge(
                parent,
                &node_id,
                "generated_code",
                json!({
                    "outer_start":field(dynamic,"outer_start"),
                    "outer_end":field(dynamic,"outer_end"),
                    "depth":field(dynamic,"depth"),
                }),
            )?;
        }
    }

    let mut vm_identities = BTreeSet::new();
    for unit in array_field(jsvm, "devirtualized_units") {
        budget.checkpoint()?;
        let parent_scan_id = required_u64(unit, "parent_scan_id", "devirtualized unit")?;
        let ordinal = required_u64(unit, "vm_ordinal", "devirtualized unit")?;
        let vm_kind = nonempty_string_field(unit, "vm_kind").unwrap_or("unknown");
        let node_id = format!("devirtualized:{parent_scan_id}:{vm_kind}:{ordinal}");
        anyhow::ensure!(
            vm_identities.insert(node_id.clone()),
            "duplicate devirtualized VM identity {node_id}"
        );
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"devirtualized_vm",
                "parent_scan_id":parent_scan_id,
                "vm_ordinal":ordinal,
                "vm_kind":vm_kind,
                "parent_function_id":field(unit,"parent_function_id"),
                "function_name":field(unit,"function_name"),
                "function_start":field(unit,"function_start"),
                "function_end":field(unit,"function_end"),
                "switch_start":field(unit,"switch_start"),
                "switch_end":field(unit,"switch_end"),
                "selector_style":field(unit,"selector_style"),
                "handler_table":field(unit,"handler_table"),
                "architecture":field(unit,"architecture"),
                "handler_count":field(unit,"handler_count"),
                "source_path":field(unit,"source_path"),
                "pseudocode_path":field(unit,"pseudocode_path"),
                "ir_path":field(unit,"ir_path"),
            }),
        )?;
        if let Some(parent) = scan_to_parent.get(&parent_scan_id) {
            graph.add_edge(
                parent,
                &node_id,
                "devirtualized_vm",
                json!({
                    "vm_kind":vm_kind,
                    "function_start":field(unit,"function_start"),
                    "function_end":field(unit,"function_end"),
                    "switch_start":field(unit,"switch_start"),
                    "switch_end":field(unit,"switch_end"),
                    "handler_table":field(unit,"handler_table"),
                }),
            )?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn budget() -> WorkBudget {
        WorkBudget::new(
            "generated-source-graph",
            work_budget::BudgetLimits::unlimited(),
        )
    }

    #[test]
    fn nested_recovery_and_vm_edges_follow_exact_generated_sources() -> Result<()> {
        let jsvm = json!({
            "code_units": [
                {"scan_id":1, "resource_id":7},
                {"scan_id":2, "origin":"generated_dynamic_code",
                    "parent_scan_id":1, "parent_dynamic_ordinal":1},
                {"scan_id":3, "origin":"generated_dynamic_code",
                    "parent_scan_id":2, "parent_dynamic_ordinal":2}
            ],
            "dynamic_code_units": [
                {"parent_scan_id":1, "ordinal":1, "child_scan_id":2,
                    "raw_dump":"src/raw.js", "analysis_path":"src/recovered.js",
                    "analysis_stage":"safe_deobfuscation",
                    "source_path":"src/readable.js"},
                {"parent_scan_id":2, "ordinal":2, "child_scan_id":3,
                    "raw_dump":"src/exact.js", "analysis_path":"src/exact.js"}
            ],
            "devirtualized_units": [
                {"parent_scan_id":2, "vm_ordinal":4, "vm_kind":"function_table",
                    "function_start":100, "function_end":120}
            ]
        });
        let mut graph = GraphBuilder::default();
        seed_generated_and_vm_evidence(&mut graph, &jsvm, &BTreeMap::new(), &budget())?;
        assert_eq!(graph.nodes["dynamic:1:1"]["type"], "generated_dynamic_code");
        assert_eq!(graph.nodes["dynamic:2:2"]["type"], "generated_dynamic_code");
        assert_eq!(
            graph.nodes["generated-recovery:1:1"]["recovery_stage"],
            "safe_deobfuscation"
        );
        assert!(!graph.nodes.contains_key("generated-recovery:2:2"));
        for (kind, from, to) in [
            ("generated_code", "resource:7", "dynamic:1:1"),
            (
                "generated_safe_recovery",
                "dynamic:1:1",
                "generated-recovery:1:1",
            ),
            ("generated_code", "generated-recovery:1:1", "dynamic:2:2"),
            (
                "devirtualized_vm",
                "generated-recovery:1:1",
                "devirtualized:2:function_table:4",
            ),
        ] {
            assert!(
                graph
                    .edges
                    .iter()
                    .any(|edge| edge["kind"] == kind && edge["from"] == from && edge["to"] == to),
                "missing {kind} edge {from} -> {to}"
            );
        }
        assert_eq!(graph.edges.len(), 4);
        Ok(())
    }

    #[test]
    fn stale_or_mismatched_generated_links_do_not_invent_parent_evidence() -> Result<()> {
        let jsvm = json!({
            "code_units": [
                {"scan_id":1, "resource_id":7},
                {"scan_id":2, "origin":"generated_dynamic_code",
                    "parent_scan_id":1, "parent_dynamic_ordinal":999},
                {"scan_id":88, "origin":"generated_dynamic_code",
                    "parent_scan_id":1, "parent_dynamic_ordinal":1},
                {"scan_id":99, "origin":"generated_dynamic_code",
                    "parent_scan_id":1, "parent_dynamic_ordinal":9}
            ],
            "dynamic_code_units": [
                {"parent_scan_id":1, "ordinal":1, "child_scan_id":2},
                {"parent_scan_id":2, "ordinal":1},
                {"parent_scan_id":88, "ordinal":1},
                {"parent_scan_id":99, "ordinal":1}
            ],
            "devirtualized_units": [
                {"parent_scan_id":2, "vm_ordinal":1, "vm_kind":"table"},
                {"parent_scan_id":88, "vm_ordinal":1, "vm_kind":"table"}
            ]
        });
        let mut graph = GraphBuilder::default();
        seed_generated_and_vm_evidence(&mut graph, &jsvm, &BTreeMap::new(), &budget())?;
        let generated = graph
            .edges
            .iter()
            .filter(|edge| edge["kind"] == "generated_code")
            .collect::<Vec<_>>();
        assert_eq!(generated.len(), 1);
        assert_eq!(generated[0]["from"], "resource:7");
        assert_eq!(generated[0]["to"], "dynamic:1:1");
        assert!(!graph
            .edges
            .iter()
            .any(|edge| edge["kind"] == "devirtualized_vm"));
        assert_eq!(
            graph.nodes["dynamic:88:1"]["type"],
            "generated_dynamic_code"
        );
        assert_eq!(
            graph.nodes["devirtualized:88:table:1"]["type"],
            "devirtualized_vm"
        );
        Ok(())
    }

    #[test]
    fn generated_child_claims_cannot_impersonate_capture_roots() -> Result<()> {
        let jsvm = json!({
            "code_units": [
                {"scan_id":1, "resource_id":7},
                {"scan_id":2, "resource_id":8}
            ],
            "dynamic_code_units": [
                {"parent_scan_id":1, "ordinal":1, "child_scan_id":2},
                {"parent_scan_id":2, "ordinal":3}
            ],
            "devirtualized_units": [
                {"parent_scan_id":2, "vm_ordinal":4, "vm_kind":"table"}
            ]
        });
        let mut graph = GraphBuilder::default();
        seed_generated_and_vm_evidence(&mut graph, &jsvm, &BTreeMap::new(), &budget())?;
        assert!(graph
            .edges
            .iter()
            .any(|edge| edge["kind"] == "generated_code"
                && edge["from"] == "resource:7"
                && edge["to"] == "dynamic:1:1"));
        assert!(!graph.edges.iter().any(|edge| edge["from"] == "resource:8"
            || edge["to"] == "dynamic:2:3"
            || edge["kind"] == "devirtualized_vm"));
        assert!(graph.nodes.contains_key("dynamic:2:3"));
        Ok(())
    }

    #[test]
    fn duplicated_generated_site_child_or_scan_identity_is_rejected() {
        let cases = [
            (
                json!({
                    "dynamic_code_units":[
                        {"parent_scan_id":1, "ordinal":2, "child_scan_id":3},
                        {"parent_scan_id":1, "ordinal":2, "child_scan_id":4}
                    ]
                }),
                "duplicate dynamic source identity",
            ),
            (
                json!({
                    "dynamic_code_units":[
                        {"parent_scan_id":1, "ordinal":2, "child_scan_id":3},
                        {"parent_scan_id":1, "ordinal":3, "child_scan_id":3}
                    ]
                }),
                "multiple generated sources claim child scan id",
            ),
            (
                json!({
                    "code_units":[
                        {"scan_id":9, "resource_id":1},
                        {"scan_id":9, "resource_id":2}
                    ]
                }),
                "duplicate code unit scan id",
            ),
            (
                json!({
                    "devirtualized_units":[
                        {"parent_scan_id":1, "vm_ordinal":2, "vm_kind":"function_table"},
                        {"parent_scan_id":1, "vm_ordinal":2, "vm_kind":"function_table"}
                    ]
                }),
                "duplicate devirtualized VM identity",
            ),
        ];
        for (jsvm, expected_error) in cases {
            let mut graph = GraphBuilder::default();
            let error =
                seed_generated_and_vm_evidence(&mut graph, &jsvm, &BTreeMap::new(), &budget())
                    .expect_err(expected_error);
            assert!(error.to_string().contains(expected_error), "{error}");
        }
    }

    #[test]
    fn deobfuscation_is_selected_for_non_generated_code_units() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let jsvm = json!({
            "code_units": [
                {"scan_id":5, "resource_id":7, "deobfuscation_ordinal":3}
            ],
            "dynamic_code_units": [
                {"parent_scan_id":5, "ordinal":8}
            ],
            "devirtualized_units": [
                {"parent_scan_id":5, "vm_ordinal":2, "vm_kind":"direct_switch"}
            ]
        });
        let deob = BTreeMap::from([(3, "deobfuscated:3".to_owned())]);
        seed_generated_and_vm_evidence(&mut graph, &jsvm, &deob, &budget())?;
        assert_eq!(graph.edges.len(), 2);
        assert!(graph
            .edges
            .iter()
            .all(|edge| edge["from"] == "deobfuscated:3"));
        Ok(())
    }
}
