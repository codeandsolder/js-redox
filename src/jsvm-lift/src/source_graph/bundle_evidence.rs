//! Static bundle payloads, factory identities and dependency resolution.
//!
//! A logical module ID is not a factory identity. Local candidates take
//! precedence over other bundles; private nested tables are filtered per
//! source factory. Unresolved evidence is owned by the factory making the
//! reference, not by its containing bundle.

use super::{
    array_field, bool_field, compact_key, digest_id, field, nonempty_string_field, required_u64,
    string_field, u64_field, GraphBuilder,
};
use anyhow::{Context, Result};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use work_budget::WorkBudget;

fn seed_bundle_payload_nodes(
    graph: &mut GraphBuilder,
    bundles: &Value,
    deob_nodes: &BTreeMap<u64, String>,
    budget: &WorkBudget,
) -> Result<BTreeMap<u64, String>> {
    let mut bundle_nodes = BTreeMap::<u64, String>::new();
    for bundle in array_field(bundles, "bundles") {
        budget.checkpoint()?;
        let bundle_id = required_u64(bundle, "bundle_id", "bundle")?;
        let node_id = format!("bundle:{bundle_id}");
        anyhow::ensure!(
            bundle_nodes.insert(bundle_id, node_id.clone()).is_none(),
            "duplicate bundle payload ID {bundle_id}"
        );
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"bundle_payload",
                "bundle_id":bundle_id,
                "resource_id":field(bundle,"resource_id"),
                "kind":field(bundle,"kind"),
                "chunk_ids":bundle.get("chunk_ids").cloned().unwrap_or_else(|| json!([])),
                "parent_path":field(bundle,"parent_path"),
                "start":field(bundle,"start"),
                "end":field(bundle,"end"),
                "module_count":field(bundle,"module_count"),
            }),
        )?;
        if let Some(parent_ordinal) = u64_field(bundle, "parent_ordinal") {
            if let Some(parent) = deob_nodes.get(&parent_ordinal) {
                graph.add_edge(
                    parent,
                    &node_id,
                    "bundle_payload",
                    json!({"chunk_ids":bundle.get("chunk_ids").cloned().unwrap_or_else(|| json!([]))}),
                )?;
            }
        }
    }

    Ok(bundle_nodes)
}

struct BundleGraphIndex<'a> {
    bundle_rows_by_id: BTreeMap<u64, &'a Value>,
    bundle_module_nodes: BTreeMap<u64, BTreeMap<&'a str, Vec<String>>>,
    module_nodes_by_id: BTreeMap<&'a str, Vec<String>>,
    module_rows: BTreeMap<String, &'a Value>,
}

fn seed_bundle_module_nodes<'a>(
    graph: &mut GraphBuilder,
    bundles: &'a Value,
    bundle_nodes: &BTreeMap<u64, String>,
    budget: &WorkBudget,
) -> Result<BundleGraphIndex<'a>> {
    let bundle_rows_by_id = array_field(bundles, "bundles")
        .iter()
        .filter_map(|bundle| Some((u64_field(bundle, "bundle_id")?, bundle)))
        .collect::<BTreeMap<_, _>>();
    let mut bundle_module_nodes = BTreeMap::<u64, BTreeMap<&str, Vec<String>>>::new();
    let mut module_nodes_by_id = BTreeMap::<&str, Vec<String>>::new();
    let mut module_rows = BTreeMap::<String, &Value>::new();
    for module in array_field(bundles, "modules") {
        budget.checkpoint()?;
        let bundle_id = required_u64(module, "bundle_id", "bundle module")?;
        let ordinal = required_u64(module, "module_ordinal", "bundle module")?;
        let node_id = format!("bundle-module:{bundle_id}:{ordinal}");
        let module_id = string_field(module, "module_id")
            .context("bundle module.module_id must be a string")?;
        bundle_module_nodes
            .entry(bundle_id)
            .or_default()
            .entry(module_id)
            .or_default()
            .push(node_id.clone());
        module_nodes_by_id
            .entry(module_id)
            .or_default()
            .push(node_id.clone());
        anyhow::ensure!(
            module_rows.insert(node_id.clone(), module).is_none(),
            "duplicate bundle factory identity {node_id}"
        );
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"bundle_module",
                "bundle_id":bundle_id,
                "module_ordinal":ordinal,
                "module_id":field(module,"module_id"),
                "resource_id":field(module,"resource_id"),
                "parent_path":field(module,"parent_path"),
                "chunk_ids":module.get("chunk_ids").cloned().unwrap_or_else(|| json!([])),
                "source_path":field(module,"source_path"),
                "formatted":bool_field(module,"formatted"),
                "sha256":field(module,"sha256"),
                "value_kind":field(module,"value_kind"),
                "dependencies":module.get("dependencies").cloned().unwrap_or_else(|| json!([])),
                "dependency_map":module.get("dependency_map").cloned().unwrap_or_else(|| json!({})),
                "export_names":module.get("export_names").cloned().unwrap_or_else(|| json!([])),
                "commonjs_export":bool_field(module,"commonjs_export"),
            }),
        )?;
        if let Some(parent) = bundle_nodes.get(&bundle_id) {
            graph.add_edge(
                parent,
                &node_id,
                "bundle_module",
                json!({"module_id":field(module,"module_id")}),
            )?;
        }
    }

    Ok(BundleGraphIndex {
        bundle_rows_by_id,
        bundle_module_nodes,
        module_nodes_by_id,
        module_rows,
    })
}

/// Do not resolve a dependency to a factory inside the source factory's
/// private Webpack module-table range.
fn nested_private_bundle_candidate(
    candidate_node: &str,
    source_module: &Value,
    index: &BundleGraphIndex<'_>,
) -> bool {
    let Some(candidate_module) = index.module_rows.get(candidate_node).copied() else {
        return false;
    };
    let Some(candidate_bundle_id) = u64_field(candidate_module, "bundle_id") else {
        return false;
    };
    let Some(candidate_bundle) = index.bundle_rows_by_id.get(&candidate_bundle_id).copied() else {
        return false;
    };
    let Some(source_path) = nonempty_string_field(source_module, "parent_path") else {
        return false;
    };
    if string_field(candidate_bundle, "kind") != Some("webpack_module_table")
        || nonempty_string_field(candidate_bundle, "parent_path") != Some(source_path)
    {
        return false;
    }
    let Some(source_start) = u64_field(source_module, "value_start") else {
        return false;
    };
    let Some(source_end) = u64_field(source_module, "value_end") else {
        return false;
    };
    let Some(bundle_start) = u64_field(candidate_bundle, "start") else {
        return false;
    };
    let Some(bundle_end) = u64_field(candidate_bundle, "end") else {
        return false;
    };
    source_start <= bundle_start && bundle_start < bundle_end && bundle_end <= source_end
}

/// Keep resolved and unresolved evidence mutually exclusive. The exact
/// candidate is borrowed from the already indexed factory rather than
/// cloning every matching module ID and candidate list for each dependency.
enum BundleDependencyResolution<'a> {
    Resolved {
        target: &'a str,
        cross_bundle: bool,
        excluded_nested_count: usize,
    },
    Unresolved {
        candidates: Vec<&'a str>,
        excluded_nested: Vec<&'a str>,
    },
}

impl BundleGraphIndex<'_> {
    fn resolve_dependency(
        &self,
        bundle_id: u64,
        source_module: &Value,
        dependency: &str,
        budget: &WorkBudget,
    ) -> Result<BundleDependencyResolution<'_>> {
        let local = self
            .bundle_module_nodes
            .get(&bundle_id)
            .and_then(|ids| ids.get(dependency))
            .map_or_default(Vec::as_slice);
        budget.consume(u64::try_from(local.len())?)?;
        match local {
            [target] => {
                return Ok(BundleDependencyResolution::Resolved {
                    target,
                    cross_bundle: false,
                    excluded_nested_count: 0,
                });
            }
            [] => {}
            _ => {
                return Ok(BundleDependencyResolution::Unresolved {
                    candidates: local.iter().map(String::as_str).collect(),
                    excluded_nested: Vec::new(),
                });
            }
        }
        let mut candidates = Vec::new();
        let mut excluded_nested = Vec::new();
        let global = self
            .module_nodes_by_id
            .get(dependency)
            .map_or_default(Vec::as_slice);
        budget.consume(u64::try_from(global.len())?)?;
        for candidate in global {
            budget.checkpoint()?;
            if nested_private_bundle_candidate(candidate, source_module, self) {
                excluded_nested.push(candidate.as_str());
            } else {
                candidates.push(candidate.as_str());
            }
        }
        Ok(if let [target] = candidates.as_slice() {
            BundleDependencyResolution::Resolved {
                target,
                cross_bundle: true,
                excluded_nested_count: excluded_nested.len(),
            }
        } else {
            BundleDependencyResolution::Unresolved {
                candidates,
                excluded_nested,
            }
        })
    }
}

fn add_unresolved_dependency(
    graph: &mut GraphBuilder,
    source_node: &str,
    bundle_id: u64,
    dependency: &str,
    candidates: &[&str],
    excluded_nested: &[&str],
) -> Result<()> {
    // The exclusion proof depends on the source factory's lexical range,
    // so sharing a reference solely by containing bundle loses provenance.
    let ref_id = digest_id(
        "bundle-module-ref:",
        &compact_key((source_node, dependency))?,
    );
    graph.add_node(
        ref_id.clone(),
        json!({
            "type":"bundle_module_reference",
            "module_id":dependency,
            "source_bundle_id":bundle_id,
            "source_module_node":source_node,
            "candidate_nodes":candidates,
            "excluded_nested_module_table_nodes":excluded_nested,
            "ambiguous":!candidates.is_empty(),
        }),
    )?;
    graph.add_edge(
        source_node,
        &ref_id,
        "bundle_module_dependency_unresolved",
        json!({
            "module_id":dependency,
            "candidate_count":candidates.len(),
            "excluded_nested_module_table_count":excluded_nested.len(),
        }),
    )?;
    Ok(())
}

fn seed_bundle_dependency_edges(
    graph: &mut GraphBuilder,
    index: &BundleGraphIndex<'_>,
    budget: &WorkBudget,
) -> Result<()> {
    for (source_node, module) in &index.module_rows {
        budget.checkpoint()?;
        let bundle_id = required_u64(module, "bundle_id", "bundle module")?;
        for dependency in array_field(module, "dependencies") {
            budget.consume(1)?;
            let dependency = dependency
                .as_str()
                .context("bundle module dependency must be a string")?;
            match index.resolve_dependency(bundle_id, module, dependency, budget)? {
                BundleDependencyResolution::Resolved {
                    target,
                    cross_bundle,
                    excluded_nested_count,
                } => {
                    graph.add_edge(
                        source_node,
                        target,
                        "bundle_module_dependency",
                        json!({
                            "module_id":dependency,
                            "cross_bundle":cross_bundle,
                            "excluded_nested_module_tables":excluded_nested_count,
                        }),
                    )?;
                }
                BundleDependencyResolution::Unresolved {
                    candidates,
                    excluded_nested,
                } => {
                    add_unresolved_dependency(
                        graph,
                        source_node,
                        bundle_id,
                        dependency,
                        &candidates,
                        &excluded_nested,
                    )?;
                }
            }
        }
    }
    Ok(())
}

pub(super) fn seed_bundle_evidence(
    graph: &mut GraphBuilder,
    bundles: &Value,
    deob_nodes: &BTreeMap<u64, String>,
    budget: &WorkBudget,
) -> Result<()> {
    let bundle_nodes = seed_bundle_payload_nodes(graph, bundles, deob_nodes, budget)?;
    let index = seed_bundle_module_nodes(graph, bundles, &bundle_nodes, budget)?;
    seed_bundle_dependency_edges(graph, &index, budget)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bundle_candidate_fixture() -> Value {
        json!({
            "bundles":[
                {"bundle_id":1,"kind":"webpack","parent_path":"a.js","start":0,"end":800},
                {"bundle_id":2,"kind":"webpack_module_table","parent_path":"a.js","start":120,"end":140},
                {"bundle_id":3,"kind":"webpack_module_table","parent_path":"a.js","start":260,"end":300},
                {"bundle_id":4,"kind":"webpack","parent_path":"b.js","start":0,"end":100}
            ],
            "modules":[
                {"bundle_id":1,"module_ordinal":0,"module_id":"entry",
                 "parent_path":"a.js","value_start":100,"value_end":200,
                 "dependencies":["local","cross","private","ambiguous","missing","dup"]},
                {"bundle_id":1,"module_ordinal":1,"module_id":"local"},
                {"bundle_id":4,"module_ordinal":1,"module_id":"cross"},
                {"bundle_id":2,"module_ordinal":1,"module_id":"private"},
                {"bundle_id":3,"module_ordinal":1,"module_id":"ambiguous"},
                {"bundle_id":4,"module_ordinal":2,"module_id":"ambiguous"},
                {"bundle_id":1,"module_ordinal":2,"module_id":"dup"},
                {"bundle_id":1,"module_ordinal":3,"module_id":"dup"},
                {"bundle_id":1,"module_ordinal":4,"module_id":"outside",
                 "parent_path":"a.js","value_start":500,"value_end":600,
                 "dependencies":["private"]}
            ]
        })
    }

    #[test]
    fn bundle_dependencies_preserve_nested_privacy_and_duplicate_id_ambiguity() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let budget = work_budget::WorkBudget::new(
            "bundle-candidate-proof",
            work_budget::BudgetLimits::unlimited(),
        );
        let mut deob_nodes = BTreeMap::new();
        deob_nodes.insert(42, "deob:42".to_owned());
        let mut fixture = bundle_candidate_fixture();
        fixture["bundles"][0]["parent_ordinal"] = json!(42);
        seed_bundle_evidence(&mut graph, &fixture, &deob_nodes, &budget)?;

        let direct = |source: &str, destination: &str| {
            graph.edges.iter().find(|edge| {
                edge["kind"] == "bundle_module_dependency"
                    && edge["from"] == source
                    && edge["to"] == destination
            })
        };
        let entry = "bundle-module:1:0";
        assert_eq!(
            direct(entry, "bundle-module:1:1").context("missing exact local factory")?
                ["cross_bundle"],
            false
        );
        assert_eq!(
            direct(entry, "bundle-module:4:1").context("missing exact cross-bundle factory")?
                ["cross_bundle"],
            true
        );
        assert_eq!(
            direct("bundle-module:1:4", "bundle-module:2:1")
                .context("missing module outside private nesting")?["cross_bundle"],
            true
        );
        assert!(
            direct(entry, "bundle-module:2:1").is_none(),
            "private nested module must not satisfy its enclosing factory"
        );
        assert!(direct(entry, "bundle-module:1:2").is_none());
        assert!(direct(entry, "bundle-module:1:3").is_none());
        let ref_for = |id: &str| -> Result<String> {
            graph
                .edges
                .iter()
                .find(|edge| {
                    edge["kind"] == "bundle_module_dependency_unresolved"
                        && edge["from"] == entry
                        && edge["module_id"] == id
                })
                .and_then(|edge| edge["to"].as_str())
                .map(ToOwned::to_owned)
                .context("missing unresolved dependency")
        };
        let private = ref_for("private")?;
        let ambiguous = ref_for("ambiguous")?;
        let missing = ref_for("missing")?;
        let duplicate = ref_for("dup")?;
        assert_eq!(
            graph.nodes[&private]["excluded_nested_module_table_nodes"],
            json!(["bundle-module:2:1"])
        );
        assert_eq!(graph.nodes[&private]["candidate_nodes"], json!([]));
        assert_eq!(graph.nodes[&private]["ambiguous"], false);
        assert_eq!(
            graph.nodes[&ambiguous]["candidate_nodes"],
            json!(["bundle-module:3:1", "bundle-module:4:2"])
        );
        assert_eq!(graph.nodes[&ambiguous]["ambiguous"], true);
        assert_eq!(graph.nodes[&missing]["ambiguous"], false);
        assert_eq!(
            graph.nodes[&duplicate]["candidate_nodes"],
            json!(["bundle-module:1:2", "bundle-module:1:3"])
        );
        assert_eq!(
            graph.nodes[&duplicate]["ambiguous"], true,
            "multiple factories sharing a logical ID must not select the last factory"
        );
        for node in [&private, &ambiguous, &missing, &duplicate] {
            assert!(graph
                .edges
                .iter()
                .any(|edge| edge["kind"] == "bundle_module_dependency_unresolved"
                    && edge["from"] == entry
                    && edge["to"] == *node));
        }
        assert!(graph
            .edges
            .iter()
            .any(|edge| edge["kind"] == "bundle_payload"
                && edge["from"] == "deob:42"
                && edge["to"] == "bundle:1"));
        Ok(())
    }

    #[test]
    fn unresolved_bundle_references_keep_each_factorys_candidate_evidence() -> Result<()> {
        let bundles = json!({
            "bundles": [
                {"bundle_id":1,"kind":"webpack","parent_path":"a.js"},
                {"bundle_id":2,"kind":"webpack_module_table","parent_path":"a.js","start":20,"end":30},
                {"bundle_id":3,"kind":"webpack_module_table","parent_path":"a.js","start":60,"end":70},
                {"bundle_id":4,"kind":"webpack","parent_path":"b.js"}
            ],
            "modules": [
                {"bundle_id":1,"module_ordinal":0,"module_id":"first","parent_path":"a.js","value_start":10,"value_end":40,"dependencies":["shared"]},
                {"bundle_id":1,"module_ordinal":1,"module_id":"second","parent_path":"a.js","value_start":50,"value_end":80,"dependencies":["shared"]},
                {"bundle_id":2,"module_ordinal":0,"module_id":"shared"},
                {"bundle_id":3,"module_ordinal":0,"module_id":"shared"},
                {"bundle_id":4,"module_ordinal":0,"module_id":"shared"}
            ]
        });
        let budget = WorkBudget::new(
            "factory-specific-bundle-reference",
            work_budget::BudgetLimits::unlimited(),
        );
        let mut graph = GraphBuilder::default();
        seed_bundle_evidence(&mut graph, &bundles, &BTreeMap::new(), &budget)?;
        let reference = |source: &str| -> Result<&Value> {
            let edge = graph
                .edges
                .iter()
                .find(|edge| {
                    edge["kind"] == "bundle_module_dependency_unresolved" && edge["from"] == source
                })
                .context("missing unresolved edge")?;
            let node = graph
                .nodes
                .get(edge["to"].as_str().context("missing target ID")?)
                .context("missing reference node")?;
            assert_eq!(node["source_module_node"], source);
            assert_eq!(edge["candidate_count"], 2);
            assert_eq!(edge["excluded_nested_module_table_count"], 1);
            Ok(node)
        };
        let first = reference("bundle-module:1:0")?;
        let second = reference("bundle-module:1:1")?;
        assert_ne!(first["id"], second["id"]);
        assert_eq!(
            first["candidate_nodes"],
            json!(["bundle-module:3:0", "bundle-module:4:0"])
        );
        assert_eq!(
            second["candidate_nodes"],
            json!(["bundle-module:2:0", "bundle-module:4:0"])
        );
        assert_eq!(
            first["excluded_nested_module_table_nodes"],
            json!(["bundle-module:2:0"])
        );
        assert_eq!(
            second["excluded_nested_module_table_nodes"],
            json!(["bundle-module:3:0"])
        );
        Ok(())
    }

    #[test]
    fn candidate_scan_charges_work_before_allocating_resolution_evidence() -> Result<()> {
        let fixture = bundle_candidate_fixture();
        let mut graph = GraphBuilder::default();
        let budget = WorkBudget::unlimited("build-bundle-index");
        let payloads = seed_bundle_payload_nodes(&mut graph, &fixture, &BTreeMap::new(), &budget)?;
        let index = seed_bundle_module_nodes(&mut graph, &fixture, &payloads, &budget)?;
        let entry = index.module_rows["bundle-module:1:0"];
        let limited = WorkBudget::new("candidate-lookup", work_budget::BudgetLimits::work(1));
        assert!(index
            .resolve_dependency(1, entry, "ambiguous", &limited)
            .is_err());
        Ok(())
    }

    #[test]
    fn missing_or_invalid_nested_range_does_not_exclude_factory() -> Result<()> {
        let mut fixture = bundle_candidate_fixture();
        fixture["bundles"][1]["parent_path"] = Value::Null;
        fixture["modules"][0]["parent_path"] = Value::Null;
        let mut graph = GraphBuilder::default();
        let budget = WorkBudget::unlimited("unknown-path-bundle");
        seed_bundle_evidence(&mut graph, &fixture, &BTreeMap::new(), &budget)?;
        assert!(graph
            .edges
            .iter()
            .any(|edge| edge["from"] == "bundle-module:1:0"
                && edge["to"] == "bundle-module:2:1"
                && edge["kind"] == "bundle_module_dependency"));
        fixture["bundles"][1]["parent_path"] = json!("a.js");
        fixture["modules"][0]["parent_path"] = json!("a.js");
        fixture["bundles"][1]["end"] = json!(110);
        let mut graph = GraphBuilder::default();
        seed_bundle_evidence(&mut graph, &fixture, &BTreeMap::new(), &budget)?;
        assert!(graph
            .edges
            .iter()
            .any(|edge| edge["from"] == "bundle-module:1:0"
                && edge["to"] == "bundle-module:2:1"
                && edge["kind"] == "bundle_module_dependency"));
        Ok(())
    }

    #[test]
    fn duplicate_factory_ordinal_is_not_a_second_logical_module_candidate() {
        let bundles = json!({"bundles":[{"bundle_id":1}],"modules":[
            {"bundle_id":1,"module_ordinal":0,"module_id":"a"},
            {"bundle_id":1,"module_ordinal":0,"module_id":"b"}
        ]});
        let budget = WorkBudget::new(
            "duplicate-factory-identity",
            work_budget::BudgetLimits::unlimited(),
        );
        let result = seed_bundle_evidence(
            &mut GraphBuilder::default(),
            &bundles,
            &BTreeMap::new(),
            &budget,
        );
        assert!(result.err().is_some_and(|error| error
            .to_string()
            .contains("duplicate bundle factory identity")));
    }
}
