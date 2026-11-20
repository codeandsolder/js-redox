//! Source-map references, independent chain map/code identities and recovered sources.

use super::{
    array_field, field, nonempty_string_field, required_u64, string_field, u64_field, GraphBuilder,
};
use anyhow::Result;
use serde_json::{json, Value};
use std::collections::BTreeSet;
use work_budget::WorkBudget;

/// All resource IDs are evidence, including the singular claimed exact ID.
/// Exact identity is available only when the union is a singleton and agrees
/// with that explicit claim. A singleton candidate list alone is not proof.
struct ResourceIdentity {
    claimed: Option<u64>,
    ids: BTreeSet<u64>,
}

impl ResourceIdentity {
    fn from_fields(
        row: &Value,
        exact: &str,
        ids: &str,
        candidates: &str,
        budget: &WorkBudget,
    ) -> Result<Self> {
        let claimed = u64_field(row, exact);
        let verified = array_field(row, ids);
        let candidates = array_field(row, candidates);
        budget.consume(u64::try_from(
            verified.len() + candidates.len() + usize::from(claimed.is_some()),
        )?)?;
        let ids = verified
            .iter()
            .chain(candidates)
            .filter_map(Value::as_u64)
            .chain(claimed)
            .collect();
        Ok(Self { claimed, ids })
    }

    fn exact(&self) -> Option<u64> {
        self.claimed.filter(|_| self.ids.len() == 1)
    }

    fn map(row: &Value, budget: &WorkBudget) -> Result<Self> {
        Self::from_fields(
            row,
            "map_resource_id",
            "map_resource_ids",
            "candidate_resource_ids",
            budget,
        )
    }

    fn code(row: &Value, budget: &WorkBudget) -> Result<Self> {
        Self::from_fields(
            row,
            "code_resource_id",
            "code_resource_ids",
            "candidate_code_resource_ids",
            budget,
        )
    }

    fn map_candidates(
        &self,
        graph: &mut GraphBuilder,
        row: &Value,
        budget: &WorkBudget,
    ) -> Result<(Vec<String>, &'static str)> {
        if !self.ids.is_empty() {
            let basis = if self.claimed.is_some() && self.ids.len() > 1 {
                "conflicting_resource_ids"
            } else if string_field(row, "map_origin") == Some("har_shared_bytes") {
                "shared_verified_bytes"
            } else {
                "url_only"
            };
            // Preserve deterministic graph-ID order independent of artifact order.
            let mut nodes = self
                .ids
                .iter()
                .map(|id| format!("resource:{id}"))
                .collect::<Vec<_>>();
            nodes.sort_unstable();
            return Ok((nodes, basis));
        }
        let Some(url) = nonempty_string_field(row, "map_url") else {
            return Ok((Vec::new(), "url_only"));
        };
        Ok((graph.targets_for(url, budget)?, "url_only"))
    }
}

fn add_map_candidate_edges(
    graph: &mut GraphBuilder,
    source: &str,
    row: &Value,
    identity: &ResourceIdentity,
    kind: &str,
    budget: &WorkBudget,
) -> Result<()> {
    let (candidates, basis) = identity.map_candidates(graph, row, budget)?;
    for node in &candidates {
        budget.checkpoint()?;
        graph.add_edge(
            source,
            node,
            kind,
            json!({"candidate_count":candidates.len(), "identity_basis":basis}),
        )?;
    }
    Ok(())
}

fn add_sourcemap_reference(
    graph: &mut GraphBuilder,
    map: &Value,
    source: &str,
    resource_id: u64,
    budget: &WorkBudget,
) -> Result<String> {
    let identity = ResourceIdentity::map(map, budget)?;
    if let Some(id) = identity.exact() {
        let node = format!("resource:{id}");
        graph.add_edge(
            source,
            &node,
            "source_map",
            json!({
                "map_url":field(map,"map_url"),
            }),
        )?;
        return Ok(node);
    }
    // Recovery from common bytes does not prove a particular HTTP response
    // instance. Own the recovered sources on the resolution evidence node.
    let reference = format!("sourcemap-reference:{resource_id}");
    graph.insert_node(
        reference.clone(),
        json!({
            "type":"source_map_reference",
            "source_resource_id":resource_id,
            "map_url":field(map,"map_url"),
            "status":field(map,"status"),
            "map_origin":field(map,"map_origin"),
            "claimed_map_resource_id":identity.claimed,
            "map_resource_ids":field(map,"map_resource_ids"),
            "candidate_resource_ids":field(map,"candidate_resource_ids"),
        }),
    )?;
    graph.add_edge(
        source,
        &reference,
        "source_map_reference",
        json!({
            "map_url":field(map,"map_url"),
            "status":field(map,"status"),
        }),
    )?;
    add_map_candidate_edges(
        graph,
        &reference,
        map,
        &identity,
        "source_map_resource_candidate",
        budget,
    )?;
    Ok(reference)
}

/// The two recovered-source stages differ only in their observed artifact
/// category and ownership. The parent must be resolved separately: an exact
/// map resource or the map-reference evidence node for originals, and an
/// optional composed-map node for final composed sources.
#[derive(Clone, Copy)]
enum RecoveredMapStage {
    Original,
    Composed,
}

impl RecoveredMapStage {
    const fn fields(self) -> (&'static str, &'static str, &'static str, &'static str) {
        match self {
            Self::Original => (
                "recovered",
                "sourcemap-source",
                "sourcemap_source",
                "source_map_source",
            ),
            Self::Composed => (
                "composed_recovered",
                "sourcemap-final",
                "sourcemap_composed_source",
                "source_map_composed_source",
            ),
        }
    }
}

fn add_recovered_sourcemap_sources(
    graph: &mut GraphBuilder,
    source_map: &Value,
    resource_id: u64,
    parent: &str,
    stage: RecoveredMapStage,
    budget: &WorkBudget,
) -> Result<()> {
    let (source_field, node_prefix, node_type, edge_kind) = stage.fields();
    for recovered in array_field(source_map, source_field) {
        budget.consume(1)?;
        if string_field(recovered, "status") != Some("recovered") {
            continue;
        }
        let ordinal = required_u64(recovered, "ordinal", source_field)?;
        let node_id = format!("{node_prefix}:{resource_id}:{ordinal}");
        anyhow::ensure!(
            !graph.nodes().contains_key(&node_id),
            "duplicate recovered source identity {node_id}"
        );
        graph.insert_node(
            node_id.clone(),
            json!({
                "type":node_type,
                "parent_resource_id":resource_id,
                "ordinal":ordinal,
                "logical_source":field(recovered,"logical_source"),
                "source_path":field(recovered,"source_path"),
                "bytes":field(recovered,"bytes"),
            }),
        )?;
        graph.add_edge(parent, &node_id, edge_kind, json!({"ordinal":ordinal}))?;
    }
    Ok(())
}

/// Preserve nested map and code identity separately. A verified shared body
/// or repeated URL can yield multiple candidates, but never an exact response.
fn add_sourcemap_chain_links(
    graph: &mut GraphBuilder,
    composition: &Value,
    resource_id: u64,
    map_node: &str,
    budget: &WorkBudget,
) -> Result<()> {
    for (link_index, link) in array_field(composition, "links").iter().enumerate() {
        budget.consume(1)?;
        let map_identity = ResourceIdentity::map(link, budget)?;
        let code_identity = ResourceIdentity::code(link, budget)?;
        let chain_node = format!("sourcemap-chain:{resource_id}:{link_index}");
        graph.insert_node(
            chain_node.clone(),
            json!({
                "type":"sourcemap_chain_link",
                "parent_resource_id":resource_id,
                "depth":field(link,"depth"),
                "source_ordinal":field(link,"source_ordinal"),
                "logical_source":field(link,"logical_source"),
                "raw_reference":field(link,"raw_reference"),
                "map_url":field(link,"map_url"),
                "map_resource_id":map_identity.exact(),
                "claimed_map_resource_id":map_identity.claimed,
                "map_resource_ids":map_identity.ids,
                "code_resource_id":code_identity.exact(),
                "claimed_code_resource_id":code_identity.claimed,
                "code_resource_ids":code_identity.ids,
                "map_origin":field(link,"map_origin"),
                "status":field(link,"status"),
            }),
        )?;
        graph.add_edge(map_node, &chain_node, "source_map_chain", json!({}))?;
        if let Some(nested_map_resource_id) = map_identity.exact() {
            graph.add_edge(
                &chain_node,
                &format!("resource:{nested_map_resource_id}"),
                "source_map_chain_resource",
                json!({}),
            )?;
        } else {
            add_map_candidate_edges(
                graph,
                &chain_node,
                link,
                &map_identity,
                "source_map_chain_resource_candidate",
                budget,
            )?;
        }
        let exact_code = code_identity.exact();
        for code_id in &code_identity.ids {
            budget.checkpoint()?;
            let proven = exact_code == Some(*code_id);
            graph.add_edge(
                    &chain_node,
                    &format!("resource:{code_id}"),
                    if proven { "source_map_chain_code" } else { "source_map_chain_code_candidate" },
                    json!({
                        "candidate_count":code_identity.ids.len(),
                        "identity_basis": if proven { "exact_resource_id" } else { "source_url_verified_common_bytes_or_ambiguous" },
                    }),
                )?;
        }
    }

    Ok(())
}

/// Build a composed map node only when composition actually produced a map.
fn add_sourcemap_composition(
    graph: &mut GraphBuilder,
    source_map: &Value,
    resource_id: u64,
    map_node: &str,
    budget: &WorkBudget,
) -> Result<()> {
    let composition = source_map.get("composition").unwrap_or(&Value::Null);
    let composed_node = if let Some(composed_map_path) =
        nonempty_string_field(composition, "composed_map_path")
    {
        let node_id = format!("sourcemap-composed:{resource_id}");
        graph.insert_node(
                node_id.clone(),
                json!({
                    "type":"composed_source_map",
                    "parent_resource_id":resource_id,
                    "source_path":composed_map_path,
                    "composed_links":composition.get("composed_links").cloned().unwrap_or_else(|| json!(0)),
                    "composed_sources":composition.get("composed_sources").cloned().unwrap_or_else(|| json!(0)),
                }),
            )?;
        graph.add_edge(map_node, &node_id, "source_map_composed", json!({}))?;
        Some(node_id)
    } else {
        None
    };

    add_sourcemap_chain_links(graph, composition, resource_id, map_node, budget)?;
    let parent = composed_node.as_deref().unwrap_or(map_node);
    add_recovered_sourcemap_sources(
        graph,
        source_map,
        resource_id,
        parent,
        RecoveredMapStage::Composed,
        budget,
    )?;
    Ok(())
}

/// Seed source-map references, original sources and composition evidence
/// without promoting candidate map/code resource identities to exact links.
pub(super) fn seed_sourcemap_evidence(
    graph: &mut GraphBuilder,
    sourcemaps: &Value,
    budget: &WorkBudget,
) -> Result<()> {
    let mut seen = BTreeSet::new();
    for source_map in array_field(sourcemaps, "source_maps") {
        budget.consume(1)?;
        let Some(resource_id) = u64_field(source_map, "resource_id") else {
            continue;
        };
        anyhow::ensure!(
            seen.insert(resource_id),
            "duplicate source-map resource identity {resource_id}"
        );
        let src = format!("resource:{resource_id}");
        let map_node = add_sourcemap_reference(graph, source_map, &src, resource_id, budget)?;

        add_recovered_sourcemap_sources(
            graph,
            source_map,
            resource_id,
            &map_node,
            RecoveredMapStage::Original,
            budget,
        )?;
        add_sourcemap_composition(graph, source_map, resource_id, &map_node, budget)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ambiguous_sourcemap_graph_fixture() -> Value {
        json!({"source_maps":[{
            "resource_id":7,
            "map_url":"https://maps.test/root.map",
            "map_origin":"har_shared_bytes",
            "map_resource_ids":[8,9],
            "recovered":[
                {"ordinal":0,"status":"recovered","source_path":"src/original.ts"},
                {"ordinal":1,"status":"missing","source_path":"src/unknown.ts"}
            ],
            "composition":{
                "composed_map_path":"maps/composed.map",
                "composed_links":3,
                "composed_sources":1,
                "links":[
                    {"map_resource_ids":[25,26],"candidate_resource_ids":[26],
                     "map_origin":"har_shared_bytes","code_resource_id":21,
                     "code_resource_ids":[21,22],"candidate_code_resource_ids":[22]},
                    {"map_resource_id":14,"code_resource_id":23,"code_resource_ids":[23]},
                    {"map_url":"https://maps.test/child.map","code_resource_ids":[40,41]}
                ]
            },
            "composed_recovered":[
                {"ordinal":0,"status":"recovered","source_path":"src/final.ts"},
                {"ordinal":1,"status":"missing"}
            ]
        }]})
    }

    #[test]
    fn sourcemap_graph_composition_keeps_ambiguous_map_and_code_candidates() -> Result<()> {
        let budget = work_budget::WorkBudget::new(
            "sourcemap-ambiguous-composition",
            work_budget::BudgetLimits::unlimited(),
        );
        let mut graph = GraphBuilder::default();
        for id in [90, 91] {
            let node = format!("resource:{id}");
            graph.insert_node(&node, json!({"type":"resource"}))?;
            graph.register_resource_url("https://maps.test/child.map", &node);
        }
        seed_sourcemap_evidence(&mut graph, &ambiguous_sourcemap_graph_fixture(), &budget)?;
        let edges_from = |kind: &str, from: &str| {
            graph
                .edges()
                .values()
                .filter(|edge| edge["kind"] == kind && edge["from"] == from)
                .collect::<Vec<_>>()
        };
        let candidate_resources =
            edges_from("source_map_resource_candidate", "sourcemap-reference:7");
        assert_eq!(candidate_resources.len(), 2);
        assert!(candidate_resources
            .iter()
            .all(|edge| edge["candidate_count"] == 2
                && edge["identity_basis"] == "shared_verified_bytes"));
        assert_eq!(edges_from("source_map_reference", "resource:7").len(), 1);
        assert_eq!(
            edges_from("source_map_source", "sourcemap-reference:7").len(),
            1
        );
        assert!(!graph.nodes().contains_key("sourcemap-source:7:1"));
        assert_eq!(
            graph.nodes()["sourcemap-composed:7"]["source_path"],
            "maps/composed.map"
        );
        assert_eq!(
            edges_from("source_map_composed", "sourcemap-reference:7").len(),
            1
        );
        assert_eq!(
            edges_from("source_map_composed_source", "sourcemap-composed:7").len(),
            1
        );
        assert!(!graph.nodes().contains_key("sourcemap-final:7:1"));

        let map_candidates =
            edges_from("source_map_chain_resource_candidate", "sourcemap-chain:7:0");
        assert_eq!(map_candidates.len(), 2);
        assert!(map_candidates
            .iter()
            .all(|edge| edge["candidate_count"] == 2
                && edge["identity_basis"] == "shared_verified_bytes"));
        let code_candidates = edges_from("source_map_chain_code_candidate", "sourcemap-chain:7:0");
        assert_eq!(code_candidates.len(), 2);
        assert!(code_candidates
            .iter()
            .all(|edge| edge["candidate_count"] == 2
                && edge["identity_basis"] == "source_url_verified_common_bytes_or_ambiguous"));
        assert_eq!(
            edges_from("source_map_chain_code", "sourcemap-chain:7:0").len(),
            0
        );
        assert_eq!(
            edges_from("source_map_chain_resource", "sourcemap-chain:7:1").len(),
            1
        );
        assert_eq!(
            edges_from("source_map_chain_code", "sourcemap-chain:7:1").len(),
            1
        );
        let url_candidates =
            edges_from("source_map_chain_resource_candidate", "sourcemap-chain:7:2");
        assert_eq!(url_candidates.len(), 2);
        assert!(url_candidates
            .iter()
            .all(|edge| edge["candidate_count"] == 2 && edge["identity_basis"] == "url_only"));
        Ok(())
    }

    #[test]
    fn sourcemap_graph_recovered_sources_keep_exact_or_reference_ownership() -> Result<()> {
        let budget = work_budget::WorkBudget::new(
            "sourcemap-recovered-ownership",
            work_budget::BudgetLimits::unlimited(),
        );
        let mut graph = GraphBuilder::default();
        let artifact = json!({"source_maps":[
            {"resource_id":42,"map_resource_id":43,
             "recovered":[{"status":"recovered","ordinal":1,"source_path":"one.ts"}],
             "composed_recovered":[{"status":"recovered","ordinal":2,"source_path":"final.ts"}]},
            {"resource_id":44,"map_url":"https://maps.test/unknown.map",
             "recovered":[{"status":"recovered","ordinal":1,"source_path":"two.ts"}],
             "composed_recovered":[{"status":"recovered","ordinal":2,"source_path":"final2.ts"}]}
        ]});
        seed_sourcemap_evidence(&mut graph, &artifact, &budget)?;
        let has_edge = |kind: &str, from: &str, to: &str| {
            graph
                .edges()
                .values()
                .any(|edge| edge["kind"] == kind && edge["from"] == from && edge["to"] == to)
        };
        assert!(has_edge("source_map", "resource:42", "resource:43"));
        assert!(has_edge(
            "source_map_source",
            "resource:43",
            "sourcemap-source:42:1"
        ));
        assert!(has_edge(
            "source_map_composed_source",
            "resource:43",
            "sourcemap-final:42:2"
        ));
        assert!(!graph.nodes().contains_key("sourcemap-reference:42"));
        assert!(!graph.nodes().contains_key("sourcemap-composed:42"));
        assert!(has_edge(
            "source_map_reference",
            "resource:44",
            "sourcemap-reference:44"
        ));
        assert!(has_edge(
            "source_map_source",
            "sourcemap-reference:44",
            "sourcemap-source:44:1"
        ));
        assert!(has_edge(
            "source_map_composed_source",
            "sourcemap-reference:44",
            "sourcemap-final:44:2"
        ));
        assert!(!graph.nodes().contains_key("sourcemap-composed:44"));
        assert_eq!(graph.external_url_count(), 1);
        assert_eq!(
            graph
                .edges()
                .values()
                .filter(|edge| edge["kind"] == "source_map_resource_candidate"
                    && edge["from"] == "sourcemap-reference:44")
                .count(),
            1
        );
        Ok(())
    }

    #[test]
    fn contradictory_map_claims_never_own_recovered_sources_on_a_resource() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let budget = WorkBudget::unlimited("contradictory-map-id");
        let artifact = json!({"source_maps":[{
            "resource_id":7,"map_resource_id":8,"candidate_resource_ids":[9],
            "recovered":[{"status":"recovered","ordinal":0}],
            "composition":{"links":[{"map_resource_id":10,"map_resource_ids":[11],"code_resource_id":12,"candidate_code_resource_ids":[13]}, {"code_resource_id":14}]}
        }]});
        seed_sourcemap_evidence(&mut graph, &artifact, &budget)?;
        let targets = |from: &str, kind: &str| -> BTreeSet<&str> {
            graph
                .edges()
                .values()
                .filter(|edge| edge["from"] == from && edge["kind"] == kind)
                .filter_map(|edge| edge["to"].as_str())
                .collect()
        };
        assert_eq!(
            graph.nodes()["sourcemap-chain:7:0"]["map_resource_id"],
            Value::Null
        );
        assert_eq!(
            graph.nodes()["sourcemap-chain:7:0"]["claimed_map_resource_id"],
            10
        );
        assert_eq!(
            graph.nodes()["sourcemap-chain:7:0"]["code_resource_id"],
            Value::Null
        );
        assert_eq!(targets("resource:7", "source_map").len(), 0);
        assert_eq!(
            targets("sourcemap-reference:7", "source_map_resource_candidate"),
            BTreeSet::from(["resource:8", "resource:9"])
        );
        assert_eq!(
            targets("sourcemap-reference:7", "source_map_source"),
            BTreeSet::from(["sourcemap-source:7:0"])
        );
        assert_eq!(
            targets("sourcemap-chain:7:0", "source_map_chain_resource").len(),
            0
        );
        assert_eq!(
            targets("sourcemap-chain:7:0", "source_map_chain_resource_candidate"),
            BTreeSet::from(["resource:10", "resource:11"])
        );
        assert_eq!(
            targets("sourcemap-chain:7:0", "source_map_chain_code").len(),
            0
        );
        assert_eq!(
            targets("sourcemap-chain:7:0", "source_map_chain_code_candidate"),
            BTreeSet::from(["resource:12", "resource:13"])
        );
        assert_eq!(
            targets("sourcemap-chain:7:1", "source_map_chain_code"),
            BTreeSet::from(["resource:14"])
        );
        assert!(graph
            .edges()
            .values()
            .filter(|edge| edge["kind"] == "source_map_chain_resource_candidate"
                || edge["kind"] == "source_map_resource_candidate")
            .all(|edge| edge["identity_basis"] == "conflicting_resource_ids"));
        Ok(())
    }

    #[test]
    fn singular_candidate_is_not_exact_and_candidate_work_is_bounded() -> Result<()> {
        let row = json!({"candidate_resource_ids":[7,7], "map_origin":"har_resource"});
        let unlimited = WorkBudget::unlimited("single-candidate");
        let identity = ResourceIdentity::map(&row, &unlimited)?;
        assert_eq!(identity.exact(), None);
        assert_eq!(identity.ids, BTreeSet::from([7]));
        let limited = WorkBudget::new("map-candidate-budget", work_budget::BudgetLimits::work(1));
        assert!(ResourceIdentity::map(&row, &limited).is_err());
        Ok(())
    }

    #[test]
    fn recovered_ordinals_are_not_silently_coalesced() {
        let budget = WorkBudget::unlimited("duplicate-map-source");
        let artifact = json!({"source_maps":[{"resource_id":7,"recovered":[{"status":"recovered","ordinal":0},{"status":"recovered","ordinal":0}]}]});
        let result = seed_sourcemap_evidence(&mut GraphBuilder::default(), &artifact, &budget);
        assert!(result.err().is_some_and(|error| error
            .to_string()
            .contains("duplicate recovered source identity")));
    }
}
