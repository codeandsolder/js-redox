//! Graph storage and publication invariants shared by every evidence stage.

use super::{digest_id, nonempty_string_field, SourceGraphSummary};
use crate::{
    analysis_artifacts::{write_artifact, SOURCE_GRAPH},
    capture_project::CaptureManifest,
};
use anyhow::{ensure, Context, Result};
use serde_json::{json, Map, Value};
use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    path::Path,
};
use work_budget::WorkBudget;

/// A graph edge is identified by its ordered endpoints, kind and complete
/// evidence. Fields are compared without concatenation ambiguities. Ordering
/// also provides canonical publication order, including tied endpoints.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct EdgeIdentity {
    from: String,
    kind: String,
    to: String,
    evidence: String,
}

enum NodeRecord {
    Occurrence(Value),
    Shared(Value),
}

impl NodeRecord {
    const fn value(&self) -> &Value {
        match self {
            Self::Occurrence(value) | Self::Shared(value) => value,
        }
    }
    fn into_value(self) -> Value {
        match self {
            Self::Occurrence(value) | Self::Shared(value) => value,
        }
    }
}

#[derive(Default)]
pub(super) struct GraphBuilder {
    nodes: BTreeMap<String, NodeRecord>,
    edges: BTreeMap<EdgeIdentity, Value>,
    resource_urls: BTreeMap<String, BTreeSet<String>>,
    external_nodes: BTreeMap<String, String>,
}

impl GraphBuilder {
    pub(super) fn node(&self, id: &str) -> Option<&Value> {
        self.nodes.get(id).map(NodeRecord::value)
    }

    pub(super) fn has_node(&self, id: &str) -> bool {
        self.nodes.contains_key(id)
    }

    #[cfg(test)]
    pub(super) fn node_value(&self, id: &str) -> &Value {
        self.nodes[id].value()
    }

    #[cfg(test)]
    pub(super) fn node_count(&self) -> usize {
        self.nodes.len()
    }

    #[cfg(test)]
    pub(super) fn node_values(&self) -> impl Iterator<Item = &Value> {
        self.nodes.values().map(NodeRecord::value)
    }

    #[cfg(test)]
    pub(super) const fn edges(&self) -> &BTreeMap<EdgeIdentity, Value> {
        &self.edges
    }

    pub(super) fn captured_targets(&self, url: &str) -> Option<&BTreeSet<String>> {
        self.resource_urls.get(url)
    }

    #[cfg(test)]
    pub(super) fn external_url_count(&self) -> usize {
        self.external_nodes.len()
    }

    fn node_record(id: &str, fields: Value) -> Result<Map<String, Value>> {
        ensure!(!id.is_empty(), "graph node ID must not be empty");
        let Value::Object(fields) = fields else {
            anyhow::bail!("graph node fields must be a JSON object");
        };
        ensure!(
            !fields.contains_key("id"),
            "graph node fields must not override the node id"
        );
        ensure!(
            fields
                .get("type")
                .and_then(Value::as_str)
                .is_some_and(|kind| !kind.is_empty()),
            "graph node {id} requires a nonempty type"
        );
        Ok(fields)
    }

    /// Occurrence identities (capture resources, sites, ordinals) must be unique.
    pub(super) fn insert_node(&mut self, id: impl Into<String>, fields: Value) -> Result<()> {
        let id = id.into();
        let mut fields = Self::node_record(&id, fields)?;
        match self.nodes.entry(id) {
            Entry::Occupied(entry) => {
                anyhow::bail!("duplicate graph node identity {}", entry.key())
            }
            Entry::Vacant(entry) => {
                fields.insert("id".into(), Value::String(entry.key().clone()));
                entry.insert(NodeRecord::Occurrence(Value::Object(fields)));
            }
        }
        Ok(())
    }

    /// Shared semantic/content identities may be reused, but overlapping
    /// non-null evidence must agree. Missing or null fields carry no claim.
    /// Validate the complete record before modifying the existing node.
    pub(super) fn intern_node(&mut self, id: impl Into<String>, fields: Value) -> Result<()> {
        let id = id.into();
        let mut fields = Self::node_record(&id, fields)?;
        match self.nodes.entry(id) {
            Entry::Vacant(entry) => {
                fields.insert("id".into(), Value::String(entry.key().clone()));
                entry.insert(NodeRecord::Shared(Value::Object(fields)));
            }
            Entry::Occupied(mut entry) => {
                let key = entry.key().clone();
                let NodeRecord::Shared(record) = entry.get_mut() else {
                    anyhow::bail!("graph node {key} was registered as a unique occurrence");
                };
                let existing = record
                    .as_object_mut()
                    .context("stored graph node must be an object")?;
                for (field, value) in &fields {
                    if let Some(previous) = existing.get(field) {
                        ensure!(
                            previous.is_null() || value.is_null() || previous == value,
                            "conflicting shared graph node {key} field {field}"
                        );
                    }
                }
                for (field, value) in fields {
                    match existing.entry(field) {
                        serde_json::map::Entry::Vacant(entry) => {
                            entry.insert(value);
                        }
                        serde_json::map::Entry::Occupied(mut entry) if entry.get().is_null() => {
                            entry.insert(value);
                        }
                        serde_json::map::Entry::Occupied(_) => {}
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn add_edge(
        &mut self,
        from: &str,
        to: &str,
        kind: &str,
        fields: Value,
    ) -> Result<()> {
        ensure!(
            !from.is_empty() && !to.is_empty() && !kind.is_empty(),
            "graph edge requires endpoints and kind"
        );
        let Value::Object(mut fields) = fields else {
            anyhow::bail!("graph edge fields must be a JSON object");
        };
        ensure!(
            !["from", "to", "kind"]
                .iter()
                .any(|key| fields.contains_key(*key)),
            "graph edge fields must not override the edge endpoints or kind"
        );
        let identity = EdgeIdentity {
            from: from.to_owned(),
            kind: kind.to_owned(),
            to: to.to_owned(),
            evidence: serde_json::to_string(&fields)?,
        };
        if let Entry::Vacant(entry) = self.edges.entry(identity) {
            fields.insert("from".into(), Value::String(from.to_owned()));
            fields.insert("to".into(), Value::String(to.to_owned()));
            fields.insert("kind".into(), Value::String(kind.to_owned()));
            entry.insert(Value::Object(fields));
        }
        Ok(())
    }

    pub(super) fn register_resource_url(&mut self, url: &str, node_id: &str) {
        self.resource_urls
            .entry(url.to_owned())
            .or_default()
            .insert(node_id.to_owned());
    }

    /// All URL fan-out is charged before allocating the candidate vector.
    pub(super) fn targets_for(&mut self, url: &str, budget: &WorkBudget) -> Result<Vec<String>> {
        if let Some(captured) = self.resource_urls.get(url) {
            budget.consume(u64::try_from(captured.len())?)?;
            return Ok(captured.iter().cloned().collect());
        }
        budget.consume(1)?;
        if let Some(existing) = self.external_nodes.get(url) {
            return Ok(vec![existing.clone()]);
        }
        let node_id = digest_id("external:", url);
        self.intern_node(
            node_id.clone(),
            json!({"type":"external_url", "url":url, "captured":false}),
        )?;
        self.external_nodes.insert(url.to_owned(), node_id.clone());
        Ok(vec![node_id])
    }

    pub(super) fn finish(
        self,
        project: &Path,
        manifest: &CaptureManifest,
        budget: &WorkBudget,
    ) -> Result<SourceGraphSummary> {
        let mut edge_counts = BTreeMap::<String, usize>::new();
        let mut unresolved_edge_counts = BTreeMap::<String, usize>::new();
        let mut edges = Vec::new();
        let mut unresolved_edges = Vec::new();
        // Resolve endpoints only after all stages have populated the inventory.
        // A partial artifact can retain claims without inventing captured nodes
        // or publishing dangling relationships as actual graph links.
        for (identity, edge) in self.edges {
            budget.checkpoint()?;
            let from_missing = !self.nodes.contains_key(&identity.from);
            let to_missing = !self.nodes.contains_key(&identity.to);
            if from_missing || to_missing {
                let missing_endpoints = [(from_missing, "from"), (to_missing, "to")]
                    .into_iter()
                    .filter_map(|(missing, endpoint)| missing.then_some(endpoint))
                    .collect::<Vec<_>>();
                *unresolved_edge_counts.entry(identity.kind).or_default() += 1;
                unresolved_edges.push(json!({"edge":edge,"missing_endpoints":missing_endpoints}));
            } else {
                *edge_counts.entry(identity.kind).or_default() += 1;
                edges.push(edge);
            }
        }
        let mut node_counts = BTreeMap::<String, usize>::new();
        for node in self.nodes.values().map(NodeRecord::value) {
            budget.checkpoint()?;
            let kind =
                nonempty_string_field(node, "type").context("stored graph node missing type")?;
            *node_counts.entry(kind.to_owned()).or_default() += 1;
        }
        let summary = SourceGraphSummary {
            nodes: self.nodes.len(),
            edges: edges.len(),
            unresolved_edges: unresolved_edges.len(),
            external_urls: node_counts.get("external_url").copied().unwrap_or(0),
        };
        budget.checkpoint()?;
        let document = json!({
            "schema": SOURCE_GRAPH.schema,
            "project": ".",
            "capture_salvaged": manifest.source.salvaged,
            "nodes": self.nodes.into_values().map(NodeRecord::into_value).collect::<Vec<_>>(),
            "edges": edges,
            "unresolved_edges": unresolved_edges,
            "summary": {
                "nodes": summary.nodes,
                "edges": summary.edges,
                "node_types": node_counts,
                "edge_kinds": edge_counts,
                "unresolved_edges": summary.unresolved_edges,
                "unresolved_edge_kinds": unresolved_edge_counts,
                "external_urls": summary.external_urls,
            },
        });
        budget.checkpoint()?;
        write_artifact(project, SOURCE_GRAPH, &document)?;
        Ok(summary)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use work_budget::BudgetLimits;

    #[test]
    fn unique_and_shared_identities_have_distinct_conflict_semantics() -> Result<()> {
        let mut graph = GraphBuilder::default();
        graph.insert_node("source:a", json!({"type":"resource","value":1}))?;
        assert!(graph
            .insert_node("source:a", json!({"type":"resource","value":1}))
            .is_err());
        assert!(graph
            .intern_node("source:a", json!({"type":"resource","additional":true}))
            .is_err());
        assert_eq!(graph.node_value("source:a")["additional"], Value::Null);
        graph.intern_node(
            "source:b",
            json!({"type":"wasm_module","sha256":"full-a","unknown":null}),
        )?;
        graph.intern_node(
            "source:b",
            json!({"type":"wasm_module","sha256":"full-a","unknown":42,"metadata":{"items":[1,2]}}),
        )?;
        graph.intern_node("source:b", json!({"type":"wasm_module","unknown":null}))?;
        assert!(graph
            .intern_node(
                "source:b",
                json!({"type":"wasm_module","sha256":"full-b","should_not_be_added":true})
            )
            .is_err());
        assert!(graph
            .intern_node("source:b", json!({"type":"runtime_script"}))
            .is_err());
        assert_eq!(
            graph.node_value("source:b"),
            &json!({"id":"source:b","type":"wasm_module","sha256":"full-a","unknown":42,"metadata":{"items":[1,2]}})
        );
        for fields in [
            json!({"id":"spoofed","type":"resource"}),
            json!([]),
            json!({}),
            json!({"type":""}),
        ] {
            assert!(graph.insert_node("invalid", fields).is_err());
        }
        assert_eq!(graph.node_count(), 2);
        Ok(())
    }

    #[test]
    fn edge_identity_is_structural_and_publication_order_is_canonical() -> Result<()> {
        let mut graph = GraphBuilder::default();
        graph.add_edge("a\0b", "c", "d", json!({}))?;
        graph.add_edge("a", "b\0c", "d", json!({}))?;
        graph.add_edge("a", "b", "reference", json!({"evidence":2}))?;
        graph.add_edge("a", "b", "reference", json!({"evidence":1}))?;
        graph.add_edge("a", "b", "reference", json!({"evidence":1}))?;
        assert_eq!(graph.edges().len(), 4);
        let witnesses = graph
            .edges()
            .values()
            .filter(|edge| edge["kind"] == "reference")
            .map(|edge| edge["evidence"].clone())
            .collect::<Vec<_>>();
        assert_eq!(witnesses, [json!(1), json!(2)]);
        for field in ["from", "to", "kind"] {
            assert!(graph
                .add_edge("a", "b", "reference", json!({(field):"spoofed"}))
                .is_err());
        }
        assert!(graph.add_edge("a", "b", "reference", Value::Null).is_err());
        assert_eq!(graph.edges().len(), 4);
        Ok(())
    }

    #[test]
    fn url_index_charges_unique_targets_before_materializing_them() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let url = "https://fixture.test/shared";
        graph.register_resource_url(url, "resource:9");
        graph.register_resource_url(url, "resource:2");
        graph.register_resource_url(url, "resource:9");
        let limited = WorkBudget::new("url-budget", BudgetLimits::work(1));
        assert!(graph.targets_for(url, &limited).is_err());
        let unlimited = WorkBudget::unlimited("url-unlimited");
        assert_eq!(
            graph.targets_for(url, &unlimited)?,
            ["resource:2", "resource:9"]
        );
        let denied = WorkBudget::new("external-budget", BudgetLimits::work(0));
        let unknown = "https://fixture.test/new";
        assert!(graph.targets_for(unknown, &denied).is_err());
        assert_eq!(graph.external_url_count(), 0);
        let first = graph.targets_for(unknown, &unlimited)?;
        assert_eq!(graph.targets_for(unknown, &unlimited)?, first);
        assert_eq!(graph.external_url_count(), 1);
        Ok(())
    }
}
