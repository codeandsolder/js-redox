//! Captured HTTP response, navigation and inline-script source identities.
//!
//! A response ID identifies one recorded HTTP response, not a URL or digest.
//! An inline script identifies its owning document and ordinal, not merely the
//! bytes or output path. Candidate links must preserve every possible owner.

use super::{
    array_field, field, nonempty_string_field, required_u64, string_field, u64_field, GraphBuilder,
};
use crate::capture_project::CaptureManifest;
use anyhow::Result;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use url::Url;
use work_budget::WorkBudget;

fn resolve_url(base: &str, reference: &str) -> String {
    Url::parse(base)
        .and_then(|url| url.join(reference))
        .map_or_else(|_| reference.to_string(), |url| url.to_string())
}

#[derive(Debug, Default)]
pub(super) struct InlineSourceIndex {
    by_identity: BTreeMap<(String, u64, u64), String>,
    by_site: BTreeMap<(u64, u64), String>,
    by_unique_raw: BTreeMap<String, Option<String>>,
}

impl InlineSourceIndex {
    pub(super) fn insert(
        &mut self,
        raw: &str,
        parent: u64,
        ordinal: u64,
        node: String,
    ) -> Result<()> {
        anyhow::ensure!(
            !self.by_site.contains_key(&(parent, ordinal)),
            "duplicate inline script site ({parent}, {ordinal})"
        );
        anyhow::ensure!(
            !self
                .by_identity
                .contains_key(&(raw.to_owned(), parent, ordinal)),
            "duplicate inline script identity {raw} ({parent}, {ordinal})"
        );
        self.by_site.insert((parent, ordinal), node.clone());
        self.by_identity
            .insert((raw.to_owned(), parent, ordinal), node.clone());
        self.by_unique_raw
            .entry(raw.to_owned())
            .and_modify(|existing| *existing = None)
            .or_insert(Some(node));
        Ok(())
    }

    pub(super) fn exact(&self, raw: &str, parent: u64, ordinal: u64) -> Option<String> {
        self.by_identity
            .get(&(raw.to_owned(), parent, ordinal))
            .cloned()
    }

    pub(super) fn for_record(&self, record: &Value) -> Option<String> {
        let raw = string_field(record, "raw_path")?;
        match (
            u64_field(record, "resource_id"),
            u64_field(record, "ordinal"),
        ) {
            (Some(parent), Some(ordinal)) => self.exact(raw, parent, ordinal),
            _ => self.by_unique_raw.get(raw).and_then(Clone::clone),
        }
    }
}

/// Indices preserve each HTTP response and inline (document, ordinal) source
/// separately even where the URL, digest, or output path is shared.
pub(super) struct CapturedSourceIndex {
    pub(super) resource_nodes_by_sha: BTreeMap<String, Vec<String>>,
    pub(super) inline_nodes: InlineSourceIndex,
    pub(super) inline_nodes_by_sha: BTreeMap<String, Vec<String>>,
}

/// Seed all capture identities before runtime, import map, WASM, or module
/// consumers begin resolving candidates.
pub(super) fn seed_capture_evidence(
    graph: &mut GraphBuilder,
    manifest: &CaptureManifest,
    source_index: &Value,
    budget: &WorkBudget,
) -> Result<CapturedSourceIndex> {
    let resource_nodes_by_sha = seed_captured_resources(graph, manifest, source_index, budget)?;
    seed_navigation_roots(graph, manifest, budget)?;
    seed_captured_reference_edges(graph, manifest, budget)?;
    let (inline_nodes, inline_nodes_by_sha) =
        seed_captured_inline_scripts(graph, manifest, budget)?;
    Ok(CapturedSourceIndex {
        resource_nodes_by_sha,
        inline_nodes,
        inline_nodes_by_sha,
    })
}

pub(super) fn seed_captured_resources(
    graph: &mut GraphBuilder,
    manifest: &CaptureManifest,
    source_index: &Value,
    budget: &WorkBudget,
) -> Result<BTreeMap<String, Vec<String>>> {
    let mut source_by_resource = BTreeMap::<u64, Vec<&Value>>::new();
    for unit in array_field(source_index, "units") {
        budget.checkpoint()?;
        if let Some(resource_id) = u64_field(unit, "resource_id") {
            source_by_resource
                .entry(resource_id)
                .or_default()
                .push(unit);
        }
    }

    let mut resource_nodes_by_sha = BTreeMap::<String, Vec<String>>::new();
    let mut seen_resource_ids = BTreeSet::new();
    for (index, resource) in manifest.resources.iter().enumerate() {
        budget.checkpoint()?;
        let resource_id = required_u64(resource, "id", &format!("manifest.resources[{index}]"))?;
        anyhow::ensure!(
            seen_resource_ids.insert(resource_id),
            "duplicate captured resource id {resource_id}"
        );
        let node_id = format!("resource:{resource_id}");
        let units = source_by_resource
            .get(&resource_id)
            .map_or_default(Vec::as_slice);
        let source_paths = units
            .iter()
            .filter_map(|unit| nonempty_string_field(unit, "source_path"))
            .map(|path| Value::String(path.to_string()))
            .collect::<Vec<_>>();
        let mut node = json!({
            "type":"resource",
            "resource_id":resource_id,
            "url":field(resource,"url"),
            "kind":field(resource,"kind"),
            "status":field(resource,"status"),
            "body_present":field(resource,"body_present"),
            "raw_path":field(resource,"output_path"),
            "source_paths":source_paths,
            "sha256":field(resource,"sha256"),
        });
        if let Some(roles) = resource.get("saved_page_reference_roles") {
            node["saved_page_reference_roles"] = roles.clone();
        }
        graph.add_node(node_id.clone(), node)?;
        if let Some(url) = nonempty_string_field(resource, "url") {
            graph.register_resource_url(url, &node_id);
        }
        if let Some(sha) = nonempty_string_field(resource, "sha256") {
            resource_nodes_by_sha
                .entry(sha.to_string())
                .or_default()
                .push(node_id);
        }
    }
    Ok(resource_nodes_by_sha)
}

pub(super) fn seed_navigation_roots(
    graph: &mut GraphBuilder,
    manifest: &CaptureManifest,
    budget: &WorkBudget,
) -> Result<()> {
    // A recorder may lack HAR log.pages, but its navigation URL still
    // establishes an HTML/browser root for the captured resource graph.
    // Only link a browser page to resource URLs exactly observed in the
    // manifest; redirects and script references remain distinct edges.
    for (index, page) in manifest.pages.iter().enumerate() {
        budget.checkpoint()?;
        if nonempty_string_field(page, "kind") != Some("recorder_navigation") {
            continue;
        }
        let page_id = format!("page:{index}");
        graph.add_node(
            page_id.clone(),
            json!({
                "type": "browser_entrypoint",
                "requested_url": field(page, "requested_url"),
                "final_url": field(page, "final_url"),
            }),
        )?;
        for (key, edge_kind) in [
            ("requested_url", "requested_navigation"),
            ("final_url", "observed_navigation"),
        ] {
            if let Some(url) = nonempty_string_field(page, key) {
                for target in graph.targets_for(url)? {
                    graph.add_edge(&page_id, &target, edge_kind, json!({"url":url}))?;
                }
            }
        }
    }
    Ok(())
}

pub(super) fn seed_captured_reference_edges(
    graph: &mut GraphBuilder,
    manifest: &CaptureManifest,
    budget: &WorkBudget,
) -> Result<()> {
    // HAR-extracted HTML/script/source-map references and redirects.
    for resource in &manifest.resources {
        budget.checkpoint()?;
        let resource_id = required_u64(resource, "id", "manifest resource")?;
        let src = format!("resource:{resource_id}");
        for reference in array_field(resource, "references") {
            let Some(url) = nonempty_string_field(reference, "resolved_url") else {
                continue;
            };
            let kind = nonempty_string_field(reference, "kind").unwrap_or("reference");
            for dst in graph.targets_for(url)? {
                graph.add_edge(
                    &src,
                    &dst,
                    kind,
                    json!({"raw":field(reference,"raw"), "resolved_url":url}),
                )?;
            }
        }

        let location = array_field(resource, "response_headers")
            .iter()
            .find(|header| {
                string_field(header, "name")
                    .is_some_and(|name| name.eq_ignore_ascii_case("location"))
            })
            .and_then(|header| nonempty_string_field(header, "value"));
        if let (Some(location), Some(base)) = (location, nonempty_string_field(resource, "url")) {
            let resolved = resolve_url(base, location);
            for dst in graph.targets_for(&resolved)? {
                graph.add_edge(
                    &src,
                    &dst,
                    "redirect",
                    json!({"raw":location, "resolved_url":resolved}),
                )?;
            }
        }
    }
    Ok(())
}

pub(super) fn seed_captured_inline_scripts(
    graph: &mut GraphBuilder,
    manifest: &CaptureManifest,
    budget: &WorkBudget,
) -> Result<(InlineSourceIndex, BTreeMap<String, Vec<String>>)> {
    // Inline scripts are generated source nodes owned by their HTML resource.
    let mut inline_nodes = InlineSourceIndex::default();
    let mut inline_nodes_by_sha = BTreeMap::<String, Vec<String>>::new();
    for (index, item) in manifest.inline_scripts.iter().enumerate() {
        budget.checkpoint()?;
        let Some(output_path) = nonempty_string_field(item, "output_path") else {
            continue;
        };
        let parent = required_u64(
            item,
            "parent_resource_id",
            &format!("manifest.inline_scripts[{index}]"),
        )?;
        let ordinal = required_u64(
            item,
            "ordinal",
            &format!("manifest.inline_scripts[{index}]"),
        )?;
        let node_id = format!("inline:{parent}:{ordinal}");
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"inline_script",
                "parent_resource_id":parent,
                "ordinal":ordinal,
                "script_type":field(item,"script_type"),
                "source_path":output_path,
                "bytes":field(item,"body_bytes"),
                "sha256":field(item,"sha256"),
            }),
        )?;
        graph.add_edge(
            &format!("resource:{parent}"),
            &node_id,
            "inline_script",
            json!({"ordinal":ordinal}),
        )?;
        inline_nodes.insert(output_path, parent, ordinal, node_id.clone())?;
        if let Some(sha) = nonempty_string_field(item, "sha256") {
            inline_nodes_by_sha
                .entry(sha.to_string())
                .or_default()
                .push(node_id);
        }
    }
    Ok((inline_nodes, inline_nodes_by_sha))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capture_project::CaptureSource;
    use serde_json::Map;

    fn budget() -> WorkBudget {
        WorkBudget::new(
            "capture-identity-test",
            work_budget::BudgetLimits::unlimited(),
        )
    }

    fn manifest(
        resources: Vec<Value>,
        inline_scripts: Vec<Value>,
        pages: Vec<Value>,
    ) -> CaptureManifest {
        CaptureManifest {
            schema: "capture-project/v1".into(),
            source: CaptureSource {
                kind: "har".into(),
                input: "capture-identity-test".into(),
                salvaged: false,
                extra: Map::new(),
            },
            pages,
            resources,
            inline_scripts,
            counts: BTreeMap::new(),
            extra: Map::new(),
        }
    }

    #[test]
    fn identical_response_url_and_digest_retain_every_captured_instance() -> Result<()> {
        let url = "https://example.test/asset.js";
        let manifest = manifest(
            vec![
                json!({"id":7,"url":url,"sha256":"same-bytes","kind":"javascript",
                    "references":[{"kind":"script_src","raw":"asset.js","resolved_url":url}]}),
                json!({"id":19,"url":url,"sha256":"same-bytes","kind":"javascript"}),
            ],
            vec![
                json!({"parent_resource_id":7,"ordinal":1,
                    "output_path":"resources/shared-inline.js","sha256":"same-inline"}),
                json!({"parent_resource_id":19,"ordinal":1,
                    "output_path":"resources/shared-inline.js","sha256":"same-inline"}),
            ],
            vec![json!({"kind":"recorder_navigation","requested_url":url,"final_url":url})],
        );
        let source_index = json!({"units":[
            {"resource_id":7,"source_path":"src/a.js"},
            {"resource_id":7,"source_path":"src/a-readable.js"},
            {"resource_id":19,"source_path":"src/b.js"}
        ]});
        let mut graph = GraphBuilder::default();
        let captured = seed_capture_evidence(&mut graph, &manifest, &source_index, &budget())?;
        assert_eq!(
            captured.resource_nodes_by_sha["same-bytes"],
            ["resource:7", "resource:19"]
        );
        assert_eq!(graph.url_to_resources[url], ["resource:7", "resource:19"]);
        assert_eq!(
            graph.nodes["resource:7"]["source_paths"],
            json!(["src/a.js", "src/a-readable.js"])
        );
        assert_eq!(
            graph.nodes["resource:19"]["source_paths"],
            json!(["src/b.js"])
        );
        assert_eq!(
            captured.inline_nodes_by_sha["same-inline"],
            ["inline:7:1", "inline:19:1"]
        );
        assert_eq!(
            captured
                .inline_nodes
                .exact("resources/shared-inline.js", 7, 1),
            Some("inline:7:1".into())
        );
        assert_eq!(
            captured
                .inline_nodes
                .exact("resources/shared-inline.js", 19, 1),
            Some("inline:19:1".into())
        );
        assert!(
            captured
                .inline_nodes
                .for_record(&json!({"raw_path":"resources/shared-inline.js"}))
                .is_none(),
            "path alone cannot prove one inline source"
        );
        for kind in ["requested_navigation", "observed_navigation", "script_src"] {
            let edges = graph
                .edges
                .iter()
                .filter(|edge| edge["kind"] == kind)
                .collect::<Vec<_>>();
            assert_eq!(edges.len(), 2, "{kind} must retain each captured instance");
            assert!(edges.iter().any(|edge| edge["to"] == "resource:7"));
            assert!(edges.iter().any(|edge| edge["to"] == "resource:19"));
        }
        Ok(())
    }

    #[test]
    fn duplicate_captured_resource_ids_are_rejected_before_merging_evidence() {
        let manifest = manifest(
            vec![
                json!({"id":4,"url":"https://example.test/first.js","sha256":"a"}),
                json!({"id":4,"url":"https://example.test/second.js","sha256":"b"}),
            ],
            vec![],
            vec![],
        );
        let mut graph = GraphBuilder::default();
        let result =
            seed_captured_resources(&mut graph, &manifest, &json!({"units":[]}), &budget());
        assert!(
            result.as_ref().is_err_and(|error| error
                .to_string()
                .contains("duplicate captured resource id 4")),
            "expected duplicate resource error: {result:?}"
        );
        assert_eq!(
            graph.nodes["resource:4"]["url"],
            "https://example.test/first.js"
        );
        assert!(!graph
            .url_to_resources
            .contains_key("https://example.test/second.js"));
    }

    #[test]
    fn duplicate_inline_document_ordinals_are_rejected_even_when_paths_differ() {
        let manifest = manifest(
            vec![],
            vec![
                json!({"parent_resource_id":4,"ordinal":2,
                "output_path":"resources/inline-a.js","sha256":"a"}),
                json!({"parent_resource_id":4,"ordinal":2,
                "output_path":"resources/inline-b.js","sha256":"b"}),
            ],
            vec![],
        );
        let mut graph = GraphBuilder::default();
        let result = seed_captured_inline_scripts(&mut graph, &manifest, &budget());
        assert!(
            result.as_ref().is_err_and(|error| error
                .to_string()
                .contains("duplicate inline script site (4, 2)")),
            "expected duplicate inline site error: {result:?}"
        );
    }

    #[test]
    fn repeated_path_with_distinct_inline_sites_is_not_a_unique_owner() -> Result<()> {
        let mut index = InlineSourceIndex::default();
        index.insert("resources/shared.js", 3, 1, "inline:3:1".into())?;
        index.insert("resources/shared.js", 3, 2, "inline:3:2".into())?;
        assert!(index
            .for_record(&json!({"raw_path":"resources/shared.js"}))
            .is_none());
        assert_eq!(
            index.for_record(&json!({
                "raw_path":"resources/shared.js","resource_id":3,"ordinal":2
            })),
            Some("inline:3:2".into())
        );
        let error = index.insert("resources/other.js", 3, 2, "inline:3:2".into());
        assert!(error.as_ref().is_err_and(|error| error
            .to_string()
            .contains("duplicate inline script site (3, 2)")));
        assert!(index
            .for_record(&json!({"raw_path":"resources/other.js"}))
            .is_none());
        Ok(())
    }

    #[test]
    fn redirect_location_resolution_preserves_all_matching_response_instances() -> Result<()> {
        let manifest = manifest(
            vec![
                json!({
                    "id":1,"url":"https://example.test/old/path.js",
                    "response_headers":[{"name":"lOcAtIoN","value":"../asset.js"}]
                }),
                json!({"id":2,"url":"https://example.test/asset.js"}),
                json!({"id":5,"url":"https://example.test/asset.js"}),
            ],
            vec![],
            vec![],
        );
        let mut graph = GraphBuilder::default();
        let _ = seed_capture_evidence(&mut graph, &manifest, &json!({"units":[]}), &budget())?;
        let redirects = graph
            .edges
            .iter()
            .filter(|edge| edge["kind"] == "redirect")
            .collect::<Vec<_>>();
        assert_eq!(redirects.len(), 2);
        assert!(redirects.iter().any(|edge| edge["to"] == "resource:2"));
        assert!(redirects.iter().any(|edge| edge["to"] == "resource:5"));
        assert!(redirects.iter().all(|edge| edge["from"] == "resource:1"
            && edge["resolved_url"] == "https://example.test/asset.js"));
        Ok(())
    }
}
