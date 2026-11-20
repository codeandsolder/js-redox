mod generated_evidence;
mod reference_evidence;
mod static_evidence;
mod wasm_evidence;

use crate::{
    analysis_artifacts::{
        load_artifact, write_artifact, API_SURFACE, BUNDLES, DEOBFUSCATION, IMPORT_MAPS,
        JSVM_INDEX, JS_REFERENCES, RUNTIME_SCRIPTS, SELECTIVE_TRACE, SOURCEMAPS, SOURCE_GRAPH,
        SOURCE_INDEX, WASM_INDEX, WASM_RESOURCE_PROVENANCE,
    },
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    capture_project::{load_manifest, CaptureManifest},
    sha256_hex,
};
use anyhow::{Context, Result};
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    path::Path,
};
use url::Url;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceGraphSummary {
    pub nodes: usize,
    pub edges: usize,
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

fn resolve_url(base: &str, reference: &str) -> String {
    Url::parse(base)
        .and_then(|url| url.join(reference))
        .map_or_else(|_| reference.to_string(), |url| url.to_string())
}

#[derive(Default)]
struct GraphBuilder {
    nodes: BTreeMap<String, Value>,
    edges: Vec<Value>,
    edge_seen: HashSet<String>,
    url_to_resources: BTreeMap<String, Vec<String>>,
    external_nodes: BTreeMap<String, String>,
}

impl GraphBuilder {
    fn add_node(&mut self, id: impl Into<String>, fields: Value) -> Result<String> {
        let id = id.into();
        let Value::Object(fields) = fields else {
            anyhow::bail!("graph node fields must be a JSON object");
        };
        anyhow::ensure!(
            !fields.contains_key("id"),
            "graph node fields must not override the node id"
        );
        if let Some(existing) = self.nodes.get_mut(&id) {
            let existing = existing
                .as_object_mut()
                .context("stored graph node must be an object")?;
            for (key, value) in fields {
                if !value.is_null() && !existing.contains_key(&key) {
                    existing.insert(key, value);
                }
            }
        } else {
            let mut node = fields;
            node.insert("id".into(), Value::String(id.clone()));
            self.nodes.insert(id.clone(), Value::Object(node));
        }
        Ok(id)
    }

    fn add_edge(&mut self, from: &str, to: &str, kind: &str, fields: Value) -> Result<()> {
        let Value::Object(fields) = fields else {
            anyhow::bail!("graph edge fields must be a JSON object");
        };
        anyhow::ensure!(
            !["from", "to", "kind"]
                .iter()
                .any(|key| fields.contains_key(*key)),
            "graph edge fields must not override the edge endpoints or kind"
        );
        let frozen = format!("{from}\0{to}\0{kind}\0{}", serde_json::to_string(&fields)?);
        if !self.edge_seen.insert(frozen) {
            return Ok(());
        }
        let mut edge = fields;
        edge.insert("from".into(), Value::String(from.to_string()));
        edge.insert("to".into(), Value::String(to.to_string()));
        edge.insert("kind".into(), Value::String(kind.to_string()));
        self.edges.push(Value::Object(edge));
        Ok(())
    }

    fn register_resource_url(&mut self, url: &str, node_id: &str) {
        self.url_to_resources
            .entry(url.to_string())
            .or_default()
            .push(node_id.to_string());
    }

    fn targets_for(&mut self, url: &str) -> Result<Vec<String>> {
        if let Some(captured) = self.url_to_resources.get(url) {
            return Ok(captured.clone());
        }
        if let Some(existing) = self.external_nodes.get(url) {
            return Ok(vec![existing.clone()]);
        }
        let node_id = digest_id("external:", url);
        self.add_node(
            node_id.clone(),
            json!({"type":"external_url", "url":url, "captured":false}),
        )?;
        self.external_nodes.insert(url.to_string(), node_id.clone());
        Ok(vec![node_id])
    }
}

fn optional_artifact(
    project: &Path,
    spec: crate::analysis_artifacts::ArtifactSpec,
    fallback: Value,
) -> Result<Value> {
    Ok(load_artifact(project, spec, true)?.unwrap_or(fallback))
}

/// Relate a runtime script to captured HTTP responses without upgrading URL
/// coincidence or parser observation into proof of response execution.
fn add_runtime_network_source_edges(
    graph: &mut GraphBuilder,
    runtime: &Value,
    runtime_node: &str,
    resource_nodes_by_sha: &BTreeMap<String, Vec<String>>,
) -> Result<()> {
    let Some(digest) = nonempty_string_field(runtime, "sha256") else {
        return Ok(());
    };
    let urls = array_field(runtime, "urls")
        .iter()
        .filter_map(Value::as_str)
        .collect::<BTreeSet<_>>();
    let hash_matches = resource_nodes_by_sha
        .get(digest)
        .map_or_default(Vec::as_slice);
    let exact = hash_matches
        .iter()
        .filter(|node| {
            graph.nodes.get(*node).is_some_and(|resource| {
                nonempty_string_field(resource, "kind") == Some("javascript")
                    && nonempty_string_field(resource, "url").is_some_and(|url| urls.contains(url))
            })
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    let (parents, basis) = if !exact.is_empty() {
        (exact, "sha256_and_url")
    } else if urls.is_empty() && !hash_matches.is_empty() {
        (
            hash_matches
                .iter()
                .filter(|node| {
                    graph.nodes.get(*node).is_some_and(|resource| {
                        nonempty_string_field(resource, "kind") == Some("javascript")
                    })
                })
                .cloned()
                .collect::<BTreeSet<_>>(),
            "sha256_only",
        )
    } else {
        // A runtime URL cannot identify which captured HTTP response supplied
        // script bytes. Preserve all URL candidates without asserting execution.
        (
            urls.iter()
                .flat_map(|url| graph.url_to_resources.get(*url).into_iter().flatten())
                .filter(|node| {
                    graph.nodes.get(*node).is_some_and(|resource| {
                        nonempty_string_field(resource, "kind") == Some("javascript")
                    })
                })
                .cloned()
                .collect::<BTreeSet<_>>(),
            "url_only",
        )
    };
    let uniquely_verified = basis == "sha256_and_url" && parents.len() == 1;
    for parent in &parents {
        let parent_url = graph
            .nodes
            .get(parent)
            .and_then(|resource| nonempty_string_field(resource, "url"));
        let execution_observed = parent_url.is_some_and(|url| {
            array_field(runtime, "script_instances")
                .iter()
                .any(|instance| {
                    nonempty_string_field(instance, "script_url") == Some(url)
                        && nonempty_string_field(&instance["execution"], "status")
                            == Some("positive")
                })
        });
        let kind = if uniquely_verified && execution_observed {
            "runtime_execution"
        } else if uniquely_verified {
            "runtime_source_match"
        } else {
            "runtime_source_candidate"
        };
        graph.add_edge(
            parent,
            runtime_node,
            kind,
            json!({
                "identity_basis":basis,
                "candidate_count":parents.len(),
                "exact_response_identity":uniquely_verified,
                "runtime_execution_observed":execution_observed,
            }),
        )?;
    }
    Ok(())
}

/// An inspector function definition is exact only for its session, script ID
/// and source digest. Definition identity is not executed-call proof.
fn add_observed_callable_definition(
    graph: &mut GraphBuilder,
    runtime_nodes: &BTreeMap<(String, String), String>,
    invocation_id: &str,
    session: &str,
    value: &Value,
    observed_as: &str,
    label: &str,
) -> Result<()> {
    let Some(definition) = value.get("functionDefinition") else {
        return Ok(());
    };
    if nonempty_string_field(definition, "source_identity") != Some("exact") {
        return Ok(());
    }
    let Some(script_id) = nonempty_string_field(definition, "scriptId") else {
        return Ok(());
    };
    let Some(sha) = nonempty_string_field(definition, "sourceSha256") else {
        return Ok(());
    };
    let (Some(line), Some(column)) = (
        u64_field(definition, "lineNumber"),
        u64_field(definition, "columnNumber"),
    ) else {
        return Ok(());
    };
    let expected = format!("runtime:{}", &sha[..sha.len().min(20)]);
    if runtime_nodes.get(&(session.to_owned(), script_id.to_owned())) != Some(&expected) {
        return Ok(());
    }
    graph.add_edge(
        &expected,
        invocation_id,
        "observed_callable_definition",
        json!({
            "observed_as": observed_as,
            "observed_label": label,
            "cdp_session":session,
            "script_id":script_id,
            "source_sha256":sha,
            "line_number":line,
            "column_number":column,
            "identity_basis":"inspector_internal_function_location_and_exact_runtime_source",
            "concrete_observation_only":true,
            "not_call_proof":true
        }),
    )?;
    Ok(())
}

#[derive(Default)]
struct InlineSourceIndex {
    by_identity: BTreeMap<(String, u64, u64), String>,
    by_unique_raw: BTreeMap<String, Option<String>>,
}

impl InlineSourceIndex {
    fn insert(&mut self, raw: &str, parent: u64, ordinal: u64, node: String) -> Result<()> {
        anyhow::ensure!(
            self.by_identity
                .insert((raw.to_owned(), parent, ordinal), node.clone())
                .is_none(),
            "duplicate inline script identity {raw} ({parent}, {ordinal})"
        );
        self.by_unique_raw
            .entry(raw.to_owned())
            .and_modify(|existing| *existing = None)
            .or_insert(Some(node));
        Ok(())
    }

    fn exact(&self, raw: &str, parent: u64, ordinal: u64) -> Option<String> {
        self.by_identity
            .get(&(raw.to_owned(), parent, ordinal))
            .cloned()
    }

    fn for_record(&self, record: &Value) -> Option<String> {
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

fn captured_sourcemap_candidates(
    graph: &mut GraphBuilder,
    row: &Value,
    url_field: &str,
) -> Result<Vec<String>> {
    let ids = array_field(row, "map_resource_ids")
        .iter()
        .chain(array_field(row, "candidate_resource_ids"))
        .filter_map(Value::as_u64)
        .map(|id| format!("resource:{id}"))
        .collect::<BTreeSet<_>>();
    if !ids.is_empty() {
        return Ok(ids.into_iter().collect());
    }
    if let Some(url) = nonempty_string_field(row, url_field) {
        return graph.targets_for(url);
    }
    Ok(Vec::new())
}

fn add_sourcemap_reference(
    graph: &mut GraphBuilder,
    map: &Value,
    source: &str,
    resource_id: u64,
) -> Result<String> {
    if let Some(id) = u64_field(map, "map_resource_id") {
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
    graph.add_node(
        reference.clone(),
        json!({
            "type":"source_map_reference",
            "source_resource_id":resource_id,
            "map_url":field(map,"map_url"),
            "status":field(map,"status"),
            "map_origin":field(map,"map_origin"),
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
    let candidates = captured_sourcemap_candidates(graph, map, "map_url")?;
    for node in &candidates {
        graph.add_edge(
            &reference,
            node,
            "source_map_resource_candidate",
            json!({
                "candidate_count":candidates.len(),
                "identity_basis":if string_field(map,"map_origin") == Some("har_shared_bytes") {
                    "shared_verified_bytes"
                } else {
                    "url_only"
                },
            }),
        )?;
    }
    Ok(reference)
}

fn seed_captured_resources(
    graph: &mut GraphBuilder,
    manifest: &CaptureManifest,
    source_index: &Value,
    budget: &work_budget::WorkBudget,
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
    for (index, resource) in manifest.resources.iter().enumerate() {
        budget.checkpoint()?;
        let resource_id = required_u64(resource, "id", &format!("manifest.resources[{index}]"))?;
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

fn seed_navigation_roots(
    graph: &mut GraphBuilder,
    manifest: &CaptureManifest,
    budget: &work_budget::WorkBudget,
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

fn seed_captured_reference_edges(
    graph: &mut GraphBuilder,
    manifest: &CaptureManifest,
    budget: &work_budget::WorkBudget,
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

fn seed_captured_inline_scripts(
    graph: &mut GraphBuilder,
    manifest: &CaptureManifest,
    budget: &work_budget::WorkBudget,
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

fn finish_source_graph(
    project: &Path,
    manifest: &CaptureManifest,
    mut graph: GraphBuilder,
    budget: &work_budget::WorkBudget,
) -> Result<SourceGraphSummary> {
    let mut edge_counts = BTreeMap::<String, usize>::new();
    for edge in &graph.edges {
        budget.checkpoint()?;
        if let Some(kind) = string_field(edge, "kind") {
            *edge_counts.entry(kind.to_string()).or_default() += 1;
        }
    }
    let mut node_counts = BTreeMap::<String, usize>::new();
    for node in graph.nodes.values() {
        budget.checkpoint()?;
        if let Some(kind) = string_field(node, "type") {
            *node_counts.entry(kind.to_string()).or_default() += 1;
        }
    }

    graph.edges.sort_by(|left, right| {
        let left_key = (
            string_field(left, "from").unwrap_or(""),
            string_field(left, "kind").unwrap_or(""),
            string_field(left, "to").unwrap_or(""),
        );
        let right_key = (
            string_field(right, "from").unwrap_or(""),
            string_field(right, "kind").unwrap_or(""),
            string_field(right, "to").unwrap_or(""),
        );
        left_key.cmp(&right_key)
    });
    let nodes = graph.nodes.into_values().collect::<Vec<_>>();
    let external_urls = nodes
        .iter()
        .filter(|node| string_field(node, "type") == Some("external_url"))
        .count();
    let summary = SourceGraphSummary {
        nodes: nodes.len(),
        edges: graph.edges.len(),
        external_urls,
    };
    let document = json!({
        "schema":SOURCE_GRAPH.schema,
        "project":project.display().to_string(),
        "capture_salvaged":manifest.source.salvaged,
        "nodes":nodes,
        "edges":graph.edges,
        "summary":{
            "nodes":summary.nodes,
            "edges":summary.edges,
            "node_types":node_counts,
            "edge_kinds":edge_counts,
            "external_urls":summary.external_urls,
        },
    });
    budget.checkpoint()?;
    write_artifact(project, SOURCE_GRAPH, &document)?;
    Ok(summary)
}

/// Contextual evidence for runtime-source classification. Identity candidates
/// remain distinct: neither a matching URL nor matching bytes prove execution.
struct RuntimeClassificationContext<'a> {
    resource_nodes_by_sha: &'a BTreeMap<String, Vec<String>>,
    inline_nodes_by_sha: &'a BTreeMap<String, Vec<String>>,
    family_counts: &'a BTreeMap<String, Value>,
    gtm_family_counts: &'a BTreeMap<String, Value>,
}

fn runtime_family_counts(runtime: &Value, field_name: &str) -> BTreeMap<String, Value> {
    array_field(runtime, field_name)
        .iter()
        .filter_map(|row| {
            Some((
                nonempty_string_field(row, "shape")?.to_string(),
                row.get("source_count").cloned().unwrap_or_else(|| json!(0)),
            ))
        })
        .collect()
}

fn index_runtime_script_instances(
    source: &Value,
    runtime_node: &str,
    known: &mut BTreeMap<(String, String), String>,
    conflicts: &mut BTreeSet<(String, String)>,
) {
    for instance in array_field(source, "script_instances") {
        let Some(script_id) = instance.get("script_id") else {
            continue;
        };
        if script_id.is_null() {
            continue;
        }
        let key = (
            nonempty_string_field(instance, "cdp_session")
                .unwrap_or("main")
                .to_string(),
            script_id
                .as_str()
                .map_or_else(|| script_id.to_string(), ToString::to_string),
        );
        if conflicts.contains(&key) {
            continue;
        }
        if let Some(previous) = known.get(&key) {
            if previous != runtime_node {
                conflicts.insert(key.clone());
                known.remove(&key);
                continue;
            }
        }
        known.insert(key, runtime_node.to_owned());
    }
}

fn add_runtime_generated_code_edges(
    graph: &mut GraphBuilder,
    generated: &Value,
    runtime_node: &str,
) -> Result<()> {
    for origin in array_field(generated, "origins") {
        let chain = array_field(origin, "chain");
        let Some(parent) = chain.first() else {
            continue;
        };
        let edge_fields = json!({
            "cdp_session": nonempty_string_field(origin,"cdp_session").or_else(|| nonempty_string_field(parent,"cdp_session")).unwrap_or("main"),
            "child_script_id":field(origin,"child_script_id"),
            "parent_script_id":field(parent,"script_id"),
            "function_name":field(parent,"function_name"),
            "line_number":field(parent,"line_number"),
            "column_number":field(parent,"column_number"),
            "generation_depth":chain.len(),
        });
        if let Some(parent_sha) = nonempty_string_field(parent, "sha256") {
            graph.add_edge(
                &format!("runtime:{}", &parent_sha[..parent_sha.len().min(20)]),
                runtime_node,
                "runtime_generated_code",
                edge_fields,
            )?;
        } else if let Some(url) = nonempty_string_field(parent, "url") {
            let candidates = graph.targets_for(url)?;
            for parent_node in &candidates {
                let mut fields = edge_fields.clone();
                fields["identity_basis"] = json!("url_only");
                fields["candidate_count"] = json!(candidates.len());
                graph.add_edge(
                    parent_node,
                    runtime_node,
                    "runtime_generated_code_candidate",
                    fields,
                )?;
            }
        }
    }
    Ok(())
}

fn add_runtime_document_inline_edges(
    graph: &mut GraphBuilder,
    source: &Value,
    runtime_node: &str,
) -> Result<()> {
    for origin in array_field(source, "document_inline_origins") {
        let document_key = compact_key((
            field(origin, "cdp_session"),
            field(origin, "url"),
            field(origin, "frame_id"),
        ))?;
        let document_node = digest_id("runtime-document:", &document_key);
        graph.add_node(
            document_node.clone(),
            json!({
                "type":"runtime_document",
                "cdp_session":field(origin,"cdp_session"),
                "url":field(origin,"url"),
                "frame_id":field(origin,"frame_id"),
            }),
        )?;
        graph.add_edge(
            &document_node,
            runtime_node,
            "runtime_document_inline",
            json!({
                "script_id":field(origin,"script_id"),
                "start_line":field(origin,"start_line"),
                "start_column":field(origin,"start_column"),
                "end_line":field(origin,"end_line"),
                "end_column":field(origin,"end_column"),
            }),
        )?;
    }
    Ok(())
}

fn add_runtime_alpine_edges(
    graph: &mut GraphBuilder,
    alpine: &Value,
    runtime_node: &str,
    family_counts: &BTreeMap<String, Value>,
) -> Result<()> {
    if let Some(shape) = nonempty_string_field(alpine, "shape") {
        let family_node = digest_id("runtime-family:", shape);
        graph.add_node(
            family_node.clone(),
            json!({
                "type":"runtime_expression_family",
                "framework":"alpine",
                "shape":shape,
                "source_count":family_counts.get(shape).cloned().unwrap_or(Value::Null),
            }),
        )?;
        graph.add_edge(
            runtime_node,
            &family_node,
            "runtime_expression_family",
            json!({}),
        )?;
    }
    for dom_match in array_field(alpine, "dom_matches") {
        let snapshot_key = compact_key((field(dom_match, "source"), field(dom_match, "path")))?;
        let snapshot_node = digest_id("dom-snapshot:", &snapshot_key);
        graph.add_node(
                        snapshot_node.clone(),
                        json!({"type":"dom_snapshot", "source":field(dom_match,"source"), "path":field(dom_match,"path")}),
                    )?;
        let directive_key = compact_key((
            field(dom_match, "source"),
            field(dom_match, "path"),
            field(dom_match, "tag_ordinal"),
            field(dom_match, "tag"),
            field(dom_match, "attribute"),
        ))?;
        let directive_node = digest_id("dom-directive:", &directive_key);
        graph.add_node(
                        directive_node.clone(),
                        json!({
                            "type":"dom_directive", "source":field(dom_match,"source"), "path":field(dom_match,"path"),
                            "tag_ordinal":field(dom_match,"tag_ordinal"), "tag":field(dom_match,"tag"), "attribute":field(dom_match,"attribute")
                        }),
                    )?;
        graph.add_edge(&snapshot_node, &directive_node, "dom_directive", json!({}))?;
        graph.add_edge(
            &directive_node,
            runtime_node,
            "runtime_alpine_compile",
            json!({
                "mapping_kind":field(alpine,"dom_mapping_kind"),
                "expression":field(alpine,"expression"),
                "compiled_expression":field(alpine,"compiled_expression"),
                "shape":field(alpine,"shape"),
            }),
        )?;
    }
    Ok(())
}

fn add_runtime_classification_edges(
    graph: &mut GraphBuilder,
    source: &Value,
    digest: &str,
    runtime_node: &str,
    context: &RuntimeClassificationContext<'_>,
) -> Result<()> {
    let classification = string_field(source, "classification");
    let alpine = source.get("alpine").unwrap_or(&Value::Null);
    let gtm = source.get("gtm").unwrap_or(&Value::Null);
    match classification {
        Some("network_response" | "network_observed") => {
            add_runtime_network_source_edges(
                graph,
                source,
                runtime_node,
                context.resource_nodes_by_sha,
            )?;
        }
        Some("inline_script") => {
            if let Some(parents) = context.inline_nodes_by_sha.get(digest) {
                // Matching inline bytes do not identify the document or
                // script ordinal whose browser instance was parsed.
                for parent in parents {
                    graph.add_edge(
                        parent,
                        runtime_node,
                        "runtime_source_candidate",
                        json!({
                            "identity_basis":"sha256_only_inline_script",
                            "candidate_count":parents.len(),
                            "exact_response_identity":false,
                            "runtime_execution_observed":bool_field(source,"observed_executed"),
                        }),
                    )?;
                }
            }
        }
        Some("document_inline_script") => {
            add_runtime_document_inline_edges(graph, source, runtime_node)?;
        }
        Some("alpine_expression") => {
            add_runtime_alpine_edges(graph, alpine, runtime_node, context.family_counts)?;
        }
        Some("gtm_custom_javascript") => {
            if let Some(shape) = nonempty_string_field(gtm, "shape") {
                let family_node =
                    digest_id("runtime-family:", &format!("google_tag_manager\0{shape}"));
                graph.add_node(
                        family_node.clone(),
                        json!({
                            "type":"runtime_expression_family", "framework":"google_tag_manager", "shape":shape,
                            "source_count":context.gtm_family_counts.get(shape).cloned().unwrap_or(Value::Null)
                        }),
                    )?;
                graph.add_edge(
                    runtime_node,
                    &family_node,
                    "runtime_expression_family",
                    json!({}),
                )?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Identity and source-path indices shared with later observed and derived
/// graph stages. The source-path index is not evidence of script execution.
struct RuntimeSourceGraphIndex {
    instances: BTreeMap<(String, String), String>,
    general_paths: BTreeMap<String, String>,
}

/// Register runtime script observations without treating URL/SHA coincidence as execution proof.
/// Conflicting (CDP session, script ID) assertions cannot identify any runtime source.
fn seed_runtime_script_evidence(
    graph: &mut GraphBuilder,
    runtime: &Value,
    source_index: &Value,
    deobfuscation: &Value,
    resource_nodes_by_sha: &BTreeMap<String, Vec<String>>,
    inline_nodes_by_sha: &BTreeMap<String, Vec<String>>,
    budget: &work_budget::WorkBudget,
) -> Result<RuntimeSourceGraphIndex> {
    // Debugger-observed runtime scripts are provenance, not independent resources.
    let family_counts = runtime_family_counts(runtime, "alpine_families");
    let gtm_family_counts = runtime_family_counts(runtime, "gtm_families");
    let runtime_general_paths = array_field(source_index, "units")
        .iter()
        .filter(|unit| string_field(unit, "origin") == Some("runtime_script"))
        .filter_map(|unit| {
            Some((
                nonempty_string_field(unit, "input_sha256")?.to_owned(),
                nonempty_string_field(unit, "source_path")?.to_owned(),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let runtime_readable_paths = array_field(deobfuscation, "units")
        .iter()
        .filter_map(|unit| {
            let digest = nonempty_string_field(unit, "raw_path")?
                .strip_prefix("resources/runtime-scripts/")?
                .strip_suffix(".js")?;
            let readable = nonempty_string_field(unit, "readable_output_path")?;
            (readable == format!("src/_readable/runtime-scripts/{digest}.js"))
                .then(|| (digest.to_owned(), readable.to_owned()))
        })
        .collect::<BTreeMap<_, _>>();

    let mut runtime_node_by_instance = BTreeMap::<(String, String), String>::new();
    let mut runtime_instance_conflicts = BTreeSet::<(String, String)>::new();
    let context = RuntimeClassificationContext {
        resource_nodes_by_sha,
        inline_nodes_by_sha,
        family_counts: &family_counts,
        gtm_family_counts: &gtm_family_counts,
    };

    for source in array_field(runtime, "sources") {
        budget.checkpoint()?;
        let Some(digest) = nonempty_string_field(source, "sha256") else {
            continue;
        };
        let runtime_node = format!("runtime:{}", &digest[..digest.len().min(20)]);
        let classification = string_field(source, "classification");
        let generated = source.get("generated").unwrap_or(&Value::Null);
        graph.add_node(
            runtime_node.clone(),
            json!({
                "type":"runtime_script",
                "classification":field(source,"classification"),
                "sha256":digest,
                "bytes":field(source,"size"),
                "capture_path":field(source,"path"),
                "event_count":field(source,"event_count"),
                "script_ids":source.get("script_ids").cloned().unwrap_or_else(|| json!([])),
                "cdp_sessions":source.get("cdp_sessions").cloned().unwrap_or_else(|| json!([])),
                "execution_context_ids":source.get("execution_context_ids").cloned().unwrap_or_else(|| json!([])),
                "script_instances":source.get("script_instances").cloned().unwrap_or_else(|| json!([])),
                "observed_executed":field(source,"observed_executed"),
                "observed_source_path":field(source,"observed_source_path"),
                "general_source_path":runtime_general_paths.get(digest),
                "safe_readable_source_path":runtime_readable_paths.get(digest),
                "urls":source.get("urls").cloned().unwrap_or_else(|| json!([])),
                "instrumentation_kind":field(source,"instrumentation_kind"),
                "generated_root_sha256s":generated.get("root_sha256s").cloned().unwrap_or_else(|| json!([])),
                "generated_root_urls":generated.get("root_urls").cloned().unwrap_or_else(|| json!([])),
                "generation_max_depth":field(generated,"max_depth"),
                "application_source":classification != Some("capture_instrumentation"),
            }),
        )?;

        index_runtime_script_instances(
            source,
            &runtime_node,
            &mut runtime_node_by_instance,
            &mut runtime_instance_conflicts,
        );
        add_runtime_generated_code_edges(graph, generated, &runtime_node)?;
        add_runtime_classification_edges(graph, source, digest, &runtime_node, &context)?;
    }
    Ok(RuntimeSourceGraphIndex {
        instances: runtime_node_by_instance,
        general_paths: runtime_general_paths,
    })
}

/// A debugger frame is exact only when its session/script ID identifies one
/// runtime source and its captured SHA agrees with that source.
fn exact_runtime_frame_identity<'a>(
    frame: &'a Value,
    session: &str,
    instances: &BTreeMap<(String, String), String>,
) -> Option<(String, &'a str, &'a str)> {
    if nonempty_string_field(frame, "source_identity") != Some("exact") {
        return None;
    }
    let script_id = frame.get("location")?.get("scriptId")?.as_str()?;
    let sha = nonempty_string_field(frame, "sourceSha256")?;
    let expected = format!("runtime:{}", &sha[..sha.len().min(20)]);
    (instances.get(&(session.to_owned(), script_id.to_owned())) == Some(&expected))
        .then_some((expected, script_id, sha))
}

fn add_observed_pause_frames(
    graph: &mut GraphBuilder,
    hit: &Value,
    session: &str,
    node_id: &str,
    runtime_node_by_instance: &BTreeMap<(String, String), String>,
) -> Result<()> {
    for (depth, frame) in array_field(hit, "frames").iter().enumerate() {
        let Some((expected, script_id, sha)) =
            exact_runtime_frame_identity(frame, session, runtime_node_by_instance)
        else {
            continue;
        };
        graph.add_edge(
            &expected,
            node_id,
            "observed_paused_call_frame",
            json!({
                "stack_depth":depth,
                "cdp_session":session,
                "script_id":script_id,
                "source_sha256":sha,
                "identity_basis":"exact_session_script_hash",
                "concrete_observation_only":true,
            }),
        )?;
    }
    Ok(())
}

fn add_observed_steps(
    graph: &mut GraphBuilder,
    hit: &Value,
    ordinal: usize,
    session: &str,
    node_id: &str,
    runtime_node_by_instance: &BTreeMap<(String, String), String>,
    budget: &work_budget::WorkBudget,
) -> Result<()> {
    for (step_index, step) in array_field(hit, "steps").iter().enumerate() {
        budget.checkpoint()?;
        let step_id = format!("observed-step:{ordinal}:{step_index}");
        let top = array_field(step, "frames").first();
        graph.add_node(
            step_id.clone(),
            json!({
                "type":"observed_step",
                "step_index":step_index,
                "point_id":field(hit,"pointId"),
                "cdp_session":session,
                "reason":field(step,"reason"),
                "hit_breakpoints":field(step,"hitBreakpoints"),
                "top_frame":top,
                "frames":field(step,"frames"),
                "scopes":field(step,"scopes"),
                "expressions":field(step,"expressions"),
                "concrete_observation_only":true,
                "complete_execution_path":false,
            }),
        )?;
        graph.add_edge(
            node_id,
            &step_id,
            "observed_next_step",
            json!({
                "step_index":step_index,
                "step_mode":field(hit,"pathWitnessMode"),
                "concrete_observation_only":true,
            }),
        )?;
        let Some(top) = top else { continue };
        let Some((expected, script_id, sha)) =
            exact_runtime_frame_identity(top, session, runtime_node_by_instance)
        else {
            continue;
        };
        graph.add_edge(
                &expected, &step_id, "observed_executed_location",
                json!({
                    "cdp_session":session,
                    "script_id":script_id,
                    "source_sha256":sha,
                    "line_number":top.get("location").and_then(|location| location.get("lineNumber")).cloned(),
                    "column_number":top.get("location").and_then(|location| location.get("columnNumber")).cloned(),
                    "step_index":step_index,
                    "identity_basis":"exact_session_script_hash",
                    "concrete_observation_only":true,
                }),
            )?;
    }
    Ok(())
}

fn add_observed_guard_witnesses(
    graph: &mut GraphBuilder,
    hit: &Value,
    ordinal: usize,
    budget: &work_budget::WorkBudget,
) -> Result<()> {
    for (guard_index, guard) in array_field(hit, "observed_guard_witnesses")
        .iter()
        .enumerate()
    {
        budget.checkpoint()?;
        let Some(step_index) = guard
            .get("step_index")
            .and_then(Value::as_u64)
            .and_then(|index| usize::try_from(index).ok())
        else {
            continue;
        };
        if step_index >= array_field(hit, "steps").len() {
            continue;
        }
        let guard_id = format!("observed-guard:{ordinal}:{guard_index}");
        graph.add_node(
            guard_id.clone(),
            json!({
                "type":"observed_guard",
                "witness":guard,
                "concrete_observation_only":true,
                "complete_execution_path":false,
            }),
        )?;
        graph.add_edge(
            &format!("observed-step:{ordinal}:{step_index}"),
            &guard_id,
            "observed_ast_guard_value",
            json!({"exact_original_ast":true,"concrete_observation_only":true}),
        )?;
        if let Some(selected_arm) = nonempty_string_field(guard, "next_pause_in_selected_arm") {
            if step_index + 1 < array_field(hit, "steps").len() {
                graph.add_edge(
                    &guard_id,
                    &format!("observed-step:{ordinal}:{}", step_index + 1),
                    "observed_next_pause_in_selected_arm",
                    json!({"arm":selected_arm,"concrete_observation_only":true}),
                )?;
            }
        }
    }
    Ok(())
}

fn add_observed_callable_witnesses(
    graph: &mut GraphBuilder,
    hit: &Value,
    session: &str,
    node_id: &str,
    runtime_node_by_instance: &BTreeMap<(String, String), String>,
    budget: &work_budget::WorkBudget,
) -> Result<()> {
    for scope in array_field(hit, "scopes") {
        budget.checkpoint()?;
        let scope_type = nonempty_string_field(scope, "type").unwrap_or("unknown");
        for variable in array_field(scope, "variables") {
            budget.checkpoint()?;
            let label = nonempty_string_field(variable, "name").unwrap_or("");
            if let Some(value) = variable.get("value") {
                add_observed_callable_definition(
                    graph,
                    runtime_node_by_instance,
                    node_id,
                    session,
                    value,
                    scope_type,
                    label,
                )?;
            }
        }
    }
    for expression in array_field(hit, "expressions") {
        budget.checkpoint()?;
        if nonempty_string_field(expression, "status") != Some("observed") {
            continue;
        }
        if let Some(value) = expression.get("value") {
            add_observed_callable_definition(
                graph,
                runtime_node_by_instance,
                node_id,
                session,
                value,
                "expression",
                nonempty_string_field(expression, "expression").unwrap_or(""),
            )?;
        }
    }
    Ok(())
}

/// Link debugger pause, next-step, AST-guard and callable-definition witnesses
/// only to exact runtime instances when their CDP session, script ID and SHA agree.
fn seed_selective_trace_witnesses(
    graph: &mut GraphBuilder,
    selective_trace: &Value,
    runtime_node_by_instance: &BTreeMap<(String, String), String>,
    budget: &work_budget::WorkBudget,
) -> Result<()> {
    // Concrete debugger pauses are observed state witnesses, not static edges.
    // Only verified (CDP session, script ID, captured source SHA) triples
    // receive a provenance edge to the matching runtime script instance.
    for (ordinal, hit) in array_field(selective_trace, "hits").iter().enumerate() {
        budget.checkpoint()?;
        let node_id = format!("observed-invocation:{ordinal}");
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"observed_invocation",
                "point_id":field(hit,"pointId"),
                "readable_view_path":field(hit,"readable_view_path"),
                "path_view_path":field(hit,"path_view_path"),
                "path_witness_status":field(hit,"pathWitnessStatus"),
                "path_witness_mode":field(hit,"pathWitnessMode"),
                "cdp_session":field(hit,"cdpSession"),
                "at":field(hit,"at"),
                "reason":field(hit,"reason"),
                "frames":field(hit,"frames"),
                "scopes":field(hit,"scopes"),
                "expressions":field(hit,"expressions"),
                "concrete_observation_only":true,
            }),
        )?;
        let session = nonempty_string_field(hit, "cdpSession").unwrap_or("main");
        add_observed_pause_frames(graph, hit, session, &node_id, runtime_node_by_instance)?;
        // Each pause and step is an observation, not proof of a complete path.
        add_observed_steps(
            graph,
            hit,
            ordinal,
            session,
            &node_id,
            runtime_node_by_instance,
            budget,
        )?;
        add_observed_guard_witnesses(graph, hit, ordinal, budget)?;
        add_observed_callable_witnesses(
            graph,
            hit,
            session,
            &node_id,
            runtime_node_by_instance,
            budget,
        )?;
    }
    Ok(())
}

/// Resolve observed WASM request initiators in the existing evidence order:
/// exact same-session script instance, captured resource IDs, then URL candidates.
/// A URL fallback may create an explicitly external node, never execution proof.
fn runtime_wasm_initiator_nodes(
    graph: &mut GraphBuilder,
    observation: &Value,
    primary: &Value,
    runtime_instances: &BTreeMap<(String, String), String>,
) -> Result<Vec<String>> {
    let mut source_nodes = Vec::<String>::new();
    if let Some(script_id) = primary.get("script_id").filter(|value| !value.is_null()) {
        let key = (
            string_field(observation, "cdp_session")
                .unwrap_or("main")
                .to_string(),
            script_id
                .as_str()
                .map_or_else(|| script_id.to_string(), ToString::to_string),
        );
        if let Some(runtime_node) = runtime_instances.get(&key) {
            source_nodes.push(runtime_node.clone());
        }
    }
    if source_nodes.is_empty() {
        source_nodes.extend(
            array_field(observation, "initiator_resource_ids")
                .iter()
                .filter_map(Value::as_u64)
                .map(|resource_id| format!("resource:{resource_id}")),
        );
    }
    if source_nodes.is_empty() {
        if let Some(url) = nonempty_string_field(primary, "url") {
            source_nodes.extend(graph.targets_for(url)?);
        }
    }
    Ok(source_nodes)
}

/// A captured response occurrence is unique only when exactly one resource
/// ID is present. Multiple response IDs must remain separate candidate edges.
fn add_runtime_wasm_response_edges(
    graph: &mut GraphBuilder,
    observation: &Value,
    observation_id: &str,
) -> Result<()> {
    let resource_ids = array_field(observation, "wasm_resource_ids")
        .iter()
        .filter_map(Value::as_u64)
        .collect::<Vec<_>>();
    let exact_resource_occurrence = resource_ids.len() == 1;
    for resource_id in resource_ids {
        graph.add_edge(
            observation_id,
            &format!("resource:{resource_id}"),
            if exact_resource_occurrence {
                "runtime_observed_wasm_response"
            } else {
                "runtime_observed_wasm_response_candidate"
            },
            json!({
                "sha256":field(observation,"sha256"),
                "url":field(observation,"url"),
                "exact_response_identity":true,
                "exact_resource_occurrence":exact_resource_occurrence,
                "response_identity_basis":field(observation,"response_identity_basis"),
            }),
        )?;
    }
    Ok(())
}

/// Record WASM request observations separately from static WASM module origins.
/// CDP initiator evidence and the captured response candidates are independent.
fn seed_runtime_wasm_observations(
    graph: &mut GraphBuilder,
    wasm_resource_provenance: &Value,
    runtime_instances: &BTreeMap<(String, String), String>,
    budget: &work_budget::WorkBudget,
) -> Result<()> {
    // Runtime-observed WASM requests are capture evidence, not universal static control flow.
    for observation in array_field(wasm_resource_provenance, "observations") {
        budget.checkpoint()?;
        let key = compact_key((
            nonempty_string_field(observation, "cdp_session").unwrap_or("main"),
            field(observation, "request_id"),
            field(observation, "url"),
            field(observation, "sha256"),
        ))?;
        let observation_id = digest_id("runtime-wasm-request:", &key);
        let primary = observation.get("primary_initiator").unwrap_or(&Value::Null);
        graph.add_node(
            observation_id.clone(),
            json!({
                "type":"runtime_wasm_request",
                "cdp_session":field(observation,"cdp_session"),
                "request_id":field(observation,"request_id"),
                "url":field(observation,"url"),
                "sha256":field(observation,"sha256"),
                "bytes":field(observation,"byte_len"),
                "initiator_type":field(observation,"initiator_type"),
                "initiator_function":field(primary,"function_name"),
                "initiator_script_id":field(primary,"script_id"),
                "initiator_url":field(primary,"url"),
                "line_number":field(primary,"line_number"),
                "column_number":field(primary,"column_number"),
                "runtime_observed":true,
                "exact_response_identity":bool_field(observation,"exact_response_identity"),
                "response_identity_basis":field(observation,"response_identity_basis"),
                "matching_resource_count":array_field(observation,"wasm_resource_ids").len(),
            }),
        )?;

        let source_nodes =
            runtime_wasm_initiator_nodes(graph, observation, primary, runtime_instances)?;
        let mut seen_sources = BTreeSet::new();
        for source_node in source_nodes {
            if !seen_sources.insert(source_node.clone()) {
                continue;
            }
            graph.add_edge(
                &source_node,
                &observation_id,
                "runtime_wasm_request_initiator",
                json!({
                    "evidence":field(observation,"evidence"),
                    "function_name":field(primary,"function_name"),
                    "script_id":field(primary,"script_id"),
                    "line_number":field(primary,"line_number"),
                    "column_number":field(primary,"column_number"),
                    "runtime_observed":true,
                }),
            )?;
        }

        add_runtime_wasm_response_edges(graph, observation, &observation_id)?;
    }

    Ok(())
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
) -> Result<()> {
    let (source_field, node_prefix, node_type, edge_kind) = stage.fields();
    for recovered in array_field(source_map, source_field) {
        if string_field(recovered, "status") != Some("recovered") {
            continue;
        }
        let ordinal = u64_field(recovered, "ordinal").unwrap_or(0);
        let node_id = format!("{node_prefix}:{resource_id}:{ordinal}");
        graph.add_node(
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
) -> Result<()> {
    for (link_index, link) in array_field(composition, "links").iter().enumerate() {
        let chain_node = format!("sourcemap-chain:{resource_id}:{link_index}");
        graph.add_node(
            chain_node.clone(),
            json!({
                "type":"sourcemap_chain_link",
                "parent_resource_id":resource_id,
                "depth":field(link,"depth"),
                "source_ordinal":field(link,"source_ordinal"),
                "logical_source":field(link,"logical_source"),
                "raw_reference":field(link,"raw_reference"),
                "map_url":field(link,"map_url"),
                "map_resource_id":field(link,"map_resource_id"),
                "map_origin":field(link,"map_origin"),
                "status":field(link,"status"),
            }),
        )?;
        graph.add_edge(map_node, &chain_node, "source_map_chain", json!({}))?;
        if let Some(nested_map_resource_id) = u64_field(link, "map_resource_id") {
            graph.add_edge(
                &chain_node,
                &format!("resource:{nested_map_resource_id}"),
                "source_map_chain_resource",
                json!({}),
            )?;
        } else {
            let candidates = captured_sourcemap_candidates(graph, link, "map_url")?;
            for node in &candidates {
                graph.add_edge(&chain_node, node, "source_map_chain_resource_candidate", json!({
                        "candidate_count":candidates.len(),
                        "identity_basis": if string_field(link,"map_origin") == Some("har_shared_bytes") {
                            "shared_verified_bytes"
                        } else {
                            "url_only"
                        },
                    }))?;
            }
        }
        let code_candidates = array_field(link, "code_resource_ids")
            .iter()
            .chain(array_field(link, "candidate_code_resource_ids"))
            .filter_map(Value::as_u64)
            .collect::<BTreeSet<_>>();
        let exact_code = u64_field(link, "code_resource_id");
        for code_id in &code_candidates {
            let proven = exact_code == Some(*code_id) && code_candidates.len() == 1;
            graph.add_edge(
                    &chain_node,
                    &format!("resource:{code_id}"),
                    if proven { "source_map_chain_code" } else { "source_map_chain_code_candidate" },
                    json!({
                        "candidate_count":code_candidates.len(),
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
) -> Result<()> {
    let composition = source_map.get("composition").unwrap_or(&Value::Null);
    let composed_node = if let Some(composed_map_path) =
        nonempty_string_field(composition, "composed_map_path")
    {
        let node_id = format!("sourcemap-composed:{resource_id}");
        graph.add_node(
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

    add_sourcemap_chain_links(graph, composition, resource_id, map_node)?;
    let parent = composed_node.as_deref().unwrap_or(map_node);
    add_recovered_sourcemap_sources(
        graph,
        source_map,
        resource_id,
        parent,
        RecoveredMapStage::Composed,
    )?;
    Ok(())
}

/// Seed source-map references, original sources and composition evidence
/// without promoting candidate map/code resource identities to exact links.
fn seed_sourcemap_evidence(
    graph: &mut GraphBuilder,
    sourcemaps: &Value,
    budget: &work_budget::WorkBudget,
) -> Result<()> {
    for source_map in array_field(sourcemaps, "source_maps") {
        budget.checkpoint()?;
        let Some(resource_id) = u64_field(source_map, "resource_id") else {
            continue;
        };
        let src = format!("resource:{resource_id}");
        let map_node = add_sourcemap_reference(graph, source_map, &src, resource_id)?;

        add_recovered_sourcemap_sources(
            graph,
            source_map,
            resource_id,
            &map_node,
            RecoveredMapStage::Original,
        )?;
        add_sourcemap_composition(graph, source_map, resource_id, &map_node)?;
    }
    Ok(())
}

fn seed_bundle_payload_nodes(
    graph: &mut GraphBuilder,
    bundles: &Value,
    deob_nodes: &BTreeMap<u64, String>,
    budget: &work_budget::WorkBudget,
) -> Result<BTreeMap<u64, String>> {
    let mut bundle_nodes = BTreeMap::<u64, String>::new();
    for bundle in array_field(bundles, "bundles") {
        budget.checkpoint()?;
        let bundle_id = required_u64(bundle, "bundle_id", "bundle")?;
        let node_id = format!("bundle:{bundle_id}");
        bundle_nodes.insert(bundle_id, node_id.clone());
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
    bundle_module_nodes: BTreeMap<(u64, String), Vec<String>>,
    module_nodes_by_id: BTreeMap<String, Vec<String>>,
    module_rows: BTreeMap<String, &'a Value>,
}

fn seed_bundle_module_nodes<'a>(
    graph: &mut GraphBuilder,
    bundles: &'a Value,
    bundle_nodes: &BTreeMap<u64, String>,
    budget: &work_budget::WorkBudget,
) -> Result<BundleGraphIndex<'a>> {
    let bundle_rows_by_id = array_field(bundles, "bundles")
        .iter()
        .filter_map(|bundle| Some((u64_field(bundle, "bundle_id")?, bundle)))
        .collect::<BTreeMap<_, _>>();
    let mut bundle_module_nodes = BTreeMap::<(u64, String), Vec<String>>::new();
    let mut module_nodes_by_id = BTreeMap::<String, Vec<String>>::new();
    let mut module_rows = BTreeMap::<String, &Value>::new();
    for module in array_field(bundles, "modules") {
        budget.checkpoint()?;
        let bundle_id = required_u64(module, "bundle_id", "bundle module")?;
        let ordinal = u64_field(module, "module_ordinal").unwrap_or(0);
        let node_id = format!("bundle-module:{bundle_id}:{ordinal}");
        let module_id = module.get("module_id").map_or_else(String::new, |value| {
            value
                .as_str()
                .map_or_else(|| value.to_string(), ToString::to_string)
        });
        bundle_module_nodes
            .entry((bundle_id, module_id.clone()))
            .or_default()
            .push(node_id.clone());
        module_nodes_by_id
            .entry(module_id)
            .or_default()
            .push(node_id.clone());
        module_rows.insert(node_id.clone(), module);
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
    if string_field(candidate_bundle, "kind") != Some("webpack_module_table")
        || string_field(candidate_bundle, "parent_path")
            != string_field(source_module, "parent_path")
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
    source_start <= bundle_start && bundle_end <= source_end
}

fn seed_bundle_dependency_edges(
    graph: &mut GraphBuilder,
    index: &BundleGraphIndex<'_>,
    budget: &work_budget::WorkBudget,
) -> Result<()> {
    let bundle_module_nodes = &index.bundle_module_nodes;
    let module_nodes_by_id = &index.module_nodes_by_id;
    let module_rows = &index.module_rows;
    for (source_node, module) in module_rows {
        budget.checkpoint()?;
        let bundle_id = required_u64(module, "bundle_id", "bundle module")?;
        for dependency in array_field(module, "dependencies") {
            let dependency = dependency
                .as_str()
                .map_or_else(|| dependency.to_string(), ToString::to_string);
            let same_bundle = bundle_module_nodes
                .get(&(bundle_id, dependency.clone()))
                .cloned()
                .unwrap_or_default();
            let mut target = if same_bundle.len() == 1 {
                same_bundle.first().cloned()
            } else {
                None
            };
            let mut cross_bundle = false;
            let mut excluded_nested = Vec::<String>::new();
            let mut candidates = Vec::<String>::new();
            if target.is_none() {
                // Same-bundle duplicate IDs are ambiguous, not proof of the
                // factory represented by the final module row.
                if same_bundle.len() > 1 {
                    candidates = same_bundle;
                } else {
                    let all_candidates = module_nodes_by_id
                        .get(&dependency)
                        .cloned()
                        .unwrap_or_default();
                    for candidate in all_candidates {
                        if nested_private_bundle_candidate(&candidate, module, index) {
                            excluded_nested.push(candidate);
                        } else {
                            candidates.push(candidate);
                        }
                    }
                    if candidates.len() == 1 {
                        target = candidates.first().cloned();
                        cross_bundle = true;
                    }
                }
            }
            if let Some(target) = target {
                graph.add_edge(
                    source_node,
                    &target,
                    "bundle_module_dependency",
                    json!({
                        "module_id":dependency,
                        "cross_bundle":cross_bundle,
                        "excluded_nested_module_tables":excluded_nested.len(),
                    }),
                )?;
                continue;
            }
            let ref_id = digest_id("bundle-module-ref:", &format!("{bundle_id}:{dependency}"));
            graph.add_node(
                ref_id.clone(),
                json!({
                    "type":"bundle_module_reference",
                    "module_id":dependency,
                    "source_bundle_id":bundle_id,
                    "candidate_nodes":candidates.clone(),
                    "excluded_nested_module_table_nodes":excluded_nested.clone(),
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
        }
    }

    Ok(())
}

fn seed_bundle_evidence(
    graph: &mut GraphBuilder,
    bundles: &Value,
    deob_nodes: &BTreeMap<u64, String>,
    budget: &work_budget::WorkBudget,
) -> Result<()> {
    let bundle_nodes = seed_bundle_payload_nodes(graph, bundles, deob_nodes, budget)?;
    let index = seed_bundle_module_nodes(graph, bundles, &bundle_nodes, budget)?;
    seed_bundle_dependency_edges(graph, &index, budget)
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
        json!({"sources":[], "alpine_families":[], "gtm_families":[]}),
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
    let resource_nodes_by_sha =
        seed_captured_resources(&mut graph, &manifest, &source_index, &budget)?;
    seed_navigation_roots(&mut graph, &manifest, &budget)?;
    seed_captured_reference_edges(&mut graph, &manifest, &budget)?;
    let (inline_nodes, inline_nodes_by_sha) =
        seed_captured_inline_scripts(&mut graph, &manifest, &budget)?;

    let runtime_index = seed_runtime_script_evidence(
        &mut graph,
        &runtime,
        &source_index,
        &deobfuscation,
        &resource_nodes_by_sha,
        &inline_nodes_by_sha,
        &budget,
    )?;
    seed_selective_trace_witnesses(
        &mut graph,
        &selective_trace,
        &runtime_index.instances,
        &budget,
    )?;

    seed_runtime_wasm_observations(
        &mut graph,
        &wasm_resource_provenance,
        &runtime_index.instances,
        &budget,
    )?;

    let deob_nodes = static_evidence::seed_safe_deobfuscation_sources(
        &mut graph,
        &deobfuscation,
        &inline_nodes,
        &runtime_index,
        &budget,
    )?;
    static_evidence::seed_browser_api_callsites(
        &mut graph,
        &api_surface,
        &deob_nodes,
        &inline_nodes,
        &budget,
    )?;

    seed_bundle_evidence(&mut graph, &bundles, &deob_nodes, &budget)?;

    seed_sourcemap_evidence(&mut graph, &sourcemaps, &budget)?;

    generated_evidence::seed_generated_and_vm_evidence(&mut graph, &jsvm, &deob_nodes, &budget)?;

    reference_evidence::seed_import_map_definitions(
        &mut graph,
        &import_maps,
        &inline_nodes,
        &budget,
    )?;
    reference_evidence::seed_js_reference_edges(&mut graph, &jsrefs, &inline_nodes, &budget)?;

    wasm_evidence::seed_static_wasm_modules(&mut graph, &wasm, &budget)?;

    finish_source_graph(&project, &manifest, graph, &budget)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        analysis_artifacts::{load_artifact, write_artifact, JS_REFERENCES, SOURCE_GRAPH},
        capture_project::{write_manifest, CaptureManifest, CaptureSource, MANIFEST_NAME},
    };

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
            graph.url_to_resources["https://fixture.invalid/shared.js"],
            ["resource:3", "resource:9"]
        );
        assert_eq!(
            graph.nodes["resource:3"]["source_paths"],
            json!(["src/a.js"])
        );
        assert_eq!(
            graph.nodes["resource:9"]["source_paths"],
            json!(["src/b.js"])
        );
        assert_eq!(
            graph.nodes["resource:9"]["saved_page_reference_roles"],
            json!(["css", "javascript"])
        );
        for kind in ["observed_navigation", "script_src", "redirect"] {
            let matching = graph
                .edges
                .iter()
                .filter(|edge| {
                    edge["kind"] == kind
                        && matches!(edge["to"].as_str(), Some("resource:3" | "resource:9"))
                })
                .count();
            assert_eq!(matching, 2, "shared URL must retain both {kind} candidates");
        }
        assert_eq!(
            graph
                .edges
                .iter()
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
        let summary = finish_source_graph(destination.path(), &manifest, graph, &budget)?;
        assert_eq!(summary.external_urls, 1);
        let artifact = load_artifact(destination.path(), SOURCE_GRAPH, false)?
            .context("finalized graph artifact missing")?;
        assert_eq!(artifact["summary"]["edge_kinds"]["redirect"], 2);
        assert_eq!(artifact["summary"]["edge_kinds"]["script_src"], 2);
        assert_eq!(artifact["summary"]["edge_kinds"]["inline_script"], 2);
        assert_eq!(artifact["summary"]["node_types"]["external_url"], 1);
        Ok(())
    }

    fn runtime_wasm_observation_fixture() -> Value {
        json!({"observations": [
            {
                "cdp_session":"worker","request_id":"exact","url":"https://w.test/a.wasm",
                "sha256":"a","exact_response_identity":true,
                "primary_initiator":{"script_id":"17","url":"https://w.test/ambiguous.js"},
                "initiator_resource_ids":[1],
                "wasm_resource_ids":[20],"response_identity_basis":"cdp_body_sha256"
            },
            {
                "cdp_session":"other","request_id":"resource-fallback","url":"https://w.test/b.wasm",
                "sha256":"b","exact_response_identity":false,
                "primary_initiator":{"script_id":"17","url":"https://w.test/ambiguous.js"},
                "initiator_resource_ids":[1,1,2],"wasm_resource_ids":[30,31],
                "response_identity_basis":"ambiguous_response"
            },
            {
                "cdp_session":"other","request_id":"url-fallback","url":"https://w.test/c.wasm",
                "primary_initiator":{"url":"https://w.test/ambiguous.js"},
                "wasm_resource_ids":[]
            },
            {
                "cdp_session":"other","request_id":"external","url":"https://w.test/d.wasm",
                "primary_initiator":{"url":"https://w.test/unseen.js"},
                "wasm_resource_ids":[]
            }
        ]})
    }

    #[test]
    fn runtime_wasm_observations_preserve_evidence_priority_and_response_ambiguity() -> Result<()> {
        let budget = work_budget::WorkBudget::new(
            "wasm-request-graph-identity",
            work_budget::BudgetLimits::unlimited(),
        );
        let mut graph = GraphBuilder::default();
        let shared = "https://w.test/ambiguous.js";
        for id in ["resource:1", "resource:2"] {
            graph.add_node(id, json!({"type":"resource","url":shared}))?;
            graph.register_resource_url(shared, id);
        }
        let mut instances = BTreeMap::new();
        instances.insert(
            ("worker".to_string(), "17".to_string()),
            "runtime:worker".to_string(),
        );
        seed_runtime_wasm_observations(
            &mut graph,
            &runtime_wasm_observation_fixture(),
            &instances,
            &budget,
        )?;
        let observation = |request_id: &str| -> Result<&str> {
            graph
                .nodes
                .values()
                .find(|node| node["request_id"] == request_id)
                .and_then(|node| node["id"].as_str())
                .with_context(|| format!("missing request {request_id}"))
        };
        let sources = |request_id: &str| -> Result<BTreeSet<&str>> {
            let target = observation(request_id)?;
            Ok(graph
                .edges
                .iter()
                .filter(|edge| {
                    edge["kind"] == "runtime_wasm_request_initiator" && edge["to"] == target
                })
                .filter_map(|edge| edge["from"].as_str())
                .collect())
        };
        assert_eq!(sources("exact")?, BTreeSet::from(["runtime:worker"]));
        assert_eq!(
            sources("resource-fallback")?,
            BTreeSet::from(["resource:1", "resource:2"])
        );
        assert_eq!(
            sources("url-fallback")?,
            BTreeSet::from(["resource:1", "resource:2"])
        );
        let external = sources("external")?;
        assert_eq!(external.len(), 1);
        assert!(external.iter().all(|node| node.starts_with("external:")));
        assert_eq!(graph.external_nodes.len(), 1);

        let exact = observation("exact")?;
        let response = graph
            .edges
            .iter()
            .filter(|edge| edge["from"] == exact)
            .collect::<Vec<_>>();
        assert_eq!(response.len(), 1);
        assert_eq!(response[0]["to"], "resource:20");
        assert_eq!(response[0]["kind"], "runtime_observed_wasm_response");
        assert_eq!(response[0]["exact_resource_occurrence"], true);

        let ambiguous = observation("resource-fallback")?;
        let candidates = graph
            .edges
            .iter()
            .filter(|edge| edge["from"] == ambiguous)
            .collect::<Vec<_>>();
        assert_eq!(candidates.len(), 2);
        assert_eq!(
            candidates
                .iter()
                .map(|edge| edge["to"].as_str().unwrap_or_default())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["resource:30", "resource:31"])
        );
        assert!(candidates.iter().all(|edge| edge["kind"]
            == "runtime_observed_wasm_response_candidate"
            && edge["exact_resource_occurrence"] == false));
        assert_eq!(graph.nodes[ambiguous]["exact_response_identity"], false);
        assert!(graph.edges.iter().all(|edge| {
            edge["kind"] != "runtime_wasm_request_initiator"
                || edge["from"] != "runtime:worker"
                || edge["to"] == exact
        }));
        Ok(())
    }

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
        let ref_for = |id: &str| digest_id("bundle-module-ref:", &format!("1:{id}"));
        let private = ref_for("private");
        let ambiguous = ref_for("ambiguous");
        let missing = ref_for("missing");
        let duplicate = ref_for("dup");
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
            graph.add_node(&node, json!({"type":"resource"}))?;
            graph.register_resource_url("https://maps.test/child.map", &node);
        }
        seed_sourcemap_evidence(&mut graph, &ambiguous_sourcemap_graph_fixture(), &budget)?;
        let edges_from = |kind: &str, from: &str| {
            graph
                .edges
                .iter()
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
        assert!(!graph.nodes.contains_key("sourcemap-source:7:1"));
        assert_eq!(
            graph.nodes["sourcemap-composed:7"]["source_path"],
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
        assert!(!graph.nodes.contains_key("sourcemap-final:7:1"));

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
                .edges
                .iter()
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
        assert!(!graph.nodes.contains_key("sourcemap-reference:42"));
        assert!(!graph.nodes.contains_key("sourcemap-composed:42"));
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
        assert!(!graph.nodes.contains_key("sourcemap-composed:44"));
        assert_eq!(graph.external_nodes.len(), 1);
        assert_eq!(
            graph
                .edges
                .iter()
                .filter(|edge| edge["kind"] == "source_map_resource_candidate"
                    && edge["from"] == "sourcemap-reference:44")
                .count(),
            1
        );
        Ok(())
    }

    fn conflicting_runtime_instance_fixture() -> (String, Value, Value) {
        let first = "a".repeat(64);
        let second = "b".repeat(64);
        let runtime = json!({
            "sources":[
                {"sha256":first,"classification":"generated_runtime","script_instances":[
                    {"cdp_session":"worker","script_id":"7"}]},
                {"sha256":second,"classification":"generated_runtime","script_instances":[
                    {"cdp_session":"worker","script_id":"7"},
                    {"cdp_session":"other","script_id":"7"}]},
            ]
        });
        let exact_frame = |sha: &str| {
            json!({
                "source_identity":"exact","sourceSha256":sha,
                "location":{"scriptId":"7","lineNumber":1,"columnNumber":2}
            })
        };
        let callable = |sha: &str| {
            json!({"type":"local","variables":[{
                "name":"function","value":{"functionDefinition":{
                    "source_identity":"exact","scriptId":"7","sourceSha256":sha,
                    "lineNumber":1,"columnNumber":2
                }}
            }]})
        };
        let trace = json!({"hits":[
            {"cdpSession":"worker","frames":[exact_frame(&first)],
             "steps":[{"frames":[exact_frame(&first)]}],
             "scopes":[callable(&first)]},
            {"cdpSession":"other","frames":[exact_frame(&second)],
             "steps":[{"frames":[exact_frame(&second)]},{"frames":[]}],
             "observed_guard_witnesses":[{"step_index":0,
                 "next_pause_in_selected_arm":"then"}],
             "scopes":[callable(&second)]},
            {"cdpSession":"other",
             "frames":[{"source_identity":"inferred","sourceSha256":second,
                 "location":{"scriptId":"7"}}],
             "steps":[{"frames":[{"source_identity":"inferred","sourceSha256":second,
                 "location":{"scriptId":"7"}}]}]}
        ]});
        (second, runtime, trace)
    }

    #[test]
    fn runtime_script_collisions_cannot_turn_pauses_into_exact_execution_proof() -> Result<()> {
        let (second, runtime, trace) = conflicting_runtime_instance_fixture();
        let budget = work_budget::WorkBudget::new(
            "runtime-source-witness-identity",
            work_budget::BudgetLimits::unlimited(),
        );
        let mut graph = GraphBuilder::default();
        let runtime_index = seed_runtime_script_evidence(
            &mut graph,
            &runtime,
            &json!({"units":[]}),
            &json!({"units":[]}),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &budget,
        )?;
        let instances = &runtime_index.instances;
        assert!(!instances.contains_key(&("worker".into(), "7".into())));
        assert_eq!(
            instances.get(&("other".into(), "7".into())),
            Some(&format!("runtime:{}", &second[..20]))
        );
        seed_selective_trace_witnesses(&mut graph, &trace, instances, &budget)?;
        let identity_edges = graph
            .edges
            .iter()
            .filter(|edge| {
                matches!(
                    edge["kind"].as_str(),
                    Some(
                        "observed_paused_call_frame"
                            | "observed_executed_location"
                            | "observed_callable_definition"
                    )
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            identity_edges.len(),
            3,
            "only the unambiguous session may prove identity"
        );
        assert!(identity_edges.iter().all(|edge| {
            edge["from"] == format!("runtime:{}", &second[..20])
                && edge["cdp_session"] == "other"
                && edge["script_id"] == "7"
                && edge["source_sha256"] == second
        }));
        assert!(graph.nodes.contains_key("observed-invocation:0"));
        assert!(graph.nodes.contains_key("observed-step:0:0"));
        assert_eq!(
            graph.nodes["observed-step:0:0"]["complete_execution_path"],
            false
        );
        assert_eq!(
            graph.nodes["observed-step:1:1"]["complete_execution_path"],
            false
        );
        assert_eq!(
            graph.nodes["observed-guard:1:0"]["concrete_observation_only"],
            true
        );
        assert!(graph
            .edges
            .iter()
            .any(|edge| edge["kind"] == "observed_ast_guard_value"));
        assert!(graph.edges.iter().any(|edge| {
            edge["kind"] == "observed_next_pause_in_selected_arm"
                && edge["to"] == "observed-step:1:1"
        }));
        assert!(!graph
            .edges
            .iter()
            .any(|edge| edge["to"] == "observed-step:2:0"
                && edge["kind"] == "observed_executed_location"));
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
            graph.add_node(
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
            "script_instances":[{
                "script_url":"https://fixture.invalid/copy.js",
                "execution":{"status":"positive"}
            }]
        });
        add_runtime_network_source_edges(&mut graph, &runtime, "runtime:parsed", &hashes)?;
        let parsed = graph
            .edges
            .iter()
            .filter(|edge| edge["to"] == "runtime:parsed")
            .collect::<Vec<_>>();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0]["from"], "resource:1");
        assert_eq!(parsed[0]["kind"], "runtime_source_match");
        assert_eq!(parsed[0]["identity_basis"], "sha256_and_url");
        assert_eq!(parsed[0]["exact_response_identity"], true);
        assert_eq!(parsed[0]["runtime_execution_observed"], false);

        let mut confirmed = runtime;
        confirmed["script_instances"][0]["script_url"] = json!("https://fixture.invalid/app.js");
        add_runtime_network_source_edges(&mut graph, &confirmed, "runtime:executed", &hashes)?;
        let executed = graph
            .edges
            .iter()
            .filter(|edge| edge["to"] == "runtime:executed")
            .collect::<Vec<_>>();
        assert_eq!(executed.len(), 1);
        assert_eq!(executed[0]["from"], "resource:1");
        assert_eq!(executed[0]["kind"], "runtime_execution");
        assert_eq!(executed[0]["runtime_execution_observed"], true);
        Ok(())
    }

    #[test]
    fn runtime_url_and_hash_only_matches_remain_ambiguous_candidates() -> Result<()> {
        let (mut graph, hashes) = runtime_match_test_graph()?;
        let runtime = json!({
            "sha256":"missing","urls":["https://fixture.invalid/app.js"],
            "observed_executed":true,
            "script_instances":[{
                "script_url":"https://fixture.invalid/app.js",
                "execution":{"status":"positive"}
            }]
        });
        add_runtime_network_source_edges(&mut graph, &runtime, "runtime:url-only", &hashes)?;
        let url_edges = graph
            .edges
            .iter()
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
        add_runtime_network_source_edges(&mut graph, &sha_only, "runtime:sha-only", &hashes)?;
        let hash_edges = graph
            .edges
            .iter()
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

    #[test]
    fn graph_builder_moves_evidence_without_overwriting_identity_or_existing_fields() -> Result<()>
    {
        let mut graph = GraphBuilder::default();
        assert_eq!(
            graph.add_node(
                "source:a",
                json!({"type":"resource","metadata":{"items":[1,2]},"empty":null}),
            )?,
            "source:a"
        );
        graph.add_node(
            "source:a",
            json!({"type":"not-a-resource","metadata":{"items":[3]},"new_field":42,"empty":"not-empty"}),
        )?;
        let node = &graph.nodes["source:a"];
        assert_eq!(node["id"], "source:a");
        assert_eq!(node["type"], "resource");
        assert_eq!(node["metadata"]["items"], json!([1, 2]));
        assert_eq!(node["new_field"], 42);
        assert_eq!(node["empty"], Value::Null);

        assert!(graph.add_node("source:a", json!({"id":"spoofed"})).is_err());
        assert!(graph.add_node("source:b", json!([])).is_err());
        assert_eq!(graph.nodes.len(), 1);

        graph.add_edge(
            "source:a",
            "source:b",
            "reference",
            json!({"metadata":{"items":[1,2]}}),
        )?;
        graph.add_edge(
            "source:a",
            "source:b",
            "reference",
            json!({"metadata":{"items":[1,2]}}),
        )?;
        assert_eq!(graph.edges.len(), 1);
        let edge = &graph.edges[0];
        assert_eq!(edge["from"], "source:a");
        assert_eq!(edge["to"], "source:b");
        assert_eq!(edge["kind"], "reference");
        assert_eq!(edge["metadata"]["items"], json!([1, 2]));
        assert!(graph
            .add_edge(
                "source:a",
                "source:b",
                "reference",
                json!({"from":"spoofed"})
            )
            .is_err());
        assert!(graph
            .add_edge("source:a", "source:b", "reference", json!({"to":"spoofed"}))
            .is_err());
        assert!(graph
            .add_edge(
                "source:a",
                "source:b",
                "reference",
                json!({"kind":"spoofed"})
            )
            .is_err());
        assert!(graph
            .add_edge("source:a", "source:b", "reference", Value::Null)
            .is_err());
        assert_eq!(graph.edges.len(), 1);

        graph.add_edge(
            "source:a",
            "source:b",
            "reference",
            json!({"metadata":{"items":[3]}}),
        )?;
        assert_eq!(graph.edges.len(), 2);
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
}
