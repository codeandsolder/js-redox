use crate::{
    analysis_artifacts::{
        load_artifact, write_artifact, API_SURFACE, BUNDLES, DEOBFUSCATION, IMPORT_MAPS,
        JSVM_INDEX, JS_REFERENCES, RUNTIME_SCRIPTS, SOURCEMAPS, SOURCE_GRAPH, SOURCE_INDEX,
        WASM_INDEX, WASM_RESOURCE_PROVENANCE,
    },
    capture_project::load_manifest,
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
        .map(Vec::as_slice)
        .unwrap_or(&[])
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
        let fields = fields
            .as_object()
            .context("graph node fields must be a JSON object")?;
        if let Some(existing) = self.nodes.get_mut(&id) {
            let existing = existing
                .as_object_mut()
                .context("stored graph node must be an object")?;
            for (key, value) in fields {
                if !value.is_null() && !existing.contains_key(key) {
                    existing.insert(key.clone(), value.clone());
                }
            }
        } else {
            let mut node = Map::new();
            node.insert("id".into(), Value::String(id.clone()));
            node.extend(fields.clone());
            self.nodes.insert(id.clone(), Value::Object(node));
        }
        Ok(id)
    }

    fn add_edge(&mut self, from: &str, to: &str, kind: &str, fields: Value) -> Result<()> {
        let fields = fields
            .as_object()
            .context("graph edge fields must be a JSON object")?;
        let frozen = format!("{from}\0{to}\0{kind}\0{}", serde_json::to_string(fields)?);
        if !self.edge_seen.insert(frozen) {
            return Ok(());
        }
        let mut edge = Map::new();
        edge.insert("from".into(), Value::String(from.to_string()));
        edge.insert("to".into(), Value::String(to.to_string()));
        edge.insert("kind".into(), Value::String(kind.to_string()));
        edge.extend(fields.clone());
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

pub fn build_source_graph(project: &Path) -> Result<SourceGraphSummary> {
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
    let import_maps = optional_artifact(
        &project,
        IMPORT_MAPS,
        json!({"maps":[], "documents":{}, "summary":{}}),
    )?;

    let mut source_by_resource = BTreeMap::<u64, Vec<&Value>>::new();
    for unit in array_field(&source_index, "units") {
        if let Some(resource_id) = u64_field(unit, "resource_id") {
            source_by_resource
                .entry(resource_id)
                .or_default()
                .push(unit);
        }
    }

    let mut graph = GraphBuilder::default();
    let mut resource_nodes_by_sha = BTreeMap::<String, Vec<String>>::new();
    for (index, resource) in manifest.resources.iter().enumerate() {
        let resource_id = required_u64(resource, "id", &format!("manifest.resources[{index}]"))?;
        let node_id = format!("resource:{resource_id}");
        let units = source_by_resource
            .get(&resource_id)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let source_paths = units
            .iter()
            .filter_map(|unit| nonempty_string_field(unit, "source_path"))
            .map(|path| Value::String(path.to_string()))
            .collect::<Vec<_>>();
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"resource",
                "resource_id":resource_id,
                "url":field(resource,"url"),
                "kind":field(resource,"kind"),
                "status":field(resource,"status"),
                "body_present":field(resource,"body_present"),
                "raw_path":field(resource,"output_path"),
                "source_paths":source_paths,
                "sha256":field(resource,"sha256"),
            }),
        )?;
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

    // HAR-extracted HTML/script/source-map references and redirects.
    for resource in &manifest.resources {
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

    // Inline scripts are generated source nodes owned by their HTML resource.
    let mut inline_node_by_raw = BTreeMap::<String, String>::new();
    let mut inline_nodes_by_sha = BTreeMap::<String, Vec<String>>::new();
    for (index, item) in manifest.inline_scripts.iter().enumerate() {
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
        inline_node_by_raw.insert(output_path.to_string(), node_id.clone());
        if let Some(sha) = nonempty_string_field(item, "sha256") {
            inline_nodes_by_sha
                .entry(sha.to_string())
                .or_default()
                .push(node_id);
        }
    }

    // Debugger-observed runtime scripts are provenance, not independent resources.
    let family_counts = array_field(&runtime, "alpine_families")
        .iter()
        .filter_map(|row| {
            Some((
                nonempty_string_field(row, "shape")?.to_string(),
                row.get("source_count").cloned().unwrap_or_else(|| json!(0)),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let gtm_family_counts = array_field(&runtime, "gtm_families")
        .iter()
        .filter_map(|row| {
            Some((
                nonempty_string_field(row, "shape")?.to_string(),
                row.get("source_count").cloned().unwrap_or_else(|| json!(0)),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let mut runtime_node_by_instance = BTreeMap::<(String, String), String>::new();
    let mut runtime_instance_conflicts = BTreeSet::<(String, String)>::new();

    for source in array_field(&runtime, "sources") {
        let Some(digest) = nonempty_string_field(source, "sha256") else {
            continue;
        };
        let runtime_node = format!("runtime:{}", &digest[..digest.len().min(20)]);
        let classification = string_field(source, "classification");
        let alpine = source.get("alpine").unwrap_or(&Value::Null);
        let gtm = source.get("gtm").unwrap_or(&Value::Null);
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
                "urls":source.get("urls").cloned().unwrap_or_else(|| json!([])),
                "instrumentation_kind":field(source,"instrumentation_kind"),
                "generated_root_sha256s":generated.get("root_sha256s").cloned().unwrap_or_else(|| json!([])),
                "generated_root_urls":generated.get("root_urls").cloned().unwrap_or_else(|| json!([])),
                "generation_max_depth":field(generated,"max_depth"),
                "application_source":classification != Some("capture_instrumentation"),
            }),
        )?;

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
            if runtime_instance_conflicts.contains(&key) {
                continue;
            }
            if let Some(previous) = runtime_node_by_instance.get(&key) {
                if previous != &runtime_node {
                    runtime_instance_conflicts.insert(key.clone());
                    runtime_node_by_instance.remove(&key);
                    continue;
                }
            }
            runtime_node_by_instance.insert(key, runtime_node.clone());
        }

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
                    &runtime_node,
                    "runtime_generated_code",
                    edge_fields,
                )?;
            } else if let Some(url) = nonempty_string_field(parent, "url") {
                for parent_node in graph.targets_for(url)? {
                    graph.add_edge(
                        &parent_node,
                        &runtime_node,
                        "runtime_generated_code",
                        edge_fields.clone(),
                    )?;
                }
            }
        }

        match classification {
            Some("network_response" | "network_observed") => {
                let mut parents = resource_nodes_by_sha
                    .get(digest)
                    .cloned()
                    .unwrap_or_default();
                if parents.is_empty() {
                    for url in array_field(source, "urls").iter().filter_map(Value::as_str) {
                        if let Some(nodes) = graph.url_to_resources.get(url) {
                            parents.extend(nodes.iter().cloned());
                        }
                    }
                }
                let mut seen = BTreeSet::new();
                for parent in parents {
                    if seen.insert(parent.clone()) {
                        graph.add_edge(&parent, &runtime_node, "runtime_execution", json!({}))?;
                    }
                }
            }
            Some("inline_script") => {
                if let Some(parents) = inline_nodes_by_sha.get(digest) {
                    for parent in parents {
                        graph.add_edge(parent, &runtime_node, "runtime_execution", json!({}))?;
                    }
                }
            }
            Some("document_inline_script") => {
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
                        &runtime_node,
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
            }
            Some("alpine_expression") => {
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
                        &runtime_node,
                        &family_node,
                        "runtime_expression_family",
                        json!({}),
                    )?;
                }
                for dom_match in array_field(alpine, "dom_matches") {
                    let snapshot_key =
                        compact_key((field(dom_match, "source"), field(dom_match, "path")))?;
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
                        &runtime_node,
                        "runtime_alpine_compile",
                        json!({
                            "mapping_kind":field(alpine,"dom_mapping_kind"),
                            "expression":field(alpine,"expression"),
                            "compiled_expression":field(alpine,"compiled_expression"),
                            "shape":field(alpine,"shape"),
                        }),
                    )?;
                }
            }
            Some("gtm_custom_javascript") => {
                if let Some(shape) = nonempty_string_field(gtm, "shape") {
                    let family_node =
                        digest_id("runtime-family:", &format!("google_tag_manager\0{shape}"));
                    graph.add_node(
                        family_node.clone(),
                        json!({
                            "type":"runtime_expression_family", "framework":"google_tag_manager", "shape":shape,
                            "source_count":gtm_family_counts.get(shape).cloned().unwrap_or(Value::Null)
                        }),
                    )?;
                    graph.add_edge(
                        &runtime_node,
                        &family_node,
                        "runtime_expression_family",
                        json!({}),
                    )?;
                }
            }
            _ => {}
        }
    }

    // Runtime-observed WASM requests are capture evidence, not universal static control flow.
    for observation in array_field(&wasm_resource_provenance, "observations") {
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
            if let Some(runtime_node) = runtime_node_by_instance.get(&key) {
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

        let resource_ids = array_field(observation, "wasm_resource_ids")
            .iter()
            .filter_map(Value::as_u64)
            .collect::<Vec<_>>();
        let exact_resource_occurrence = resource_ids.len() == 1;
        for resource_id in resource_ids {
            graph.add_edge(
                &observation_id,
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
    }

    // Safe static deobfuscation is a provenance-preserving source transform.
    let mut deob_nodes = BTreeMap::<u64, String>::new();
    for unit in array_field(&deobfuscation, "units") {
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
            .and_then(|raw| inline_node_by_raw.get(raw).cloned())
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

    // Static browser API callsites hang off the exact selected source derivative.
    for row in array_field(&api_surface, "callsites") {
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
            parent =
                string_field(row, "raw_path").and_then(|raw| inline_node_by_raw.get(raw).cloned());
        }
        if parent.is_none() {
            parent =
                u64_field(row, "resource_id").map(|resource_id| format!("resource:{resource_id}"));
        }
        if let Some(parent) = parent {
            graph.add_edge(&parent, &node_id, "api_callsite", json!({}))?;
        }
        if bool_field(row, "absolute_network_url")
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

    // Statically explicit Webpack/Next module tables become navigable project modules.
    let mut bundle_nodes = BTreeMap::<u64, String>::new();
    for bundle in array_field(&bundles, "bundles") {
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

    let bundle_rows_by_id = array_field(&bundles, "bundles")
        .iter()
        .filter_map(|bundle| Some((u64_field(bundle, "bundle_id")?, bundle)))
        .collect::<BTreeMap<_, _>>();
    let mut bundle_module_nodes = BTreeMap::<(u64, String), String>::new();
    let mut module_nodes_by_id = BTreeMap::<String, Vec<String>>::new();
    let mut module_rows = BTreeMap::<String, &Value>::new();
    for module in array_field(&bundles, "modules") {
        let bundle_id = required_u64(module, "bundle_id", "bundle module")?;
        let ordinal = u64_field(module, "module_ordinal").unwrap_or(0);
        let node_id = format!("bundle-module:{bundle_id}:{ordinal}");
        let module_id = module.get("module_id").map_or_else(String::new, |value| {
            value
                .as_str()
                .map_or_else(|| value.to_string(), ToString::to_string)
        });
        bundle_module_nodes.insert((bundle_id, module_id.clone()), node_id.clone());
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

    let nested_private_bundle_candidate = |candidate_node: &str, source_module: &Value| -> bool {
        let Some(candidate_module) = module_rows.get(candidate_node).copied() else {
            return false;
        };
        let Some(candidate_bundle_id) = u64_field(candidate_module, "bundle_id") else {
            return false;
        };
        let Some(candidate_bundle) = bundle_rows_by_id.get(&candidate_bundle_id).copied() else {
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
    };

    for (source_node, module) in &module_rows {
        let bundle_id = required_u64(module, "bundle_id", "bundle module")?;
        for dependency in array_field(module, "dependencies") {
            let dependency = dependency
                .as_str()
                .map_or_else(|| dependency.to_string(), ToString::to_string);
            let mut target = bundle_module_nodes
                .get(&(bundle_id, dependency.clone()))
                .cloned();
            let mut cross_bundle = false;
            let mut excluded_nested = Vec::<String>::new();
            let mut candidates = Vec::<String>::new();
            if target.is_none() {
                let all_candidates = module_nodes_by_id
                    .get(&dependency)
                    .cloned()
                    .unwrap_or_default();
                for candidate in all_candidates {
                    if nested_private_bundle_candidate(&candidate, module) {
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

    // Source maps link generated JS -> map resource -> recovered original source.
    for source_map in array_field(&sourcemaps, "source_maps") {
        let Some(resource_id) = u64_field(source_map, "resource_id") else {
            continue;
        };
        let src = format!("resource:{resource_id}");
        let mut map_node = None::<String>;
        if let Some(map_resource_id) = u64_field(source_map, "map_resource_id") {
            let node = format!("resource:{map_resource_id}");
            graph.add_edge(
                &src,
                &node,
                "source_map",
                json!({"map_url":field(source_map,"map_url")}),
            )?;
            map_node = Some(node);
        } else if let Some(map_url) = nonempty_string_field(source_map, "map_url") {
            let targets = graph.targets_for(map_url)?;
            map_node = targets.first().cloned();
            for dst in targets {
                graph.add_edge(&src, &dst, "source_map", json!({"map_url":map_url}))?;
            }
        }

        for recovered in array_field(source_map, "recovered") {
            if string_field(recovered, "status") != Some("recovered") {
                continue;
            }
            let ordinal = u64_field(recovered, "ordinal").unwrap_or(0);
            let node_id = format!("sourcemap-source:{resource_id}:{ordinal}");
            graph.add_node(
                node_id.clone(),
                json!({
                    "type":"sourcemap_source",
                    "parent_resource_id":resource_id,
                    "ordinal":ordinal,
                    "logical_source":field(recovered,"logical_source"),
                    "source_path":field(recovered,"source_path"),
                    "bytes":field(recovered,"bytes"),
                }),
            )?;
            graph.add_edge(
                map_node.as_deref().unwrap_or(&src),
                &node_id,
                "source_map_source",
                json!({"ordinal":ordinal}),
            )?;
        }

        let composition = source_map.get("composition").unwrap_or(&Value::Null);
        let mut composed_node = None::<String>;
        if let Some(composed_map_path) = nonempty_string_field(composition, "composed_map_path") {
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
            graph.add_edge(
                map_node.as_deref().unwrap_or(&src),
                &node_id,
                "source_map_composed",
                json!({}),
            )?;
            composed_node = Some(node_id);
        }

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
            graph.add_edge(
                map_node.as_deref().unwrap_or(&src),
                &chain_node,
                "source_map_chain",
                json!({}),
            )?;
            if let Some(nested_map_resource_id) = u64_field(link, "map_resource_id") {
                graph.add_edge(
                    &chain_node,
                    &format!("resource:{nested_map_resource_id}"),
                    "source_map_chain_resource",
                    json!({}),
                )?;
            } else if let Some(map_url) = string_field(link, "map_url") {
                for dst in graph.targets_for(map_url)? {
                    graph.add_edge(&chain_node, &dst, "source_map_chain_resource", json!({}))?;
                }
            }
        }

        for recovered in array_field(source_map, "composed_recovered") {
            if string_field(recovered, "status") != Some("recovered") {
                continue;
            }
            let ordinal = u64_field(recovered, "ordinal").unwrap_or(0);
            let node_id = format!("sourcemap-final:{resource_id}:{ordinal}");
            graph.add_node(
                node_id.clone(),
                json!({
                    "type":"sourcemap_composed_source",
                    "parent_resource_id":resource_id,
                    "ordinal":ordinal,
                    "logical_source":field(recovered,"logical_source"),
                    "source_path":field(recovered,"source_path"),
                    "bytes":field(recovered,"bytes"),
                }),
            )?;
            let parent = composed_node
                .as_deref()
                .or(map_node.as_deref())
                .unwrap_or(&src);
            graph.add_edge(
                parent,
                &node_id,
                "source_map_composed_source",
                json!({"ordinal":ordinal}),
            )?;
        }
    }

    // Static Function(...) recovery is a generated-code provenance edge.
    let mut generated_analysis_parent = BTreeMap::<u64, String>::new();
    for dynamic in array_field(&jsvm, "dynamic_code_units") {
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
        if let Some(child_scan_id) = u64_field(dynamic, "child_scan_id") {
            generated_analysis_parent.insert(child_scan_id, analysis_parent);
        }
    }

    let mut scan_to_parent = BTreeMap::<u64, String>::new();
    for unit in array_field(&jsvm, "code_units") {
        let Some(scan_id) = u64_field(unit, "scan_id") else {
            continue;
        };
        let parent = if string_field(unit, "origin") == Some("generated_dynamic_code") {
            if let Some(parent) = generated_analysis_parent.get(&scan_id) {
                Some(parent.clone())
            } else {
                let Some(parent_scan_id) = u64_field(unit, "parent_scan_id") else {
                    continue;
                };
                let Some(ordinal) = u64_field(unit, "parent_dynamic_ordinal") else {
                    continue;
                };
                Some(format!("dynamic:{parent_scan_id}:{ordinal}"))
            }
        } else if let Some(deob_ordinal) = u64_field(unit, "deobfuscation_ordinal") {
            deob_nodes.get(&deob_ordinal).cloned()
        } else {
            u64_field(unit, "resource_id").map(|resource_id| format!("resource:{resource_id}"))
        };
        if let Some(parent) = parent {
            scan_to_parent.insert(scan_id, parent);
        }
    }

    for dynamic in array_field(&jsvm, "dynamic_code_units") {
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

    for unit in array_field(&jsvm, "devirtualized_units") {
        let parent_scan_id = required_u64(unit, "parent_scan_id", "devirtualized unit")?;
        let ordinal = required_u64(unit, "vm_ordinal", "devirtualized unit")?;
        let vm_kind = nonempty_string_field(unit, "vm_kind").unwrap_or("unknown");
        let node_id = format!("devirtualized:{parent_scan_id}:{vm_kind}:{ordinal}");
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

    // Import-map definitions are captured provenance too, not just resolver state.
    for record in array_field(&import_maps, "maps") {
        let Some(raw_path) = string_field(record, "raw_path") else {
            continue;
        };
        let Some(src) = inline_node_by_raw.get(raw_path).cloned() else {
            continue;
        };
        let document_resource_id = field(record, "document_resource_id");
        if let Some(imports) = object_field(record, "imports") {
            for (specifier, resolved) in imports {
                let Some(resolved) = resolved.as_str() else {
                    continue;
                };
                for dst in graph.targets_for(resolved)? {
                    graph.add_edge(
                        &src,
                        &dst,
                        "import_map_entry",
                        json!({
                            "specifier":specifier,
                            "resolved_url":resolved,
                            "document_resource_id":document_resource_id.clone(),
                            "scope":Value::Null,
                        }),
                    )?;
                }
            }
        }
        if let Some(scopes) = object_field(record, "scopes") {
            for (scope, entries) in scopes {
                let Some(entries) = entries.as_object() else {
                    continue;
                };
                for (specifier, resolved) in entries {
                    let Some(resolved) = resolved.as_str() else {
                        continue;
                    };
                    for dst in graph.targets_for(resolved)? {
                        graph.add_edge(
                            &src,
                            &dst,
                            "import_map_entry",
                            json!({
                                "specifier":specifier,
                                "resolved_url":resolved,
                                "document_resource_id":document_resource_id.clone(),
                                "scope":scope,
                            }),
                        )?;
                    }
                }
            }
        }
    }

    // AST-backed JavaScript module / worker references.
    let mut specifier_nodes = BTreeMap::<String, String>::new();
    for unit in array_field(&jsrefs, "code_units") {
        let Some(resource_id) = u64_field(unit, "resource_id") else {
            continue;
        };
        let src = string_field(unit, "raw_path")
            .and_then(|raw| inline_node_by_raw.get(raw).cloned())
            .unwrap_or_else(|| format!("resource:{resource_id}"));
        for reference in array_field(unit, "references") {
            let mut candidates = Vec::<Value>::new();
            if let Some(resolved) = nonempty_string_field(reference, "resolved_url") {
                let contexts = array_field(reference, "resolution_candidates");
                if contexts.is_empty() {
                    candidates.push(json!({
                        "resolved_url":resolved,
                        "document_resource_id":Value::Null,
                        "resolution":field(reference,"resolution"),
                        "import_map_key":field(reference,"import_map_key"),
                        "scope":field(reference,"scope"),
                    }));
                } else {
                    for context in contexts {
                        candidates.push(json!({
                            "resolved_url":resolved,
                            "document_resource_id":field(context,"document_resource_id"),
                            "resolution":field(reference,"resolution"),
                            "import_map_key":field(reference,"import_map_key"),
                            "scope":field(reference,"scope"),
                        }));
                    }
                }
            } else {
                for context in array_field(reference, "resolution_candidates") {
                    if nonempty_string_field(context, "resolved_url").is_some() {
                        candidates.push(context.clone());
                    }
                }
            }

            if !candidates.is_empty() {
                for candidate in candidates {
                    let Some(candidate_url) = string_field(&candidate, "resolved_url") else {
                        continue;
                    };
                    for dst in graph.targets_for(candidate_url)? {
                        graph.add_edge(
                            &src,
                            &dst,
                            &format!(
                                "js_{}",
                                string_field(reference, "kind").unwrap_or("reference")
                            ),
                            json!({
                                "specifier":field(reference,"specifier"),
                                "glob":field(reference,"glob"),
                                "glob_match_url":field(&candidate,"glob_match_url"),
                                "resolved_url":candidate_url,
                                "resolution":field(&candidate,"resolution"),
                                "import_map_key":field(&candidate,"import_map_key"),
                                "scope":field(&candidate,"scope"),
                                "document_resource_id":field(&candidate,"document_resource_id"),
                                "start":field(reference,"start"),
                                "end":field(reference,"end"),
                            }),
                        )?;
                    }
                }
                continue;
            }

            let specifier = string_field(reference, "specifier").unwrap_or("");
            let node_id = if let Some(node_id) = specifier_nodes.get(specifier) {
                node_id.clone()
            } else {
                let node_id = digest_id("specifier:", specifier);
                graph.add_node(
                    node_id.clone(),
                    json!({
                        "type":"module_specifier",
                        "specifier":specifier,
                        "bare":bool_field(reference,"bare_specifier"),
                        "captured":false,
                    }),
                )?;
                specifier_nodes.insert(specifier.to_string(), node_id.clone());
                node_id
            };
            graph.add_edge(
                &src,
                &node_id,
                &format!(
                    "js_{}",
                    string_field(reference, "kind").unwrap_or("reference")
                ),
                json!({
                    "specifier":specifier,
                    "glob":field(reference,"glob"),
                    "resolved_url":Value::Null,
                    "resolution":field(reference,"resolution"),
                    "import_map_key":field(reference,"import_map_key"),
                    "scope":field(reference,"scope"),
                    "start":field(reference,"start"),
                    "end":field(reference,"end"),
                }),
            )?;
        }
    }

    // Captured or statically recovered WebAssembly modules are first-class derived sources.
    for module in array_field(&wasm, "modules") {
        let digest = string_field(module, "sha256").context("WASM module sha256 is required")?;
        let node_id = format!("wasm:{}", &digest[..digest.len().min(20)]);
        graph.add_node(
            node_id.clone(),
            json!({
                "type":"wasm_module",
                "sha256":digest,
                "bytes":field(module,"byte_len"),
                "binary_path":field(module,"binary_path"),
                "extracted":bool_field(module,"extracted"),
                "status":field(module,"status"),
                "report_path":field(module,"report_path"),
                "readable_wat_path":field(module,"wat_path"),
                "deep_analysis_path":field(module,"deep_path"),
            }),
        )?;
        for origin in array_field(module, "origins") {
            let kind = string_field(origin, "type");
            let parent = match kind {
                Some("resource" | "resource_inline_base64" | "resource_static_bytes") => {
                    u64_field(origin, "resource_id")
                        .map(|resource_id| format!("resource:{resource_id}"))
                }
                Some("inline_script_base64" | "inline_script_static_bytes") => {
                    match (
                        u64_field(origin, "parent_resource_id"),
                        u64_field(origin, "ordinal"),
                    ) {
                        (Some(parent_resource_id), Some(ordinal)) => {
                            Some(format!("inline:{parent_resource_id}:{ordinal}"))
                        }
                        _ => None,
                    }
                }
                _ => None,
            };
            let Some(parent) = parent else {
                continue;
            };
            let edge_kind = match kind {
                Some("resource") => "wasm_resource",
                Some("resource_static_bytes" | "inline_script_static_bytes") => "wasm_static_bytes",
                _ => "wasm_inline_base64",
            };
            graph.add_edge(
                &parent,
                &node_id,
                edge_kind,
                json!({
                    "encoding":field(origin,"encoding"),
                    "recovery_kind":field(origin,"recovery_kind"),
                    "start":field(origin,"byte_start"),
                    "end":field(origin,"byte_end"),
                }),
            )?;
        }
    }

    let mut edge_counts = BTreeMap::<String, usize>::new();
    for edge in &graph.edges {
        if let Some(kind) = string_field(edge, "kind") {
            *edge_counts.entry(kind.to_string()).or_default() += 1;
        }
    }
    let mut node_counts = BTreeMap::<String, usize>::new();
    for node in graph.nodes.values() {
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
    write_artifact(&project, SOURCE_GRAPH, &document)?;
    Ok(summary)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        analysis_artifacts::{load_artifact, SOURCE_GRAPH},
        capture_project::{write_manifest, CaptureManifest, CaptureSource, MANIFEST_NAME},
    };

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
        let summary = build_source_graph(&project)?;
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
