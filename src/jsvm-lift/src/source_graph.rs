mod bundle_evidence;
mod capture_evidence;
mod generated_evidence;
mod reference_evidence;
mod runtime_evidence;
mod sourcemap_evidence;
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
use capture_evidence::InlineSourceIndex;
use runtime_evidence::{seed_runtime_script_evidence, RuntimeInstances, RuntimeSourceGraphIndex};
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    path::Path,
};

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

/// An inspector function definition is exact only for its session, script ID
/// and source digest. Definition identity is not executed-call proof.
fn add_observed_callable_definition(
    graph: &mut GraphBuilder,
    runtime_nodes: &RuntimeInstances,
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
    let Some(expected) = runtime_nodes.exact_node(session, script_id, sha) else {
        return Ok(());
    };
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

/// A debugger frame is exact only when its session/script ID identifies one
/// runtime source and its captured SHA agrees with that source.
fn exact_runtime_frame_identity<'a>(
    frame: &'a Value,
    session: &str,
    instances: &RuntimeInstances,
) -> Option<(String, &'a str, &'a str)> {
    if nonempty_string_field(frame, "source_identity") != Some("exact") {
        return None;
    }
    let script_id = frame.get("location")?.get("scriptId")?.as_str()?;
    let sha = nonempty_string_field(frame, "sourceSha256")?;
    let expected = instances.exact_node(session, script_id, sha)?;
    Some((expected, script_id, sha))
}

fn add_observed_pause_frames(
    graph: &mut GraphBuilder,
    hit: &Value,
    session: &str,
    node_id: &str,
    runtime_node_by_instance: &RuntimeInstances,
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
    runtime_node_by_instance: &RuntimeInstances,
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
    runtime_node_by_instance: &RuntimeInstances,
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
    runtime_node_by_instance: &RuntimeInstances,
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
    runtime_instances: &RuntimeInstances,
) -> Result<Vec<String>> {
    let mut source_nodes = Vec::<String>::new();
    if let Some(runtime_node) = primary.get("script_id").and_then(|script_id| {
        runtime_instances.observed_node(
            nonempty_string_field(observation, "cdp_session").unwrap_or("main"),
            script_id,
        )
    }) {
        source_nodes.push(runtime_node);
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
    runtime_instances: &RuntimeInstances,
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
    let capture_evidence::CapturedSourceIndex {
        resource_nodes_by_sha,
        inline_nodes,
        inline_nodes_by_sha,
    } = capture_evidence::seed_capture_evidence(&mut graph, &manifest, &source_index, &budget)?;

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

    finish_source_graph(&project, &manifest, graph, &budget)
}

#[cfg(test)]
mod tests {
    use super::capture_evidence::{
        seed_captured_inline_scripts, seed_captured_reference_edges, seed_captured_resources,
        seed_navigation_roots,
    };
    use super::runtime_evidence::add_runtime_network_source_edges;
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
        let mut instances = RuntimeInstances::default();
        instances.register("worker", "17", "worker");
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
        assert!(instances.observed_node("worker", &json!("7")).is_none());
        assert_eq!(
            instances.observed_node("other", &json!("7")),
            Some(format!("runtime:{}", &second[..20]))
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
            "coverage_mode":"best-effort",
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
        assert_eq!(parsed[0]["coverage_mode"], "best-effort");

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
