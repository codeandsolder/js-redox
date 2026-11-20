//! Runtime WASM requests: observed request evidence is not static call proof.
//!
//! Body identity, unique response occurrence and initiator identity are
//! independent claims. Never upgrade candidates by selecting the only row.

use super::{
    array_field, bool_field, compact_key, digest_id, field, nonempty_string_field,
    runtime_evidence::RuntimeInstances, GraphBuilder,
};
use anyhow::Result;
use serde_json::{json, Value};
use std::collections::BTreeSet;
use work_budget::WorkBudget;

#[derive(Clone, Copy)]
enum InitiatorBasis {
    SessionScriptId,
    SessionScriptIdAndDigest,
    CapturedResources,
    UrlOnly,
    Unknown,
}

impl InitiatorBasis {
    const fn as_str(self) -> &'static str {
        match self {
            Self::SessionScriptId => "session_script_id",
            Self::SessionScriptIdAndDigest => "session_script_id_and_sha256",
            Self::CapturedResources => "captured_resource_candidates",
            Self::UrlOnly => "url_only",
            Self::Unknown => "unknown",
        }
    }
    const fn exact_runtime_instance(self) -> bool {
        matches!(self, Self::SessionScriptId | Self::SessionScriptIdAndDigest)
    }
}

struct InitiatorResolution {
    nodes: Vec<String>,
    basis: InitiatorBasis,
}

fn resource_ids(row: &Value, name: &str, budget: &WorkBudget) -> Result<BTreeSet<u64>> {
    let values = array_field(row, name);
    budget.consume(u64::try_from(values.len())?)?;
    Ok(values.iter().filter_map(Value::as_u64).collect())
}

/// Prefer an unambiguous runtime instance. An explicit captured SHA must
/// agree with the full digest in that instance index; otherwise only
/// captured resource candidates or the recorded URL may provide context.
fn resolve_initiator(
    graph: &mut GraphBuilder,
    observation: &Value,
    primary: &Value,
    runtime_instances: &RuntimeInstances,
    budget: &WorkBudget,
) -> Result<InitiatorResolution> {
    let session = nonempty_string_field(observation, "cdp_session").unwrap_or("main");
    let expected_sha = nonempty_string_field(observation, "initiator_runtime_sha256");
    if let Some(node) = primary
        .get("script_id")
        .and_then(|id| runtime_instances.observed_node(session, id, expected_sha))
    {
        return Ok(InitiatorResolution {
            nodes: vec![node],
            basis: if expected_sha.is_some() {
                InitiatorBasis::SessionScriptIdAndDigest
            } else {
                InitiatorBasis::SessionScriptId
            },
        });
    }
    let ids = resource_ids(observation, "initiator_resource_ids", budget)?;
    if !ids.is_empty() {
        return Ok(InitiatorResolution {
            nodes: ids.into_iter().map(|id| format!("resource:{id}")).collect(),
            basis: InitiatorBasis::CapturedResources,
        });
    }
    if let Some(url) = nonempty_string_field(primary, "url") {
        let nodes = graph.targets_for(url, budget)?;
        return Ok(InitiatorResolution {
            nodes,
            basis: InitiatorBasis::UrlOnly,
        });
    }
    Ok(InitiatorResolution {
        nodes: Vec::new(),
        basis: InitiatorBasis::Unknown,
    })
}

struct ObservedResponse {
    resource_ids: BTreeSet<u64>,
    exact_body: bool,
}

impl ObservedResponse {
    fn from_observation(row: &Value, budget: &WorkBudget) -> Result<Self> {
        let ids = resource_ids(row, "wasm_resource_ids", budget)?;
        let exact_body = bool_field(row, "exact_response_identity")
            && nonempty_string_field(row, "sha256").is_some()
            && !ids.is_empty()
            && array_field(row, "wasm_resource_ids")
                .iter()
                .all(|value| value.is_u64());
        Ok(Self {
            resource_ids: ids,
            exact_body,
        })
    }
    fn exact_occurrence(&self) -> bool {
        self.exact_body && self.resource_ids.len() == 1
    }
    fn add_edges(
        &self,
        graph: &mut GraphBuilder,
        observation: &Value,
        observation_id: &str,
        budget: &WorkBudget,
    ) -> Result<()> {
        let exact_occurrence = self.exact_occurrence();
        let kind = if exact_occurrence {
            "runtime_observed_wasm_response"
        } else {
            "runtime_observed_wasm_response_candidate"
        };
        for id in &self.resource_ids {
            budget.checkpoint()?;
            graph.add_edge(
                observation_id,
                &format!("resource:{id}"),
                kind,
                json!({
                    "sha256":field(observation,"sha256"),
                    "url":field(observation,"url"),
                    "exact_response_identity":self.exact_body,
                    "exact_resource_occurrence":exact_occurrence,
                    "response_identity_basis":field(observation,"response_identity_basis"),
                }),
            )?;
        }
        Ok(())
    }
}

/// Publish the observed request and its independently resolved provenance.
pub(super) fn seed_runtime_wasm_observations(
    graph: &mut GraphBuilder,
    wasm_resource_provenance: &Value,
    runtime_instances: &RuntimeInstances,
    budget: &WorkBudget,
) -> Result<()> {
    for observation in array_field(wasm_resource_provenance, "observations") {
        budget.consume(1)?;
        let session = nonempty_string_field(observation, "cdp_session").unwrap_or("main");
        let key = compact_key((
            session,
            field(observation, "request_id"),
            field(observation, "url"),
            field(observation, "sha256"),
        ))?;
        let observation_id = digest_id("runtime-wasm-request:", &key);
        let primary = observation.get("primary_initiator").unwrap_or(&Value::Null);
        let response = ObservedResponse::from_observation(observation, budget)?;
        let initiator = resolve_initiator(graph, observation, primary, runtime_instances, budget)?;
        graph.insert_node(
            observation_id.clone(),
            json!({
                "type":"runtime_wasm_request",
                "cdp_session":session,
                "request_id":field(observation,"request_id"),
                "url":field(observation,"url"),
                "sha256":field(observation,"sha256"),
                "bytes":field(observation,"byte_len"),
                "initiator_type":field(observation,"initiator_type"),
                "initiator_function":field(primary,"function_name"),
                "initiator_script_id":field(primary,"script_id"),
                "initiator_url":field(primary,"url"),
                "initiator_runtime_sha256":field(observation,"initiator_runtime_sha256"),
                "line_number":field(primary,"line_number"),
                "column_number":field(primary,"column_number"),
                "runtime_observed":true,
                "exact_response_identity":response.exact_body,
                "exact_resource_occurrence":response.exact_occurrence(),
                "response_identity_basis":field(observation,"response_identity_basis"),
                "matching_resource_count":response.resource_ids.len(),
                "initiator_identity_basis":initiator.basis.as_str(),
                "exact_runtime_instance":initiator.basis.exact_runtime_instance(),
                "initiator_candidate_count":initiator.nodes.len(),
            }),
        )?;
        for node in &initiator.nodes {
            budget.checkpoint()?;
            graph.add_edge(
                node,
                &observation_id,
                "runtime_wasm_request_initiator",
                json!({
                    "evidence":field(observation,"evidence"),
                    "function_name":field(primary,"function_name"),
                    "script_id":field(primary,"script_id"),
                    "line_number":field(primary,"line_number"),
                    "column_number":field(primary,"column_number"),
                    "runtime_observed":true,
                    "identity_basis":initiator.basis.as_str(),
                    "exact_runtime_instance":initiator.basis.exact_runtime_instance(),
                    "candidate_count":initiator.nodes.len(),
                }),
            )?;
        }
        response.add_edges(graph, observation, &observation_id, budget)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Context;

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
            graph.insert_node(id, json!({"type":"resource","url":shared}))?;
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
                .node_values()
                .find(|node| node["request_id"] == request_id)
                .and_then(|node| node["id"].as_str())
                .with_context(|| format!("missing request {request_id}"))
        };
        let sources = |request_id: &str| -> Result<BTreeSet<&str>> {
            let target = observation(request_id)?;
            Ok(graph
                .edges()
                .values()
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
        assert_eq!(graph.external_url_count(), 1);

        let exact = observation("exact")?;
        let response = graph
            .edges()
            .values()
            .filter(|edge| edge["from"] == exact)
            .collect::<Vec<_>>();
        assert_eq!(response.len(), 1);
        assert_eq!(response[0]["to"], "resource:20");
        assert_eq!(response[0]["kind"], "runtime_observed_wasm_response");
        assert_eq!(response[0]["exact_resource_occurrence"], true);

        let ambiguous = observation("resource-fallback")?;
        let candidates = graph
            .edges()
            .values()
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
            && edge["exact_resource_occurrence"] == false
            && edge["exact_response_identity"] == false));
        assert_eq!(
            graph.node_value(ambiguous)["exact_response_identity"],
            false
        );
        assert!(graph.edges().values().all(|edge| {
            edge["kind"] != "runtime_wasm_request_initiator"
                || edge["from"] != "runtime:worker"
                || edge["to"] == exact
        }));
        Ok(())
    }

    #[test]
    fn response_occurrence_requires_proven_body_and_one_distinct_resource() -> Result<()> {
        let budget = WorkBudget::unlimited("response-identity");
        let cases = [
            (
                json!({"wasm_resource_ids":[7],"sha256":"body","exact_response_identity":false}),
                false,
                false,
                1,
            ),
            (
                json!({"wasm_resource_ids":[7,7],"sha256":"body","exact_response_identity":true}),
                true,
                true,
                1,
            ),
            (
                json!({"wasm_resource_ids":[7,8],"sha256":"body","exact_response_identity":true}),
                true,
                false,
                2,
            ),
            (
                json!({"wasm_resource_ids":[7],"exact_response_identity":true}),
                false,
                false,
                1,
            ),
            (
                json!({"wasm_resource_ids":[7,"invalid"],"sha256":"body","exact_response_identity":true}),
                false,
                false,
                1,
            ),
        ];
        for (row, body, occurrence, count) in cases {
            let response = ObservedResponse::from_observation(&row, &budget)?;
            assert_eq!(response.exact_body, body);
            assert_eq!(response.exact_occurrence(), occurrence);
            let mut graph = GraphBuilder::default();
            response.add_edges(&mut graph, &row, "request", &budget)?;
            assert_eq!(graph.edges().len(), count);
            for edge in graph.edges().values() {
                assert_eq!(edge["exact_response_identity"], body);
                assert_eq!(edge["exact_resource_occurrence"], occurrence);
                assert_eq!(
                    edge["kind"],
                    if occurrence {
                        "runtime_observed_wasm_response"
                    } else {
                        "runtime_observed_wasm_response_candidate"
                    }
                );
            }
        }
        Ok(())
    }

    #[test]
    fn initiator_digest_must_agree_beyond_graph_node_prefix() -> Result<()> {
        let prefix = "a".repeat(20);
        let digest = format!("{prefix}{}", "b".repeat(44));
        let other = format!("{prefix}{}", "c".repeat(44));
        let mut instances = RuntimeInstances::default();
        instances.register("worker", "17", &digest);
        let primary = json!({"script_id":17});
        let mut observation = json!({"cdp_session":"worker", "initiator_runtime_sha256":other, "initiator_resource_ids":[5,5]});
        let mut graph = GraphBuilder::default();
        let budget = WorkBudget::unlimited("initiator-identity");
        let fallback = resolve_initiator(&mut graph, &observation, &primary, &instances, &budget)?;
        assert_eq!(fallback.nodes, ["resource:5"]);
        assert!(!fallback.basis.exact_runtime_instance());
        observation["initiator_runtime_sha256"] = json!(digest);
        let exact = resolve_initiator(&mut graph, &observation, &primary, &instances, &budget)?;
        assert_eq!(exact.nodes, [format!("runtime:{prefix}")]);
        assert_eq!(exact.basis.as_str(), "session_script_id_and_sha256");
        assert!(exact.basis.exact_runtime_instance());
        let limited = WorkBudget::new("response-id-budget", work_budget::BudgetLimits::work(1));
        assert!(
            ObservedResponse::from_observation(&json!({"wasm_resource_ids":[1,2]}), &limited)
                .is_err()
        );
        Ok(())
    }
}
