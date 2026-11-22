//! Graph consumers of already captured selective debugger observations.
//!
//! Exact provenance is session-, script- and content-scoped. A pause,
//! source location, callable definition and AST guard each certify only
//! their own recorded observation, never an unobserved execution path.

use super::{
    array_field, field, nonempty_string_field, runtime_evidence::RuntimeInstances, u64_field,
    GraphBuilder,
};
use crate::{
    runtime_identity::{script_id_text, session_name},
    trace_identity::same_verified_stack_shape,
};
use anyhow::Result;
use serde_json::{json, Value};
use std::borrow::Cow;
use work_budget::WorkBudget;

/// An inspector function definition is exact only for its session, script ID
/// and source digest. Definition identity is not executed-call proof.
fn add_observed_callable_definition(
    graph: &mut GraphBuilder,
    runtime_nodes: &RuntimeInstances,
    invocation_id: &str,
    session: Option<&str>,
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
    let Some(script_id) = definition.get("scriptId").and_then(script_id_text) else {
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
    let Some(expected) =
        session.and_then(|session| runtime_nodes.exact_node(session, &script_id, sha))
    else {
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

struct ExactFrame<'a> {
    node: String,
    script_id: Cow<'a, str>,
    sha: &'a str,
    location: &'a Value,
}

impl ExactFrame<'_> {
    fn coordinates(&self) -> Option<(u64, u64)> {
        Some((
            u64_field(self.location, "lineNumber")?,
            u64_field(self.location, "columnNumber")?,
        ))
    }
}

/// A source identity does not itself establish a particular coordinate.
fn exact_runtime_frame_identity<'a>(
    frame: &'a Value,
    session: Option<&str>,
    instances: &RuntimeInstances,
) -> Option<ExactFrame<'a>> {
    if nonempty_string_field(frame, "source_identity") != Some("exact") {
        return None;
    }
    let location = frame.get("location")?;
    let script_id = location.get("scriptId").and_then(script_id_text)?;
    let sha = nonempty_string_field(frame, "sourceSha256")?;
    let node = instances.exact_node(session?, &script_id, sha)?;
    Some(ExactFrame {
        node,
        script_id,
        sha,
        location,
    })
}

fn add_observed_pause_frames(
    graph: &mut GraphBuilder,
    hit: &Value,
    session: Option<&str>,
    node_id: &str,
    runtime_node_by_instance: &RuntimeInstances,
    budget: &WorkBudget,
) -> Result<()> {
    for (depth, frame) in array_field(hit, "frames").iter().enumerate() {
        budget.consume(1)?;
        let Some(identity) = exact_runtime_frame_identity(frame, session, runtime_node_by_instance)
        else {
            continue;
        };
        graph.add_edge(
            &identity.node,
            node_id,
            "observed_paused_call_frame",
            json!({
                "stack_depth":depth,
                "cdp_session":session,
                "script_id":identity.script_id,
                "source_sha256":identity.sha,
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
    session: Option<&str>,
    node_id: &str,
    runtime_node_by_instance: &RuntimeInstances,
    budget: &WorkBudget,
) -> Result<()> {
    for (step_index, step) in array_field(hit, "steps").iter().enumerate() {
        budget.consume(1)?;
        let step_id = format!("observed-step:{ordinal}:{step_index}");
        let top = array_field(step, "frames").first();
        graph.insert_node(
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
        let Some(identity) = exact_runtime_frame_identity(top, session, runtime_node_by_instance)
        else {
            continue;
        };
        let Some((line, column)) = identity.coordinates() else {
            continue;
        };
        graph.add_edge(
            &identity.node,
            &step_id,
            "observed_executed_location",
            json!({
                "cdp_session":session,
                "script_id":identity.script_id,
                "source_sha256":identity.sha,
                "line_number":line,
                "column_number":column,
                "step_index":step_index,
                "identity_basis":"exact_session_script_hash",
                "concrete_observation_only":true,
            }),
        )?;
    }
    Ok(())
}

/// Consume the producer's AST proof only when it is tied to the exact
/// source of the recorded executing step and its recorded boolean value.
fn exact_guard_identity<'a>(
    guard: &Value,
    step: &'a Value,
    session: Option<&str>,
    instances: &RuntimeInstances,
    budget: &WorkBudget,
) -> Result<Option<ExactFrame<'a>>> {
    if nonempty_string_field(guard, "evidence") != Some("exact_source_ast_and_boolean_pause") {
        return Ok(None);
    }
    let Some(frame) = array_field(step, "frames")
        .first()
        .and_then(|frame| exact_runtime_frame_identity(frame, session, instances))
    else {
        return Ok(None);
    };
    if frame.coordinates().is_none()
        || guard.get("script_id").and_then(script_id_text).as_deref()
            != Some(frame.script_id.as_ref())
        || nonempty_string_field(guard, "source_sha256") != Some(frame.sha)
    {
        return Ok(None);
    }
    let (Some(guard_start), Some(test_start), Some(test_end), Some(condition), Some(value)) = (
        u64_field(guard, "guard_start_byte"),
        u64_field(guard, "test_start_byte"),
        u64_field(guard, "test_end_byte"),
        nonempty_string_field(guard, "expression"),
        guard.get("observed_value").and_then(Value::as_bool),
    ) else {
        return Ok(None);
    };
    if !(guard_start <= test_start && test_start < test_end) {
        return Ok(None);
    }
    let expressions = array_field(step, "expressions");
    budget.consume(u64::try_from(expressions.len())?)?;
    let witnessed = expressions.iter().any(|expression| {
        nonempty_string_field(expression, "status") == Some("observed")
            && nonempty_string_field(expression, "expression") == Some(condition)
            && expression.pointer("/value/type").and_then(Value::as_str) == Some("boolean")
            && expression.pointer("/value/value").and_then(Value::as_bool) == Some(value)
    });
    Ok(witnessed.then_some(frame))
}

fn add_observed_guard_witnesses(
    graph: &mut GraphBuilder,
    hit: &Value,
    ordinal: usize,
    session: Option<&str>,
    instances: &RuntimeInstances,
    budget: &WorkBudget,
) -> Result<()> {
    let steps = array_field(hit, "steps");
    for (guard_index, guard) in array_field(hit, "observed_guard_witnesses")
        .iter()
        .enumerate()
    {
        budget.consume(1)?;
        let Some(step_index) =
            u64_field(guard, "step_index").and_then(|index| usize::try_from(index).ok())
        else {
            continue;
        };
        let Some(step) = steps.get(step_index) else {
            continue;
        };
        let identity = exact_guard_identity(guard, step, session, instances, budget)?;
        let exact = identity.is_some();
        let guard_id = format!("observed-guard:{ordinal}:{guard_index}");
        graph.insert_node(
            guard_id.clone(),
            json!({
                "type":"observed_guard",
                "witness":guard,
                "exact_original_ast":exact,
                "concrete_observation_only":true,
                "complete_execution_path":false,
            }),
        )?;
        graph.add_edge(
            &format!("observed-step:{ordinal}:{step_index}"),
            &guard_id,
            if exact {
                "observed_ast_guard_value"
            } else {
                "observed_guard_candidate"
            },
            json!({"exact_original_ast":exact,"concrete_observation_only":true}),
        )?;
        if !exact {
            continue;
        }
        let selected_arm = if guard["observed_value"] == true {
            "consequent"
        } else {
            "alternate"
        };
        if nonempty_string_field(guard, "next_pause_in_selected_arm") != Some(selected_arm) {
            continue;
        }
        let Some(next) = steps.get(step_index + 1) else {
            continue;
        };
        if !same_verified_stack_shape(step, next, budget, |script, sha| {
            session.is_some_and(|session| instances.exact_node(session, script, sha).is_some())
        })? {
            continue;
        }
        if !array_field(next, "frames")
            .first()
            .and_then(|frame| frame.get("location"))
            .is_some_and(|location| {
                u64_field(location, "lineNumber").is_some()
                    && u64_field(location, "columnNumber").is_some()
            })
        {
            continue;
        }
        graph.add_edge(
            &guard_id,
            &format!("observed-step:{ordinal}:{}", step_index + 1),
            "observed_next_pause_in_selected_arm",
            json!({"arm":selected_arm,"same_verified_stack_shape":true,"same_activation_proven":false,"concrete_observation_only":true}),
        )?;
    }
    Ok(())
}

fn add_observed_callable_witnesses(
    graph: &mut GraphBuilder,
    hit: &Value,
    session: Option<&str>,
    node_id: &str,
    runtime_node_by_instance: &RuntimeInstances,
    budget: &WorkBudget,
) -> Result<()> {
    for scope in array_field(hit, "scopes") {
        budget.consume(1)?;
        let scope_type = nonempty_string_field(scope, "type").unwrap_or("unknown");
        for variable in array_field(scope, "variables") {
            budget.consume(1)?;
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
        budget.consume(1)?;
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
pub(super) fn seed_selective_trace_witnesses(
    graph: &mut GraphBuilder,
    selective_trace: &Value,
    runtime_node_by_instance: &RuntimeInstances,
    budget: &WorkBudget,
) -> Result<()> {
    // Concrete debugger pauses are observed state witnesses, not static edges.
    // Only verified (CDP session, script ID, captured source SHA) triples
    // receive a provenance edge to the matching runtime script instance.
    for (ordinal, hit) in array_field(selective_trace, "hits").iter().enumerate() {
        budget.consume(1)?;
        let node_id = format!("observed-invocation:{ordinal}");
        graph.insert_node(
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
        let session = session_name(hit.get("cdpSession"));
        add_observed_pause_frames(
            graph,
            hit,
            session,
            &node_id,
            runtime_node_by_instance,
            budget,
        )?;
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
        add_observed_guard_witnesses(
            graph,
            hit,
            ordinal,
            session,
            runtime_node_by_instance,
            budget,
        )?;
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

#[cfg(test)]
mod tests {
    use super::super::runtime_evidence::seed_runtime_script_evidence;
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn unscoped_trace_hits_retain_observations_without_main_source_proof() -> Result<()> {
        let digest = "a".repeat(64);
        let frame = json!({"source_identity":"exact","sourceSha256":digest,"location":{"scriptId":7,"lineNumber":1,"columnNumber":2}});
        let hit = |session: Value| json!({"cdpSession":session,"frames":[frame],"steps":[{"frames":[frame]}]});
        let mut absent = hit(Value::Null);
        absent
            .as_object_mut()
            .ok_or_else(|| anyhow::anyhow!("fixture hit"))?
            .remove("cdpSession");
        let trace = json!({"hits":[hit(json!("main")),hit(json!(true)),hit(json!("")),absent]});
        let mut index = RuntimeInstances::default();
        index.register("main", "7", &digest);
        let mut graph = GraphBuilder::default();
        seed_selective_trace_witnesses(
            &mut graph,
            &trace,
            &index,
            &WorkBudget::unlimited("unscoped-trace"),
        )?;
        for ordinal in 0..4 {
            let invocation = format!("observed-invocation:{ordinal}");
            let step = format!("observed-step:{ordinal}:0");
            assert!(graph.node(&invocation).is_some());
            assert!(graph.node(&step).is_some());
            assert!(graph.edges().values().any(|edge| edge["from"] == invocation
                && edge["to"] == step
                && edge["kind"] == "observed_next_step"));
            assert_eq!(
                graph
                    .edges()
                    .values()
                    .filter(|edge| (edge["to"] == invocation
                        && edge["kind"] == "observed_paused_call_frame")
                        || (edge["to"] == step && edge["kind"] == "observed_executed_location"))
                    .count(),
                if ordinal == 0 { 2 } else { 0 }
            );
        }
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
                "location":{"scriptId":"7","lineNumber":1,"columnNumber":2},
                "functionLocation":{"scriptId":"7","lineNumber":0,"columnNumber":0}
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
        let guard = |sha: &str| json!({"step_index":0,"script_id":"7","source_sha256":sha,"guard_start_byte":10,"test_start_byte":13,"test_end_byte":14,"expression":"x","observed_value":true,"next_pause_in_selected_arm":"consequent","evidence":"exact_source_ast_and_boolean_pause"});
        let step = |sha: &str| json!({"frames":[exact_frame(sha)],"expressions":[{"status":"observed","expression":"x","value":{"type":"boolean","value":true}}]});
        let mut next = step(&second);
        next["frames"][0]["location"]["columnNumber"] = json!(5);
        let trace = json!({"hits":[
            {"cdpSession":"worker","frames":[exact_frame(&first)],
             "steps":[step(&first)],"observed_guard_witnesses":[guard(&first)],
             "scopes":[callable(&first)]},
            {"cdpSession":"other","frames":[exact_frame(&second)],
             "steps":[step(&second),next],
             "observed_guard_witnesses":[guard(&second)],
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
        let instances = &runtime_index;
        assert!(instances
            .observed_node("worker", &json!("7"), None)
            .is_none());
        assert_eq!(
            instances.observed_node("other", &json!("7"), None),
            Some(format!("runtime:{}", &second[..20]))
        );
        seed_selective_trace_witnesses(&mut graph, &trace, instances, &budget)?;
        let identity_edges = graph
            .edges()
            .values()
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
            4,
            "only the unambiguous session may prove identity"
        );
        assert!(identity_edges.iter().all(|edge| {
            edge["from"] == format!("runtime:{}", &second[..20])
                && edge["cdp_session"] == "other"
                && edge["script_id"] == "7"
                && edge["source_sha256"] == second
        }));
        assert!(graph.has_node("observed-invocation:0"));
        assert_eq!(
            graph.node_value("observed-guard:0:0")["exact_original_ast"],
            false
        );
        assert_eq!(
            graph.node_value("observed-guard:1:0")["exact_original_ast"],
            true
        );
        assert!(graph
            .edges()
            .values()
            .any(|edge| edge["kind"] == "observed_guard_candidate"
                && edge["to"] == "observed-guard:0:0"));
        assert!(graph.has_node("observed-step:0:0"));
        assert_eq!(
            graph.node_value("observed-step:0:0")["complete_execution_path"],
            false
        );
        assert_eq!(
            graph.node_value("observed-step:1:1")["complete_execution_path"],
            false
        );
        assert_eq!(
            graph.node_value("observed-guard:1:0")["concrete_observation_only"],
            true
        );
        assert!(graph
            .edges()
            .values()
            .any(|edge| edge["kind"] == "observed_ast_guard_value"));
        assert!(graph.edges().values().any(|edge| {
            edge["kind"] == "observed_next_pause_in_selected_arm"
                && edge["to"] == "observed-step:1:1"
        }));
        assert!(!graph
            .edges()
            .values()
            .any(|edge| edge["to"] == "observed-step:2:0"
                && edge["kind"] == "observed_executed_location"));
        let mut uncertain = trace["hits"][1].clone();
        let outer = json!({"source_identity":"exact","sourceSha256":"c".repeat(64),"location":{"scriptId":"99","lineNumber":1,"columnNumber":0},"functionLocation":{"scriptId":"99","lineNumber":0,"columnNumber":0}});
        for step in uncertain["steps"]
            .as_array_mut()
            .ok_or_else(|| anyhow::anyhow!("steps"))?
        {
            step["frames"]
                .as_array_mut()
                .ok_or_else(|| anyhow::anyhow!("frames"))?
                .push(outer.clone());
        }
        let mut graph = GraphBuilder::default();
        seed_selective_trace_witnesses(
            &mut graph,
            &json!({"hits":[uncertain]}),
            instances,
            &budget,
        )?;
        assert!(graph
            .edges()
            .values()
            .any(|edge| edge["kind"] == "observed_ast_guard_value"));
        assert!(!graph
            .edges()
            .values()
            .any(|edge| edge["kind"] == "observed_next_pause_in_selected_arm"));
        Ok(())
    }

    #[test]
    fn exact_guard_requires_matching_boolean_pause_and_source_coordinates() -> Result<()> {
        let (sha, runtime, trace) = conflicting_runtime_instance_fixture();
        let budget = WorkBudget::unlimited("guard-identity");
        let mut graph = GraphBuilder::default();
        let index = seed_runtime_script_evidence(
            &mut graph,
            &runtime,
            &json!({}),
            &json!({}),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &budget,
        )?;
        let mut hit = trace["hits"][1].clone();
        let guard = hit["observed_guard_witnesses"][0].clone();
        let step = hit["steps"][0].clone();
        assert!(exact_guard_identity(&guard, &step, Some("other"), &index, &budget)?.is_some());
        let mut wrong = guard.clone();
        wrong["source_sha256"] = json!(format!("{}{}", &sha[..20], "c".repeat(44)));
        assert!(exact_guard_identity(&wrong, &step, Some("other"), &index, &budget)?.is_none());
        let mut wrong = guard.clone();
        wrong["observed_value"] = json!(false);
        assert!(exact_guard_identity(&wrong, &step, Some("other"), &index, &budget)?.is_none());
        let mut wrong_step = step.clone();
        wrong_step["frames"][0]["location"]["lineNumber"] = Value::Null;
        assert!(
            exact_guard_identity(&guard, &wrong_step, Some("other"), &index, &budget)?.is_none()
        );
        hit["steps"][1]["frames"][0]["functionLocation"]["lineNumber"] = json!(9);
        seed_selective_trace_witnesses(&mut graph, &json!({"hits":[hit]}), &index, &budget)?;
        assert!(graph
            .edges()
            .values()
            .any(|edge| edge["kind"] == "observed_ast_guard_value"));
        assert!(!graph
            .edges()
            .values()
            .any(|edge| edge["kind"] == "observed_next_pause_in_selected_arm"));
        let limited = WorkBudget::new("guard-budget", work_budget::BudgetLimits::work(0));
        assert!(exact_guard_identity(&guard, &step, Some("other"), &index, &limited).is_err());
        Ok(())
    }
}
