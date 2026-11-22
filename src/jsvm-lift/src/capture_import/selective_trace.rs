//! Verified, selective CDP breakpoint witnesses from a concrete browser run.
use crate::{
    analysis_artifacts::{load_artifact, write_artifact, RUNTIME_SCRIPTS, SELECTIVE_TRACE},
    analysis_budget::AnalysisBudgets,
    runtime_identity::{script_id_text, session_name, ScriptIdentityIndex},
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::{fs, path::Path};
use work_budget::WorkBudget;

/// Verify an inspector-provided definition against the captured script
/// inventory. This proves the code location of one observed function value,
/// not that the function was invoked or selected for every possible input.
fn verify_function_definition(
    value: &mut Value,
    session: Option<&str>,
    identities: &ScriptIdentityIndex<String>,
    verified: &mut u64,
    unresolved: &mut u64,
) {
    let Some(definition) = value.get_mut("functionDefinition") else {
        return;
    };
    let script = definition.get("scriptId").and_then(script_id_text);
    let evidence = definition.get("evidence").and_then(Value::as_str);
    let line = definition.get("lineNumber").and_then(Value::as_u64);
    let column = definition.get("columnNumber").and_then(Value::as_u64);
    let exact = (|| {
        if evidence != Some("Runtime.getProperties.internalProperties.[[FunctionLocation]]")
            || line.is_none()
            || column.is_none()
        {
            return None;
        }
        let script = script?;
        identities.get(session?, &script).map(String::as_str)
    })();
    if let Some(sha) = exact {
        definition["source_identity"] = json!("exact");
        definition["sourceSha256"] = json!(sha);
        *verified += 1;
    } else {
        definition["source_identity"] = json!("unresolved");
        *unresolved += 1;
    }
}

fn verify_observed_frame_source(
    frame: &mut Value,
    session: Option<&str>,
    identities: &ScriptIdentityIndex<String>,
) -> bool {
    let script = frame
        .get("location")
        .and_then(|location| location.get("scriptId"))
        .and_then(script_id_text);
    let reported = frame.get("sourceSha256").and_then(Value::as_str);
    let actual = script
        .and_then(|id| identities.get(session?, &id))
        .map(String::as_str);
    let exact = actual.is_some() && actual == reported;
    frame["source_identity"] = json!(if exact { "exact" } else { "unresolved" });
    exact
}

#[derive(Default)]
struct VerificationCounts {
    verified: u64,
    unresolved: u64,
}

impl VerificationCounts {
    fn frames(
        &mut self,
        frames: &mut [Value],
        session: Option<&str>,
        identities: &ScriptIdentityIndex<String>,
        budget: &WorkBudget,
    ) -> Result<()> {
        for frame in frames {
            budget.consume(1)?;
            if verify_observed_frame_source(frame, session, identities) {
                self.verified += 1;
            } else {
                self.unresolved += 1;
            }
        }
        Ok(())
    }

    fn definition(
        &mut self,
        value: &mut Value,
        session: Option<&str>,
        identities: &ScriptIdentityIndex<String>,
    ) {
        verify_function_definition(
            value,
            session,
            identities,
            &mut self.verified,
            &mut self.unresolved,
        );
    }
}

#[derive(Default)]
struct TraceVerification {
    hit_frames: VerificationCounts,
    step_frames: VerificationCounts,
    definitions: VerificationCounts,
}

impl TraceVerification {
    fn verify_hit(
        &mut self,
        hit: &mut Value,
        identities: &ScriptIdentityIndex<String>,
        budget: &WorkBudget,
    ) -> Result<()> {
        budget.consume(1)?;
        let session = session_name(hit.get("cdpSession")).map(ToOwned::to_owned);
        let frames = hit
            .get_mut("frames")
            .and_then(Value::as_array_mut)
            .context("trace hit missing frames[]")?;
        self.hit_frames
            .frames(frames, session.as_deref(), identities, budget)?;
        self.verify_steps(hit, session.as_deref(), identities, budget)?;
        self.verify_definitions(hit, session.as_deref(), identities, budget)
    }

    fn verify_steps(
        &mut self,
        hit: &mut Value,
        session: Option<&str>,
        identities: &ScriptIdentityIndex<String>,
        budget: &WorkBudget,
    ) -> Result<()> {
        let steps = hit.get_mut("steps").and_then(Value::as_array_mut);
        if let Some(steps) = steps {
            if steps.len() > 32 {
                bail!("observed path has more than 32 bounded debugger step events");
            }
            for (index, step) in steps.iter_mut().enumerate() {
                budget.consume(1)?;
                if step.get("index").and_then(Value::as_u64) != Some(index as u64) {
                    bail!("observed path step indices must be sequential");
                }
                let frames = step
                    .get_mut("frames")
                    .and_then(Value::as_array_mut)
                    .context("observed path step requires frames[]")?;
                self.step_frames
                    .frames(frames, session, identities, budget)?;
            }
        }
        Ok(())
    }

    fn verify_definitions(
        &mut self,
        hit: &mut Value,
        session: Option<&str>,
        identities: &ScriptIdentityIndex<String>,
        budget: &WorkBudget,
    ) -> Result<()> {
        for scope in hit
            .get_mut("scopes")
            .and_then(Value::as_array_mut)
            .into_iter()
            .flatten()
        {
            budget.consume(1)?;
            for variable in scope
                .get_mut("variables")
                .and_then(Value::as_array_mut)
                .into_iter()
                .flatten()
            {
                budget.consume(1)?;
                if let Some(value) = variable.get_mut("value") {
                    self.definitions.definition(value, session, identities);
                }
            }
        }
        for expression in hit
            .get_mut("expressions")
            .and_then(Value::as_array_mut)
            .into_iter()
            .flatten()
        {
            budget.consume(1)?;
            if expression.get("status").and_then(Value::as_str) != Some("observed") {
                continue;
            }
            if let Some(value) = expression.get_mut("value") {
                self.definitions.definition(value, session, identities);
            }
        }
        Ok(())
    }

    fn publish_summary(&self, trace: &mut Value) {
        trace["schema"] = json!(SELECTIVE_TRACE.schema);
        trace["summary"]["verifiedSourceFrames"] = json!(self.hit_frames.verified);
        trace["summary"]["unresolvedSourceFrames"] = json!(self.hit_frames.unresolved);
        trace["summary"]["verifiedStepFrames"] = json!(self.step_frames.verified);
        trace["summary"]["unresolvedStepFrames"] = json!(self.step_frames.unresolved);
        trace["summary"]["verifiedFunctionDefinitions"] = json!(self.definitions.verified);
        trace["summary"]["unresolvedFunctionDefinitions"] = json!(self.definitions.unresolved);
    }
}

pub(super) fn import_selective_trace(
    capture: &Path,
    project: &Path,
    budgets: &AnalysisBudgets,
) -> Result<()> {
    let path = capture.join("selective-trace.json");
    if !path.is_file() {
        return Ok(());
    }
    let budget = budgets.scope("selective-breakpoint-trace");
    let mut trace: Value = serde_json::from_slice(&fs::read(&path)?)
        .with_context(|| format!("parsing {}", path.display()))?;
    if trace.get("schema").and_then(Value::as_str) != Some("js-redox/selective-breakpoint-trace/v1")
    {
        bail!("invalid or unsupported selective breakpoint trace");
    }
    let runtime = load_artifact(project, RUNTIME_SCRIPTS)
        .context("runtime inventory required for breakpoint source verification")?;
    let identities =
        ScriptIdentityIndex::from_runtime_report(&runtime, &budget, |sha, _, _| sha.to_owned())?;
    let mut verification = TraceVerification::default();
    let hits = trace
        .get_mut("hits")
        .and_then(Value::as_array_mut)
        .context("selective trace requires hits[]")?;
    for hit in hits {
        verification.verify_hit(hit, &identities, &budget)?;
    }
    verification.publish_summary(&mut trace);
    write_artifact(project, SELECTIVE_TRACE, &trace)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn source_identity_requires_exact_session_script_and_hash() -> Result<()> {
        let temp = TempDir::new()?;
        let capture = temp.path().join("capture");
        let project = temp.path().join("project");
        fs::create_dir_all(&capture)?;
        fs::create_dir_all(&project)?;
        write_artifact(
            &project,
            RUNTIME_SCRIPTS,
            &json!({
                "schema":RUNTIME_SCRIPTS.schema,
                "script_identity_conflicts":[{"cdp_session":"main","script_id":"8","sha256_claims":["abc","missing-body"]}],
                "sources":[{"sha256":"abc", "script_instances":[{"cdp_session":"main","script_id":"6"},{"cdp_session":"main","script_id":"8"}]}],
                "alpine_families":[], "gtm_families":[], "summary":{}
            }),
        )?;
        fs::write(
            capture.join("selective-trace.json"),
            serde_json::to_vec(&json!({
                "schema":"js-redox/selective-breakpoint-trace/v1",
                "summary":{"capturedHits":1},"errors":[],
                "hits":[{"cdpSession":"main", "frames":[
                    {"location":{"scriptId":"6"},"sourceSha256":"abc"},
                    {"location":{"scriptId":"6"},"sourceSha256":"other"},
                    {"location":{"scriptId":"8"},"sourceSha256":"abc"}
                ], "steps":[{"index":0,"frames":[
                    {"location":{"scriptId":"6","lineNumber":2,"columnNumber":1},"sourceSha256":"abc"},
                    {"location":{"scriptId":"8","lineNumber":2,"columnNumber":1},"sourceSha256":"abc"}
                ]}], "scopes":[{"type":"local","variables":[
                    {"name":"handler","value":{"type":"function","functionDefinition":{
                        "scriptId":"6","lineNumber":0,"columnNumber":21,
                        "evidence":"Runtime.getProperties.internalProperties.[[FunctionLocation]]"}}},
                    {"name":"ambiguous","value":{"type":"function","functionDefinition":{
                        "scriptId":"8","lineNumber":0,"columnNumber":0,
                        "evidence":"Runtime.getProperties.internalProperties.[[FunctionLocation]]"}}}
                ]}], "expressions":[
                    {"expression":"handler","status":"observed","value":{"type":"function",
                        "functionDefinition":{"scriptId":"6","lineNumber":0,"columnNumber":21,
                        "evidence":"Runtime.getProperties.internalProperties.[[FunctionLocation]]"}}},
                    {"expression":"ignored","status":"evaluation_rejected","value":{"type":"function",
                        "functionDefinition":{"scriptId":"6","lineNumber":0,"columnNumber":0,
                        "evidence":"Runtime.getProperties.internalProperties.[[FunctionLocation]]"}}},
                    {"expression":"fabricated","status":"observed","value":{"type":"function",
                        "functionDefinition":{"scriptId":"6","lineNumber":0,"columnNumber":0,
                        "evidence":"unsupported"}}}
                ]}]
            }))?,
        )?;
        import_selective_trace(&capture, &project, &AnalysisBudgets::standard("fixture"))?;
        let result = load_artifact(&project, SELECTIVE_TRACE).context("missing trace")?;
        assert_eq!(result["summary"]["verifiedSourceFrames"], 1);
        assert_eq!(result["summary"]["unresolvedSourceFrames"], 2);
        assert_eq!(result["summary"]["verifiedStepFrames"], 1);
        assert_eq!(result["summary"]["unresolvedStepFrames"], 1);
        assert_eq!(
            result["hits"][0]["steps"][0]["frames"][0]["source_identity"],
            "exact"
        );
        assert_eq!(
            result["hits"][0]["steps"][0]["frames"][1]["source_identity"],
            "unresolved"
        );
        assert_eq!(result["hits"][0]["frames"][0]["source_identity"], "exact");
        assert_eq!(result["summary"]["verifiedFunctionDefinitions"], 2);
        assert_eq!(result["summary"]["unresolvedFunctionDefinitions"], 2);
        assert_eq!(
            result["hits"][0]["scopes"][0]["variables"][0]["value"]["functionDefinition"]
                ["source_identity"],
            "exact"
        );
        assert_eq!(
            result["hits"][0]["scopes"][0]["variables"][0]["value"]["functionDefinition"]
                ["sourceSha256"],
            "abc"
        );
        assert_eq!(
            result["hits"][0]["scopes"][0]["variables"][1]["value"]["functionDefinition"]
                ["source_identity"],
            "unresolved"
        );
        assert!(
            result["hits"][0]["expressions"][0]["value"]["functionDefinition"]["sourceSha256"]
                .as_str()
                .is_some()
        );
        Ok(())
    }
}
