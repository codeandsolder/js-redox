//! Verified, selective CDP breakpoint witnesses from a concrete browser run.
use crate::{
    analysis_artifacts::{load_artifact, write_artifact, RUNTIME_SCRIPTS, SELECTIVE_TRACE},
    analysis_budget::AnalysisBudgets,
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::{collections::HashMap, fs, path::Path};

/// Verify an inspector-provided definition against the captured script
/// inventory. This proves the code location of one observed function value,
/// not that the function was invoked or selected for every possible input.
fn verify_function_definition(
    value: &mut Value,
    session: &str,
    identities: &HashMap<(String, String), Option<String>>,
    verified: &mut u64,
    unresolved: &mut u64,
) {
    let Some(definition) = value.get_mut("functionDefinition") else {
        return;
    };
    let script = definition.get("scriptId").and_then(Value::as_str);
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
        identities
            .get(&(session.to_owned(), script.to_owned()))
            .and_then(Option::as_deref)
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
    let runtime = load_artifact(project, RUNTIME_SCRIPTS, false)?
        .context("runtime inventory required for breakpoint source verification")?;
    let mut identities = HashMap::<(String, String), Option<String>>::new();
    for source in runtime
        .get("sources")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        budget.consume(1)?;
        let Some(sha) = source.get("sha256").and_then(Value::as_str) else {
            continue;
        };
        for instance in source
            .get("script_instances")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            budget.consume(1)?;
            let Some(session) = instance.get("cdp_session").and_then(Value::as_str) else {
                continue;
            };
            let Some(script) = instance.get("script_id").and_then(Value::as_str) else {
                continue;
            };
            let key = (session.to_owned(), script.to_owned());
            match identities.get(&key) {
                Some(Some(previous)) if previous != sha => {
                    identities.insert(key, None);
                }
                Some(None) => {}
                _ => {
                    identities.insert(key, Some(sha.to_owned()));
                }
            }
        }
    }
    let mut verified = 0_u64;
    let mut unresolved = 0_u64;
    let mut verified_definitions = 0_u64;
    let mut unresolved_definitions = 0_u64;
    let hits = trace
        .get_mut("hits")
        .and_then(Value::as_array_mut)
        .context("selective trace requires hits[]")?;
    for hit in hits {
        budget.consume(1)?;
        let session = hit
            .get("cdpSession")
            .and_then(Value::as_str)
            .context("trace hit missing cdpSession")?
            .to_owned();
        let frames = hit
            .get_mut("frames")
            .and_then(Value::as_array_mut)
            .context("trace hit missing frames[]")?;
        for frame in frames {
            budget.consume(1)?;
            let script = frame
                .get("location")
                .and_then(|location| location.get("scriptId"))
                .and_then(Value::as_str);
            let reported = frame.get("sourceSha256").and_then(Value::as_str);
            let actual = script
                .and_then(|id| identities.get(&(session.clone(), id.to_owned())))
                .and_then(Option::as_deref);
            let exact = actual.is_some() && actual == reported;
            frame["source_identity"] = json!(if exact { "exact" } else { "unresolved" });
            if exact {
                verified += 1;
            } else {
                unresolved += 1;
            }
        }
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
                    verify_function_definition(
                        value,
                        &session,
                        &identities,
                        &mut verified_definitions,
                        &mut unresolved_definitions,
                    );
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
                verify_function_definition(
                    value,
                    &session,
                    &identities,
                    &mut verified_definitions,
                    &mut unresolved_definitions,
                );
            }
        }
    }
    trace["schema"] = json!(SELECTIVE_TRACE.schema);
    trace["summary"]["verifiedSourceFrames"] = json!(verified);
    trace["summary"]["unresolvedSourceFrames"] = json!(unresolved);
    trace["summary"]["verifiedFunctionDefinitions"] = json!(verified_definitions);
    trace["summary"]["unresolvedFunctionDefinitions"] = json!(unresolved_definitions);
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
                "sources":[{"sha256":"abc", "script_instances":[{"cdp_session":"main","script_id":"6"}]}],
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
                ], "scopes":[{"type":"local","variables":[
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
        let result = load_artifact(&project, SELECTIVE_TRACE, false)?.context("missing trace")?;
        assert_eq!(result["summary"]["verifiedSourceFrames"], 1);
        assert_eq!(result["summary"]["unresolvedSourceFrames"], 2);
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
