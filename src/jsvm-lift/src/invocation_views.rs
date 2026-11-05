//! Human-readable browser execution witnesses with exact original-source context.
//! This is evidence from a particular paused invocation, never a general proof.
use crate::{
    analysis_artifacts::{load_artifact, write_artifact, RUNTIME_SCRIPTS, SELECTIVE_TRACE},
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    sha256_hex,
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, HashMap},
    fs,
    path::Path,
};

fn fence(value: &str, language: &str) -> String {
    let longest = value.split(|ch| ch != '~').map(str::len).max().unwrap_or(0);
    let border = "~".repeat((longest + 1).max(3));
    format!("{border}{language}\n{value}\n{border}\n")
}

fn display_json(value: &Value) -> Result<String> {
    let raw = serde_json::to_string_pretty(value)?;
    let limit = 16_000;
    if raw.chars().count() <= limit {
        return Ok(fence(&raw, "json"));
    }
    let shortened = raw.chars().take(limit).collect::<String>();
    Ok(fence(&format!("{shortened}\n... truncated in this view; complete values remain in analysis/selective-trace.json"), "text"))
}

fn verified_sha(value: &Value) -> Option<&str> {
    value
        .as_str()
        .filter(|digest| digest.len() == 64 && digest.bytes().all(|byte| byte.is_ascii_hexdigit()))
}

fn source_excerpt(raw: &str, line: u64, first_line: Option<u64>) -> String {
    let Some(start) = first_line else {
        return "CDP script start offset was not recorded; raw source link is authoritative.\n"
            .into();
    };
    let Some(local_line) = line
        .checked_sub(start)
        .and_then(|v| usize::try_from(v).ok())
    else {
        return "Paused location precedes the script start offset; no excerpt claimed.\n".into();
    };
    let lines = raw.lines().collect::<Vec<_>>();
    if local_line >= lines.len() {
        return "Paused location is outside the captured raw source lines; no excerpt claimed.\n"
            .into();
    }
    let begin = local_line.saturating_sub(2);
    let end = (local_line + 3).min(lines.len());
    let mut excerpt = String::new();
    for (index, text) in lines.iter().enumerate().take(end).skip(begin) {
        let shown = text.chars().take(260).collect::<String>();
        let cropped = if text.chars().count() > 260 {
            " …"
        } else {
            ""
        };
        excerpt.push_str(&format!(
            "{} {:>6} | {shown}{cropped}\n",
            if index == local_line { ">" } else { " " },
            index + 1 + usize::try_from(start).unwrap_or(0),
        ));
    }
    fence(excerpt.trim_end(), "js")
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RuntimeSourceIdentity {
    sha256: String,
    start_line: Option<u64>,
    capture_instrumentation: bool,
}

type RuntimeIdentityIndex = HashMap<(String, String), Option<RuntimeSourceIdentity>>;

fn runtime_identity_index(runtime: &Value) -> RuntimeIdentityIndex {
    let mut found = HashMap::new();
    for source in runtime
        .get("sources")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        let Some(sha) = source.get("sha256").and_then(verified_sha) else {
            continue;
        };
        for instance in source
            .get("script_instances")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let Some(session) = instance.get("cdp_session").and_then(Value::as_str) else {
                continue;
            };
            let Some(script) = instance.get("script_id").and_then(Value::as_str) else {
                continue;
            };
            let next = RuntimeSourceIdentity {
                sha256: sha.to_owned(),
                start_line: instance.get("start_line").and_then(Value::as_u64),
                capture_instrumentation: source.get("classification").and_then(Value::as_str)
                    == Some("capture_instrumentation"),
            };
            let key = (session.to_owned(), script.to_owned());
            match found.get(&key) {
                Some(Some(previous)) if previous != &next => {
                    found.insert(key, None);
                }
                Some(None) => {}
                _ => {
                    found.insert(key, Some(next));
                }
            }
        }
    }
    found
}

/// Group source definitions by exact script and original coordinate, not by
/// display name or inspector handle. Multiple function objects may share one
/// definition site; observations remain separate from reference equality.
fn append_observed_callable_definitions(
    page: &mut String,
    project: &Path,
    identities: &RuntimeIdentityIndex,
    session: &str,
    hit: &Value,
) -> Result<()> {
    let mut sites = BTreeMap::<(String, String, u64, u64), Vec<Value>>::new();
    let mut add = |value: &Value, seen_as: Value| {
        let Some(definition) = value.get("functionDefinition") else {
            return;
        };
        if definition.get("source_identity").and_then(Value::as_str) != Some("exact") {
            return;
        }
        let Some(script) = definition.get("scriptId").and_then(Value::as_str) else {
            return;
        };
        let Some(sha) = definition.get("sourceSha256").and_then(verified_sha) else {
            return;
        };
        let (Some(line), Some(column)) = (
            definition.get("lineNumber").and_then(Value::as_u64),
            definition.get("columnNumber").and_then(Value::as_u64),
        ) else {
            return;
        };
        if identities
            .get(&(session.to_owned(), script.to_owned()))
            .and_then(Option::as_ref)
            .is_none_or(|identity| identity.sha256 != sha)
        {
            return;
        }
        sites
            .entry((script.to_owned(), sha.to_owned(), line, column))
            .or_default()
            .push(seen_as);
    };
    for scope in hit
        .get("scopes")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        for variable in scope
            .get("variables")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            add(
                &variable["value"],
                json!({
                    "kind":"scope",
                    "scope_type":scope.get("type"),
                    "variable":variable.get("name"),
                }),
            );
        }
    }
    for expression in hit
        .get("expressions")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        if expression.get("status").and_then(Value::as_str) != Some("observed") {
            continue;
        }
        add(
            &expression["value"],
            json!({
                "kind":"expression", "expression":expression.get("expression")
            }),
        );
    }
    if sites.is_empty() {
        return Ok(());
    }
    page.push_str("## Verified observed callable definitions\n\n");
    page.push_str("These are source definitions of function values **observed at this pause**, not proof that a function was called or is selected for every input.\n\n");
    for ((script, sha, line, column), seen_as) in sites {
        let location = identities
            .get(&(session.to_owned(), script.clone()))
            .and_then(Option::as_ref)
            .context("missing verified runtime source location")?;
        let raw_path = format!("resources/runtime-scripts/{sha}.js");
        let bytes = fs::read(project.join(&raw_path))
            .with_context(|| format!("missing original callable definition source {sha}"))?;
        if sha256_hex(&bytes) != sha {
            bail!("original callable definition hash mismatch: {sha}");
        }
        let source = String::from_utf8(bytes)
            .with_context(|| format!("non-UTF8 callable definition source: {sha}"))?;
        page.push_str(&format!(
            "### V8 script {script}, original line {}, column {} (1-based)\n\n",
            line.saturating_add(1),
            column.saturating_add(1),
        ));
        page.push_str(&format!(
            "Source SHA-256: **{sha}**. [Original code](../../../resources/runtime-scripts/{sha}.js).\n\n"
        ));
        let readable = format!("src/_readable/runtime-scripts/{sha}.js");
        if project.join(&readable).is_file() {
            page.push_str(&format!("[Shared readable code](../../../{readable}) — original V8 coordinates do not apply to transformed code.\n\n"));
        }
        page.push_str("Observed references to this **definition site**:\n\n");
        page.push_str(&display_json(&json!(seen_as))?);
        page.push('\n');
        page.push_str(&source_excerpt(&source, line, location.start_line));
        page.push('\n');
    }
    Ok(())
}

/// Render a separate sequential execution witness; never filter unreachable
/// branches or replace a general source tree based on a single observed run.
fn build_observed_path_view(
    project: &Path,
    identities: &RuntimeIdentityIndex,
    session: &str,
    hit: &Value,
    ordinal: usize,
) -> Result<String> {
    let steps = hit
        .get("steps")
        .and_then(Value::as_array)
        .context("path view requires bounded steps[]")?;
    let mut page = format!(
        "# Observed execution path {ordinal:04}\n\n         This is an **ordered sequence of {} debugger step pauses** in CDP session {session}.          It is not a complete or universally feasible program path, and debugger instrumentation          may perturb timing. Source excerpts refer to original captured code only.\n\n",
        steps.len()
    );
    page.push_str(&format!(
        "Requested mode: {}. Capture status: {}.\n\n",
        hit.get("pathWitnessMode")
            .and_then(Value::as_str)
            .unwrap_or("unknown"),
        hit.get("pathWitnessStatus")
            .and_then(Value::as_str)
            .unwrap_or("unknown"),
    ));
    for (index, step) in steps.iter().enumerate() {
        let top = step
            .get("frames")
            .and_then(Value::as_array)
            .and_then(|frames| frames.first());
        let Some(top) = top else {
            page.push_str(&format!("## Step {index}: no executing frame captured\n\n"));
            continue;
        };
        let function = top
            .get("functionName")
            .and_then(Value::as_str)
            .filter(|s| !s.is_empty())
            .unwrap_or("<anonymous>");
        let location = &top["location"];
        let script = location
            .get("scriptId")
            .and_then(Value::as_str)
            .unwrap_or("?");
        let line = location.get("lineNumber").and_then(Value::as_u64);
        let column = location.get("columnNumber").and_then(Value::as_u64);
        page.push_str(&format!(
            "## Step {index}: {}\n\nV8 script **{script}**, original line {}, column {} (zero-based).\n\n",
            function.replace('\n', " "),
            line.map_or_else(|| "?".to_owned(), |v| v.to_string()),
            column.map_or_else(|| "?".to_owned(), |v| v.to_string()),
        ));
        let sha = top.get("sourceSha256").and_then(verified_sha);
        let identity = identities
            .get(&(session.to_owned(), script.to_owned()))
            .and_then(Option::as_ref);
        let exact = top.get("source_identity").and_then(Value::as_str) == Some("exact")
            && sha.is_some()
            && identity.is_some_and(|source| Some(source.sha256.as_str()) == sha);
        if exact {
            let sha = sha.context("checked exact original step source")?;
            let raw_path = format!("resources/runtime-scripts/{sha}.js");
            if identity.is_some_and(|source| source.capture_instrumentation)
                && !project.join(&raw_path).is_file()
            {
                page.push_str(&format!(
                    "Exact captured script SHA-256 **{sha}**; this is **recorder instrumentation**,                      intentionally excluded from the recovered application source tree.                      No original-source excerpt or application link is claimed.\n\n"
                ));
            } else {
                let bytes = fs::read(project.join(&raw_path)).with_context(|| {
                    format!("missing original application execution step source {sha}")
                })?;
                if sha256_hex(&bytes) != sha {
                    bail!("original execution step source hash mismatch: {sha}");
                }
                let raw = String::from_utf8(bytes)
                    .with_context(|| format!("execution step code is not UTF-8: {sha}"))?;
                page.push_str(&format!(
                    "Verified [original source](../../../{raw_path}), SHA-256 **{sha}**.\n\n"
                ));
                let readable = format!("src/_readable/runtime-scripts/{sha}.js");
                if project.join(&readable).is_file() {
                    page.push_str(&format!(
                        "[General safe-readable view](../../../{readable}) (different source offsets).\n\n"
                    ));
                }
                if let Some(line) = line {
                    page.push_str(&source_excerpt(
                        &raw,
                        line,
                        identity.and_then(|source| source.start_line),
                    ));
                    page.push('\n');
                }
            }
        } else {
            page.push_str("Original source identity **unresolved**; no code excerpt claimed.\n\n");
        }
        let expressions = step.get("expressions").and_then(Value::as_array);
        if expressions.is_some_and(|items| !items.is_empty()) {
            page.push_str("Expressions evaluated at this pause (rejected/unavailable results remain explicitly marked):\n\n");
            page.push_str(&display_json(&json!(expressions))?);
            page.push('\n');
        }
    }
    page.push_str(
        "[Full machine-readable path and paused state](../../../analysis/selective-trace.json)\n",
    );
    Ok(page)
}

/// Render every recorded invocation, including unresolved frames, without
/// treating source offsets from transformed code as original CDP locations.
/// Re-runnable on an already reconstructed project; no deobfuscation rescan.
pub fn materialize_invocation_views(project: &Path, budgets: &AnalysisBudgets) -> Result<usize> {
    let Some(mut trace) = load_artifact(project, SELECTIVE_TRACE, true)? else {
        return Ok(0);
    };
    let runtime = load_artifact(project, RUNTIME_SCRIPTS, false)?
        .context("invocation views require the runtime source inventory")?;
    let identities = runtime_identity_index(&runtime);
    let budget = budgets.operation(
        AnalysisOperation::SourceMaterialization,
        "observed invocation views",
    );
    let output = project.join("src/_observed/invocations");
    fs::create_dir_all(&output)?;
    let hits = trace
        .get_mut("hits")
        .and_then(Value::as_array_mut)
        .context("selective trace missing hits[]")?;
    let mut index = String::from(
        "# Concrete observed invocations\n\nThese are **individual browser breakpoint witnesses**, \
         not an exhaustive execution trace or a proof that other branches are impossible.\n\
         Code locations use original captured V8 script coordinates (zero-based, UTF-16); \
         formatted or deobfuscated source positions may differ.\n\n"
    );

    for (ordinal, hit) in hits.iter_mut().enumerate() {
        budget.checkpoint()?;
        let name = format!("{ordinal:04}.md");
        let destination = format!("src/_observed/invocations/{name}");
        let session = hit
            .get("cdpSession")
            .and_then(Value::as_str)
            .context("observed invocation missing CDP session")?
            .to_owned();
        let mut view = format!(
            "# Observed invocation {ordinal:04}\n\n\
             CDP session: **{session}**. Breakpoint point, pause state and provenance:\n\n"
        );
        let header = json!({
            "pointId": hit.get("pointId"),
            "at": hit.get("at"),
            "reason": hit.get("reason"),
            "hitBreakpoints": hit.get("hitBreakpoints")
        });
        view.push_str(&display_json(&header)?);
        view.push_str("\n## Captured call stack (top frame first)\n\n");

        for (depth, frame) in hit
            .get("frames")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .take(16)
            .enumerate()
        {
            budget.checkpoint()?;
            let function = frame
                .get("functionName")
                .and_then(Value::as_str)
                .filter(|name| !name.is_empty())
                .unwrap_or("<anonymous>");
            let location = frame.get("location").unwrap_or(&Value::Null);
            let script = location
                .get("scriptId")
                .and_then(Value::as_str)
                .unwrap_or("?");
            let line = location.get("lineNumber").and_then(Value::as_u64);
            let column = location.get("columnNumber").and_then(Value::as_u64);
            view.push_str(&format!(
                "### Frame {depth}: {}\n\nCDP script ID: **{script}**, line: **{}**, column: **{}** (zero-based).\n\n",
                function.replace('\n', " "),
                line.map_or_else(|| "?".into(), |n| n.to_string()),
                column.map_or_else(|| "?".into(), |n| n.to_string())
            ));
            let expected = frame.get("sourceSha256").and_then(verified_sha);
            let actual = identities
                .get(&(session.clone(), script.to_owned()))
                .and_then(Option::as_ref);
            let identity_verified = frame.get("source_identity").and_then(Value::as_str)
                == Some("exact")
                && expected.is_some()
                && actual.is_some_and(|source| Some(source.sha256.as_str()) == expected);
            if !identity_verified {
                view.push_str("Source identity **unresolved**; no source code excerpt or provenance link is asserted.\n\n");
                continue;
            }
            let sha = expected.context("checked exact source identity")?;
            let raw_path = format!("resources/runtime-scripts/{sha}.js");
            let raw_bytes = fs::read(project.join(&raw_path))
                .with_context(|| format!("missing exact recorded runtime source {sha}"))?;
            if sha256_hex(&raw_bytes) != sha {
                bail!("captured runtime source byte identity mismatch: {sha}");
            }
            let raw = String::from_utf8(raw_bytes)
                .with_context(|| format!("runtime source is not UTF-8: {sha}"))?;
            view.push_str(&format!(
                "Exact captured source SHA-256: **{sha}**. [Raw recorded code](../../../resources/runtime-scripts/{sha}.js).\n\n"
            ));
            // The per-instance CDP origin is stronger context than a URL
            // pooled across unrelated identical source bodies.
            let matched_instance = runtime
                .get("sources")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter(|source| source.get("sha256").and_then(Value::as_str) == Some(sha))
                .flat_map(|source| {
                    source
                        .get("script_instances")
                        .and_then(Value::as_array)
                        .into_iter()
                        .flatten()
                })
                .find(|instance| {
                    instance.get("cdp_session").and_then(Value::as_str) == Some(session.as_str())
                        && instance.get("script_id").and_then(Value::as_str) == Some(script)
                });
            if let Some(instance) = matched_instance {
                if let Some(url) = instance.get("script_url").and_then(Value::as_str) {
                    if let Ok(mut parsed) = url::Url::parse(url) {
                        parsed.set_query(None);
                        parsed.set_fragment(None);
                        view.push_str(&format!("Script origin (query omitted): {}\n\n", parsed));
                    }
                }
                if let Some(context) = instance.get("execution_context_id") {
                    view.push_str(&format!("V8 execution context ID: {}\n\n", context));
                }
            }

            for (target, label) in [
                (format!("src/runtime-scripts/{sha}.js"), "General source"),
                (
                    format!("src/_readable/runtime-scripts/{sha}.js"),
                    "Shared readable view",
                ),
                (format!("src/_observed/{sha}.js"), "Observed source view"),
            ] {
                if project.join(&target).is_file() {
                    view.push_str(&format!("- [{label}](../../../{target})\n"));
                }
            }
            view.push('\n');
            if let Some(line) = line {
                view.push_str(&source_excerpt(
                    &raw,
                    line,
                    actual.and_then(|source| source.start_line),
                ));
                view.push('\n');
            }
        }
        append_observed_callable_definitions(&mut view, project, &identities, &session, hit)?;
        if hit
            .get("steps")
            .and_then(Value::as_array)
            .is_some_and(|steps| !steps.is_empty())
        {
            let path_name = format!("{ordinal:04}-path.md");
            let path_destination = format!("src/_observed/invocations/{path_name}");
            let path_view = build_observed_path_view(project, &identities, &session, hit, ordinal)?;
            fs::write(output.join(&path_name), path_view)?;
            hit["path_view_path"] = json!(path_destination);
            view.push_str(&format!(
                "## Ordered execution witness\n\n[Browse {} observed debugger steps](./{path_name}). This is a bounded sequence, not universal path specialization.\n\n",
                hit.get("steps").and_then(Value::as_array).map_or(0, Vec::len),
            ));
        }
        view.push_str("## Observed bindings and expression results\n\n");
        view.push_str("Only values captured at this pause. Expressions were requested with side-effect checks; rejected or unavailable evaluations are not facts.\n\n");
        view.push_str(&display_json(&json!({
            "scopes": hit.get("scopes"),
            "expressions": hit.get("expressions"),
        }))?);
        view.push_str("\n[Full machine-readable trace](../../../analysis/selective-trace.json)\n");
        fs::write(output.join(&name), view)?;
        hit["readable_view_path"] = json!(destination);
        let point = hit
            .get("pointId")
            .and_then(Value::as_str)
            .unwrap_or("unnamed");
        index.push_str(&format!("- [Invocation {ordinal:04}](./{name}) — breakpoint point {} in CDP session {session}\n",
            point.replace('\n', " ")));
    }

    // Remove only our own obsolete numbered outputs, never user files.
    let keep = hits.len();
    for item in fs::read_dir(&output)? {
        let item = item?;
        let file = item.file_name();
        let Some(file) = file.to_str() else { continue };
        let page_ordinal = file
            .strip_suffix("-path.md")
            .and_then(|value| value.parse::<usize>().ok())
            .or_else(|| {
                file.strip_suffix(".md")
                    .and_then(|value| value.parse::<usize>().ok())
            });
        if let Some(number) = page_ordinal {
            if number >= keep && number.to_string().len() <= 4 {
                fs::remove_file(item.path())?;
            }
        }
        if let Some(number) = file
            .strip_suffix("-path.md")
            .and_then(|value| value.parse::<usize>().ok())
        {
            if number < keep
                && !hits[number]
                    .get("steps")
                    .and_then(Value::as_array)
                    .is_some_and(|steps| !steps.is_empty())
            {
                fs::remove_file(item.path())?;
            }
        }
    }
    fs::write(output.join("README.md"), index)?;
    write_artifact(project, SELECTIVE_TRACE, &trace)?;
    Ok(keep)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn embedded_script_start_offset_is_applied_to_original_source_only() {
        let source = "const a = 1;\nconst b = a + 2;\n";
        let excerpt = source_excerpt(source, 11, Some(10));
        assert!(excerpt.contains(">     12 | const b = a + 2;"));
        assert!(source_excerpt(source, 11, None).contains("start offset was not recorded"));
        assert!(source_excerpt(source, 9, Some(10)).contains("precedes"));
    }

    #[test]
    fn exact_invocation_renders_raw_location_and_values_not_deob_offsets() -> Result<()> {
        let tmp = TempDir::new()?;
        let project = tmp.path();
        let source = "function dispatch(opcode) {\n  const handler = registry[opcode];\n  return handler(opcode);\n}\n";
        let digest = sha256_hex(source.as_bytes());
        fs::create_dir_all(project.join("resources/runtime-scripts"))?;
        fs::write(
            project.join(format!("resources/runtime-scripts/{digest}.js")),
            source,
        )?;
        write_artifact(
            project,
            RUNTIME_SCRIPTS,
            &json!({
                "schema":RUNTIME_SCRIPTS.schema,
                "summary":{}, "alpine_families":[], "gtm_families":[],
                "sources":[{
                    "sha256":digest,
                    "classification":"application",
                    "script_instances":[{"cdp_session":"main","script_id":"6","start_line":0}],
                },{
                    "sha256":"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                    "classification":"capture_instrumentation",
                    "script_instances":[{"cdp_session":"main","script_id":"7","start_line":0}]
                }]
            }),
        )?;
        write_artifact(
            project,
            SELECTIVE_TRACE,
            &json!({
                "schema":SELECTIVE_TRACE.schema,
                "summary":{"capturedHits":1},
                "errors":[],
                "hits":[{"cdpSession":"main","pointId":"trace-0","frames":[
                    {"functionName":"dispatch","location":{"scriptId":"6","lineNumber":2,"columnNumber":2},
                     "sourceSha256":digest,"source_identity":"exact"},
                    {"location":{"scriptId":"missing","lineNumber":42},"source_identity":"unresolved"},
                ],"steps":[{"index":0,"reason":"other","frames":[
                    {"functionName":"dispatch","location":{"scriptId":"6","lineNumber":2,"columnNumber":2},
                     "sourceSha256":digest,"source_identity":"exact"}
                ],"expressions":[{"expression":"opcode === 34","status":"observed",
                    "value":{"type":"boolean","value":true}}],"scopes":[]},
                {"index":1,"reason":"other","frames":[
                    {"functionName":"","location":{"scriptId":"7","lineNumber":1,"columnNumber":1},
                     "sourceSha256":"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                     "source_identity":"exact"}
                ],"expressions":[],"scopes":[]}],
                "pathWitnessStatus":"bounded_steps_recorded","pathWitnessMode":"into",
                "scopes":[{"type":"local","variables":[
                    {"name":"opcode","value":{"type":"number","value":34}},
                    {"name":"handler","value":{"type":"function","functionDefinition":{
                        "scriptId":"6","lineNumber":0,"columnNumber":9,
                        "sourceSha256":digest,"source_identity":"exact"}}}
                ]}],
                "expressions":[{"expression":"handler === registry[opcode]","status":"observed",
                    "value":{"type":"boolean","value":true}}]}]
            }),
        )?;
        assert_eq!(
            materialize_invocation_views(project, &AnalysisBudgets::standard("fixture"))?,
            1
        );
        let page = fs::read_to_string(project.join("src/_observed/invocations/0000.md"))?;
        assert!(page.contains("return handler(opcode)"));
        assert!(page.contains("handler === registry[opcode]"));
        assert!(page.contains("Raw recorded code"));
        assert!(page.contains("Source identity **unresolved**"));
        assert!(page.contains("Verified observed callable definitions"));
        assert!(page.contains("original line 1, column 10"));
        assert!(page.contains("function dispatch(opcode)"));
        assert!(page.contains("0000-path.md"));
        let path = fs::read_to_string(project.join("src/_observed/invocations/0000-path.md"))?;
        assert!(path.contains("Step 0: dispatch"));
        assert!(path.contains("return handler(opcode)"));
        assert!(path.contains("opcode === 34"));
        assert!(path.contains("recorder instrumentation"));
        assert!(path.contains("Step 1"));
        assert!(path.contains("true"));

        let trace = load_artifact(project, SELECTIVE_TRACE, false)?.context("trace")?;
        assert_eq!(
            trace["hits"][0]["readable_view_path"],
            "src/_observed/invocations/0000.md"
        );
        assert_eq!(
            trace["hits"][0]["path_view_path"],
            "src/_observed/invocations/0000-path.md"
        );
        Ok(())
    }
}
