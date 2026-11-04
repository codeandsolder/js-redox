//! Human-readable browser execution witnesses with exact original-source context.
//! This is evidence from a particular paused invocation, never a general proof.
use crate::{
    analysis_artifacts::{load_artifact, write_artifact, RUNTIME_SCRIPTS, SELECTIVE_TRACE},
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    sha256_hex,
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::{collections::HashMap, fs, path::Path};

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

fn runtime_identity_index(
    runtime: &Value,
) -> HashMap<(String, String), Option<(String, Option<u64>)>> {
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
            let next = (
                sha.to_owned(),
                instance.get("start_line").and_then(Value::as_u64),
            );
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
                && actual.is_some_and(|(sha, _)| Some(sha.as_str()) == expected);
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
                    actual.and_then(|(_, start)| *start),
                ));
                view.push('\n');
            }
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
        if let Some(number) = file
            .strip_suffix(".md")
            .and_then(|text| text.parse::<usize>().ok())
        {
            if number >= keep && number.to_string().len() <= 4 {
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
                    "script_instances":[{"cdp_session":"main","script_id":"6","start_line":0}],
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
                ],"scopes":[{"type":"local","variables":[{"name":"opcode","value":{"type":"number","value":34}}]}],
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
        let trace = load_artifact(project, SELECTIVE_TRACE, false)?.context("trace")?;
        assert_eq!(
            trace["hits"][0]["readable_view_path"],
            "src/_observed/invocations/0000.md"
        );
        Ok(())
    }
}
