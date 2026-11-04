//! Readable views of sources whose execution has positive V8 coverage.
//! Parsed, absent, or zero-count scripts are not proof of non-execution.
use crate::{
    analysis_artifacts::{
        load_artifact, write_artifact, DEOBFUSCATION, EXECUTION_COVERAGE, OBSERVED_SOURCE,
        RUNTIME_SCRIPTS,
    },
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    capture_project::read_manifest,
    js_format::format_source,
    sha256_hex,
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::{fs, path::Path};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ObservedSourceSummary {
    pub witnessed_sources: usize,
    pub formatted_sources: usize,
    pub unformatted_sources: usize,
}

/// Recovered source bytes are checked against their capture CAS identities.
/// Only counter-positive script instances are included in this curated tree.
pub fn materialize_observed_runtime_sources(
    project: &Path,
    budgets: &AnalysisBudgets,
) -> Result<ObservedSourceSummary> {
    let manifest = read_manifest(&project.join("capture-manifest.json"))?;
    if manifest.source.kind != "recorder"
        || load_artifact(project, EXECUTION_COVERAGE, true)?.is_none()
    {
        return Ok(ObservedSourceSummary::default());
    }
    let Some(mut index) = load_artifact(project, RUNTIME_SCRIPTS, true)? else {
        return Ok(ObservedSourceSummary::default());
    };
    let deob = load_artifact(project, DEOBFUSCATION, true)?;
    let safe_views = deob
        .as_ref()
        .and_then(|report| report.get("units"))
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|unit| {
            let raw = unit.get("raw_path")?.as_str()?;
            let readable = unit.get("readable_output_path")?.as_str()?;
            if unit.get("exit").and_then(Value::as_i64) != Some(0) {
                return None;
            }
            Some((raw.to_owned(), (readable.to_owned(), unit.clone())))
        })
        .collect::<std::collections::HashMap<_, _>>();
    let capture = Path::new(&manifest.source.input);
    let sources = index
        .get_mut("sources")
        .and_then(Value::as_array_mut)
        .context("runtime-script index missing sources[]")?;
    let mut entries = Vec::new();
    let mut readme = String::from(
        "# Positively observed JavaScript\n\n\
         Positive V8 counters show code executed during this browser interval.\n\
         Zero or missing coverage does not prove other code never executed.\n\
         See analysis/observed-source.json and analysis/runtime-scripts.json for \
         provenance, script IDs, sessions, and original URLs.\n\n",
    );
    let mut summary = ObservedSourceSummary::default();
    for source in sources {
        if source.get("observed_executed") != Some(&Value::Bool(true))
            || source.get("classification").and_then(Value::as_str)
                == Some("capture_instrumentation")
        {
            continue;
        }
        let digest = source
            .get("sha256")
            .and_then(Value::as_str)
            .context("runtime source has no digest")?
            .to_owned();
        if digest.len() != 64 || !digest.bytes().all(|b| b.is_ascii_hexdigit()) {
            bail!("invalid runtime source digest: {digest}");
        }
        let rel = format!("runtime-scripts/{digest}.js");
        if source.get("path").and_then(Value::as_str) != Some(rel.as_str()) {
            bail!("runtime source path is not its content-addressed JavaScript path");
        }
        let raw = fs::read(capture.join(&rel))
            .with_context(|| format!("missing observed runtime source {rel}"))?;
        if sha256_hex(&raw) != digest {
            bail!("runtime source digest mismatch: {rel}");
        }
        let code = std::str::from_utf8(&raw)
            .with_context(|| format!("runtime source not UTF-8: {rel}"))?;
        let staged_raw = format!("resources/{rel}");
        // A safe-deob result in the central general code-unit pipeline is
        // authoritative over separately formatting the unchanged runtime body.
        // Only accept this exact content-addressed runtime path.
        let safe = safe_views
            .get(&staged_raw)
            .filter(|(path, _)| *path == format!("src/_readable/{rel}"));
        let (text, was_formatted, error, safe_deob) = if let Some((readable, record)) = safe {
            let text = fs::read_to_string(project.join(readable))
                .with_context(|| format!("reading proven-safe source view {readable}"))?;
            (
                text,
                record
                    .get("readable_formatted")
                    .and_then(Value::as_bool)
                    .unwrap_or(false),
                None,
                Some(json!({
                    "readable_path": readable,
                    "changed": record.get("changed").cloned().unwrap_or(Value::Null),
                    "transforms": record.get("transforms").cloned().unwrap_or(Value::Null),
                    "proof_report_path": record.get("report_path").cloned().unwrap_or(Value::Null),
                })),
            )
        } else {
            let budget = budgets.operation(AnalysisOperation::Format, &rel);
            match format_source(code, &budget) {
                Ok(text) => (text, true, None, None),
                Err(error) => (code.to_owned(), false, Some(error.to_string()), None),
            }
        };
        let target = format!("src/_observed/{digest}.js");
        let absolute = project.join(&target);
        if let Some(parent) = absolute.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&absolute, text)?;
        summary.witnessed_sources += 1;
        if was_formatted {
            summary.formatted_sources += 1;
        } else {
            summary.unformatted_sources += 1;
        }
        let category = source
            .get("classification")
            .and_then(Value::as_str)
            .unwrap_or("unknown")
            .to_owned();
        source["observed_source_path"] = json!(target);
        source["observed_source_formatted"] = json!(was_formatted);
        readme.push_str(&format!(
            "- [{digest}](./{digest}.js) - {category}{}\n",
            if was_formatted {
                ""
            } else {
                " (raw parse fallback)"
            }
        ));
        entries.push(json!({
            "sha256":digest,
            "source_path":target,
            "raw_capture_path":rel,
            "classification":category,
            "urls":source.get("urls").cloned().unwrap_or(Value::Null),
            "script_instances":source.get("script_instances").cloned().unwrap_or(Value::Null),
            "formatted":was_formatted,
            "format_error":error,
            "safe_deob": safe_deob,
        }));
    }
    if summary.witnessed_sources > 0 {
        fs::write(project.join("src/_observed/README.md"), readme)?;
    }
    let doc = json!({
        "schema":OBSERVED_SOURCE.schema,
        "summary":{
            "witnessed_sources":summary.witnessed_sources,
            "formatted_sources":summary.formatted_sources,
            "unformatted_sources":summary.unformatted_sources,
            "positive_coverage_only":true,
        },
        "sources":entries,
    });
    write_artifact(project, OBSERVED_SOURCE, &doc)?;
    write_artifact(project, RUNTIME_SCRIPTS, &index)?;
    Ok(summary)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capture_project::{write_manifest, CaptureManifest, CaptureSource};
    use serde_json::Map;
    use std::collections::BTreeMap;
    use tempfile::TempDir;

    #[test]
    fn observed_tree_requires_positive_counters_and_keeps_raw_bytes() -> Result<()> {
        let temp = TempDir::new()?;
        let capture = temp.path().join("capture");
        let project = temp.path().join("project");
        fs::create_dir_all(capture.join("runtime-scripts"))?;
        fs::create_dir_all(&project)?;
        let script = "const answer=21+21;\n";
        let digest = sha256_hex(script.as_bytes());
        let rel = format!("runtime-scripts/{digest}.js");
        fs::write(capture.join(&rel), script)?;
        write_manifest(
            &project.join("capture-manifest.json"),
            &CaptureManifest {
                schema: "capture-project/v1".into(),
                source: CaptureSource {
                    kind: "recorder".into(),
                    input: capture.display().to_string(),
                    salvaged: false,
                    extra: Map::new(),
                },
                pages: vec![],
                resources: vec![],
                inline_scripts: vec![],
                counts: BTreeMap::new(),
                extra: Map::new(),
            },
        )?;
        write_artifact(
            &project,
            RUNTIME_SCRIPTS,
            &json!({
                "schema":RUNTIME_SCRIPTS.schema,"summary":{},"alpine_families":[],
                "gtm_families":[],"sources":[{
                    "sha256":digest,"path":rel,"classification":"network_response",
                    "observed_executed":true,"script_instances":[{"cdp_session":"main",
                        "script_id":"7","execution":{"status":"positive"}}],
                }],
            }),
        )?;
        write_artifact(
            &project,
            EXECUTION_COVERAGE,
            &json!({"schema":EXECUTION_COVERAGE.schema,"summary":{},"scripts":[]}),
        )?;
        let result = materialize_observed_runtime_sources(
            &project,
            &AnalysisBudgets::standard("observed-test"),
        )?;
        assert_eq!(result.witnessed_sources, 1);
        assert_eq!(result.formatted_sources, 1);
        assert!(project.join(format!("src/_observed/{digest}.js")).is_file());
        assert_eq!(fs::read_to_string(capture.join(rel))?, script);
        let runtime = load_artifact(&project, RUNTIME_SCRIPTS, false)?.context("index")?;
        assert_eq!(
            runtime["sources"][0]["observed_source_path"],
            json!(format!("src/_observed/{digest}.js"))
        );
        Ok(())
    }
}
