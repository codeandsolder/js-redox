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
    report_markdown::literal_text,
    runtime_coverage::RuntimeCoverageIndex,
    sha256_hex,
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::fmt::Write as _;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ObservedSourceSummary {
    pub witnessed_sources: usize,
    pub formatted_sources: usize,
    pub unformatted_sources: usize,
}

/// A compact human-facing locator, not a replacement for the recorded URL.
/// Keep original query strings and complete generation chains in JSON provenance.
fn display_origin(source: &Value) -> Option<String> {
    let urls = source
        .get("urls")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str);
    let generation_roots = source
        .get("generated")
        .and_then(|generated| generated.get("root_urls"))
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str);
    urls.chain(generation_roots).find_map(|raw| {
        let url = url::Url::parse(raw).ok()?;
        let host = url.host_str()?;
        let path = url.path();
        let short_path = path.chars().take(88).collect::<String>();
        let truncated = if path.chars().count() > 88 { "…" } else { "" };
        Some(format!("{host}{short_path}{truncated}"))
    })
}

fn classification_heading(classification: &str) -> &'static str {
    match classification {
        "network_response" | "network_observed" => "Network scripts",
        "inline_script" => "Inline scripts",
        "generated_runtime" => "Generated runtime scripts",
        _ => "Other observed scripts",
    }
}

/// Recovered source bytes are checked against their capture CAS identities.
/// Only counter-positive script instances are included in this curated tree.
///
/// # Errors
///
/// Fails if capture metadata/artifacts or source files cannot be read or written; rejects
/// invalid content-addressed paths, malformed source digests and digest mismatches. Budget and
/// output materialization errors also propagate.
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
    let coverage_budget = budgets.operation(
        AnalysisOperation::SourceMaterialization,
        "positive runtime coverage witnesses",
    );
    let coverage = RuntimeCoverageIndex::build(&index, &coverage_budget)?;
    let previous = load_artifact(project, OBSERVED_SOURCE, true)?;
    let mut stale_paths = previous
        .as_ref()
        .and_then(|artifact| artifact.get("sources"))
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|row| {
            let digest = row.get("sha256")?.as_str()?;
            if !crate::content_dedup::is_canonical_sha256(digest) {
                return None;
            }
            let path = format!("src/_observed/{digest}.js");
            (row.get("source_path")?.as_str()? == path).then_some(path)
        })
        .collect::<BTreeSet<_>>();
    let sources = index
        .get_mut("sources")
        .and_then(Value::as_array_mut)
        .context("runtime-script index missing sources[]")?;
    let mut entries = Vec::new();
    let mut readme = String::from(
        "# Positively observed JavaScript\n\n\
         Positive V8 counters witness execution under the recorded observation mode.\n\
         Best-effort coverage is incomplete; precise coverage changes JIT behavior.\n\
         Zero or missing coverage does not prove other code never executed.\n\
         See analysis/observed-source.json and analysis/runtime-scripts.json for \
         provenance, script IDs, sessions, and original URLs.\n\n",
    );
    let mut grouped_links = BTreeMap::<&str, Vec<String>>::new();
    let mut summary = ObservedSourceSummary::default();
    for source in sources {
        coverage_budget.consume(1)?;
        let digest = source
            .get("sha256")
            .and_then(Value::as_str)
            .context("runtime source has no digest")?
            .to_owned();
        let all_witnesses = coverage.witnesses(&digest);
        coverage_budget.consume(u64::try_from(all_witnesses.len())?)?;
        source["observed_executed"] = json!(!all_witnesses.is_empty());
        let witnesses = all_witnesses
            .iter()
            .filter(|witness| !witness.capture_instrumentation)
            .collect::<Vec<_>>();
        if witnesses.is_empty()
            || source.get("classification").and_then(Value::as_str)
                == Some("capture_instrumentation")
        {
            if let Some(row) = source.as_object_mut() {
                row.remove("observed_source_path");
                row.remove("observed_source_formatted");
            }
            continue;
        }
        if !crate::content_dedup::is_canonical_sha256(&digest) {
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
        crate::report_file::write_text(&absolute, &text)?;
        stale_paths.remove(&target);
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
        let origin = display_origin(source).unwrap_or_else(|| category.clone());
        let (functions, ranges) =
            witnesses
                .iter()
                .fold((0_u64, 0_u64), |(functions, ranges), witness| {
                    (
                        functions.saturating_add(witness.positive_functions),
                        ranges.saturating_add(witness.positive_ranges),
                    )
                });
        let instances = witnesses.len();
        let (status, readable_link) = match &safe_deob {
            Some(info) if info["changed"] == true => (
                "safe transform",
                format!(" · [general readable source](../_readable/runtime-scripts/{digest}.js)"),
            ),
            Some(_) => (
                "safe unchanged",
                format!(" · [general readable source](../_readable/runtime-scripts/{digest}.js)"),
            ),
            None => ("formatted only", String::new()),
        };
        grouped_links
            .entry(classification_heading(&category))
            .or_default()
            .push(format!(
                "- [{} · {}](./{digest}.js) — {status}; {instances} witnessed script instance(s), {functions} positive functions, {ranges} positive ranges{readable_link}{}",
                literal_text(&origin),
                &digest[..12],
                if was_formatted { "" } else { "; unformatted fallback" },
            ));
        entries.push(json!({
            "sha256":digest,
            "source_path":target,
            "raw_capture_path":rel,
            "classification":category,
            "urls":source.get("urls").cloned().unwrap_or(Value::Null),
            "script_instances":source.get("script_instances").cloned().unwrap_or(Value::Null),
            "positive_witnesses":witnesses,
            "coverage_mode":source.get("coverage_mode").cloned().unwrap_or(Value::Null),
            "formatted":was_formatted,
            "format_error":error,
            "safe_deob": safe_deob,
        }));
    }
    for path in stale_paths {
        coverage_budget.consume(1)?;
        match fs::remove_file(project.join(path)) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.into()),
        }
    }
    if summary.witnessed_sources > 0 || project.join("src/_observed/README.md").is_file() {
        for (heading, links) in grouped_links {
            let _ = write!(readme, "## {heading} ({})\n\n", links.len());
            for link in links {
                readme.push_str(&link);
                readme.push('\n');
            }
            readme.push('\n');
        }
        crate::report_file::write_text(&project.join("src/_observed/README.md"), &readme)?;
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
    fn visible_navigation_uses_urls_without_including_query_tokens() {
        let source = json!({
            "urls": ["https://example.test/assets/app.js?session=secret"],
        });
        assert_eq!(
            display_origin(&source).as_deref(),
            Some("example.test/assets/app.js")
        );
        let generated = json!({
            "urls": [],
            "generated": {"root_urls": ["https://example.test/boot?q=secret"]},
        });
        assert_eq!(
            display_origin(&generated).as_deref(),
            Some("example.test/boot")
        );
        assert_eq!(
            classification_heading("generated_runtime"),
            "Generated runtime scripts"
        );
        assert_eq!(classification_heading("inline_script"), "Inline scripts");
    }

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
                "schema":RUNTIME_SCRIPTS.schema,
                "script_identity_conflicts":[],"summary":{},"alpine_families":[],
                "gtm_families":[],"sources":[{
                    "sha256":digest,"path":rel,"classification":"network_response",
                    "observed_executed":true,"script_instances":[{"cdp_session":"main",
                        "script_id":"7","execution":{"status":"positive","positive_functions":1,"positive_ranges":2}}],
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
        let readme = fs::read_to_string(project.join("src/_observed/README.md"))?;
        assert!(readme.contains("## Network scripts (1)"));
        assert!(readme.contains("1 witnessed script instance(s)"));
        assert!(readme.contains(&digest[..12]));
        assert!(project.join(format!("src/_observed/{digest}.js")).is_file());
        assert_eq!(fs::read_to_string(capture.join(rel))?, script);
        let mut runtime = load_artifact(&project, RUNTIME_SCRIPTS, false)?.context("index")?;
        assert_eq!(
            runtime["sources"][0]["observed_source_path"],
            json!(format!("src/_observed/{digest}.js"))
        );
        runtime["script_identity_conflicts"] = json!([{"cdp_session":"main","script_id":"7","sha256_claims":[digest,"unavailable-body"]}]);
        write_artifact(&project, RUNTIME_SCRIPTS, &runtime)?;
        let again = materialize_observed_runtime_sources(
            &project,
            &AnalysisBudgets::standard("observed-conflicting"),
        )?;
        assert_eq!(again.witnessed_sources, 0);
        assert!(!project.join(format!("src/_observed/{digest}.js")).is_file());
        let runtime = load_artifact(&project, RUNTIME_SCRIPTS, false)?.context("index")?;
        assert_eq!(runtime["sources"][0]["observed_executed"], false);
        assert!(runtime["sources"][0].get("observed_source_path").is_none());
        assert!(
            load_artifact(&project, OBSERVED_SOURCE, false)?.context("observed report")?["sources"]
                .as_array()
                .is_some_and(Vec::is_empty)
        );
        Ok(())
    }
}
