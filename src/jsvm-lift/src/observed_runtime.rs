//! Readable views of sources whose execution has positive V8 coverage.
//! Parsed, absent, or zero-count scripts are not proof of non-execution.
use crate::{
    analysis_artifacts::{
        load_optional_artifact, write_artifact, DEOBFUSCATION, EXECUTION_COVERAGE, OBSERVED_SOURCE,
        RUNTIME_SCRIPTS,
    },
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    capture_project::read_manifest,
    js_format::format_source,
    report_markdown::literal_text,
    runtime_coverage::{PositiveCoverageWitness, RuntimeCoverageIndex},
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
use work_budget::WorkBudget;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ObservedSourceSummary {
    pub witnessed: usize,
    pub formatted: usize,
    pub unformatted: usize,
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

type SafeViews = BTreeMap<String, (String, Value)>;

fn load_safe_views(project: &Path) -> Result<SafeViews> {
    let deob = load_optional_artifact(project, DEOBFUSCATION)?;
    Ok(deob
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
        .collect())
}

fn stale_observed_paths(project: &Path) -> Result<BTreeSet<String>> {
    let previous = load_optional_artifact(project, OBSERVED_SOURCE)?;
    Ok(previous
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
        .collect())
}

fn verified_runtime_source(
    capture: &Path,
    source: &Value,
    digest: &str,
) -> Result<(String, String)> {
    if !crate::content_dedup::is_canonical_sha256(digest) {
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
    let code =
        String::from_utf8(raw).with_context(|| format!("runtime source not UTF-8: {rel}"))?;
    Ok((rel, code))
}

struct ObservedView {
    text: String,
    formatted: bool,
    error: Option<String>,
    safe_deob: Option<Value>,
}

fn choose_view(
    project: &Path,
    rel: &str,
    code: &str,
    safe_views: &SafeViews,
    budgets: &AnalysisBudgets,
) -> Result<ObservedView> {
    let staged_raw = format!("resources/{rel}");
    // A safe-deob result in the central general code-unit pipeline is
    // authoritative over separately formatting the unchanged runtime body.
    // Only accept this exact content-addressed runtime path.
    let safe = safe_views
        .get(&staged_raw)
        .filter(|(path, _)| *path == format!("src/_readable/{rel}"));
    if let Some((readable, record)) = safe {
        let text = fs::read_to_string(project.join(readable))
            .with_context(|| format!("reading proven-safe source view {readable}"))?;
        Ok(ObservedView {
            text,
            formatted: record
                .get("readable_formatted")
                .and_then(Value::as_bool)
                .unwrap_or(false),
            error: None,
            safe_deob: Some(json!({
                "readable_path": readable,
                "changed": record.get("changed").cloned().unwrap_or(Value::Null),
                "transforms": record.get("transforms").cloned().unwrap_or(Value::Null),
                "proof_report_path": record.get("report_path").cloned().unwrap_or(Value::Null),
            })),
        })
    } else {
        let budget = budgets.operation(AnalysisOperation::Format, rel);
        match format_source(code, &budget) {
            Ok(text) => Ok(ObservedView {
                text,
                formatted: true,
                error: None,
                safe_deob: None,
            }),
            Err(error) => Ok(ObservedView {
                text: code.to_owned(),
                formatted: false,
                error: Some(error.to_string()),
                safe_deob: None,
            }),
        }
    }
}

fn witness_link(
    source: &Value,
    digest: &str,
    category: &str,
    view: &ObservedView,
    witnesses: &[&PositiveCoverageWitness],
) -> String {
    let origin = display_origin(source).unwrap_or_else(|| category.to_owned());
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
    let (status, readable_link) = match &view.safe_deob {
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
    format!(
            "- [{} · {}](./{digest}.js) — {status}; {instances} witnessed script instance(s), {functions} positive functions, {ranges} positive ranges{readable_link}{}",
            literal_text(&origin),
            &digest[..12],
            if view.formatted { "" } else { "; unformatted fallback" },
        )
}

struct ObservedSources<'a> {
    project: &'a Path,
    capture: &'a Path,
    budgets: &'a AnalysisBudgets,
    coverage_budget: WorkBudget,
    safe_views: SafeViews,
    stale_paths: BTreeSet<String>,
    entries: Vec<Value>,
    grouped_links: BTreeMap<&'static str, Vec<String>>,
    summary: ObservedSourceSummary,
}

impl ObservedSources<'_> {
    fn record(&mut self, source: &mut Value, coverage: &RuntimeCoverageIndex) -> Result<()> {
        self.coverage_budget.consume(1)?;
        let digest = source
            .get("sha256")
            .and_then(Value::as_str)
            .context("runtime source has no digest")?
            .to_owned();
        let all_witnesses = coverage.witnesses(&digest);
        self.coverage_budget
            .consume(u64::try_from(all_witnesses.len())?)?;
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
            return Ok(());
        }
        let (rel, code) = verified_runtime_source(self.capture, source, &digest)?;
        let view = choose_view(self.project, &rel, &code, &self.safe_views, self.budgets)?;
        let target = format!("src/_observed/{digest}.js");
        let absolute = self.project.join(&target);
        crate::report_file::write_text(&absolute, &view.text)?;
        self.stale_paths.remove(&target);
        self.summary.witnessed += 1;
        if view.formatted {
            self.summary.formatted += 1;
        } else {
            self.summary.unformatted += 1;
        }
        let category = source
            .get("classification")
            .and_then(Value::as_str)
            .unwrap_or("unknown")
            .to_owned();
        source["observed_source_path"] = json!(target);
        source["observed_source_formatted"] = json!(view.formatted);
        self.grouped_links
            .entry(classification_heading(&category))
            .or_default()
            .push(witness_link(source, &digest, &category, &view, &witnesses));
        self.entries.push(json!({
            "sha256":digest,
            "source_path":target,
            "raw_capture_path":rel,
            "classification":category,
            "urls":source.get("urls").cloned().unwrap_or(Value::Null),
            "script_instances":source.get("script_instances").cloned().unwrap_or(Value::Null),
            "positive_witnesses":witnesses,
            "coverage_mode":source.get("coverage_mode").cloned().unwrap_or(Value::Null),
            "formatted":view.formatted,
            "format_error":view.error,
            "safe_deob": view.safe_deob,
        }));
        Ok(())
    }

    fn publish(self, index: &Value) -> Result<ObservedSourceSummary> {
        for path in self.stale_paths {
            self.coverage_budget.consume(1)?;
            match fs::remove_file(self.project.join(path)) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => return Err(error.into()),
            }
        }
        let mut readme = String::from(
            "# Positively observed JavaScript\n\n\
             Positive V8 counters witness execution under the recorded observation mode.\n\
             Best-effort coverage is incomplete; precise coverage changes JIT behavior.\n\
             Zero or missing coverage does not prove other code never executed.\n\
             See analysis/observed-source.json and analysis/runtime-scripts.json for \
             provenance, script IDs, sessions, and original URLs.\n\n",
        );
        if self.summary.witnessed > 0 || self.project.join("src/_observed/README.md").is_file() {
            for (heading, links) in self.grouped_links {
                let _ = write!(readme, "## {heading} ({})\n\n", links.len());
                for link in links {
                    readme.push_str(&link);
                    readme.push('\n');
                }
                readme.push('\n');
            }
            crate::report_file::write_text(&self.project.join("src/_observed/README.md"), &readme)?;
        }
        let doc = json!({
            "schema":OBSERVED_SOURCE.schema,
            "summary":{
                "witnessed_sources":self.summary.witnessed,
                "formatted_sources":self.summary.formatted,
                "unformatted_sources":self.summary.unformatted,
                "positive_coverage_only":true,
            },
            "sources":self.entries,
        });
        write_artifact(self.project, OBSERVED_SOURCE, &doc)?;
        write_artifact(self.project, RUNTIME_SCRIPTS, index)?;
        Ok(self.summary)
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
        || load_optional_artifact(project, EXECUTION_COVERAGE)?.is_none()
    {
        return Ok(ObservedSourceSummary::default());
    }
    let Some(mut index) = load_optional_artifact(project, RUNTIME_SCRIPTS)? else {
        return Ok(ObservedSourceSummary::default());
    };
    let capture = Path::new(&manifest.source.input);
    let coverage_budget = budgets.operation(
        AnalysisOperation::SourceMaterialization,
        "positive runtime coverage witnesses",
    );
    let coverage = RuntimeCoverageIndex::build(&index, &coverage_budget)?;
    let sources = index
        .get_mut("sources")
        .and_then(Value::as_array_mut)
        .context("runtime-script index missing sources[]")?;
    let mut observed = ObservedSources {
        project,
        capture,
        budgets,
        coverage_budget,
        safe_views: load_safe_views(project)?,
        stale_paths: stale_observed_paths(project)?,
        entries: Vec::new(),
        grouped_links: BTreeMap::new(),
        summary: ObservedSourceSummary::default(),
    };
    for source in sources {
        observed.record(source, &coverage)?;
    }
    observed.publish(&index)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis_artifacts::load_artifact;
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
        assert_eq!(result.witnessed, 1);
        assert_eq!(result.formatted, 1);
        let readme = fs::read_to_string(project.join("src/_observed/README.md"))?;
        assert!(readme.contains("## Network scripts (1)"));
        assert!(readme.contains("1 witnessed script instance(s)"));
        assert!(readme.contains(&digest[..12]));
        assert!(project.join(format!("src/_observed/{digest}.js")).is_file());
        assert_eq!(fs::read_to_string(capture.join(rel))?, script);
        let mut runtime = load_artifact(&project, RUNTIME_SCRIPTS).context("index")?;
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
        assert_eq!(again.witnessed, 0);
        assert!(!project.join(format!("src/_observed/{digest}.js")).is_file());
        let runtime = load_artifact(&project, RUNTIME_SCRIPTS).context("index")?;
        assert_eq!(runtime["sources"][0]["observed_executed"], false);
        assert!(runtime["sources"][0].get("observed_source_path").is_none());
        assert!(
            load_artifact(&project, OBSERVED_SOURCE).context("observed report")?["sources"]
                .as_array()
                .is_some_and(Vec::is_empty)
        );
        Ok(())
    }
}
