use crate::{
    analysis_artifacts::{
        load_artifact, write_artifact, DEOBFUSCATION, SOURCE_INDEX, STRING_RECOVERY,
    },
    content_dedup::{default_jobs, link_or_copy},
    js_format::format_source,
    safe_deob::{deobfuscate_source, SafeDeobReport, SourceMode},
    sha256_hex,
};
use anyhow::{bail, Context, Result};
use rayon::{prelude::*, ThreadPoolBuilder};
use serde_json::{json, Map, Value};
#[cfg(unix)]
use std::os::unix::process::CommandExt;
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::Duration,
};
use tempfile::Builder as TempDirBuilder;
use wait_timeout::ChildExt;

#[derive(Debug, Clone)]
pub struct ProjectDeobOptions {
    pub repo_root: PathBuf,
    pub string_recoverer: PathBuf,
    pub decoder_recoverer: PathBuf,
    pub jobs: Option<usize>,
    pub max_iterations: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProjectDeobSummary {
    pub javascript_units: usize,
    pub unique_raw_inputs: usize,
    pub unique_pre_deob_inputs: usize,
    pub unique_deob_outputs: usize,
    pub changed_units: usize,
    pub failed_units: usize,
    pub string_recovery_changed_units: usize,
    pub string_recovery_replacements: usize,
}

#[derive(Debug, Clone)]
struct Occurrence {
    ordinal: usize,
    unit: Value,
    raw_path: String,
    source: PathBuf,
    raw_sha: String,
    mode: SourceMode,
}

type ContentKey = (String, SourceMode);

#[derive(Debug, Clone)]
struct StringResult {
    mode: SourceMode,
    canonical_ordinal: usize,
    canonical_raw_path: String,
    report_path: Option<PathBuf>,
    exit: i32,
    changed: bool,
    replacements: usize,
    decoders: Value,
    selected_path: PathBuf,
    selected_sha: String,
    error: Option<String>,
}

#[derive(Debug, Clone)]
struct DeobResult {
    mode: SourceMode,
    report: Option<SafeDeobReport>,
    output_path: Option<PathBuf>,
    exit: i32,
    error: Option<String>,
}

#[derive(Debug, Clone)]
struct ReadableResult {
    path: PathBuf,
    formatted: bool,
    error: Option<String>,
}

fn source_value<'a>(unit: &'a Value, field: &str) -> Option<&'a str> {
    unit.get(field).and_then(Value::as_str)
}

fn derived_path(raw_path: &str, root: &str) -> PathBuf {
    let raw = Path::new(raw_path);
    let mut components = raw.components();
    let first = components.next();
    let mut output = PathBuf::from("src");
    output.push(root);
    match first.and_then(|component| component.as_os_str().to_str()) {
        Some("resources" | "src") => output.extend(components),
        Some(_) => output.push(raw),
        None => {}
    }
    output
}

fn tail(text: &[u8], limit: usize) -> String {
    let start = text.len().saturating_sub(limit);
    String::from_utf8_lossy(&text[start..]).into_owned()
}

#[derive(Debug)]
struct CommandResult {
    code: i32,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

fn run_command_with_timeout(
    command: &mut Command,
    work: &Path,
    timeout: Duration,
) -> Result<CommandResult> {
    fs::create_dir_all(work).with_context(|| format!("creating {}", work.display()))?;
    let stdout_path = work.join("stdout.log");
    let stderr_path = work.join("stderr.log");
    let stdout = fs::File::create(&stdout_path)
        .with_context(|| format!("creating {}", stdout_path.display()))?;
    let stderr = fs::File::create(&stderr_path)
        .with_context(|| format!("creating {}", stderr_path.display()))?;
    let rendered = format!("{command:?}");
    #[cfg(unix)]
    command.process_group(0);
    let mut child = command
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr))
        .spawn()
        .with_context(|| format!("launching {rendered}"))?;
    let status = match child
        .wait_timeout(timeout)
        .with_context(|| format!("waiting for {rendered}"))?
    {
        Some(status) => (status, false),
        None => {
            #[cfg(unix)]
            {
                // The helper gets its own process group above. Kill the group so
                // a timed-out `uv` wrapper cannot leave its Python child behind.
                let group = format!("-{}", child.id());
                let killed_group = Command::new("kill")
                    .arg("-KILL")
                    .arg("--")
                    .arg(group)
                    .status()
                    .is_ok_and(|status| status.success());
                if !killed_group && child.try_wait()?.is_none() {
                    child
                        .kill()
                        .with_context(|| format!("killing timed-out {rendered}"))?;
                }
            }
            #[cfg(not(unix))]
            child
                .kill()
                .with_context(|| format!("killing timed-out {rendered}"))?;
            let status = child
                .wait()
                .with_context(|| format!("reaping timed-out {rendered}"))?;
            (status, true)
        }
    };
    let mut stdout =
        fs::read(&stdout_path).with_context(|| format!("reading {}", stdout_path.display()))?;
    let mut stderr =
        fs::read(&stderr_path).with_context(|| format!("reading {}", stderr_path.display()))?;
    if status.1 {
        stderr.extend_from_slice(format!("\ntimed out after {}s", timeout.as_secs()).as_bytes());
    }
    Ok(CommandResult {
        code: if status.1 {
            124
        } else {
            status.0.code().unwrap_or(1)
        },
        stdout: std::mem::take(&mut stdout),
        stderr: std::mem::take(&mut stderr),
    })
}

fn command_error(output: &CommandResult) -> String {
    let mut bytes = Vec::with_capacity(output.stdout.len() + output.stderr.len());
    bytes.extend_from_slice(&output.stdout);
    bytes.extend_from_slice(&output.stderr);
    tail(&bytes, 3000)
}

fn write_json(path: &Path, value: &impl serde::Serialize) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    let mut encoded = serde_json::to_string_pretty(value)?;
    encoded.push('\n');
    fs::write(path, encoded).with_context(|| format!("writing {}", path.display()))
}

fn run_string_recovery(
    options: &ProjectDeobOptions,
    work: &Path,
    key: &ContentKey,
    group: &[Occurrence],
) -> Result<StringResult> {
    let (raw_sha, mode) = key;
    let canonical = group.first().context("empty raw-source group")?;
    let cache = work.join("string").join(mode.as_str()).join(raw_sha);
    fs::create_dir_all(&cache).with_context(|| format!("creating {}", cache.display()))?;
    let recovered = cache.join(format!("recovered{}", mode.suffix()));
    let report = cache.join("report.json");

    let mut command = Command::new("uv");
    command
        .arg("run")
        .arg("--no-project")
        .arg("python")
        .arg(&options.string_recoverer)
        .arg(&canonical.source)
        .arg(&recovered)
        .arg("--report")
        .arg(&report)
        .arg("--decoder-recoverer")
        .arg(&options.decoder_recoverer)
        .current_dir(&options.repo_root);
    let output = run_command_with_timeout(&mut command, &cache, Duration::from_secs(180))?;

    let mut result = StringResult {
        mode: *mode,
        canonical_ordinal: canonical.ordinal,
        canonical_raw_path: canonical.raw_path.clone(),
        report_path: None,
        exit: output.code,
        changed: false,
        replacements: 0,
        decoders: json!([]),
        selected_path: canonical.source.clone(),
        selected_sha: raw_sha.clone(),
        error: None,
    };

    if output.code != 0 || !report.is_file() || !recovered.is_file() {
        result.error = Some(command_error(&output));
        return Ok(result);
    }

    let report_text =
        fs::read_to_string(&report).with_context(|| format!("reading {}", report.display()))?;
    let meta: Value = serde_json::from_str(&report_text)
        .with_context(|| format!("parsing {}", report.display()))?;
    let recovered_bytes =
        fs::read(&recovered).with_context(|| format!("reading {}", recovered.display()))?;
    let recovered_sha = sha256_hex(&recovered_bytes);
    if meta.get("safe_static_only").and_then(Value::as_bool) != Some(true) {
        bail!(
            "unsafe string recovery report for {}",
            canonical.source.display()
        );
    }
    if meta.get("input_sha256").and_then(Value::as_str) != Some(raw_sha.as_str()) {
        bail!(
            "string recovery input hash mismatch for {}",
            canonical.source.display()
        );
    }
    if meta.get("output_sha256").and_then(Value::as_str) != Some(recovered_sha.as_str()) {
        bail!(
            "string recovery output hash mismatch for {}",
            canonical.source.display()
        );
    }

    result.exit = 0;
    result.changed = meta
        .get("changed")
        .and_then(Value::as_bool)
        .unwrap_or(false);
    result.replacements = meta
        .get("replacements")
        .and_then(Value::as_u64)
        .and_then(|count| usize::try_from(count).ok())
        .unwrap_or(0);
    result.decoders = meta.get("decoders").cloned().unwrap_or_else(|| json!([]));
    result.selected_path = recovered;
    result.selected_sha = recovered_sha;
    result.report_path = Some(report);
    Ok(result)
}

fn run_safe_deob(
    work: &Path,
    key: &ContentKey,
    raw_group_keys: &[ContentKey],
    string_results: &BTreeMap<ContentKey, StringResult>,
    max_iterations: usize,
) -> Result<DeobResult> {
    let (selected_sha, mode) = key;
    let representative_key = raw_group_keys
        .first()
        .context("empty pre-deob source group")?;
    let representative = string_results
        .get(representative_key)
        .context("missing string-recovery result")?;
    let selected = fs::read_to_string(&representative.selected_path)
        .with_context(|| format!("reading {}", representative.selected_path.display()))?;
    if sha256_hex(selected.as_bytes()) != *selected_sha {
        bail!(
            "pre-deob input hash mismatch for {}",
            representative.selected_path.display()
        );
    }

    match deobfuscate_source(
        &selected,
        representative.canonical_raw_path.clone(),
        *mode,
        max_iterations,
        false,
    ) {
        Ok(outcome) => {
            let cache = work.join("deob").join(mode.as_str()).join(selected_sha);
            fs::create_dir_all(&cache).with_context(|| format!("creating {}", cache.display()))?;
            let output_path = cache.join(format!("safe{}", mode.suffix()));
            fs::write(&output_path, outcome.source.as_bytes())
                .with_context(|| format!("writing {}", output_path.display()))?;
            Ok(DeobResult {
                mode: *mode,
                report: Some(outcome.report),
                output_path: Some(output_path),
                exit: 0,
                error: None,
            })
        }
        Err(error) => Ok(DeobResult {
            mode: *mode,
            report: None,
            output_path: None,
            exit: 1,
            error: Some(error.to_string()),
        }),
    }
}

fn format_output(work: &Path, key: &ContentKey, deob: &DeobResult) -> Result<ReadableResult> {
    let (output_sha, mode) = key;
    let output_path = deob
        .output_path
        .as_ref()
        .context("missing deobfuscated output")?;
    let exact = fs::read_to_string(output_path)
        .with_context(|| format!("reading {}", output_path.display()))?;
    let (source, formatted, error) = match format_source(&exact) {
        Ok(source) => (source, true, None),
        Err(error) => (exact, false, Some(error.to_string())),
    };
    let cache = work.join("readable").join(mode.as_str()).join(output_sha);
    fs::create_dir_all(&cache).with_context(|| format!("creating {}", cache.display()))?;
    let path = cache.join("readable.js");
    fs::write(&path, source.as_bytes()).with_context(|| format!("writing {}", path.display()))?;
    Ok(ReadableResult {
        path,
        formatted,
        error,
    })
}

fn as_object_mut(value: &mut Value) -> Result<&mut Map<String, Value>> {
    value
        .as_object_mut()
        .context("artifact row must be an object")
}

pub fn materialize_project_deobfuscation(
    project: &Path,
    options: &ProjectDeobOptions,
) -> Result<ProjectDeobSummary> {
    let source_index = load_artifact(project, SOURCE_INDEX, false)?
        .context("source index is required for project deobfuscation")?;
    let source_units = source_index
        .get("units")
        .and_then(Value::as_array)
        .context("source index units must be an array")?;

    let analysis_dir = project.join("analysis");
    fs::create_dir_all(&analysis_dir)
        .with_context(|| format!("creating {}", analysis_dir.display()))?;
    let work = TempDirBuilder::new()
        .prefix(".safe-deob-")
        .tempdir_in(&analysis_dir)
        .with_context(|| {
            format!(
                "creating temporary work directory in {}",
                analysis_dir.display()
            )
        })?;
    let work_path = work.path();

    let mut occurrences = Vec::<Occurrence>::new();
    let mut raw_groups = BTreeMap::<ContentKey, Vec<Occurrence>>::new();
    for (ordinal, unit) in source_units.iter().enumerate() {
        if source_value(unit, "kind") != Some("javascript") {
            continue;
        }
        let Some(source_path) = source_value(unit, "source_path") else {
            continue;
        };
        let Some(raw_path) = source_value(unit, "raw_path") else {
            continue;
        };
        let source = project.join(raw_path);
        if !source.is_file() {
            continue;
        }
        let raw_bytes =
            fs::read(&source).with_context(|| format!("reading {}", source.display()))?;
        let raw_sha = sha256_hex(&raw_bytes);
        let mode = SourceMode::for_path(Path::new(source_path));
        let occurrence = Occurrence {
            ordinal,
            unit: unit.clone(),
            raw_path: raw_path.to_string(),
            source,
            raw_sha: raw_sha.clone(),
            mode,
        };
        raw_groups
            .entry((raw_sha, mode))
            .or_default()
            .push(occurrence.clone());
        occurrences.push(occurrence);
    }

    let jobs = options.jobs.unwrap_or_else(|| default_jobs(8)).max(1);
    let pool = ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .context("building project-deobfuscation thread pool")?;

    let raw_group_refs = raw_groups.iter().collect::<Vec<_>>();
    let string_results = pool
        .install(|| {
            raw_group_refs
                .par_iter()
                .map(|(key, group)| {
                    run_string_recovery(options, work_path, key, group)
                        .map(|result| ((*key).clone(), result))
                })
                .collect::<Vec<_>>()
        })
        .into_iter()
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .collect::<BTreeMap<_, _>>();

    let mut pre_deob_groups = BTreeMap::<ContentKey, Vec<ContentKey>>::new();
    for (raw_key, result) in &string_results {
        pre_deob_groups
            .entry((result.selected_sha.clone(), result.mode))
            .or_default()
            .push(raw_key.clone());
    }

    let pre_group_refs = pre_deob_groups.iter().collect::<Vec<_>>();
    let deob_results = pool
        .install(|| {
            pre_group_refs
                .par_iter()
                .map(|(key, raw_keys)| {
                    run_safe_deob(
                        work_path,
                        key,
                        raw_keys,
                        &string_results,
                        options.max_iterations,
                    )
                    .map(|result| ((*key).clone(), result))
                })
                .collect::<Vec<_>>()
        })
        .into_iter()
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .collect::<BTreeMap<_, _>>();

    let mut output_groups = BTreeMap::<ContentKey, Vec<ContentKey>>::new();
    for (pre_key, result) in &deob_results {
        let Some(report) = &result.report else {
            continue;
        };
        output_groups
            .entry((report.output_sha256.clone(), result.mode))
            .or_default()
            .push(pre_key.clone());
    }

    let output_group_refs = output_groups.iter().collect::<Vec<_>>();
    let readable_results = pool
        .install(|| {
            output_group_refs
                .par_iter()
                .map(|(key, pre_keys)| {
                    let representative = pre_keys
                        .first()
                        .and_then(|pre_key| deob_results.get(pre_key))
                        .context("missing representative deob result")?;
                    format_output(work_path, key, representative)
                        .map(|result| ((*key).clone(), result))
                })
                .collect::<Vec<_>>()
        })
        .into_iter()
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .collect::<BTreeMap<_, _>>();

    let deob_report_dir = project.join("analysis/deobfuscation");
    let string_report_dir = project.join("analysis/string-recovery");
    fs::create_dir_all(&deob_report_dir)?;
    fs::create_dir_all(&string_report_dir)?;

    let mut units = Vec::<Value>::new();
    let mut string_units = Vec::<Value>::new();
    for occurrence in &occurrences {
        let raw_key = (occurrence.raw_sha.clone(), occurrence.mode);
        let raw_group = raw_groups.get(&raw_key).context("missing raw group")?;
        let string_result = string_results
            .get(&raw_key)
            .context("missing string-recovery result")?;
        let pre_key = (string_result.selected_sha.clone(), occurrence.mode);
        let deob_result = deob_results.get(&pre_key).context("missing deob result")?;

        let report_rel = PathBuf::from(format!(
            "analysis/deobfuscation/{:04}.json",
            occurrence.ordinal
        ));
        let string_report_rel = PathBuf::from(format!(
            "analysis/string-recovery/{:04}.json",
            occurrence.ordinal
        ));
        if let Some(source_report) = &string_result.report_path {
            link_or_copy(source_report, &project.join(&string_report_rel))?;
        }
        if let Some(report) = &deob_result.report {
            write_json(&project.join(&report_rel), report)?;
        }

        let deduplicated = occurrence.ordinal != string_result.canonical_ordinal;
        let mut string_row = json!({
            "ordinal": occurrence.ordinal,
            "resource_id": occurrence.unit.get("resource_id").cloned().unwrap_or(Value::Null),
            "url": occurrence.unit.get("url").cloned().unwrap_or(Value::Null),
            "input_path": occurrence.raw_path,
            "report_path": string_report_rel.to_string_lossy(),
            "input_sha256": occurrence.raw_sha,
            "source_mode": occurrence.mode.as_str(),
            "output_sha256": string_result.selected_sha,
            "exit": string_result.exit,
            "changed": string_result.changed,
            "replacements": string_result.replacements,
            "decoders": string_result.decoders,
            "content_group_size": raw_group.len(),
            "deduplicated": deduplicated,
            "deduplicated_from_ordinal": if deduplicated { Value::from(string_result.canonical_ordinal) } else { Value::Null },
        });
        if let Some(error) = &string_result.error {
            let row = as_object_mut(&mut string_row)?;
            row.insert("error".into(), Value::String(error.clone()));
            row.insert(
                "fallback".into(),
                Value::String("original source passed to safe deobfuscator".into()),
            );
        }
        string_units.push(string_row);

        let rel = derived_path(&occurrence.raw_path, "_deobfuscated");
        let readable_rel = derived_path(&occurrence.raw_path, "_readable");
        let mut row = json!({
            "ordinal": occurrence.ordinal,
            "resource_id": occurrence.unit.get("resource_id").cloned().unwrap_or(Value::Null),
            "url": occurrence.unit.get("url").cloned().unwrap_or(Value::Null),
            "raw_path": occurrence.raw_path,
            "input_path": occurrence.raw_path,
            "output_path": rel.to_string_lossy(),
            "readable_output_path": readable_rel.to_string_lossy(),
            "report_path": report_rel.to_string_lossy(),
            "string_recovery_report_path": string_report_rel.to_string_lossy(),
            "string_recovery_changed": string_result.changed,
            "string_recovery_replacements": string_result.replacements,
            "input_sha256": occurrence.raw_sha,
            "source_mode": occurrence.mode.as_str(),
            "pre_deob_sha256": string_result.selected_sha,
            "exit": deob_result.exit,
            "content_group_size": raw_group.len(),
            "deduplicated": deduplicated,
            "deduplicated_from_ordinal": if deduplicated { Value::from(string_result.canonical_ordinal) } else { Value::Null },
        });
        let Some(report) = &deob_result.report else {
            if let Some(error) = &deob_result.error {
                as_object_mut(&mut row)?.insert("error".into(), Value::String(error.clone()));
            }
            units.push(row);
            continue;
        };

        let mut transforms = report.transforms.clone();
        if string_result.replacements != 0 {
            transforms.insert("encoded_string_decode".into(), string_result.replacements);
        }
        let output_path = deob_result
            .output_path
            .as_ref()
            .context("missing successful deob output")?;
        link_or_copy(output_path, &project.join(&rel))?;
        let output_key = (report.output_sha256.clone(), occurrence.mode);
        let readable = readable_results
            .get(&output_key)
            .context("missing readable output")?;
        link_or_copy(&readable.path, &project.join(&readable_rel))?;
        let row_object = as_object_mut(&mut row)?;
        row_object.extend(Map::from_iter([
            (
                "changed".into(),
                Value::Bool(report.changed || string_result.changed),
            ),
            ("iterations".into(), Value::from(report.iterations)),
            ("transforms".into(), serde_json::to_value(&transforms)?),
            (
                "arithmetic_state_proofs".into(),
                serde_json::to_value(&report.arithmetic_state_proofs)?,
            ),
            (
                "safe_static_only".into(),
                Value::Bool(report.safe_static_only),
            ),
            (
                "presentation_formatted".into(),
                Value::Bool(report.presentation_formatted),
            ),
            (
                "runtime_semantics_preserved_by_design".into(),
                Value::Bool(report.runtime_semantics_preserved_by_design),
            ),
            (
                "output_sha256".into(),
                Value::String(report.output_sha256.clone()),
            ),
            ("readable_formatted".into(), Value::Bool(readable.formatted)),
        ]));
        if let Some(error) = &readable.error {
            row_object.insert("readable_format_error".into(), Value::String(error.clone()));
        }
        units.push(row);
    }

    let string_changed = string_units
        .iter()
        .filter(|unit| unit.get("changed").and_then(Value::as_bool) == Some(true))
        .count();
    let string_failed = string_units
        .iter()
        .filter(|unit| unit.get("exit").and_then(Value::as_i64).unwrap_or(0) != 0)
        .count();
    let string_replacements = string_units
        .iter()
        .filter_map(|unit| unit.get("replacements").and_then(Value::as_u64))
        .filter_map(|count| usize::try_from(count).ok())
        .fold(0usize, usize::saturating_add);
    let string_index = json!({
        "schema": STRING_RECOVERY.schema,
        "safe_static_only": true,
        "mode_sensitive_deduplication": true,
        "recoverer": options.string_recoverer.to_string_lossy(),
        "units": string_units,
        "summary": {
            "javascript_units": occurrences.len(),
            "unique_input_bodies": raw_groups.len(),
            "deduplicated_units": occurrences.len().saturating_sub(raw_groups.len()),
            "unique_post_recovery_bodies": pre_deob_groups.len(),
            "changed_units": string_changed,
            "failed_units": string_failed,
            "replacements": string_replacements,
            "invocations": raw_groups.len(),
        },
    });
    write_artifact(project, STRING_RECOVERY, &string_index)?;

    let changed = units
        .iter()
        .filter(|unit| unit.get("changed").and_then(Value::as_bool) == Some(true))
        .count();
    let failed = units
        .iter()
        .filter(|unit| unit.get("exit").and_then(Value::as_i64).unwrap_or(0) != 0)
        .count();
    let mut totals = BTreeMap::<String, usize>::new();
    for unit in &units {
        if let Some(transforms) = unit.get("transforms").and_then(Value::as_object) {
            for (kind, count) in transforms {
                let count = count
                    .as_u64()
                    .and_then(|value| usize::try_from(value).ok())
                    .unwrap_or(0);
                *totals.entry(kind.clone()).or_default() += count;
            }
        }
    }

    let index = json!({
        "schema": DEOBFUSCATION.schema,
        "safe_static_only": true,
        "mode_sensitive_deduplication": true,
        "runtime_semantics_preserved_by_design": true,
        "presentation_formatted": false,
        "deobfuscator": "jsvm_lift::safe_deob",
        "formatter": "jsvm_lift::js_format",
        "string_recovery": STRING_RECOVERY.relative_path,
        "units": units,
        "summary": {
            "javascript_units": occurrences.len(),
            "unique_raw_inputs": raw_groups.len(),
            "deduplicated_raw_units": occurrences.len().saturating_sub(raw_groups.len()),
            "unique_pre_deob_inputs": pre_deob_groups.len(),
            "unique_deob_outputs": output_groups.len(),
            "string_recovery_invocations": raw_groups.len(),
            "safe_deob_invocations": pre_deob_groups.len(),
            "readable_format_invocations": output_groups.len(),
            "jobs": jobs,
            "changed_units": changed,
            "failed_units": failed,
            "string_recovery_changed_units": string_changed,
            "string_recovery_replacements": string_replacements,
            "transforms": totals,
        },
    });
    write_artifact(project, DEOBFUSCATION, &index)?;

    Ok(ProjectDeobSummary {
        javascript_units: occurrences.len(),
        unique_raw_inputs: raw_groups.len(),
        unique_pre_deob_inputs: pre_deob_groups.len(),
        unique_deob_outputs: output_groups.len(),
        changed_units: changed,
        failed_units: failed,
        string_recovery_changed_units: string_changed,
        string_recovery_replacements: string_replacements,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis_artifacts::{
        load_artifact, write_artifact, DEOBFUSCATION, SOURCE_INDEX, STRING_RECOVERY,
    };
    use std::time::Duration;

    #[test]
    fn optional_helper_timeout_is_bounded_and_kills_descendants() -> Result<()> {
        let work = tempfile::tempdir()?;
        let pid_file = work.path().join("grandchild.pid");
        let mut command = Command::new("sh");
        command
            .arg("-c")
            .arg("sleep 30 & echo $! > \"$1\"; wait")
            .arg("sh")
            .arg(&pid_file);
        let result =
            run_command_with_timeout(&mut command, work.path(), Duration::from_millis(200))?;
        assert_eq!(result.code, 124);
        assert!(String::from_utf8_lossy(&result.stderr).contains("timed out"));
        #[cfg(unix)]
        {
            let grandchild = fs::read_to_string(&pid_file)
                .with_context(|| format!("reading {}", pid_file.display()))?;
            let status = Command::new("kill")
                .arg("-0")
                .arg(grandchild.trim())
                .status()?;
            assert!(!status.success(), "timed-out helper grandchild survived");
        }
        Ok(())
    }

    #[test]
    fn project_mode_keeps_identical_module_and_commonjs_inputs_semantically_distinct() -> Result<()>
    {
        let temp = tempfile::tempdir()?;
        let project = temp.path().join("project");
        let analysis = project.join("analysis");
        let src = project.join("src");
        fs::create_dir_all(&analysis)?;
        fs::create_dir_all(&src)?;
        let source = b"return 1;\n";
        fs::write(src.join("same.mjs"), source)?;
        fs::write(src.join("same.cjs"), source)?;
        write_artifact(
            &project,
            SOURCE_INDEX,
            &json!({
                "schema": SOURCE_INDEX.schema,
                "units": [
                    {"kind":"javascript","raw_path":"src/same.mjs","source_path":"src/same.mjs"},
                    {"kind":"javascript","raw_path":"src/same.cjs","source_path":"src/same.cjs"}
                ],
                "summary": {}
            }),
        )?;

        let recoverer = temp.path().join("recover.py");
        fs::write(
            &recoverer,
            r#"import hashlib, json, sys
from pathlib import Path
src, dst = Path(sys.argv[1]), Path(sys.argv[2])
report = Path(sys.argv[sys.argv.index("--report") + 1])
source = src.read_bytes()
recovered = source + b"// recovered\n"
dst.parent.mkdir(parents=True, exist_ok=True)
dst.write_bytes(recovered)
report.parent.mkdir(parents=True, exist_ok=True)
report.write_text(json.dumps({
    "safe_static_only": True,
    "input_sha256": hashlib.sha256(source).hexdigest(),
    "output_sha256": hashlib.sha256(recovered).hexdigest(),
    "changed": True,
    "replacements": 1,
    "decoders": [],
}) + "\n")
"#,
        )?;

        let summary = materialize_project_deobfuscation(
            &project,
            &ProjectDeobOptions {
                repo_root: std::env::current_dir()?,
                string_recoverer: recoverer,
                decoder_recoverer: temp.path().join("unused-decoder"),
                jobs: Some(2),
                max_iterations: 16,
            },
        )?;
        assert_eq!(summary.javascript_units, 2);
        assert_eq!(summary.unique_raw_inputs, 2);
        assert_eq!(summary.unique_pre_deob_inputs, 2);

        let artifact =
            load_artifact(&project, DEOBFUSCATION, false)?.context("missing deob artifact")?;
        assert_eq!(
            artifact
                .get("mode_sensitive_deduplication")
                .and_then(Value::as_bool),
            Some(true)
        );
        let units = artifact["units"].as_array().context("deob units")?;
        let module = units
            .iter()
            .find(|unit| unit["raw_path"] == "src/same.mjs")
            .context("module row")?;
        let commonjs = units
            .iter()
            .find(|unit| unit["raw_path"] == "src/same.cjs")
            .context("commonjs row")?;
        assert_eq!(module["source_mode"], "module");
        assert_eq!(commonjs["source_mode"], "commonjs");
        assert_ne!(module["exit"], 0);
        assert_eq!(commonjs["exit"], 0);
        assert_eq!(commonjs["safe_static_only"], true);
        assert_ne!(module["pre_deob_sha256"], module["input_sha256"]);
        assert_ne!(commonjs["pre_deob_sha256"], commonjs["input_sha256"]);

        let strings =
            load_artifact(&project, STRING_RECOVERY, false)?.context("missing string artifact")?;
        let rows = strings["units"].as_array().context("string rows")?;
        let modes = rows
            .iter()
            .filter_map(|row| row["source_mode"].as_str())
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            modes,
            std::collections::BTreeSet::from(["commonjs", "module"])
        );
        assert!(rows.iter().all(|row| row["exit"] == 0));
        assert!(rows.iter().all(|row| row.get("fallback").is_none()));
        assert!(rows.iter().all(|row| row["changed"] == true));
        assert!(rows
            .iter()
            .all(|row| row["input_sha256"] != row["output_sha256"]));
        assert_eq!(strings["summary"]["unique_input_bodies"], 2);
        assert_eq!(strings["summary"]["failed_units"], 0);
        Ok(())
    }
}
