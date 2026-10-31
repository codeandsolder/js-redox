use crate::{
    analysis_artifacts::{
        load_artifact, write_artifact, BUNDLES, DEOBFUSCATION, GENERATED_RECOVERY, JSVM_INDEX,
        SOURCE_INDEX,
    },
    bounded_process::{command_error, run_command_with_timeout, CommandResult},
    content_dedup::{link_or_copy, sha256_path},
    js_format::format_source,
    safe_deob::{deobfuscate_source, SourceMode},
    scan_report::{scan_file, ScanReport},
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::Duration,
};
use tempfile::Builder as TempDirBuilder;

#[derive(Debug, Clone)]
pub struct ProjectScanOptions {
    pub repo_root: PathBuf,
    pub string_recoverer: PathBuf,
    pub switch_ir: PathBuf,
    pub table_ir: PathBuf,
    pub max_generated_depth: usize,
    pub max_code_units: usize,
}

impl ProjectScanOptions {
    #[must_use]
    pub fn with_defaults(
        repo_root: PathBuf,
        string_recoverer: PathBuf,
        switch_ir: PathBuf,
        table_ir: PathBuf,
    ) -> Self {
        Self {
            repo_root,
            string_recoverer,
            switch_ir,
            table_ir,
            max_generated_depth: 8,
            max_code_units: 256,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProjectScanSummary {
    pub code_units: usize,
    pub scanner_invocations: usize,
    pub deduplicated_scans: usize,
    pub dynamic_units: usize,
    pub confirmed_vm_units: usize,
    pub handler_table_candidates: usize,
    pub failures: usize,
}

fn write_json(path: &Path, value: &impl serde::Serialize) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    let mut encoded = serde_json::to_string_pretty(value)?;
    encoded.push('\n');
    fs::write(path, encoded).with_context(|| format!("writing {}", path.display()))
}

fn value_string(value: &Value, field: &str) -> Option<String> {
    value
        .get(field)
        .and_then(Value::as_str)
        .map(ToOwned::to_owned)
}

fn value_usize(value: &Value, field: &str) -> usize {
    value
        .get(field)
        .and_then(Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
        .unwrap_or(0)
}

fn relative_string(project: &Path, path: &Path) -> Result<String> {
    Ok(path
        .strip_prefix(project)
        .with_context(|| {
            format!(
                "{} is outside project {}",
                path.display(),
                project.display()
            )
        })?
        .to_string_lossy()
        .into_owned())
}

fn generated_output_path(root: &str, scan_id: usize, ordinal: usize) -> PathBuf {
    PathBuf::from("src")
        .join(root)
        .join(format!("{scan_id:04}"))
        .join(format!("embedded-{ordinal:03}.js"))
}

fn direct_summary(report: &ScanReport) -> Map<String, Value> {
    let handler_tables = &report.handler_function_tables;
    let mut summary = Map::new();
    summary.insert(
        "confirmed_dispatchers".into(),
        report
            .functions
            .iter()
            .filter(|function| function.confirmed_dispatch)
            .count()
            .into(),
    );
    summary.insert("opcode_maps".into(), report.opcode_maps.len().into());
    summary.insert(
        "direct_switch_maps".into(),
        report.direct_switch_maps.len().into(),
    );
    summary.insert(
        "confirmed_direct_switch_maps".into(),
        report
            .direct_switch_maps
            .iter()
            .filter(|map| map.confirmed_vm)
            .count()
            .into(),
    );
    summary.insert(
        "weak_direct_switch_maps".into(),
        report
            .direct_switch_maps
            .iter()
            .filter(|map| !map.confirmed_vm && map.vm_evidence_score >= 3)
            .count()
            .into(),
    );
    summary.insert("handler_tables".into(), handler_tables.len().into());
    summary.insert(
        "largest_handler_table".into(),
        handler_tables
            .iter()
            .map(|table| table.function_values)
            .max()
            .unwrap_or(0)
            .into(),
    );
    summary.insert(
        "byte_transducers".into(),
        report.byte_transducers.len().into(),
    );
    summary.insert("table_vms".into(), report.table_vms.len().into());
    summary.insert("embedded_code_units".into(), report.embedded.len().into());
    summary
}

fn recover_generated_unit(
    project: &Path,
    raw: &Path,
    raw_rel: &str,
    scan_id: usize,
    ordinal: usize,
    options: &ProjectScanOptions,
) -> Result<Value> {
    let recovery_rel =
        PathBuf::from("analysis/generated-recovery").join(format!("{scan_id:04}-{ordinal:03}"));
    let recovery_dir = project.join(&recovery_rel);
    fs::create_dir_all(&recovery_dir)
        .with_context(|| format!("creating {}", recovery_dir.display()))?;
    let string_tmp = recovery_dir.join("string-recovered.js");
    let string_report = recovery_dir.join("string-recovery.json");
    let deob_report = recovery_dir.join("deobfuscation.json");
    let safe_rel = generated_output_path("_dynamic_deobfuscated", scan_id, ordinal);
    let safe_dest = project.join(&safe_rel);
    let readable_rel = generated_output_path("_dynamic", scan_id, ordinal);
    let readable_dest = project.join(&readable_rel);
    if let Some(parent) = safe_dest.parent() {
        fs::create_dir_all(parent)?;
    }
    if let Some(parent) = readable_dest.parent() {
        fs::create_dir_all(parent)?;
    }

    let raw_sha = sha256_path(raw)?;
    let mut row = json!({
        "parent_scan_id": scan_id,
        "ordinal": ordinal,
        "raw_path": raw_rel,
        "raw_sha256": raw_sha,
        "string_recovery_report": relative_string(project, &string_report)?,
        "deobfuscation_report": relative_string(project, &deob_report)?,
    });

    let string_work = TempDirBuilder::new()
        .prefix(".string-recovery-")
        .tempdir_in(&recovery_dir)
        .with_context(|| format!("creating helper scratch in {}", recovery_dir.display()))?;
    let mut string_command = Command::new("uv");
    string_command
        .arg("run")
        .arg("--no-project")
        .arg("python")
        .arg(&options.string_recoverer)
        .arg(raw)
        .arg(&string_tmp)
        .arg("--report")
        .arg(&string_report)
        .current_dir(&options.repo_root);
    let string_output = run_command_with_timeout(
        &mut string_command,
        string_work.path(),
        Duration::from_secs(180),
    )?;

    let mut selected = raw.to_path_buf();
    let mut string_ok = false;
    let mut string_changed = false;
    if string_output.code == 0 && string_tmp.is_file() && string_report.is_file() {
        let metadata = fs::read_to_string(&string_report)
            .ok()
            .and_then(|text| serde_json::from_str::<Value>(&text).ok());
        if let Some(metadata) = metadata {
            let output_sha = sha256_path(&string_tmp)?;
            string_ok = metadata.get("safe_static_only").and_then(Value::as_bool) == Some(true)
                && metadata.get("input_sha256").and_then(Value::as_str) == Some(raw_sha.as_str())
                && metadata.get("output_sha256").and_then(Value::as_str)
                    == Some(output_sha.as_str());
            if string_ok {
                selected = string_tmp.clone();
                string_changed = metadata
                    .get("changed")
                    .and_then(Value::as_bool)
                    .unwrap_or(false);
                row["string_recovery"] = json!({
                    "exit": 0,
                    "changed": string_changed,
                    "replacements": value_usize(&metadata, "replacements"),
                    "output_sha256": output_sha,
                });
            }
        }
    }
    if !string_ok {
        row["string_recovery"] = json!({
            "exit": if string_output.code == 0 { 1 } else { string_output.code },
            "changed": false,
            "replacements": 0,
            "error": if string_output.code == 0 {
                "string-recovery provenance/hash validation failed".to_owned()
            } else {
                command_error(&string_output)
            },
        });
    }

    let selected_source =
        fs::read_to_string(&selected).with_context(|| format!("reading {}", selected.display()))?;
    let selected_sha = sha256_path(&selected)?;
    let deob = deobfuscate_source(
        &selected_source,
        selected.display().to_string(),
        SourceMode::Auto,
        16,
        false,
    );
    let (analysis_rel, selected_stage) = match deob {
        Ok(outcome) => {
            let output_sha = crate::sha256_hex(outcome.source.as_bytes());
            if outcome.report.input_sha256 != selected_sha
                || outcome.report.output_sha256 != output_sha
                || !outcome.report.safe_static_only
                || !outcome.report.runtime_semantics_preserved_by_design
                || outcome.report.presentation_formatted
            {
                bail!(
                    "safe deobfuscation provenance invariant failed for {}",
                    selected.display()
                );
            }
            fs::write(&safe_dest, outcome.source.as_bytes())
                .with_context(|| format!("writing {}", safe_dest.display()))?;
            write_json(&deob_report, &outcome.report)?;
            row["deobfuscation"] = json!({
                "exit": 0,
                "changed": outcome.report.changed,
                "iterations": outcome.report.iterations,
                "transforms": outcome.report.transforms,
                "output_sha256": output_sha,
            });
            (safe_rel.clone(), "safe_deobfuscation")
        }
        Err(error) => {
            row["deobfuscation"] = json!({"exit": 1, "changed": false, "error": error.to_string()});
            if string_ok && string_changed {
                fs::copy(&string_tmp, &safe_dest).with_context(|| {
                    format!(
                        "copying {} to {}",
                        string_tmp.display(),
                        safe_dest.display()
                    )
                })?;
                (safe_rel.clone(), "string_recovery_only")
            } else {
                (PathBuf::from(raw_rel), "exact_fallback")
            }
        }
    };

    let analysis_source = project.join(&analysis_rel);
    let exact = fs::read_to_string(&analysis_source)
        .with_context(|| format!("reading {}", analysis_source.display()))?;
    let (readable, readable_formatted, format_error) = match format_source(&exact) {
        Ok(formatted) => (formatted, true, None),
        Err(error) => (exact, false, Some(error.to_string())),
    };
    fs::write(&readable_dest, readable.as_bytes())
        .with_context(|| format!("writing {}", readable_dest.display()))?;
    let object = row
        .as_object_mut()
        .context("generated recovery row must be an object")?;
    object.insert("selected_stage".into(), selected_stage.into());
    object.insert(
        "analysis_path".into(),
        analysis_rel.to_string_lossy().into_owned().into(),
    );
    object.insert(
        "analysis_sha256".into(),
        sha256_path(&analysis_source)?.into(),
    );
    object.insert(
        "readable_path".into(),
        readable_rel.to_string_lossy().into_owned().into(),
    );
    object.insert("readable_formatted".into(), readable_formatted.into());
    object.insert(
        "readable_sha256".into(),
        sha256_path(&readable_dest)?.into(),
    );
    if let Some(error) = format_error {
        object.insert("readable_format_error".into(), error.into());
    }
    Ok(row)
}

fn reuse_generated_unit(
    project: &Path,
    raw_rel: &str,
    scan_id: usize,
    ordinal: usize,
    cached: &Value,
) -> Result<Value> {
    let recovery_rel =
        PathBuf::from("analysis/generated-recovery").join(format!("{scan_id:04}-{ordinal:03}"));
    let recovery_dir = project.join(&recovery_rel);
    fs::create_dir_all(&recovery_dir)?;
    let string_report_rel = recovery_rel.join("string-recovery.json");
    let deob_report_rel = recovery_rel.join("deobfuscation.json");
    for (field, destination) in [
        ("string_recovery_report", &string_report_rel),
        ("deobfuscation_report", &deob_report_rel),
    ] {
        if let Some(source) = value_string(cached, field) {
            let source = project.join(source);
            if source.is_file() {
                link_or_copy(&source, &project.join(destination))?;
            }
        }
    }

    let safe_rel = generated_output_path("_dynamic_deobfuscated", scan_id, ordinal);
    let readable_rel = generated_output_path("_dynamic", scan_id, ordinal);
    let selected_stage = value_string(cached, "selected_stage").unwrap_or_default();
    let analysis_rel = if selected_stage == "exact_fallback" {
        PathBuf::from(raw_rel)
    } else {
        let source =
            value_string(cached, "analysis_path").context("cached analysis_path missing")?;
        link_or_copy(&project.join(source), &project.join(&safe_rel))?;
        safe_rel.clone()
    };
    let cached_readable =
        value_string(cached, "readable_path").context("cached readable_path missing")?;
    link_or_copy(&project.join(cached_readable), &project.join(&readable_rel))?;

    let mut row = cached.clone();
    let object = row
        .as_object_mut()
        .context("cached generated recovery row must be object")?;
    object.insert("parent_scan_id".into(), scan_id.into());
    object.insert("ordinal".into(), ordinal.into());
    object.insert("raw_path".into(), raw_rel.into());
    object.insert(
        "string_recovery_report".into(),
        string_report_rel.to_string_lossy().into_owned().into(),
    );
    object.insert(
        "deobfuscation_report".into(),
        deob_report_rel.to_string_lossy().into_owned().into(),
    );
    object.insert(
        "analysis_path".into(),
        analysis_rel.to_string_lossy().into_owned().into(),
    );
    object.insert(
        "readable_path".into(),
        readable_rel.to_string_lossy().into_owned().into(),
    );
    object.insert("deduplicated".into(), true.into());
    object.insert(
        "deduplicated_from_parent_scan_id".into(),
        cached.get("parent_scan_id").cloned().unwrap_or(Value::Null),
    );
    object.insert(
        "deduplicated_from_ordinal".into(),
        cached.get("ordinal").cloned().unwrap_or(Value::Null),
    );
    Ok(row)
}

fn run_ir_tool(
    executable: &Path,
    source: &Path,
    report_path: &Path,
    output_path: &Path,
    repo_root: &Path,
) -> Result<CommandResult> {
    let parent = output_path
        .parent()
        .context("IR output path has no parent")?;
    let work = TempDirBuilder::new()
        .prefix(".ir-tool-")
        .tempdir_in(parent)
        .with_context(|| format!("creating IR helper scratch in {}", parent.display()))?;
    let mut command = Command::new(executable);
    command
        .arg(source)
        .arg(report_path)
        .arg("--output")
        .arg(output_path)
        .current_dir(repo_root);
    run_command_with_timeout(&mut command, work.path(), Duration::from_secs(180))
}

fn queue_unit(
    queue: &mut VecDeque<Value>,
    seen_paths: &mut BTreeSet<String>,
    unit: Value,
    max_code_units: usize,
    accepted: usize,
) -> Option<usize> {
    let path = value_string(&unit, "path")?;
    if seen_paths.contains(&path) || accepted + queue.len() >= max_code_units {
        return None;
    }
    seen_paths.insert(path);
    let scan_id = accepted + queue.len();
    queue.push_back(unit);
    Some(scan_id)
}

pub fn scan_project(project: &Path, options: &ProjectScanOptions) -> Result<ProjectScanSummary> {
    let source_index = load_artifact(project, SOURCE_INDEX, false)?
        .context("source index is required for VM project scanning")?;
    let deob = load_artifact(project, DEOBFUSCATION, true)?.unwrap_or_else(|| json!({"units": []}));
    let deob_by_raw = deob
        .get("units")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|unit| {
            let raw = value_string(unit, "raw_path")?;
            if value_usize(unit, "exit") != 0
                || unit.get("output_path").and_then(Value::as_str).is_none()
            {
                return None;
            }
            Some((raw, unit.clone()))
        })
        .collect::<BTreeMap<_, _>>();

    let mut bundle_spans_by_parent = BTreeMap::<String, BTreeSet<(i64, i64)>>::new();
    if let Some(bundles) = load_artifact(project, BUNDLES, true)? {
        for bundle in bundles
            .get("bundles")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let Some(parent) = value_string(bundle, "parent_path") else {
                continue;
            };
            let Some(start) = bundle.get("module_table_start").and_then(Value::as_i64) else {
                continue;
            };
            let Some(end) = bundle.get("module_table_end").and_then(Value::as_i64) else {
                continue;
            };
            bundle_spans_by_parent
                .entry(parent)
                .or_default()
                .insert((start, end));
        }
    }

    let outdir = project.join("analysis/jsvm");
    fs::create_dir_all(&outdir)?;
    let mut queue = VecDeque::<Value>::new();
    let mut seen_paths = BTreeSet::<String>::new();
    let source_units = source_index
        .get("units")
        .and_then(Value::as_array)
        .context("source index units must be an array")?;
    for source_unit in source_units {
        let kind = source_unit.get("kind").and_then(Value::as_str);
        if !matches!(kind, Some("javascript" | "javascript_unparsed")) {
            continue;
        }
        let Some(raw_path) = value_string(source_unit, "raw_path") else {
            continue;
        };
        let derived = deob_by_raw.get(&raw_path);
        let scan_path = derived
            .and_then(|unit| value_string(unit, "output_path"))
            .unwrap_or_else(|| raw_path.clone());
        let mut unit = json!({
            "origin": source_unit.get("origin").and_then(Value::as_str).unwrap_or("resource"),
            "resource_id": source_unit.get("resource_id").cloned().unwrap_or(Value::Null),
            "url": source_unit.get("url").cloned().unwrap_or(Value::Null),
            "raw_path": raw_path,
            "path": scan_path,
            "analysis_origin": if derived.is_some() { "safe_deobfuscation" } else { "captured_source" },
            "deobfuscation_ordinal": derived.and_then(|unit| unit.get("ordinal")).cloned().unwrap_or(Value::Null),
            "generated_depth": 0,
        });
        if let Some(ordinal) = source_unit.get("ordinal") {
            unit["ordinal"] = ordinal.clone();
        }
        let _ = queue_unit(&mut queue, &mut seen_paths, unit, options.max_code_units, 0);
    }

    let mut rows = Vec::<Value>::new();
    let mut dynamic_units = Vec::<Value>::new();
    let mut generated_recovery = Vec::<Value>::new();
    let mut generated_recovery_cache = BTreeMap::<String, Value>::new();
    let mut scanner_cache = BTreeMap::<String, (usize, ScanReport)>::new();
    let mut scanner_invocations = 0usize;
    let mut deduplicated_scans = 0usize;

    while let Some(unit) = queue.pop_front() {
        let scan_id = rows.len();
        let path = value_string(&unit, "path").context("queued unit path missing")?;
        let source = project.join(&path);
        let mut row = unit.clone();
        row["scan_id"] = scan_id.into();
        if !source.is_file() {
            row["scanner_exit"] = 1.into();
            row["error"] = format!("missing source path: {}", source.display()).into();
            rows.push(row);
            continue;
        }

        let source_sha = sha256_path(&source)?;
        row["analysis_sha256"] = source_sha.clone().into();
        let cached = scanner_cache.get(&source_sha);
        let (report, deduplicated_from) = match cached {
            Some((cached_scan_id, cached_report)) if cached_report.embedded.is_empty() => {
                deduplicated_scans += 1;
                (cached_report.clone(), Some(*cached_scan_id))
            }
            _ => {
                let dump_dir = outdir.join("embedded").join(format!("{scan_id:04}"));
                scanner_invocations += 1;
                let report = match scan_file(&source, Some(&dump_dir)) {
                    Ok(report) => report,
                    Err(error) => {
                        row["scanner_exit"] = 1.into();
                        row["scanner_deduplicated"] = false.into();
                        row["error"] = error.to_string().into();
                        rows.push(row);
                        continue;
                    }
                };
                if report.embedded.is_empty() {
                    scanner_cache.insert(source_sha, (scan_id, report.clone()));
                }
                (report, None)
            }
        };
        row["scanner_exit"] = 0.into();
        row["scanner_deduplicated"] = deduplicated_from.is_some().into();
        if let Some(cached_scan_id) = deduplicated_from {
            row["scanner_deduplicated_from_scan_id"] = cached_scan_id.into();
        }
        row["bytes"] = fs::metadata(&source)?.len().into();
        let report_path = outdir.join(format!("{scan_id:04}.json"));
        write_json(&report_path, &report)?;
        row["report"] = relative_string(project, &report_path)?.into();
        for (key, value) in direct_summary(&report) {
            row[key] = value;
        }

        let known_bundle_spans = bundle_spans_by_parent.get(&path);
        let large_handler_tables = report
            .handler_function_tables
            .iter()
            .filter(|table| table.function_values >= 32)
            .collect::<Vec<_>>();
        let dense_large_handler_tables = large_handler_tables
            .iter()
            .copied()
            .filter(|table| table.entries > 0 && table.function_values * 4 >= table.entries * 3)
            .collect::<Vec<_>>();
        let bundle_handler_tables = dense_large_handler_tables
            .iter()
            .copied()
            .filter(|table| {
                known_bundle_spans.is_some_and(|spans| {
                    spans.contains(&(i64::from(table.start), i64::from(table.end)))
                })
            })
            .count();
        let non_bundle_handler_tables = dense_large_handler_tables
            .iter()
            .copied()
            .filter(|table| {
                !known_bundle_spans.is_some_and(|spans| {
                    spans.contains(&(i64::from(table.start), i64::from(table.end)))
                })
            })
            .collect::<Vec<_>>();
        let looped_dynamic_handler_tables = non_bundle_handler_tables
            .iter()
            .copied()
            .filter(|table| table.looped_dynamic_call_sites > 0)
            .collect::<Vec<_>>();
        row["large_handler_tables"] = large_handler_tables.len().into();
        row["dense_large_handler_tables"] = dense_large_handler_tables.len().into();
        row["bundle_module_table_handler_tables"] = bundle_handler_tables.into();
        row["largest_non_bundle_handler_table"] = non_bundle_handler_tables
            .iter()
            .map(|table| table.function_values)
            .max()
            .unwrap_or(0)
            .into();
        row["looped_dynamic_handler_tables"] = looped_dynamic_handler_tables.len().into();
        row["largest_looped_dynamic_handler_table"] = looped_dynamic_handler_tables
            .iter()
            .map(|table| table.function_values)
            .max()
            .unwrap_or(0)
            .into();

        let parent_depth = value_usize(&unit, "generated_depth");
        let mut embedded_units = Vec::<Value>::new();
        for (offset, node) in report.embedded.iter().enumerate() {
            let ordinal = offset + 1;
            let Some(dumped) = node.dump_path.as_deref() else {
                continue;
            };
            let raw = PathBuf::from(dumped);
            let raw_rel = relative_string(project, &raw)?;
            let depth = parent_depth + 1;
            let raw_sha = sha256_path(&raw)?;
            let recovery = match generated_recovery_cache.get(&raw_sha) {
                Some(cached) => reuse_generated_unit(project, &raw_rel, scan_id, ordinal, cached)?,
                None => {
                    let mut recovery =
                        recover_generated_unit(project, &raw, &raw_rel, scan_id, ordinal, options)?;
                    recovery["deduplicated"] = false.into();
                    generated_recovery_cache.insert(raw_sha, recovery.clone());
                    recovery
                }
            };
            let recovery_ordinal = generated_recovery.len();
            generated_recovery.push(recovery.clone());
            let mut item = json!({
                "parent_scan_id": scan_id,
                "ordinal": ordinal,
                "depth": depth,
                "kind": node.kind,
                "outer_start": node.outer_start,
                "outer_end": node.outer_end,
                "body_bytes": node.body_bytes,
                "raw_dump": raw_rel,
                "source_path": recovery.get("readable_path").cloned().unwrap_or(Value::Null),
                "analysis_path": recovery.get("analysis_path").cloned().unwrap_or(Value::Null),
                "analysis_stage": recovery.get("selected_stage").cloned().unwrap_or(Value::Null),
                "recovery_report": format!("analysis/generated-recovery/{scan_id:04}-{ordinal:03}"),
                "formatted": recovery.get("readable_formatted").cloned().unwrap_or(Value::Bool(false)),
                "handler_tables": node.handler_function_tables.len(),
                "table_vms": node.table_vms.len(),
                "opcode_maps": node.opcode_maps.len(),
            });
            let child_scan_id = if depth <= options.max_generated_depth {
                let child = json!({
                    "origin": "generated_dynamic_code",
                    "resource_id": unit.get("resource_id").cloned().unwrap_or(Value::Null),
                    "url": unit.get("url").cloned().unwrap_or(Value::Null),
                    "raw_path": raw_rel,
                    "path": recovery.get("analysis_path").cloned().unwrap_or(Value::Null),
                    "readable_path": recovery.get("readable_path").cloned().unwrap_or(Value::Null),
                    "analysis_origin": recovery.get("selected_stage").cloned().unwrap_or(Value::Null),
                    "generated_recovery_ordinal": recovery_ordinal,
                    "parent_scan_id": scan_id,
                    "parent_dynamic_ordinal": ordinal,
                    "generated_depth": depth,
                });
                queue_unit(
                    &mut queue,
                    &mut seen_paths,
                    child,
                    options.max_code_units,
                    rows.len() + 1,
                )
            } else {
                None
            };
            item["child_scan_id"] = child_scan_id.map_or(Value::Null, Value::from);
            embedded_units.push(item.clone());
            dynamic_units.push(item);
        }
        row["embedded_units"] = Value::Array(embedded_units);

        if value_usize(&row, "confirmed_direct_switch_maps") > 0 {
            let output_path = outdir.join(format!("{scan_id:04}.switch-ir.json"));
            let output = run_ir_tool(
                &options.switch_ir,
                &source,
                &report_path,
                &output_path,
                &options.repo_root,
            )?;
            row["switch_ir_exit"] = output.code.into();
            if output.code == 0 {
                row["switch_ir"] = relative_string(project, &output_path)?.into();
            } else {
                row["switch_ir_error"] = command_error(&output).into();
            }
        }
        if value_usize(&row, "table_vms") > 0 {
            let output_path = outdir.join(format!("{scan_id:04}.table-ir.json"));
            let output = run_ir_tool(
                &options.table_ir,
                &source,
                &report_path,
                &output_path,
                &options.repo_root,
            )?;
            row["table_ir_exit"] = output.code.into();
            if output.code == 0 {
                row["table_ir"] = relative_string(project, &output_path)?.into();
            } else {
                row["table_ir_error"] = command_error(&output).into();
            }
        }

        let confirmed_vm_signal = [
            "confirmed_dispatchers",
            "opcode_maps",
            "confirmed_direct_switch_maps",
            "table_vms",
            "byte_transducers",
        ]
        .iter()
        .any(|field| value_usize(&row, field) > 0);
        let large_handler_table_candidate =
            !confirmed_vm_signal && value_usize(&row, "largest_looped_dynamic_handler_table") >= 32;
        let vm_signal = confirmed_vm_signal
            || value_usize(&row, "weak_direct_switch_maps") > 0
            || large_handler_table_candidate;
        row["confirmed_vm_signal"] = confirmed_vm_signal.into();
        row["large_handler_table_candidate"] = large_handler_table_candidate.into();
        row["vm_signal"] = vm_signal.into();
        rows.push(row);
    }

    let safe_deobfuscation = generated_recovery
        .iter()
        .filter(|row| {
            row.get("selected_stage").and_then(Value::as_str) == Some("safe_deobfuscation")
        })
        .count();
    let string_recovery_only = generated_recovery
        .iter()
        .filter(|row| {
            row.get("selected_stage").and_then(Value::as_str) == Some("string_recovery_only")
        })
        .count();
    let exact_fallback = generated_recovery
        .iter()
        .filter(|row| row.get("selected_stage").and_then(Value::as_str) == Some("exact_fallback"))
        .count();
    let deduplicated_units = generated_recovery
        .iter()
        .filter(|row| row.get("deduplicated").and_then(Value::as_bool) == Some(true))
        .count();
    let recovery_index = json!({
        "schema": GENERATED_RECOVERY.schema,
        "safe_static_only": true,
        "units": generated_recovery,
        "summary": {
            "generated_units": generated_recovery.len(),
            "unique_raw_inputs": generated_recovery_cache.len(),
            "deduplicated_units": deduplicated_units,
            "safe_deobfuscation": safe_deobfuscation,
            "string_recovery_only": string_recovery_only,
            "exact_fallback": exact_fallback,
        },
    });
    write_artifact(project, GENERATED_RECOVERY, &recovery_index)?;

    let index = json!({
        "schema": JSVM_INDEX.schema,
        "recursive_generated_code": true,
        "generated_recovery": GENERATED_RECOVERY.relative_path,
        "max_generated_depth": options.max_generated_depth,
        "max_code_units": options.max_code_units,
        "scanner_invocations": scanner_invocations,
        "deduplicated_scans": deduplicated_scans,
        "code_units": rows,
        "dynamic_code_units": dynamic_units,
    });
    write_artifact(project, JSVM_INDEX, &index)?;

    let rows = index["code_units"]
        .as_array()
        .context("code_units missing")?;
    let confirmed_vm_units = rows
        .iter()
        .filter(|row| row.get("confirmed_vm_signal").and_then(Value::as_bool) == Some(true))
        .count();
    let handler_table_candidates = rows
        .iter()
        .filter(|row| {
            row.get("large_handler_table_candidate")
                .and_then(Value::as_bool)
                == Some(true)
        })
        .count();
    let failures = rows
        .iter()
        .filter(|row| {
            value_usize(row, "scanner_exit") != 0
                || row.get("error").is_some()
                || value_usize(row, "switch_ir_exit") != 0
                || value_usize(row, "table_ir_exit") != 0
        })
        .count();
    Ok(ProjectScanSummary {
        code_units: rows.len(),
        scanner_invocations,
        deduplicated_scans,
        dynamic_units: index["dynamic_code_units"].as_array().map_or(0, Vec::len),
        confirmed_vm_units,
        handler_table_candidates,
        failures,
    })
}
