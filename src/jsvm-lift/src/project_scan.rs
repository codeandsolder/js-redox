use crate::{
    analysis_artifacts::{
        load_artifact, load_optional_artifact, write_artifact, BUNDLES, DEOBFUSCATION,
        GENERATED_RECOVERY, JSVM_INDEX, SOURCE_INDEX,
    },
    analysis_budget::{recoverable_unit_error, AnalysisBudgets, AnalysisOperation},
    content_dedup::{link_or_copy, sha256_path},
    js_format::format_source,
    report_file::{project_relative_path as relative_string, write_json},
    safe_deob::{deobfuscate_source, SourceMode},
    scan_report::{scan_file, ScanReport},
    string_recovery::recover_static_strings,
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    path::{Path, PathBuf},
    rc::Rc,
};
use work_budget::WorkBudget;

#[derive(Debug, Clone)]
pub struct ProjectScanOptions {
    pub max_generated_depth: usize,
    pub max_code_units: usize,
    pub budgets: AnalysisBudgets,
}

impl Default for ProjectScanOptions {
    fn default() -> Self {
        Self {
            max_generated_depth: 8,
            max_code_units: 256,
            budgets: AnalysisBudgets::standard("project-scan"),
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

struct GeneratedPaths {
    string_tmp: PathBuf,
    string_report: PathBuf,
    deob_report: PathBuf,
    safe_rel: PathBuf,
    safe_dest: PathBuf,
    readable_rel: PathBuf,
    readable_dest: PathBuf,
}

impl GeneratedPaths {
    fn create(project: &Path, scan_id: usize, ordinal: usize) -> Result<Self> {
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

        Ok(Self {
            string_tmp,
            string_report,
            deob_report,
            safe_rel,
            safe_dest,
            readable_rel,
            readable_dest,
        })
    }
}

struct StringSelection {
    input_path: PathBuf,
    changed: bool,
}

#[derive(Clone, Copy)]
enum AnalysisStage {
    SafeDeobfuscation,
    StringRecoveryOnly,
    ExactFallback,
}

impl AnalysisStage {
    const fn name(self) -> &'static str {
        match self {
            Self::SafeDeobfuscation => "safe_deobfuscation",
            Self::StringRecoveryOnly => "string_recovery_only",
            Self::ExactFallback => "exact_fallback",
        }
    }
}

struct AnalysisSelection {
    relative_path: PathBuf,
    stage: AnalysisStage,
}

struct GeneratedRecovery<'a> {
    project: &'a Path,
    raw: &'a Path,
    raw_rel: &'a str,
    budget: &'a WorkBudget,
    paths: GeneratedPaths,
    row: Value,
    raw_sha: String,
}

impl<'a> GeneratedRecovery<'a> {
    fn new(
        project: &'a Path,
        raw: &'a Path,
        raw_rel: &'a str,
        scan_id: usize,
        ordinal: usize,
        budget: &'a WorkBudget,
    ) -> Result<Self> {
        let paths = GeneratedPaths::create(project, scan_id, ordinal)?;
        let raw_sha = sha256_path(raw)?;
        let row = json!({
            "parent_scan_id": scan_id,
            "ordinal": ordinal,
            "raw_path": raw_rel,
            "raw_sha256": raw_sha,
            "string_recovery_report": relative_string(project, &paths.string_report)?,
            "deobfuscation_report": relative_string(project, &paths.deob_report)?,
        });

        Ok(Self {
            project,
            raw,
            raw_rel,
            budget,
            paths,
            row,
            raw_sha,
        })
    }

    fn recover_strings(&mut self) -> Result<StringSelection> {
        let raw_source = fs::read_to_string(self.raw)
            .with_context(|| format!("reading {}", self.raw.display()))?;
        if crate::sha256_hex(raw_source.as_bytes()) != self.raw_sha {
            bail!(
                "generated string recovery input hash mismatch for {}",
                self.raw.display()
            );
        }
        let string_budget = AnalysisOperation::StaticStringRecovery
            .under(self.budget, self.raw.display().to_string());
        match recover_static_strings(
            &raw_source,
            self.raw_rel,
            SourceMode::Auto,
            8,
            &string_budget,
        ) {
            Ok(string_outcome) => {
                crate::report_file::write_text(&self.paths.string_tmp, &string_outcome.source)?;
                write_json(&self.paths.string_report, &string_outcome.report)?;
                let output_sha = crate::sha256_hex(string_outcome.source.as_bytes());
                let string_ok = string_outcome
                    .report
                    .get("safe_static_only")
                    .and_then(Value::as_bool)
                    == Some(true)
                    && string_outcome
                        .report
                        .get("input_sha256")
                        .and_then(Value::as_str)
                        == Some(self.raw_sha.as_str())
                    && string_outcome
                        .report
                        .get("output_sha256")
                        .and_then(Value::as_str)
                        == Some(output_sha.as_str());
                if !string_ok {
                    bail!(
                        "generated string-recovery provenance/hash validation failed for {}",
                        self.raw.display()
                    );
                }
                let string_changed = string_outcome
                    .report
                    .get("changed")
                    .and_then(Value::as_bool)
                    .unwrap_or(false);
                self.row["string_recovery"] = json!({
                    "exit": 0,
                    "changed": string_changed,
                    "replacements": value_usize(&string_outcome.report, "replacements"),
                    "output_sha256": output_sha,
                });
                Ok(StringSelection {
                    input_path: self.paths.string_tmp.clone(),
                    changed: string_changed,
                })
            }
            Err(error) => {
                let error = recoverable_unit_error(anyhow::Error::new(error))?;
                self.row["string_recovery_report"] = Value::Null;
                self.row["string_recovery"] = json!({
                    "exit": 1,
                    "changed": false,
                    "error": error.to_string(),
                });
                Ok(StringSelection {
                    input_path: self.raw.to_path_buf(),
                    changed: false,
                })
            }
        }
    }

    fn recover_analysis(&mut self, strings: &StringSelection) -> Result<AnalysisSelection> {
        let selected = &strings.input_path;
        let selected_source = fs::read_to_string(selected)
            .with_context(|| format!("reading {}", selected.display()))?;
        let selected_sha = sha256_path(selected)?;
        let deob_budget =
            AnalysisOperation::SafeDeobfuscation.under(self.budget, selected.display().to_string());
        let deob = deobfuscate_source(
            &selected_source,
            self.raw_rel,
            SourceMode::Auto,
            16,
            false,
            &deob_budget,
        );
        match deob {
            Ok(outcome) => {
                let output_sha = crate::sha256_hex(outcome.source.as_bytes());
                if outcome.report.input_sha256 != selected_sha
                    || outcome.report.output_sha256 != output_sha
                    || !outcome.report.guarantees.safe_static_only
                    || !outcome
                        .report
                        .guarantees
                        .runtime_semantics_preserved_by_design
                    || outcome.report.guarantees.presentation_formatted
                {
                    bail!(
                        "safe deobfuscation provenance invariant failed for {}",
                        selected.display()
                    );
                }
                crate::report_file::write_text(&self.paths.safe_dest, &outcome.source)?;
                write_json(&self.paths.deob_report, &outcome.report)?;
                self.row["deobfuscation"] = json!({
                    "exit": 0,
                    "changed": outcome.report.changed,
                    "iterations": outcome.report.iterations,
                    "transforms": outcome.report.transforms,
                    "output_sha256": output_sha,
                });
                Ok(AnalysisSelection {
                    relative_path: self.paths.safe_rel.clone(),
                    stage: AnalysisStage::SafeDeobfuscation,
                })
            }
            Err(error) => {
                let error = recoverable_unit_error(error)?;
                self.row["deobfuscation_report"] = Value::Null;
                self.row["deobfuscation"] =
                    json!({"exit": 1, "changed": false, "error": error.to_string()});
                if strings.changed {
                    link_or_copy(&self.paths.string_tmp, &self.paths.safe_dest)?;
                    Ok(AnalysisSelection {
                        relative_path: self.paths.safe_rel.clone(),
                        stage: AnalysisStage::StringRecoveryOnly,
                    })
                } else {
                    Ok(AnalysisSelection {
                        relative_path: PathBuf::from(self.raw_rel),
                        stage: AnalysisStage::ExactFallback,
                    })
                }
            }
        }
    }

    fn publish(mut self, selection: &AnalysisSelection) -> Result<Value> {
        let analysis_source = self.project.join(&selection.relative_path);
        let exact = fs::read_to_string(&analysis_source)
            .with_context(|| format!("reading {}", analysis_source.display()))?;
        let format_budget =
            AnalysisOperation::Format.under(self.budget, analysis_source.display().to_string());
        let formatted = format_source(&exact, &format_budget);
        let (readable, readable_formatted, format_error) = match formatted {
            Ok(formatted) => (formatted, true, None),
            Err(error) => {
                let error = recoverable_unit_error(error)?;
                (exact, false, Some(error.to_string()))
            }
        };
        crate::report_file::write_text(&self.paths.readable_dest, &readable)?;
        let object = self
            .row
            .as_object_mut()
            .context("generated recovery row must be an object")?;
        object.insert("selected_stage".into(), selection.stage.name().into());
        object.insert(
            "analysis_path".into(),
            selection
                .relative_path
                .to_string_lossy()
                .into_owned()
                .into(),
        );
        object.insert(
            "analysis_sha256".into(),
            sha256_path(&analysis_source)?.into(),
        );
        object.insert(
            "readable_path".into(),
            self.paths
                .readable_rel
                .to_string_lossy()
                .into_owned()
                .into(),
        );
        object.insert("readable_formatted".into(), readable_formatted.into());
        object.insert(
            "readable_sha256".into(),
            sha256_path(&self.paths.readable_dest)?.into(),
        );
        if let Some(error) = format_error {
            object.insert("readable_format_error".into(), error.into());
        }
        Ok(self.row)
    }
}

fn recover_generated_unit(
    project: &Path,
    raw: &Path,
    raw_rel: &str,
    scan_id: usize,
    ordinal: usize,
    parent_budget: &WorkBudget,
) -> Result<Value> {
    let mut recovery =
        GeneratedRecovery::new(project, raw, raw_rel, scan_id, ordinal, parent_budget)?;
    let strings = recovery.recover_strings()?;
    let analysis = recovery.recover_analysis(&strings)?;
    recovery.publish(&analysis)
}

fn reuse_generated_unit(
    project: &Path,
    raw_rel: &str,
    scan_id: usize,
    ordinal: usize,
    cached: &Value,
) -> Result<Value> {
    let paths = GeneratedPaths::create(project, scan_id, ordinal)?;
    let mut row = cached.clone();
    for (field, destination) in [
        ("string_recovery_report", &paths.string_report),
        ("deobfuscation_report", &paths.deob_report),
    ] {
        if let Some(source) = value_string(cached, field) {
            link_or_copy(&project.join(source), destination)?;
            row[field] = relative_string(project, destination)?.into();
        }
    }
    let selected_stage = value_string(cached, "selected_stage").unwrap_or_default();
    let analysis_rel = if selected_stage == "exact_fallback" {
        PathBuf::from(raw_rel)
    } else {
        let source =
            value_string(cached, "analysis_path").context("cached analysis_path missing")?;
        link_or_copy(&project.join(source), &paths.safe_dest)?;
        paths.safe_rel
    };
    let cached_readable =
        value_string(cached, "readable_path").context("cached readable_path missing")?;
    link_or_copy(&project.join(cached_readable), &paths.readable_dest)?;

    let object = row
        .as_object_mut()
        .context("cached generated recovery row must be object")?;
    object.insert("parent_scan_id".into(), scan_id.into());
    object.insert("ordinal".into(), ordinal.into());
    object.insert("raw_path".into(), raw_rel.into());
    object.insert(
        "analysis_path".into(),
        analysis_rel.to_string_lossy().into_owned().into(),
    );
    object.insert(
        "readable_path".into(),
        paths.readable_rel.to_string_lossy().into_owned().into(),
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

struct ScanQueue {
    pending: VecDeque<Value>,
    seen: BTreeSet<String>,
    accepted: usize,
    limit: usize,
}

impl ScanQueue {
    const fn new(limit: usize) -> Self {
        Self {
            pending: VecDeque::new(),
            seen: BTreeSet::new(),
            accepted: 0,
            limit,
        }
    }

    fn enqueue(&mut self, unit: Value) -> Option<usize> {
        let path = value_string(&unit, "path")?;
        if self.accepted + self.pending.len() >= self.limit || !self.seen.insert(path) {
            return None;
        }
        let id = self.accepted + self.pending.len();
        self.pending.push_back(unit);
        Some(id)
    }

    fn pop(&mut self) -> Option<(usize, Value)> {
        let unit = self.pending.pop_front()?;
        let id = self.accepted;
        self.accepted += 1;
        Some((id, unit))
    }
}

fn load_scan_queue(project: &Path, limit: usize) -> Result<ScanQueue> {
    let source_index = load_artifact(project, SOURCE_INDEX)
        .context("source index is required for VM project scanning")?;
    let deob =
        load_optional_artifact(project, DEOBFUSCATION)?.unwrap_or_else(|| json!({"units": []}));
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

    let mut queue = ScanQueue::new(limit);
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
        let _ = queue.enqueue(unit);
    }

    Ok(queue)
}

type BundleSpans = BTreeMap<String, BTreeSet<(i64, i64)>>;

fn bundle_spans(project: &Path) -> Result<BundleSpans> {
    let mut bundle_spans_by_parent = BTreeMap::<String, BTreeSet<(i64, i64)>>::new();
    if let Some(bundles) = load_optional_artifact(project, BUNDLES)? {
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

    Ok(bundle_spans_by_parent)
}

fn summarize_handler_tables(
    row: &mut Value,
    report: &ScanReport,
    known_bundle_spans: Option<&BTreeSet<(i64, i64)>>,
) {
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
}

fn classify_vm_signal(row: &mut Value) {
    let confirmed_vm_signal = [
        "confirmed_dispatchers",
        "opcode_maps",
        "confirmed_direct_switch_maps",
        "table_vms",
        "byte_transducers",
    ]
    .iter()
    .any(|field| value_usize(row, field) > 0);
    let large_handler_table_candidate =
        !confirmed_vm_signal && value_usize(row, "largest_looped_dynamic_handler_table") >= 32;
    let vm_signal = confirmed_vm_signal
        || value_usize(row, "weak_direct_switch_maps") > 0
        || large_handler_table_candidate;
    row["confirmed_vm_signal"] = confirmed_vm_signal.into();
    row["large_handler_table_candidate"] = large_handler_table_candidate.into();
    row["vm_signal"] = vm_signal.into();
}

#[derive(Clone, Copy)]
enum IrKind {
    Switch,
    Table,
}

impl IrKind {
    const fn name(self) -> &'static str {
        match self {
            Self::Switch => "switch",
            Self::Table => "table",
        }
    }
}

struct ProjectScanner<'a> {
    project: &'a Path,
    budget: &'a WorkBudget,
    max_depth: usize,
    outdir: PathBuf,
    queue: ScanQueue,
    bundle_spans: BundleSpans,
    rows: Vec<Value>,
    dynamic_units: Vec<Value>,
    generated_recovery: Vec<Value>,
    generated_cache: BTreeMap<String, Value>,
    scanner_cache: BTreeMap<String, (usize, Rc<ScanReport>)>,
    scanner_invocations: usize,
    deduplicated_scans: usize,
}

impl ProjectScanner<'_> {
    fn scan_report(
        &mut self,
        source: &Path,
        source_sha: String,
        scan_id: usize,
    ) -> Result<(Rc<ScanReport>, Option<usize>)> {
        if let Some((cached_id, report)) = self.scanner_cache.get(&source_sha) {
            self.deduplicated_scans += 1;
            return Ok((Rc::clone(report), Some(*cached_id)));
        }
        let dump_dir = self.outdir.join("embedded").join(format!("{scan_id:04}"));
        self.scanner_invocations += 1;
        let budget =
            AnalysisOperation::StructuralScan.under(self.budget, source.display().to_string());
        let report = Rc::new(scan_file(
            source,
            Some(&dump_dir),
            Some(self.project),
            &budget,
        )?);
        if report.embedded.is_empty() {
            self.scanner_cache
                .insert(source_sha, (scan_id, Rc::clone(&report)));
        }
        Ok((report, None))
    }

    fn scan_unit(&mut self, scan_id: usize, unit: Value) -> Result<Value> {
        let path = value_string(&unit, "path").context("queued unit path missing")?;
        let source = self.project.join(&path);
        let mut row = unit;
        row["scan_id"] = scan_id.into();
        if !source.is_file() {
            row["scanner_exit"] = 1.into();
            row["error"] = format!("missing source path: {}", source.display()).into();
            return Ok(row);
        }

        let source_sha = sha256_path(&source)?;
        row["analysis_sha256"] = source_sha.clone().into();
        let (report, deduplicated_from) = match self.scan_report(&source, source_sha, scan_id) {
            Ok(result) => result,
            Err(error) => {
                let error = recoverable_unit_error(error)?;
                row["scanner_exit"] = 1.into();
                row["scanner_deduplicated"] = false.into();
                row["error"] = error.to_string().into();
                return Ok(row);
            }
        };
        row["scanner_exit"] = 0.into();
        row["scanner_deduplicated"] = deduplicated_from.is_some().into();
        if let Some(cached_scan_id) = deduplicated_from {
            row["scanner_deduplicated_from_scan_id"] = cached_scan_id.into();
        }
        row["bytes"] = fs::metadata(&source)?.len().into();
        let report_path = self.outdir.join(format!("{scan_id:04}.json"));
        write_json(&report_path, report.as_ref())?;
        row["report"] = relative_string(self.project, &report_path)?.into();
        for (key, value) in direct_summary(&report) {
            row[key] = value;
        }

        summarize_handler_tables(&mut row, &report, self.bundle_spans.get(&path));
        row["embedded_units"] = Value::Array(self.recover_embedded(scan_id, &row, &report)?);
        self.materialize_ir(scan_id, &source, &report_path, &mut row)?;
        classify_vm_signal(&mut row);
        Ok(row)
    }

    fn recover_embedded(
        &mut self,
        scan_id: usize,
        unit: &Value,
        report: &ScanReport,
    ) -> Result<Vec<Value>> {
        let parent_depth = value_usize(unit, "generated_depth");
        let mut embedded_units = Vec::<Value>::new();
        for (offset, node) in report.embedded.iter().enumerate() {
            let ordinal = offset + 1;
            let Some(dumped) = node.dump_path.as_deref() else {
                continue;
            };
            let raw = self.project.join(dumped);
            let raw_rel = dumped.to_owned();
            let depth = parent_depth + 1;
            let raw_sha = sha256_path(&raw)?;
            let recovery = if let Some(cached) = self.generated_cache.get(&raw_sha) {
                reuse_generated_unit(self.project, &raw_rel, scan_id, ordinal, cached)?
            } else {
                let mut recovery = recover_generated_unit(
                    self.project,
                    &raw,
                    &raw_rel,
                    scan_id,
                    ordinal,
                    self.budget,
                )?;
                recovery["deduplicated"] = false.into();
                self.generated_cache.insert(raw_sha, recovery.clone());
                recovery
            };
            let recovery_ordinal = self.generated_recovery.len();
            self.generated_recovery.push(recovery.clone());
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
            let child_scan_id = if depth <= self.max_depth {
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
                self.queue.enqueue(child)
            } else {
                None
            };
            item["child_scan_id"] = child_scan_id.map_or(Value::Null, Value::from);
            embedded_units.push(item.clone());
            self.dynamic_units.push(item);
        }
        Ok(embedded_units)
    }

    fn materialize_ir(
        &self,
        scan_id: usize,
        source: &Path,
        report_path: &Path,
        row: &mut Value,
    ) -> Result<()> {
        if value_usize(row, "confirmed_direct_switch_maps") > 0 {
            self.write_ir(scan_id, source, report_path, row, IrKind::Switch)?;
        }
        if value_usize(row, "table_vms") > 0 {
            self.write_ir(scan_id, source, report_path, row, IrKind::Table)?;
        }
        Ok(())
    }

    fn write_ir(
        &self,
        scan_id: usize,
        source: &Path,
        report_path: &Path,
        row: &mut Value,
        kind: IrKind,
    ) -> Result<()> {
        let name = kind.name();
        let output_path = self.outdir.join(format!("{scan_id:04}.{name}-ir.json"));
        let budget = AnalysisOperation::IrMaterialization
            .under(self.budget, format!("{name}-ir:{}", source.display()));
        let (exit, path, error, result) = match kind {
            IrKind::Switch => (
                "switch_ir_exit",
                "switch_ir",
                "switch_ir_error",
                crate::switch_ir::materialize(
                    source,
                    report_path,
                    &output_path,
                    Some(self.project),
                    &budget,
                ),
            ),
            IrKind::Table => (
                "table_ir_exit",
                "table_ir",
                "table_ir_error",
                crate::table_ir::materialize(
                    source,
                    report_path,
                    &output_path,
                    Some(self.project),
                    &budget,
                ),
            ),
        };
        match result {
            Ok(()) => {
                row[exit] = 0.into();
                row[path] = relative_string(self.project, &output_path)?.into();
            }
            Err(failure) => {
                let failure = recoverable_unit_error(failure)?;
                row[exit] = 1.into();
                row[error] = failure.to_string().into();
            }
        }
        Ok(())
    }

    fn publish_generated_recovery(&self) -> Result<()> {
        let safe_deobfuscation = self
            .generated_recovery
            .iter()
            .filter(|row| {
                row.get("selected_stage").and_then(Value::as_str) == Some("safe_deobfuscation")
            })
            .count();
        let string_recovery_only = self
            .generated_recovery
            .iter()
            .filter(|row| {
                row.get("selected_stage").and_then(Value::as_str) == Some("string_recovery_only")
            })
            .count();
        let exact_fallback = self
            .generated_recovery
            .iter()
            .filter(|row| {
                row.get("selected_stage").and_then(Value::as_str) == Some("exact_fallback")
            })
            .count();
        let deduplicated_units = self
            .generated_recovery
            .iter()
            .filter(|row| row.get("deduplicated").and_then(Value::as_bool) == Some(true))
            .count();
        let recovery_index = json!({
            "schema": GENERATED_RECOVERY.schema,
            "safe_static_only": true,
            "units": self.generated_recovery,
            "summary": {
                "generated_units": self.generated_recovery.len(),
                "unique_raw_inputs": self.generated_cache.len(),
                "deduplicated_units": deduplicated_units,
                "safe_deobfuscation": safe_deobfuscation,
                "string_recovery_only": string_recovery_only,
                "exact_fallback": exact_fallback,
            },
        });
        write_artifact(self.project, GENERATED_RECOVERY, &recovery_index)
    }

    fn publish(&self) -> Result<ProjectScanSummary> {
        self.publish_generated_recovery()?;
        let index = json!({
            "schema": JSVM_INDEX.schema,
            "recursive_generated_code": true,
            "generated_recovery": GENERATED_RECOVERY.relative_path,
            "max_generated_depth": self.max_depth,
            "max_code_units": self.queue.limit,
            "scanner_invocations": self.scanner_invocations,
            "deduplicated_scans": self.deduplicated_scans,
            "code_units": self.rows,
            "dynamic_code_units": self.dynamic_units,
        });
        write_artifact(self.project, JSVM_INDEX, &index)?;

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
            scanner_invocations: self.scanner_invocations,
            deduplicated_scans: self.deduplicated_scans,
            dynamic_units: index["dynamic_code_units"].as_array().map_or(0, Vec::len),
            confirmed_vm_units,
            handler_table_candidates,
            failures,
        })
    }
}

/// Scan indexed project sources for supported VM forms and persist their findings.
///
/// # Errors
///
/// Fails if the source index is unavailable, source files or metadata cannot be read, analysis
/// output cannot be created or written, or an analysis budget is exceeded.
pub fn scan_project(project: &Path, options: &ProjectScanOptions) -> Result<ProjectScanSummary> {
    let stage_budget = options
        .budgets
        .scope(format!("project-scan:{}", project.display()));
    stage_budget.checkpoint()?;
    let queue = load_scan_queue(project, options.max_code_units)?;
    let bundle_spans = bundle_spans(project)?;
    let outdir = project.join("analysis/jsvm");
    fs::create_dir_all(&outdir)?;
    let mut scanner = ProjectScanner {
        project,
        budget: &stage_budget,
        max_depth: options.max_generated_depth,
        outdir,
        queue,
        bundle_spans,
        rows: Vec::new(),
        dynamic_units: Vec::new(),
        generated_recovery: Vec::new(),
        generated_cache: BTreeMap::new(),
        scanner_cache: BTreeMap::new(),
        scanner_invocations: 0,
        deduplicated_scans: 0,
    };
    while let Some((scan_id, unit)) = scanner.queue.pop() {
        stage_budget.checkpoint()?;
        let row = scanner.scan_unit(scan_id, unit)?;
        scanner.rows.push(row);
    }
    scanner.publish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scan_queue_preserves_assigned_ids_across_recursive_enqueues() -> Result<()> {
        let mut queue = ScanQueue::new(3);
        assert_eq!(queue.enqueue(json!({"path":"a"})), Some(0));
        assert_eq!(queue.enqueue(json!({"path":"b"})), Some(1));
        assert_eq!(queue.enqueue(json!({"path":"a"})), None);
        let (id, unit) = queue.pop().context("first source")?;
        assert_eq!((id, unit["path"].as_str()), (0, Some("a")));
        assert_eq!(queue.enqueue(json!({"path":"generated"})), Some(2));
        assert_eq!(queue.enqueue(json!({"path":"a"})), None);
        assert_eq!(queue.enqueue(json!({"path":"extra"})), None);
        assert_eq!(queue.pop().map(|(id, _)| id), Some(1));
        assert_eq!(queue.pop().map(|(id, _)| id), Some(2));
        assert!(queue.pop().is_none());
        Ok(())
    }

    #[test]
    fn reused_generated_fallback_preserves_absent_proof_reports() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path();
        let raw_rel = "resources/fallback.js";
        let readable_rel = "src/_dynamic/0000/embedded-001.js";
        for rel in [raw_rel, readable_rel] {
            let path = project.join(rel);
            fs::create_dir_all(path.parent().context("fixture parent")?)?;
            fs::write(path, "void 0;")?;
        }
        let cached = json!({
            "parent_scan_id": 0,
            "ordinal": 1,
            "selected_stage": "exact_fallback",
            "string_recovery_report": null,
            "deobfuscation_report": null,
            "analysis_path": raw_rel,
            "readable_path": readable_rel,
        });
        let reused = reuse_generated_unit(project, raw_rel, 7, 2, &cached)?;
        assert_eq!(reused["parent_scan_id"], 7);
        assert_eq!(reused["ordinal"], 2);
        assert_eq!(reused["analysis_path"], raw_rel);
        assert_eq!(reused["string_recovery_report"], Value::Null);
        assert_eq!(reused["deobfuscation_report"], Value::Null);
        assert_eq!(reused["deduplicated"], true);
        assert_eq!(reused["deduplicated_from_parent_scan_id"], 0);
        assert_eq!(reused["deduplicated_from_ordinal"], 1);
        let readable = value_string(&reused, "readable_path").context("reused readable path")?;
        assert_eq!(fs::read_to_string(project.join(readable))?, "void 0;");
        Ok(())
    }
}
