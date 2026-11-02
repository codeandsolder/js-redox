use crate::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    js_format::format_source,
    safe_deob::{deobfuscate_source, SourceMode},
    scan_report::{scan_source, EmbeddedScanReport, ScanReport},
    sha256_hex,
};
use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
    process::Command,
};
use tempfile::TempDir;
use work_budget::{run_command, WorkBudget};

#[derive(Debug, Default, Deserialize)]
pub struct CorpusDefaults {
    #[serde(default)]
    pub expect_diagnostics_max: Option<usize>,
}

#[derive(Debug, Deserialize)]
pub struct CorpusManifest {
    pub schema: String,
    #[serde(default)]
    pub defaults: CorpusDefaults,
    pub samples: Vec<CorpusSample>,
}

#[derive(Debug, Clone, Copy, Default, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CorpusRole {
    #[default]
    Raw,
    Reference,
    DeobfuscatedReference,
}

#[derive(Debug, Deserialize)]
pub struct CorpusSample {
    pub id: String,
    pub family: String,
    #[serde(default)]
    pub role: CorpusRole,
    pub path: PathBuf,
    pub bytes: u64,
    pub sha256: String,
    #[serde(default)]
    pub source: Option<String>,
    #[serde(default)]
    pub pretty_path: Option<PathBuf>,
    #[serde(default)]
    pub pretty_bytes: Option<u64>,
    #[serde(default)]
    pub pretty_sha256: Option<String>,
    #[serde(default)]
    pub expect_deob_rewrites_min: Option<usize>,
    #[serde(default)]
    pub expect_diagnostics_max: Option<usize>,
    #[serde(default)]
    pub expect_confirmed_max: Option<usize>,
    #[serde(default)]
    pub expect_opcode_map_max: Option<usize>,
    #[serde(default)]
    pub expect_table_vm_max: Option<usize>,
    #[serde(default)]
    pub expect_deob_transforms_min: BTreeMap<String, usize>,
    #[serde(default)]
    pub expect_deob_strings: Vec<String>,
    #[serde(default)]
    pub forbid_deob_strings: Vec<String>,
    #[serde(default)]
    pub expect_scan_signals_min: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ScannerMetrics {
    pub diagnostics: usize,
    pub functions: usize,
    pub arrays: usize,
    pub decoder_candidates: usize,
    pub direct_switch_maps: usize,
    pub handler_function_tables: usize,
    pub handler_tables: usize,
    pub opcode_maps: usize,
    pub push_builders: usize,
    pub state_machines: usize,
    pub table_vms: usize,
    pub byte_transducers: usize,
    pub embedded: usize,
    pub embedded_recursive: usize,
    pub direct_switch_maps_recursive: usize,
    pub handler_function_tables_recursive: usize,
    pub if_ladder_state_machines_recursive: usize,
    pub confirmed_dispatchers_recursive: usize,
    pub opcode_maps_recursive: usize,
    pub table_vms_recursive: usize,
}

impl ScannerMetrics {
    fn is_known_signal(key: &str) -> bool {
        matches!(
            key,
            "arrays"
                | "decoder_candidates"
                | "direct_switch_maps"
                | "handler_function_tables"
                | "handler_tables"
                | "opcode_maps"
                | "push_builders"
                | "state_machines"
                | "table_vms"
                | "byte_transducers"
                | "embedded"
                | "functions"
                | "embedded_recursive"
                | "direct_switch_maps_recursive"
                | "handler_function_tables_recursive"
                | "if_ladder_state_machines_recursive"
                | "confirmed_dispatchers_recursive"
                | "opcode_maps_recursive"
                | "table_vms_recursive"
        )
    }

    fn signal(&self, key: &str) -> Option<usize> {
        match key {
            "arrays" => Some(self.arrays),
            "decoder_candidates" => Some(self.decoder_candidates),
            "direct_switch_maps" => Some(self.direct_switch_maps),
            "handler_function_tables" => Some(self.handler_function_tables),
            "handler_tables" => Some(self.handler_tables),
            "opcode_maps" => Some(self.opcode_maps),
            "push_builders" => Some(self.push_builders),
            "state_machines" => Some(self.state_machines),
            "table_vms" => Some(self.table_vms),
            "byte_transducers" => Some(self.byte_transducers),
            "embedded" => Some(self.embedded),
            "functions" => Some(self.functions),
            "embedded_recursive" => Some(self.embedded_recursive),
            "direct_switch_maps_recursive" => Some(self.direct_switch_maps_recursive),
            "handler_function_tables_recursive" => Some(self.handler_function_tables_recursive),
            "if_ladder_state_machines_recursive" => Some(self.if_ladder_state_machines_recursive),
            "confirmed_dispatchers_recursive" => Some(self.confirmed_dispatchers_recursive),
            "opcode_maps_recursive" => Some(self.opcode_maps_recursive),
            "table_vms_recursive" => Some(self.table_vms_recursive),
            _ => None,
        }
    }
}

#[derive(Debug, Serialize)]
pub struct CorpusEvalRow {
    pub id: String,
    pub family: String,
    pub role: CorpusRole,
    pub bytes: u64,
    pub sha256: String,
    pub formatter_bytes: Option<usize>,
    pub deob_changed: Option<bool>,
    pub deob_iterations: Option<usize>,
    pub deob_rewrites: Option<usize>,
    pub deob_transforms: Option<BTreeMap<String, usize>>,
    pub arithmetic_state_proofs: Option<Value>,
    pub scanner: Option<ScannerMetrics>,
    pub status: String,
}

#[derive(Debug, Serialize)]
pub struct CorpusEvalSummary {
    pub samples: usize,
    pub raw_samples: usize,
    pub reference_samples: usize,
    pub proven_rewrites: usize,
    pub confirmed_dispatchers: usize,
}

#[derive(Debug, Serialize)]
pub struct CorpusEvalReport {
    pub schema: &'static str,
    pub source_schema: String,
    pub manifest: String,
    pub corpus_root: String,
    pub samples: Vec<CorpusEvalRow>,
    pub summary: CorpusEvalSummary,
}

fn relative_sample_path(path: &Path) -> bool {
    !path.is_absolute()
        && path.components().all(|component| {
            !matches!(
                component,
                Component::ParentDir | Component::RootDir | Component::Prefix(_)
            )
        })
}

fn canonical_corpus_path(root: &Path, relative: &Path, label: &str) -> Result<PathBuf> {
    if !relative_sample_path(relative) {
        bail!("{label}: path must stay under corpus root");
    }
    let candidate = root.join(relative);
    let canonical = candidate
        .canonicalize()
        .with_context(|| format!("{label}: resolving {}", candidate.display()))?;
    if !canonical.starts_with(root) {
        bail!(
            "{label}: resolved path {} escapes corpus root {}",
            canonical.display(),
            root.display()
        );
    }
    Ok(canonical)
}

fn validate_manifest(manifest: &CorpusManifest) -> Result<()> {
    if manifest.samples.is_empty() {
        bail!("corpus manifest has no samples");
    }
    let mut ids = BTreeSet::new();
    for sample in &manifest.samples {
        if !ids.insert(sample.id.as_str()) {
            bail!("duplicate sample id: {}", sample.id);
        }
        if !relative_sample_path(&sample.path) {
            bail!("{}: sample path must stay under corpus root", sample.id);
        }
        if let Some(path) = sample.pretty_path.as_deref() {
            if !relative_sample_path(path) {
                bail!("{}: pretty path must stay under corpus root", sample.id);
            }
        }
        if sample.pretty_bytes.is_some() != sample.pretty_sha256.is_some() {
            bail!(
                "{}: pretty_bytes and pretty_sha256 must be specified together",
                sample.id
            );
        }
        if (sample.pretty_bytes.is_some() || sample.pretty_sha256.is_some())
            && sample.pretty_path.is_none()
        {
            bail!("{}: pretty hash policy requires pretty_path", sample.id);
        }
        for signal in sample.expect_scan_signals_min.keys() {
            if !ScannerMetrics::is_known_signal(signal) {
                bail!("{}: unknown scanner signal {signal}", sample.id);
            }
        }
    }
    Ok(())
}

fn recursive_embedded_count(rows: &[EmbeddedScanReport]) -> usize {
    rows.iter()
        .map(|row| 1 + recursive_embedded_count(&row.embedded))
        .sum()
}

fn recursive_direct_switch_maps(rows: &[EmbeddedScanReport]) -> usize {
    rows.iter()
        .map(|row| row.direct_switch_maps.len() + recursive_direct_switch_maps(&row.embedded))
        .sum()
}

fn recursive_handler_function_tables(rows: &[EmbeddedScanReport]) -> usize {
    rows.iter()
        .map(|row| {
            row.handler_function_tables.len() + recursive_handler_function_tables(&row.embedded)
        })
        .sum()
}

fn recursive_if_ladders(rows: &[EmbeddedScanReport]) -> usize {
    rows.iter()
        .map(|row| row.if_ladder_state_machines.len() + recursive_if_ladders(&row.embedded))
        .sum()
}

fn recursive_confirmed_dispatchers(rows: &[EmbeddedScanReport]) -> usize {
    rows.iter()
        .map(|row| {
            row.functions
                .iter()
                .filter(|function| function.confirmed_dispatch)
                .count()
                + recursive_confirmed_dispatchers(&row.embedded)
        })
        .sum()
}

fn recursive_opcode_maps(rows: &[EmbeddedScanReport]) -> usize {
    rows.iter()
        .map(|row| row.opcode_maps.len() + recursive_opcode_maps(&row.embedded))
        .sum()
}

fn recursive_table_vms(rows: &[EmbeddedScanReport]) -> usize {
    rows.iter()
        .map(|row| row.table_vms.len() + recursive_table_vms(&row.embedded))
        .sum()
}

fn scanner_metrics(report: &ScanReport) -> ScannerMetrics {
    ScannerMetrics {
        diagnostics: report.diagnostics,
        functions: report.functions.len(),
        arrays: report.arrays.len(),
        decoder_candidates: report.decoder_candidates.len(),
        direct_switch_maps: report.direct_switch_maps.len(),
        handler_function_tables: report.handler_function_tables.len(),
        handler_tables: report.handler_tables.len(),
        opcode_maps: report.opcode_maps.len(),
        push_builders: report.push_builders.len(),
        state_machines: report.state_machines.len(),
        table_vms: report.table_vms.len(),
        byte_transducers: report.byte_transducers.len(),
        embedded: report.embedded.len(),
        embedded_recursive: recursive_embedded_count(&report.embedded),
        direct_switch_maps_recursive: report.direct_switch_maps.len()
            + recursive_direct_switch_maps(&report.embedded),
        handler_function_tables_recursive: report.handler_function_tables.len()
            + recursive_handler_function_tables(&report.embedded),
        if_ladder_state_machines_recursive: report.if_ladder_state_machines.len()
            + recursive_if_ladders(&report.embedded),
        confirmed_dispatchers_recursive: report
            .functions
            .iter()
            .filter(|function| function.confirmed_dispatch)
            .count()
            + recursive_confirmed_dispatchers(&report.embedded),
        opcode_maps_recursive: report.opcode_maps.len() + recursive_opcode_maps(&report.embedded),
        table_vms_recursive: report.table_vms.len() + recursive_table_vms(&report.embedded),
    }
}

fn assert_node_syntax(
    temp: &TempDir,
    label: &str,
    suffix: &str,
    source: &str,
    mode: SourceMode,
    budget: &WorkBudget,
) -> Result<()> {
    let safe_label = label
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || matches!(character, '-' | '_' | '.') {
                character
            } else {
                '_'
            }
        })
        .take(96)
        .collect::<String>();
    let extension = mode.suffix().trim_start_matches('.');
    let path = temp
        .path()
        .join(format!("{safe_label}.{suffix}.{extension}"));
    fs::write(&path, source).with_context(|| format!("writing {}", path.display()))?;
    let mut command = Command::new("node");
    command.arg("--check").arg(&path);
    let output = run_command(&mut command, budget).context("running node --check")?;
    if !output.status.success() {
        bail!(
            "node --check failed for {label}/{suffix}: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(())
}

fn verify_file(
    path: &Path,
    expected_bytes: u64,
    expected_sha256: &str,
    label: &str,
) -> Result<Vec<u8>> {
    let bytes = fs::read(path).with_context(|| format!("reading {label}: {}", path.display()))?;
    if u64::try_from(bytes.len()).context("file length does not fit u64")? != expected_bytes {
        bail!("{label}: byte length mismatch for {}", path.display());
    }
    let digest = sha256_hex(&bytes);
    if digest != expected_sha256 {
        bail!("{label}: SHA-256 mismatch for {}", path.display());
    }
    Ok(bytes)
}

fn validate_sample_policy(
    sample: &CorpusSample,
    defaults: &CorpusDefaults,
    deob_source: &str,
    transforms: &BTreeMap<String, usize>,
    rewrites: usize,
    metrics: &ScannerMetrics,
) -> Result<()> {
    if let Some(minimum) = sample.expect_deob_rewrites_min {
        if rewrites < minimum {
            bail!("{}: deob rewrites {rewrites} < {minimum}", sample.id);
        }
    }
    for (transform, minimum) in &sample.expect_deob_transforms_min {
        let actual = transforms.get(transform).copied().unwrap_or_default();
        if actual < *minimum {
            bail!("{}: transform {transform} {actual} < {minimum}", sample.id);
        }
    }
    for expected in &sample.expect_deob_strings {
        if !deob_source.contains(expected) {
            bail!("{}: expected deob string missing: {expected:?}", sample.id);
        }
    }
    for forbidden in &sample.forbid_deob_strings {
        if deob_source.contains(forbidden) {
            bail!(
                "{}: forbidden deob string present: {forbidden:?}",
                sample.id
            );
        }
    }
    let max_diagnostics = sample
        .expect_diagnostics_max
        .or(defaults.expect_diagnostics_max)
        .unwrap_or(16);
    if metrics.diagnostics > max_diagnostics {
        bail!(
            "{}: scanner diagnostics {} > {max_diagnostics}",
            sample.id,
            metrics.diagnostics
        );
    }
    if let Some(maximum) = sample.expect_confirmed_max {
        if metrics.confirmed_dispatchers_recursive > maximum {
            bail!(
                "{}: confirmed dispatchers {} > {maximum}",
                sample.id,
                metrics.confirmed_dispatchers_recursive
            );
        }
    }
    if let Some(maximum) = sample.expect_opcode_map_max {
        if metrics.opcode_maps_recursive > maximum {
            bail!(
                "{}: opcode maps {} > {maximum}",
                sample.id,
                metrics.opcode_maps_recursive
            );
        }
    }
    if let Some(maximum) = sample.expect_table_vm_max {
        if metrics.table_vms_recursive > maximum {
            bail!(
                "{}: table VMs {} > {maximum}",
                sample.id,
                metrics.table_vms_recursive
            );
        }
    }
    for (signal, minimum) in &sample.expect_scan_signals_min {
        let actual = metrics
            .signal(signal)
            .with_context(|| format!("{}: unknown scanner signal {signal}", sample.id))?;
        if actual < *minimum {
            bail!(
                "{}: scanner signal {signal} {actual} < {minimum}",
                sample.id
            );
        }
    }
    Ok(())
}

pub fn evaluate_manifest(manifest_path: &Path, corpus_root: &Path) -> Result<CorpusEvalReport> {
    let manifest_text = fs::read_to_string(manifest_path)
        .with_context(|| format!("reading manifest {}", manifest_path.display()))?;
    let manifest: CorpusManifest = serde_json::from_str(&manifest_text)
        .with_context(|| format!("parsing manifest {}", manifest_path.display()))?;
    validate_manifest(&manifest)
        .with_context(|| format!("validating manifest {}", manifest_path.display()))?;
    let corpus_root = corpus_root
        .canonicalize()
        .with_context(|| format!("resolving corpus root {}", corpus_root.display()))?;

    let temp = TempDir::new().context("creating corpus-eval scratch directory")?;
    let budgets = AnalysisBudgets::standard(format!("corpus-eval:{}", manifest_path.display()));
    let mut rows = Vec::with_capacity(manifest.samples.len());
    let mut proven_rewrites = 0_usize;
    let mut confirmed_dispatchers = 0_usize;
    let mut raw_samples = 0_usize;
    let mut reference_samples = 0_usize;

    for sample in &manifest.samples {
        let sample_budget = budgets.operation(AnalysisOperation::CorpusEvaluation, &sample.id);
        sample_budget.checkpoint()?;
        let raw_path =
            canonical_corpus_path(&corpus_root, &sample.path, &format!("{} sample", sample.id))?;
        let raw_bytes = verify_file(&raw_path, sample.bytes, &sample.sha256, &sample.id)?;

        if let Some(source) = sample
            .source
            .as_deref()
            .map(Path::new)
            .filter(|path| path.is_file())
        {
            let mirrored =
                fs::read(source).with_context(|| format!("reading {}", source.display()))?;
            if sha256_hex(&mirrored) != sample.sha256 {
                bail!("{}: mirrored source bytes differ from corpus", sample.id);
            }
        }

        if sample.role != CorpusRole::Raw {
            reference_samples += 1;
            rows.push(CorpusEvalRow {
                id: sample.id.clone(),
                family: sample.family.clone(),
                role: sample.role,
                bytes: sample.bytes,
                sha256: sample.sha256.clone(),
                formatter_bytes: None,
                deob_changed: None,
                deob_iterations: None,
                deob_rewrites: None,
                deob_transforms: None,
                arithmetic_state_proofs: None,
                scanner: None,
                status: "reference-hash-ok".to_owned(),
            });
            continue;
        }
        raw_samples += 1;
        let raw_source = std::str::from_utf8(&raw_bytes)
            .with_context(|| format!("{}: JavaScript is not UTF-8", sample.id))?;

        // Module/CommonJS semantics belong to the manifest's logical filename,
        // not to a canonical symlink target whose suffix may differ.
        let source_mode = SourceMode::for_path(&sample.path);
        let format_budget =
            budgets.operation_under(&sample_budget, AnalysisOperation::Format, &sample.id);
        let pretty = format_source(raw_source, &format_budget)
            .with_context(|| format!("{}: formatting", sample.id))?;
        let syntax_budget = budgets.operation_under(
            &sample_budget,
            AnalysisOperation::SyntaxCheck,
            format!("{}:pretty", sample.id),
        );
        assert_node_syntax(
            &temp,
            &sample.id,
            "pretty",
            &pretty,
            source_mode,
            &syntax_budget,
        )?;
        if let Some(pretty_path) = &sample.pretty_path {
            let committed_path =
                canonical_corpus_path(&corpus_root, pretty_path, &format!("{} pretty", sample.id))?;
            if let (Some(expected_bytes), Some(expected_sha)) =
                (sample.pretty_bytes, sample.pretty_sha256.as_deref())
            {
                let committed = verify_file(
                    &committed_path,
                    expected_bytes,
                    expected_sha,
                    &format!("{} pretty", sample.id),
                )?;
                if sha256_hex(pretty.as_bytes()) != sha256_hex(&committed) {
                    bail!("{}: committed analyst view is stale", sample.id);
                }
            }
        }

        let deob_budget = budgets.operation_under(
            &sample_budget,
            AnalysisOperation::SafeDeobfuscation,
            &sample.id,
        );
        let deob = deobfuscate_source(
            raw_source,
            raw_path.display().to_string(),
            source_mode,
            16,
            false,
            &deob_budget,
        )
        .with_context(|| format!("{}: safe deobfuscation", sample.id))?;
        let syntax_budget = budgets.operation_under(
            &sample_budget,
            AnalysisOperation::SyntaxCheck,
            format!("{}:deob", sample.id),
        );
        assert_node_syntax(
            &temp,
            &sample.id,
            "deob",
            &deob.source,
            source_mode,
            &syntax_budget,
        )?;
        if !deob.report.safe_static_only
            || deob.report.presentation_formatted
            || !deob.report.runtime_semantics_preserved_by_design
            || deob.report.transforms.contains_key("presentation_codegen")
        {
            bail!("{}: safe-deob report contract violated", sample.id);
        }
        let rewrites = deob
            .report
            .transforms
            .iter()
            .filter(|(kind, _)| {
                kind.as_str() != "canonical_codegen" && kind.as_str() != "presentation_codegen"
            })
            .map(|(_, count)| *count)
            .sum::<usize>();

        let scan_budget = budgets.operation_under(
            &sample_budget,
            AnalysisOperation::StructuralScan,
            &sample.id,
        );
        let scan = scan_source(&pretty, sample.id.clone(), None, source_mode, &scan_budget)?;
        if scan.fatal_error {
            bail!("{}: scanner fatal error", sample.id);
        }
        let metrics = scanner_metrics(&scan);
        validate_sample_policy(
            sample,
            &manifest.defaults,
            &deob.source,
            &deob.report.transforms,
            rewrites,
            &metrics,
        )?;
        proven_rewrites += rewrites;
        confirmed_dispatchers += metrics.confirmed_dispatchers_recursive;

        rows.push(CorpusEvalRow {
            id: sample.id.clone(),
            family: sample.family.clone(),
            role: sample.role,
            bytes: sample.bytes,
            sha256: sample.sha256.clone(),
            formatter_bytes: Some(pretty.len()),
            deob_changed: Some(deob.report.changed),
            deob_iterations: Some(deob.report.iterations),
            deob_rewrites: Some(rewrites),
            deob_transforms: Some(deob.report.transforms),
            arithmetic_state_proofs: Some(serde_json::to_value(
                deob.report.arithmetic_state_proofs,
            )?),
            scanner: Some(metrics),
            status: "ok".to_owned(),
        });
    }

    Ok(CorpusEvalReport {
        schema: "jsvm-corpus-eval/v1",
        source_schema: manifest.schema,
        manifest: manifest_path.display().to_string(),
        corpus_root: corpus_root.display().to_string(),
        summary: CorpusEvalSummary {
            samples: rows.len(),
            raw_samples,
            reference_samples,
            proven_rewrites,
            confirmed_dispatchers,
        },
        samples: rows,
    })
}

pub fn write_report(report: &CorpusEvalReport, path: &Path) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    let mut encoded = serde_json::to_string_pretty(report)?;
    encoded.push('\n');
    fs::write(path, encoded).with_context(|| format!("writing {}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_adtech_style_expectation_fields() -> Result<()> {
        let manifest: CorpusManifest = serde_json::from_str(
            r#"{
              "schema":"js-real-adtech-corpus/v1",
              "samples":[{
                "id":"sample","family":"fixture","path":"sample.js","bytes":1,
                "sha256":"00","pretty_path":"sample.pretty.js","pretty_bytes":2,
                "pretty_sha256":"11","expect_deob_rewrites_min":3,
                "expect_diagnostics_max":4,"expect_confirmed_max":5,
                "expect_opcode_map_max":6,"expect_table_vm_max":7
              }]
            }"#,
        )?;
        let sample = manifest.samples.first().context("sample missing")?;
        assert_eq!(sample.role, CorpusRole::Raw);
        assert_eq!(sample.expect_deob_rewrites_min, Some(3));
        assert_eq!(sample.expect_table_vm_max, Some(7));
        Ok(())
    }

    #[test]
    fn manifest_rejects_unknown_corpus_role() {
        let result = serde_json::from_str::<CorpusManifest>(
            r#"{
              "schema":"jsvm-corpus/v1",
              "samples":[{
                "id":"bad-role","family":"fixture","role":"refernece",
                "path":"sample.js","bytes":1,"sha256":"00"
              }]
            }"#,
        );
        assert!(matches!(
            result,
            Err(ref error) if error.to_string().contains("unknown variant")
        ));
    }

    #[cfg(unix)]
    #[test]
    fn canonical_corpus_path_rejects_symlink_escape() -> Result<()> {
        use std::os::unix::fs::symlink;

        let scratch = TempDir::new()?;
        let corpus = scratch.path().join("corpus");
        fs::create_dir(&corpus)?;
        let outside = scratch.path().join("outside.js");
        fs::write(&outside, "export const escaped = true;")?;
        symlink(&outside, corpus.join("sample.js"))?;
        let canonical_root = corpus.canonicalize()?;

        assert!(matches!(
            canonical_corpus_path(&canonical_root, Path::new("sample.js"), "fixture"),
            Err(ref error) if error.to_string().contains("escapes corpus root")
        ));
        Ok(())
    }

    #[test]
    fn scanner_signal_names_are_manifest_driven() {
        let metrics = ScannerMetrics {
            diagnostics: 0,
            functions: 1,
            arrays: 2,
            decoder_candidates: 3,
            direct_switch_maps: 4,
            handler_function_tables: 5,
            handler_tables: 6,
            opcode_maps: 7,
            push_builders: 8,
            state_machines: 9,
            table_vms: 10,
            byte_transducers: 11,
            embedded: 12,
            embedded_recursive: 13,
            direct_switch_maps_recursive: 14,
            handler_function_tables_recursive: 15,
            if_ladder_state_machines_recursive: 16,
            confirmed_dispatchers_recursive: 17,
            opcode_maps_recursive: 18,
            table_vms_recursive: 19,
        };
        assert_eq!(metrics.signal("handler_function_tables"), Some(5));
        assert_eq!(
            metrics.signal("if_ladder_state_machines_recursive"),
            Some(16)
        );
        assert_eq!(metrics.signal("unknown"), None);
    }
}
