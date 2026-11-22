use crate::{
    analysis_artifacts::{write_artifact, WASM_INDEX},
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    capture_project::{load_manifest, CaptureManifest},
    sha256_hex,
    static_bytes::{
        analyze_webassembly_byte_artifacts, RecoveredByteArtifact, RecoveredInlineWasmArtifact,
    },
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};
use wasm_redox::wax_view::{write_wax_view, WaxViewOrigin};
use work_budget::WorkBudget;

const PARSE_REFUSAL: &str = "JavaScript did not parse as unambiguous or CommonJS source";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmMaterializeSummary {
    pub modules: usize,
    pub origins: usize,
    pub failed: usize,
}

#[derive(Debug, Clone)]
struct SourceCandidate {
    path: PathBuf,
    source_path: String,
    provenance: Map<String, Value>,
}

fn contains_bytes(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty()
        && haystack
            .windows(needle.len())
            .any(|window| window == needle)
}

fn relative_path(project: &Path, path: &Path) -> Result<String> {
    Ok(path
        .strip_prefix(project)
        .with_context(|| {
            format!(
                "derived WASM path {} escaped project {}",
                path.display(),
                project.display()
            )
        })?
        .to_string_lossy()
        .replace('\\', "/"))
}

fn write_recovered_binary(root: &Path, digest: &str, bytes: &[u8]) -> Result<PathBuf> {
    fs::create_dir_all(root).with_context(|| format!("creating {}", root.display()))?;
    let path = root.join(format!("{digest}.wasm"));
    if path.exists() {
        let existing = fs::read(&path).with_context(|| format!("reading {}", path.display()))?;
        if sha256_hex(&existing) != digest {
            bail!(
                "existing recovered WASM file has wrong digest: {}",
                path.display()
            );
        }
    } else {
        crate::report_file::write_bytes(&path, bytes)?;
    }
    Ok(path)
}

fn origin_with(
    provenance: &Map<String, Value>,
    fields: impl IntoIterator<Item = (String, Value)>,
) -> Value {
    let mut origin = provenance.clone();
    origin.extend(fields);
    Value::Object(origin)
}

fn analyze_module(
    binary: &Path,
    output_dir: &Path,
    wax: Option<&Path>,
    budget: &WorkBudget,
) -> Result<()> {
    budget.checkpoint()?;
    let bytes = fs::read(binary).with_context(|| format!("reading {}", binary.display()))?;
    let report = wasm_redox::analyze(&bytes, budget)?;
    budget.checkpoint()?;
    let wat = wasm_redox::folded_wat(&bytes, budget)?;
    budget.checkpoint()?;
    let deep = wasm_redox::deep_analyze(&bytes, &report, budget)?;
    budget.checkpoint()?;

    fs::create_dir_all(output_dir).with_context(|| format!("creating {}", output_dir.display()))?;
    let reports = [
        crate::report_file::stage_json(&output_dir.join("module.report.json"), &report)?,
        crate::report_file::stage_text(&output_dir.join("module.readable.wat"), &wat)?,
        crate::report_file::stage_json(&output_dir.join("module.deep.json"), &deep)?,
    ];
    for report in reports {
        report.publish()?;
    }
    let wax_output = output_dir.join("module.readable.wax");
    if let Some(wax) = wax {
        budget.checkpoint()?;
        write_wax_view(
            binary,
            &wax_output,
            wax,
            budget,
            WaxViewOrigin::ProjectMaterialization,
        )?;
        budget.checkpoint()?;
    } else if wax_output.exists() {
        fs::remove_file(&wax_output)
            .with_context(|| format!("removing stale {}", wax_output.display()))?;
    }
    Ok(())
}

struct ModuleOrigins {
    binary: PathBuf,
    origins: Vec<Value>,
    direct: bool,
    inline: bool,
}

impl ModuleOrigins {
    const fn new(binary: PathBuf) -> Self {
        Self {
            binary,
            origins: Vec::new(),
            direct: false,
            inline: false,
        }
    }
}

struct WasmInventory<'a> {
    project: &'a Path,
    inline_root: PathBuf,
    modules: BTreeMap<String, ModuleOrigins>,
    seen_occurrences: BTreeSet<(String, &'static str, u32, u32)>,
}

impl WasmInventory<'_> {
    fn collect_direct(&mut self, manifest: &CaptureManifest, budget: &WorkBudget) -> Result<()> {
        for resource in &manifest.resources {
            budget.checkpoint()?;
            if resource.get("kind").and_then(Value::as_str) != Some("wasm")
                || resource.get("body_present").and_then(Value::as_bool) != Some(true)
            {
                continue;
            }
            let Some(raw_path) = resource.get("output_path").and_then(Value::as_str) else {
                continue;
            };
            let path = self.project.join(raw_path);
            if !path.is_file() {
                continue;
            }
            let bytes = fs::read(&path).with_context(|| format!("reading {}", path.display()))?;
            let digest = sha256_hex(&bytes);
            let module = self
                .modules
                .entry(digest)
                .or_insert_with(|| ModuleOrigins::new(path));
            module.direct = true;
            module.origins.push(json!({
                "type": "resource",
                "resource_id": resource.get("id").cloned().unwrap_or(Value::Null),
                "url": resource.get("url").cloned().unwrap_or(Value::Null),
                "source_path": raw_path,
            }));
        }

        Ok(())
    }

    fn collect_source(
        &mut self,
        source: &SourceCandidate,
        stage_budget: &WorkBudget,
    ) -> Result<()> {
        let budget =
            AnalysisOperation::WasmAnalysis.under(stage_budget, source.path.display().to_string());
        budget.checkpoint()?;
        let raw =
            fs::read(&source.path).with_context(|| format!("reading {}", source.path.display()))?;
        if !contains_bytes(&raw, b"AGFzbQ") && !contains_bytes(&raw, b"WebAssembly") {
            return Ok(());
        }
        let text = std::str::from_utf8(&raw)
            .with_context(|| format!("{} is not UTF-8 JavaScript", source.path.display()))?;
        let recovery = match analyze_webassembly_byte_artifacts(text, &budget) {
            Ok(recovery) => recovery,
            Err(error) if error.to_string() == PARSE_REFUSAL => return Ok(()),
            Err(error) => {
                return Err(error).with_context(|| format!("analyzing {}", source.path.display()));
            }
        };
        budget.checkpoint()?;

        for artifact in recovery.inline_wasm_literals {
            self.record_inline(source, artifact, &budget)?;
        }
        for artifact in recovery.artifacts {
            self.record_assembly(source, artifact, &budget)?;
        }
        Ok(())
    }

    fn record_recovered(
        &mut self,
        occurrence: (String, &'static str, u32, u32),
        digest: String,
        bytes: &[u8],
    ) -> Result<Option<&mut ModuleOrigins>> {
        if !self.seen_occurrences.insert(occurrence) {
            return Ok(None);
        }
        let binary = write_recovered_binary(&self.inline_root, &digest, bytes)?;
        let module = self
            .modules
            .entry(digest)
            .or_insert_with(|| ModuleOrigins::new(binary));
        module.inline = true;
        Ok(Some(module))
    }

    fn record_inline(
        &mut self,
        source: &SourceCandidate,
        artifact: RecoveredInlineWasmArtifact,
        budget: &WorkBudget,
    ) -> Result<()> {
        budget.checkpoint()?;
        let Some(module) = self.record_recovered(
            (
                source.source_path.clone(),
                "inline_base64_literal",
                artifact.source_start,
                artifact.source_end,
            ),
            artifact.sha256,
            &artifact.bytes,
        )?
        else {
            return Ok(());
        };
        module.origins.push(origin_with(
            &source.provenance,
            [
                ("encoding".into(), Value::String(artifact.encoding.into())),
                ("byte_start".into(), Value::from(artifact.source_start)),
                ("byte_end".into(), Value::from(artifact.source_end)),
                (
                    "carrier_path".into(),
                    artifact.carrier_path.map_or(Value::Null, Value::String),
                ),
                (
                    "recovery_kind".into(),
                    Value::String("validated_static_wasm_carrier".into()),
                ),
            ],
        ));
        Ok(())
    }

    fn record_assembly(
        &mut self,
        source: &SourceCandidate,
        artifact: RecoveredByteArtifact,
        budget: &WorkBudget,
    ) -> Result<()> {
        budget.checkpoint()?;
        let Some(module) = self.record_recovered(
            (
                source.source_path.clone(),
                "static_byte_assembly",
                artifact.allocation_start,
                artifact.sink_end,
            ),
            artifact.sha256,
            &artifact.bytes,
        )?
        else {
            return Ok(());
        };
        let assembled_type = match source.provenance.get("type").and_then(Value::as_str) {
            Some("resource_inline_base64") => "resource_static_bytes",
            _ => "inline_script_static_bytes",
        };
        module.origins.push(origin_with(
            &source.provenance,
            [
                ("type".into(), Value::String(assembled_type.into())),
                (
                    "encoding".into(),
                    Value::String("static_byte_assembly".into()),
                ),
                ("byte_start".into(), Value::from(artifact.allocation_start)),
                ("byte_end".into(), Value::from(artifact.sink_end)),
                (
                    "recovery_kind".into(),
                    Value::String("proven_static_byte_assembly".into()),
                ),
                ("sink_kind".into(), Value::String(artifact.sink_kind.into())),
                ("sink_start".into(), Value::from(artifact.sink_start)),
                ("sink_end".into(), Value::from(artifact.sink_end)),
                ("copy_writes".into(), Value::from(artifact.copy_writes)),
            ],
        ));
        Ok(())
    }

    fn publish(self, wax: Option<&Path>, budget: &WorkBudget) -> Result<WasmMaterializeSummary> {
        let mut modules = Vec::with_capacity(self.modules.len());
        let mut failed = 0;
        let mut origin_count = 0;
        let mut direct_resources = 0;
        let mut inline_extracted = 0;
        for (digest, module) in self.modules {
            budget.checkpoint()?;
            origin_count += module.origins.len();
            direct_resources += usize::from(module.direct);
            inline_extracted += usize::from(module.inline);
            let (row, analysis_failed) = module_report(self.project, &digest, module, wax, budget)?;
            failed += usize::from(analysis_failed);
            modules.push(row);
        }
        let summary = WasmMaterializeSummary {
            modules: modules.len(),
            origins: origin_count,
            failed,
        };
        let index = json!({
            "schema": WASM_INDEX.schema,
            "modules": modules,
            "summary": {
                "modules": summary.modules,
                "direct_resources": direct_resources,
                "inline_extracted": inline_extracted,
                "failed": summary.failed,
                "origins": summary.origins,
            },
        });
        write_artifact(self.project, WASM_INDEX, &index)?;
        Ok(summary)
    }
}

fn source_candidates(project: &Path, manifest: &CaptureManifest) -> Vec<SourceCandidate> {
    let mut sources = Vec::new();
    for resource in &manifest.resources {
        if resource.get("kind").and_then(Value::as_str) != Some("javascript")
            || resource.get("body_present").and_then(Value::as_bool) != Some(true)
        {
            continue;
        }
        let Some(raw_path) = resource.get("output_path").and_then(Value::as_str) else {
            continue;
        };
        let path = project.join(raw_path);
        if !path.is_file() {
            continue;
        }
        let mut provenance = Map::new();
        provenance.insert(
            "type".into(),
            Value::String("resource_inline_base64".into()),
        );
        provenance.insert(
            "resource_id".into(),
            resource.get("id").cloned().unwrap_or(Value::Null),
        );
        provenance.insert(
            "url".into(),
            resource.get("url").cloned().unwrap_or(Value::Null),
        );
        provenance.insert("source_path".into(), Value::String(raw_path.to_owned()));
        sources.push(SourceCandidate {
            path,
            source_path: raw_path.to_owned(),
            provenance,
        });
    }
    for item in &manifest.inline_scripts {
        let Some(raw_path) = item.get("output_path").and_then(Value::as_str) else {
            continue;
        };
        let path = project.join(raw_path);
        if !path.is_file() {
            continue;
        }
        let mut provenance = Map::new();
        provenance.insert("type".into(), Value::String("inline_script_base64".into()));
        provenance.insert(
            "parent_resource_id".into(),
            item.get("parent_resource_id")
                .cloned()
                .unwrap_or(Value::Null),
        );
        provenance.insert(
            "ordinal".into(),
            item.get("ordinal").cloned().unwrap_or(Value::Null),
        );
        provenance.insert("source_path".into(), Value::String(raw_path.to_owned()));
        sources.push(SourceCandidate {
            path,
            source_path: raw_path.to_owned(),
            provenance,
        });
    }

    sources
}

fn module_report(
    project: &Path,
    digest: &str,
    module: ModuleOrigins,
    wax: Option<&Path>,
    stage_budget: &WorkBudget,
) -> Result<(Value, bool)> {
    let binary = &module.binary;
    let output = project.join("analysis/wasm/modules").join(digest);
    let budget = AnalysisOperation::WasmAnalysis.under(stage_budget, digest);
    let analysis = analyze_module(binary, &output, wax, &budget);
    let failed = analysis.is_err();
    let mut row = Map::new();
    row.insert("sha256".into(), Value::String(digest.to_owned()));
    row.insert(
        "byte_len".into(),
        Value::from(
            fs::metadata(binary)
                .with_context(|| format!("stat {}", binary.display()))?
                .len(),
        ),
    );
    row.insert(
        "binary_path".into(),
        Value::String(relative_path(project, binary)?),
    );
    row.insert("extracted".into(), Value::Bool(!module.direct));
    row.insert("has_direct_resource".into(), Value::Bool(module.direct));
    row.insert("has_inline_origin".into(), Value::Bool(module.inline));
    row.insert("origins".into(), Value::Array(module.origins));
    match analysis {
        Ok(()) => {
            row.insert("status".into(), Value::String("ok".into()));
            row.insert("error".into(), Value::Null);
            row.insert(
                "report_path".into(),
                Value::String(relative_path(project, &output.join("module.report.json"))?),
            );
            row.insert(
                "wat_path".into(),
                Value::String(relative_path(project, &output.join("module.readable.wat"))?),
            );
            row.insert(
                "deep_path".into(),
                Value::String(relative_path(project, &output.join("module.deep.json"))?),
            );
            let wax_path = output.join("module.readable.wax");
            if wax_path.is_file() {
                row.insert(
                    "wax_path".into(),
                    Value::String(relative_path(project, &wax_path)?),
                );
            }
        }
        Err(error) => {
            row.insert("status".into(), Value::String("failed".into()));
            row.insert("error".into(), Value::String(format!("{error:#}")));
        }
    }
    Ok((Value::Object(row), failed))
}

/// Extract and analyze verified WebAssembly modules from the capture project.
///
/// # Errors
///
/// Fails when the project/manifest cannot be resolved or read, an indexed module cannot be
/// read or analyzed, output artifacts cannot be written, or the WebAssembly analysis budget is
/// exhausted.
pub fn materialize_wasm(
    project: &Path,
    wax: Option<&Path>,
    budgets: &AnalysisBudgets,
) -> Result<WasmMaterializeSummary> {
    let project = project
        .canonicalize()
        .with_context(|| format!("resolving project {}", project.display()))?;
    let stage_budget = budgets.operation(
        AnalysisOperation::WasmAnalysis,
        project.display().to_string(),
    );
    stage_budget.checkpoint()?;
    let manifest = load_manifest(&project)?;
    let mut inventory = WasmInventory {
        project: &project,
        inline_root: project.join("src/_wasm/inline"),
        modules: BTreeMap::new(),
        seen_occurrences: BTreeSet::new(),
    };
    inventory.collect_direct(&manifest, &stage_budget)?;
    for source in source_candidates(&project, &manifest) {
        inventory.collect_source(&source, &stage_budget)?;
    }
    inventory.publish(wax, &stage_budget)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capture_project::{validate_manifest_value, write_manifest};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn test_project() -> Result<PathBuf> {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let project =
            std::env::temp_dir().join(format!("wasm-materialize-{}-{nonce}", std::process::id()));
        fs::create_dir_all(project.join("resources"))?;
        Ok(project)
    }

    #[test]
    fn deduplicates_direct_and_static_carrier_origins() -> Result<()> {
        let project = test_project()?;
        let result = (|| -> Result<()> {
            let wasm = b"\0asm\x01\0\0\0";
            let digest = sha256_hex(wasm);
            fs::write(project.join("resources/direct.wasm"), wasm)?;
            fs::write(
                project.join("resources/loader.js"),
                r#"const module = "AGFzbQEAAAA="; consume(module);"#,
            )?;
            let manifest_value = json!({
                "schema": "capture-project/v1",
                "source": {"kind": "synthetic", "input": "test", "salvaged": false},
                "pages": [],
                "resources": [
                    {"id": 7, "kind": "wasm", "body_present": true, "url": "https://x/module.wasm", "output_path": "resources/direct.wasm"},
                    {"id": 42, "kind": "javascript", "body_present": true, "url": "https://x/loader.js", "output_path": "resources/loader.js"}
                ],
                "inline_scripts": [],
                "counts": {}
            });
            let manifest = validate_manifest_value(&manifest_value, "test")?;
            write_manifest(&project.join("capture-manifest.json"), &manifest)?;

            let summary = materialize_wasm(
                &project,
                None,
                &AnalysisBudgets::standard("wasm-materialize-test"),
            )?;
            assert_eq!(summary.modules, 1);
            assert_eq!(summary.origins, 2);
            assert_eq!(summary.failed, 0);

            let index: Value = serde_json::from_str(&fs::read_to_string(
                project.join("analysis/wasm/index.json"),
            )?)?;
            assert_eq!(index["summary"]["modules"], 1);
            assert_eq!(index["summary"]["direct_resources"], 1);
            assert_eq!(index["summary"]["inline_extracted"], 1);
            assert_eq!(index["summary"]["origins"], 2);
            let module = index["modules"]
                .as_array()
                .and_then(|modules| modules.first())
                .context("WASM module row missing")?;
            assert_eq!(module["sha256"], digest);
            assert_eq!(module["extracted"], false);
            assert_eq!(module["has_direct_resource"], true);
            assert_eq!(module["has_inline_origin"], true);
            assert_eq!(
                module["binary_path"],
                Value::String("resources/direct.wasm".into())
            );
            assert!(project
                .join(format!("src/_wasm/inline/{digest}.wasm"))
                .is_file());
            assert!(project
                .join(format!("analysis/wasm/modules/{digest}/module.report.json"))
                .is_file());
            Ok(())
        })();
        let cleanup = fs::remove_dir_all(&project);
        result?;
        cleanup?;
        Ok(())
    }
}
