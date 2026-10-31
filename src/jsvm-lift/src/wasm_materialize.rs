use crate::{
    analysis_artifacts::{write_artifact, WASM_INDEX},
    capture_project::load_manifest,
    sha256_hex,
    static_bytes::analyze_webassembly_byte_artifacts,
};
use anyhow::{bail, Context, Result};
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::ErrorKind,
    path::{Path, PathBuf},
    process::Command,
};

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
        fs::write(&path, bytes).with_context(|| format!("writing {}", path.display()))?;
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

fn write_wax(binary: &Path, output: &Path, wax: &Path) -> Result<()> {
    let result = Command::new(wax).arg(binary).output();
    let result = match result {
        Ok(result) => result,
        Err(error) if error.kind() == ErrorKind::NotFound => {
            eprintln!(
                "wasm-materialize: Wax not found at {}; skipping high-level view",
                wax.display()
            );
            return Ok(());
        }
        Err(error) => return Err(error).with_context(|| format!("running {}", wax.display())),
    };
    if !result.status.success() {
        eprintln!(
            "wasm-materialize: Wax failed for {} ({}); keeping folded WAT fallback\n{}",
            binary.display(),
            result.status,
            String::from_utf8_lossy(&result.stderr)
        );
        return Ok(());
    }
    fs::write(output, result.stdout).with_context(|| format!("writing {}", output.display()))
}

fn analyze_module(binary: &Path, output_dir: &Path, wax: Option<&Path>) -> Result<()> {
    let bytes = fs::read(binary).with_context(|| format!("reading {}", binary.display()))?;
    let report = wasm_redox::analyze(&bytes)?;
    let wat = wasm_redox::folded_wat(&bytes)?;
    let deep = wasm_redox::deep_analyze(&bytes, &report);

    fs::create_dir_all(output_dir).with_context(|| format!("creating {}", output_dir.display()))?;
    fs::write(
        output_dir.join("module.report.json"),
        serde_json::to_vec_pretty(&report)?,
    )?;
    fs::write(output_dir.join("module.readable.wat"), wat)?;
    fs::write(
        output_dir.join("module.deep.json"),
        serde_json::to_vec_pretty(&deep)?,
    )?;
    let wax_output = output_dir.join("module.readable.wax");
    if let Some(wax) = wax {
        write_wax(binary, &wax_output, wax)?;
    } else if wax_output.exists() {
        fs::remove_file(&wax_output)
            .with_context(|| format!("removing stale {}", wax_output.display()))?;
    }
    Ok(())
}

pub fn materialize_wasm(project: &Path, wax: Option<&Path>) -> Result<WasmMaterializeSummary> {
    let project = project
        .canonicalize()
        .with_context(|| format!("resolving project {}", project.display()))?;
    let manifest = load_manifest(&project)?;
    let analysis_root = project.join("analysis/wasm");
    let modules_root = analysis_root.join("modules");
    let inline_root = project.join("src/_wasm/inline");

    let mut origins: BTreeMap<String, Vec<Value>> = BTreeMap::new();
    let mut binary_paths: BTreeMap<String, PathBuf> = BTreeMap::new();
    let mut direct_origin = BTreeSet::new();
    let mut inline_origin = BTreeSet::new();

    for resource in &manifest.resources {
        if resource.get("kind").and_then(Value::as_str) != Some("wasm")
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
        let bytes = fs::read(&path).with_context(|| format!("reading {}", path.display()))?;
        let digest = sha256_hex(&bytes);
        binary_paths.entry(digest.clone()).or_insert(path);
        direct_origin.insert(digest.clone());
        origins.entry(digest).or_default().push(json!({
            "type": "resource",
            "resource_id": resource.get("id").cloned().unwrap_or(Value::Null),
            "url": resource.get("url").cloned().unwrap_or(Value::Null),
            "source_path": raw_path,
        }));
    }

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

    let mut seen_occurrences: BTreeSet<(String, &'static str, u32, u32)> = BTreeSet::new();
    for source in sources {
        let raw =
            fs::read(&source.path).with_context(|| format!("reading {}", source.path.display()))?;
        if !contains_bytes(&raw, b"AGFzbQ") && !contains_bytes(&raw, b"WebAssembly") {
            continue;
        }
        let text = std::str::from_utf8(&raw)
            .with_context(|| format!("{} is not UTF-8 JavaScript", source.path.display()))?;
        let recovery = match analyze_webassembly_byte_artifacts(text) {
            Ok(recovery) => recovery,
            Err(error) if error.to_string() == PARSE_REFUSAL => continue,
            Err(error) => {
                return Err(error).with_context(|| format!("analyzing {}", source.path.display()));
            }
        };

        for artifact in recovery.inline_wasm_literals {
            let key = (
                source.source_path.clone(),
                "inline_base64_literal",
                artifact.source_start,
                artifact.source_end,
            );
            if !seen_occurrences.insert(key) {
                continue;
            }
            let binary = write_recovered_binary(&inline_root, &artifact.sha256, &artifact.bytes)?;
            binary_paths
                .entry(artifact.sha256.clone())
                .or_insert(binary);
            inline_origin.insert(artifact.sha256.clone());
            origins
                .entry(artifact.sha256)
                .or_default()
                .push(origin_with(
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
        }

        for artifact in recovery.artifacts {
            let key = (
                source.source_path.clone(),
                "static_byte_assembly",
                artifact.allocation_start,
                artifact.sink_end,
            );
            if !seen_occurrences.insert(key) {
                continue;
            }
            let binary = write_recovered_binary(&inline_root, &artifact.sha256, &artifact.bytes)?;
            binary_paths
                .entry(artifact.sha256.clone())
                .or_insert(binary);
            inline_origin.insert(artifact.sha256.clone());
            let assembled_type = match source.provenance.get("type").and_then(Value::as_str) {
                Some("resource_inline_base64") => "resource_static_bytes",
                _ => "inline_script_static_bytes",
            };
            origins
                .entry(artifact.sha256)
                .or_default()
                .push(origin_with(
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
        }
    }

    let mut modules = Vec::with_capacity(origins.len());
    let mut failed = 0usize;
    let mut origin_count = 0usize;
    for (digest, module_origins) in &origins {
        origin_count += module_origins.len();
        let binary = binary_paths
            .get(digest)
            .with_context(|| format!("missing binary path for recovered WASM {digest}"))?;
        let output = modules_root.join(digest);
        let analysis = analyze_module(binary, &output, wax);
        let mut row = Map::new();
        row.insert("sha256".into(), Value::String(digest.clone()));
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
            Value::String(relative_path(&project, binary)?),
        );
        row.insert(
            "extracted".into(),
            Value::Bool(!direct_origin.contains(digest)),
        );
        row.insert(
            "has_direct_resource".into(),
            Value::Bool(direct_origin.contains(digest)),
        );
        row.insert(
            "has_inline_origin".into(),
            Value::Bool(inline_origin.contains(digest)),
        );
        row.insert("origins".into(), Value::Array(module_origins.clone()));

        match analysis {
            Ok(()) => {
                row.insert("status".into(), Value::String("ok".into()));
                row.insert("error".into(), Value::Null);
                row.insert(
                    "report_path".into(),
                    Value::String(relative_path(&project, &output.join("module.report.json"))?),
                );
                row.insert(
                    "wat_path".into(),
                    Value::String(relative_path(
                        &project,
                        &output.join("module.readable.wat"),
                    )?),
                );
                row.insert(
                    "deep_path".into(),
                    Value::String(relative_path(&project, &output.join("module.deep.json"))?),
                );
                let wax_path = output.join("module.readable.wax");
                if wax_path.is_file() {
                    row.insert(
                        "wax_path".into(),
                        Value::String(relative_path(&project, &wax_path)?),
                    );
                }
            }
            Err(error) => {
                failed += 1;
                row.insert("status".into(), Value::String("failed".into()));
                row.insert("error".into(), Value::String(format!("{error:#}")));
            }
        }
        modules.push(Value::Object(row));
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
            "direct_resources": direct_origin.len(),
            "inline_extracted": inline_origin.len(),
            "failed": summary.failed,
            "origins": summary.origins,
        },
    });
    write_artifact(&project, WASM_INDEX, &index)?;
    Ok(summary)
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

            let summary = materialize_wasm(&project, None)?;
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
