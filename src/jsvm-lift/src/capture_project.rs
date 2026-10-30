use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

pub const SCHEMA: &str = "capture-project/v1";
pub const MANIFEST_NAME: &str = "capture-manifest.json";

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct CaptureSource {
    pub kind: String,
    pub input: String,
    pub salvaged: bool,
    #[serde(flatten)]
    pub extra: Map<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct CaptureManifest {
    pub schema: String,
    pub source: CaptureSource,
    pub pages: Vec<Value>,
    pub resources: Vec<Value>,
    pub inline_scripts: Vec<Value>,
    pub counts: BTreeMap<String, usize>,
    #[serde(flatten)]
    pub extra: Map<String, Value>,
}

fn validate_project_relative_path(value: &str, label: &str) -> Result<()> {
    if value.is_empty() {
        bail!("{label}: path must be a non-empty string");
    }
    if value.contains('\0') {
        bail!("{label}: path contains NUL");
    }
    if value.contains('\\') {
        bail!("{label}: backslash paths are not allowed");
    }
    let bytes = value.as_bytes();
    if bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':' {
        bail!("{label}: drive-qualified path is not allowed");
    }
    if value.starts_with('/')
        || value
            .split('/')
            .any(|part| part.is_empty() || matches!(part, "." | ".."))
    {
        bail!("{label}: path must stay inside the capture project");
    }
    Ok(())
}

fn validate_output_path(value: Option<&Value>, label: &str) -> Result<()> {
    let Some(value) = value else {
        return Ok(());
    };
    if value.is_null() {
        return Ok(());
    }
    let Some(path) = value.as_str() else {
        bail!("{label}: output_path must be a string or null");
    };
    validate_project_relative_path(path, label)?;
    if !path.starts_with("resources/") {
        bail!("{label}: output_path must be under resources/");
    }
    Ok(())
}

pub fn validate_manifest(manifest: &CaptureManifest, label: &str) -> Result<()> {
    if manifest.schema != SCHEMA {
        bail!("{label}: expected schema {SCHEMA:?}");
    }
    if manifest.source.kind.is_empty() {
        bail!("{label}: source.kind must be a non-empty string");
    }
    if manifest.source.input.is_empty() {
        bail!("{label}: source.input must be a non-empty string");
    }

    for (index, resource) in manifest.resources.iter().enumerate() {
        let Some(object) = resource.as_object() else {
            bail!("{label}: resources[{index}] must be an object");
        };
        if object.get("id").and_then(Value::as_u64) != Some(index as u64) {
            bail!("{label}: resources[{index}].id must equal {index}");
        }
        validate_output_path(
            object.get("output_path"),
            &format!("{label}: resources[{index}].output_path"),
        )?;
    }

    for (index, script) in manifest.inline_scripts.iter().enumerate() {
        let Some(object) = script.as_object() else {
            bail!("{label}: inline_scripts[{index}] must be an object");
        };
        let parent = object.get("parent_resource_id").and_then(Value::as_u64);
        if parent.is_none_or(|parent| parent >= manifest.resources.len() as u64) {
            bail!("{label}: inline_scripts[{index}].parent_resource_id is out of range");
        }
        validate_output_path(
            object.get("output_path"),
            &format!("{label}: inline_scripts[{index}].output_path"),
        )?;
    }
    Ok(())
}

pub fn validate_manifest_value(document: &Value, label: &str) -> Result<CaptureManifest> {
    let manifest: CaptureManifest = serde_json::from_value(document.clone())
        .with_context(|| format!("{label}: invalid capture manifest shape"))?;
    validate_manifest(&manifest, label)?;
    Ok(manifest)
}

pub fn read_manifest(path: &Path) -> Result<CaptureManifest> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("failed to read capture manifest {}", path.display()))?;
    let manifest: CaptureManifest = serde_json::from_str(&text)
        .with_context(|| format!("failed to parse capture manifest {}", path.display()))?;
    validate_manifest(&manifest, &path.display().to_string())?;
    Ok(manifest)
}

pub fn write_manifest(path: &Path, manifest: &CaptureManifest) -> Result<()> {
    validate_manifest(manifest, &path.display().to_string())?;
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    let mut encoded = serde_json::to_string_pretty(manifest)?;
    encoded.push('\n');
    fs::write(path, encoded).with_context(|| format!("writing {}", path.display()))
}

#[must_use]
pub fn manifest_path(project: &Path) -> PathBuf {
    project.join(MANIFEST_NAME)
}

pub fn load_manifest(project: &Path) -> Result<CaptureManifest> {
    read_manifest(&manifest_path(project))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn valid_manifest() -> CaptureManifest {
        serde_json::from_value(json!({
            "schema": SCHEMA,
            "source": {"kind": "har", "input": "/capture.har", "har_version": "1.2", "salvaged": false},
            "pages": [], "resources": [], "inline_scripts": [], "counts": {}
        }))
        .expect("test fixture")
    }

    #[test]
    fn rejects_unsafe_resource_paths_and_invalid_ids() {
        for hostile in [
            "../../outside.js",
            "/tmp/outside.js",
            "C:/outside.js",
            "resources/../outside.js",
            "resources\\outside.js",
        ] {
            let mut manifest = valid_manifest();
            manifest.resources = vec![json!({"id": 0, "output_path": hostile})];
            assert!(
                validate_manifest(&manifest, "test").is_err(),
                "accepted {hostile}"
            );
        }
        let mut wrong_prefix = valid_manifest();
        wrong_prefix.resources = vec![json!({"id": 0, "output_path": "src/outside.js"})];
        assert!(validate_manifest(&wrong_prefix, "test").is_err());

        let mut wrong_id = valid_manifest();
        wrong_id.resources = vec![json!({"id": 1, "output_path": "resources/a.js"})];
        assert!(validate_manifest(&wrong_id, "test").is_err());
    }

    #[test]
    fn rejects_inline_parent_outside_resource_range() {
        let mut manifest = valid_manifest();
        manifest.resources = vec![json!({"id": 0, "output_path": "resources/a.js"})];
        manifest.inline_scripts =
            vec![json!({"parent_resource_id": 9, "output_path": "resources/inline.js"})];
        assert!(validate_manifest(&manifest, "test").is_err());
    }
}
