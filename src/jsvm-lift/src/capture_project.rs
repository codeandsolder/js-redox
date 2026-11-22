use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
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

pub(crate) fn validate_project_relative_path(value: &str, label: &str) -> Result<()> {
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

fn check_shared_source_sha(
    object: &Map<String, Value>,
    known: &mut BTreeMap<String, String>,
    label: &str,
) -> Result<()> {
    let (Some(path), Some(sha)) = (
        object.get("output_path").and_then(Value::as_str),
        object.get("sha256").and_then(Value::as_str),
    ) else {
        return Ok(());
    };
    if let Some(existing) = known.get(path) {
        if existing != sha {
            bail!("{label}: conflicting SHA-256 claims for shared capture path {path}");
        }
    } else {
        known.insert(path.to_owned(), sha.to_owned());
    }
    Ok(())
}

/// Validate the capture manifest schema and internal reference integrity.
///
/// # Errors
///
/// Fails on an incorrect schema, empty source metadata, duplicate or malformed resource IDs, unsafe output paths or inline scripts referencing unknown resources.
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

    let mut resource_ids = BTreeSet::new();
    let mut shared_path_hashes = BTreeMap::<String, String>::new();
    for (index, resource) in manifest.resources.iter().enumerate() {
        let Some(object) = resource.as_object() else {
            bail!("{label}: resources[{index}] must be an object");
        };
        let Some(resource_id) = object.get("id").and_then(Value::as_u64) else {
            bail!("{label}: resources[{index}].id must be a non-negative integer");
        };
        if !resource_ids.insert(resource_id) {
            bail!("{label}: duplicate resource id {resource_id}");
        }
        validate_output_path(
            object.get("output_path"),
            &format!("{label}: resources[{index}].output_path"),
        )?;
        check_shared_source_sha(object, &mut shared_path_hashes, label)?;
    }

    for (index, script) in manifest.inline_scripts.iter().enumerate() {
        let Some(object) = script.as_object() else {
            bail!("{label}: inline_scripts[{index}] must be an object");
        };
        let parent = object.get("parent_resource_id").and_then(Value::as_u64);
        if parent.is_none_or(|parent| !resource_ids.contains(&parent)) {
            bail!("{label}: inline_scripts[{index}].parent_resource_id does not name a resource");
        }
        validate_output_path(
            object.get("output_path"),
            &format!("{label}: inline_scripts[{index}].output_path"),
        )?;
        check_shared_source_sha(object, &mut shared_path_hashes, label)?;
    }
    Ok(())
}

/// Deserialize and validate a capture manifest from a JSON value.
///
/// # Errors
///
/// Fails when the JSON has the wrong manifest shape or violates `validate_manifest` invariants.
pub fn validate_manifest_value(document: &Value, label: &str) -> Result<CaptureManifest> {
    let manifest: CaptureManifest = serde_json::from_value(document.clone())
        .with_context(|| format!("{label}: invalid capture manifest shape"))?;
    validate_manifest(&manifest, label)?;
    Ok(manifest)
}

/// Read, decode and validate the capture project's manifest.
///
/// # Errors
///
/// Fails on filesystem reads, malformed JSON or invalid capture-manifest invariants.
pub fn read_manifest(path: &Path) -> Result<CaptureManifest> {
    let manifest = crate::report_file::read_json(path, "capture manifest")?;
    validate_manifest(&manifest, &path.display().to_string())?;
    Ok(manifest)
}

/// Prepare an output directory without overwriting unrelated data.
///
/// # Errors
///
/// Rejects symlink output paths, existing paths without overwrite permission, non-directories and nonempty directories lacking a capture manifest; also propagates filesystem errors.
pub(crate) fn prepare_project_output(output: &Path, overwrite: bool) -> Result<()> {
    if let Ok(metadata) = fs::symlink_metadata(output) {
        if metadata.file_type().is_symlink() {
            bail!("refusing symlink output path: {}", output.display());
        }
    }
    if output.exists() {
        if !overwrite {
            bail!(
                "output directory already exists: {} (use --overwrite)",
                output.display()
            );
        }
        if !output.is_dir() {
            bail!(
                "refusing to replace non-directory output: {}",
                output.display()
            );
        }
        let empty = fs::read_dir(output)?.next().is_none();
        if !empty && !output.join(MANIFEST_NAME).is_file() {
            bail!("refusing to recursively replace non-project output: {}; expected an empty directory or {MANIFEST_NAME}", output.display());
        }
        fs::remove_dir_all(output)?;
    }
    fs::create_dir_all(output)?;
    Ok(())
}

/// Validate and serialize the capture manifest to its destination.
///
/// # Errors
///
/// Fails on invalid manifest contents, directory creation or serialization errors, or writing the manifest.
pub fn write_manifest(path: &Path, manifest: &CaptureManifest) -> Result<()> {
    validate_manifest(manifest, &path.display().to_string())?;
    crate::report_file::write_json(path, manifest)
}

#[must_use]
pub fn manifest_path(project: &Path) -> PathBuf {
    project.join(MANIFEST_NAME)
}

/// Load the capture manifest from its standard project location.
///
/// # Errors
///
/// Propagates read, parse and validation errors from `read_manifest`.
pub fn load_manifest(project: &Path) -> Result<CaptureManifest> {
    read_manifest(&manifest_path(project))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn valid_manifest() -> CaptureManifest {
        let mut source_extra = Map::new();
        source_extra.insert("har_version".into(), Value::String("1.2".into()));
        CaptureManifest {
            schema: SCHEMA.into(),
            source: CaptureSource {
                kind: "har".into(),
                input: "/capture.har".into(),
                salvaged: false,
                extra: source_extra,
            },
            pages: Vec::new(),
            resources: Vec::new(),
            inline_scripts: Vec::new(),
            counts: BTreeMap::new(),
            extra: Map::new(),
        }
    }

    #[test]
    fn manifest_replacement_preserves_previous_valid_snapshot() -> Result<()> {
        let directory = tempfile::tempdir()?;
        let path = manifest_path(directory.path());
        let first = valid_manifest();
        write_manifest(&path, &first)?;
        let original = fs::read(&path)?;
        let mut invalid = first.clone();
        invalid.resources = vec![json!({"id":0,"output_path":"../outside.js"})];
        assert!(write_manifest(&path, &invalid).is_err());
        assert_eq!(fs::read(&path)?, original);
        let snapshot = directory.path().join("previous-manifest.json");
        fs::hard_link(&path, &snapshot)?;
        let mut next = first.clone();
        next.source.input = "new capture".into();
        next.extra
            .insert("future_field".into(), json!({"value":42}));
        write_manifest(&path, &next)?;
        assert_eq!(read_manifest(&path)?, next);
        assert_eq!(read_manifest(&snapshot)?, first);
        assert_eq!(fs::read(snapshot)?, original);
        Ok(())
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

        let mut sparse_id = valid_manifest();
        sparse_id.resources = vec![json!({"id": 7, "output_path": "resources/a.js"})];
        assert!(validate_manifest(&sparse_id, "test").is_ok());

        let mut duplicate_id = valid_manifest();
        duplicate_id.resources = vec![
            json!({"id": 7, "output_path": "resources/a.js"}),
            json!({"id": 7, "output_path": "resources/b.js"}),
        ];
        assert!(validate_manifest(&duplicate_id, "test").is_err());
    }

    #[test]
    fn shared_capture_paths_require_consistent_digest_claims() {
        let mut manifest = valid_manifest();
        manifest.resources = vec![
            json!({"id":1,"output_path":"resources/shared.js","sha256":"digest-a"}),
            json!({"id":2,"output_path":"resources/shared.js","sha256":"digest-a"}),
            json!({"id":3,"output_path":"resources/other.js"}),
        ];
        manifest.inline_scripts = vec![json!({
            "parent_resource_id":1,
            "ordinal":1,
            "output_path":"resources/shared.js",
            "sha256":"digest-a"
        })];
        assert!(validate_manifest(&manifest, "consistent reuse").is_ok());
        manifest.inline_scripts[0]["sha256"] = json!("digest-b");
        assert!(validate_manifest(&manifest, "conflicting inline").is_err());
        manifest.inline_scripts[0]["sha256"] = json!("digest-a");
        manifest.resources[1]["sha256"] = json!("digest-c");
        assert!(validate_manifest(&manifest, "conflicting network").is_err());
    }

    #[test]
    fn rejects_inline_parent_outside_resource_range() {
        let mut manifest = valid_manifest();
        manifest.resources = vec![json!({"id": 7, "output_path": "resources/a.js"})];
        manifest.inline_scripts =
            vec![json!({"parent_resource_id": 7, "output_path": "resources/inline.js"})];
        assert!(validate_manifest(&manifest, "test").is_ok());
        manifest.inline_scripts[0]["parent_resource_id"] = json!(9);
        assert!(validate_manifest(&manifest, "test").is_err());
    }
}
