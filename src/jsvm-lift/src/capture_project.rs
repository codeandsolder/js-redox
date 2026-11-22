use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
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

#[derive(Default)]
struct BodyClaims<'a> {
    digest: Option<&'a str>,
    bytes: Option<u64>,
}

#[derive(Default)]
struct CapturePaths<'a> {
    claims: BTreeMap<&'a str, BodyClaims<'a>>,
}

impl<'a> CapturePaths<'a> {
    fn record(&mut self, object: &'a Map<String, Value>, label: &str) -> Result<()> {
        let Some(value) = object.get("output_path").filter(|value| !value.is_null()) else {
            return Ok(());
        };
        let Some(path) = value.as_str() else {
            bail!("{label}: output_path must be a string or null");
        };
        validate_project_relative_path(path, label)?;
        if !path.starts_with("resources/") {
            bail!("{label}: output_path must be under resources/");
        }
        let claim = self.claims.entry(path).or_default();
        if let Some(value) = object.get("sha256").filter(|value| !value.is_null()) {
            let digest = value
                .as_str()
                .context("capture SHA-256 claim must be a string")?;
            if claim.digest.is_some_and(|previous| previous != digest) {
                bail!("{label}: conflicting SHA-256 claims for shared capture path {path}");
            }
            claim.digest = Some(digest);
        }
        if let Some(value) = object.get("body_bytes").filter(|value| !value.is_null()) {
            let bytes = value
                .as_u64()
                .context("capture body size must be a non-negative integer")?;
            if claim.bytes.is_some_and(|previous| previous != bytes) {
                bail!("{label}: conflicting byte counts for shared capture path {path}");
            }
            claim.bytes = Some(bytes);
        }
        Ok(())
    }

    /// File paths cannot be ancestors of other file paths, regardless of
    /// whether either row supplies a digest or length claim.
    fn validate_namespace(&self, label: &str) -> Result<()> {
        for &path in self.claims.keys() {
            for (boundary, _) in path.match_indices('/') {
                let parent = &path[..boundary];
                if self.claims.contains_key(parent) {
                    bail!(
                        "{label}: capture paths {parent} and {path} conflict as file and directory"
                    );
                }
            }
        }
        Ok(())
    }
}

fn validate_extra_fields(extra: &Map<String, Value>, reserved: &[&str], label: &str) -> Result<()> {
    if let Some(field) = reserved.iter().find(|&&field| extra.contains_key(field)) {
        bail!("{label}: extra metadata shadows reserved field {field}");
    }
    Ok(())
}

/// Validate the capture manifest schema and internal reference integrity.
///
/// # Errors
///
/// Fails on an incorrect schema, shadowed canonical fields, malformed record
/// identities, unsafe output paths or contradictory shared-file claims.
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

    validate_extra_fields(
        &manifest.extra,
        &[
            "schema",
            "source",
            "pages",
            "resources",
            "inline_scripts",
            "counts",
        ],
        label,
    )?;
    validate_extra_fields(
        &manifest.source.extra,
        &["kind", "input", "salvaged"],
        &format!("{label}: source"),
    )?;
    for (index, page) in manifest.pages.iter().enumerate() {
        if !page.is_object() {
            bail!("{label}: pages[{index}] must be an object");
        }
    }

    let mut resource_ids = BTreeSet::new();
    let mut paths = CapturePaths::default();
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
        paths.record(object, &format!("{label}: resources[{index}]"))?;
    }

    let mut script_ids = BTreeSet::new();
    for (index, script) in manifest.inline_scripts.iter().enumerate() {
        let Some(object) = script.as_object() else {
            bail!("{label}: inline_scripts[{index}] must be an object");
        };
        let Some(parent) = object
            .get("parent_resource_id")
            .and_then(Value::as_u64)
            .filter(|parent| resource_ids.contains(parent))
        else {
            bail!("{label}: inline_scripts[{index}].parent_resource_id does not name a resource");
        };
        let Some(ordinal) = object
            .get("ordinal")
            .and_then(Value::as_u64)
            .filter(|&ordinal| ordinal != 0)
        else {
            bail!("{label}: inline_scripts[{index}].ordinal must be a positive integer");
        };
        if !script_ids.insert((parent, ordinal)) {
            bail!("{label}: duplicate inline script identity ({parent}, {ordinal})");
        }
        paths.record(object, &format!("{label}: inline_scripts[{index}]"))?;
    }
    paths.validate_namespace(label)
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
    use std::fs;

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
    fn canonical_manifest_fields_cannot_be_shadowed_by_metadata() -> Result<()> {
        let root = tempfile::tempdir()?;
        let path = manifest_path(root.path());
        let original = valid_manifest();
        write_manifest(&path, &original)?;
        let bytes = fs::read(&path)?;
        for field in [
            "schema",
            "source",
            "pages",
            "resources",
            "inline_scripts",
            "counts",
        ] {
            let mut invalid = original.clone();
            invalid.extra.insert(field.into(), Value::Null);
            assert!(write_manifest(&path, &invalid).is_err(), "{field}");
            assert_eq!(fs::read(&path)?, bytes);
        }
        for field in ["kind", "input", "salvaged"] {
            let mut invalid = original.clone();
            invalid.source.extra.insert(field.into(), Value::Null);
            assert!(write_manifest(&path, &invalid).is_err(), "{field}");
            assert_eq!(fs::read(&path)?, bytes);
        }
        Ok(())
    }

    #[test]
    fn capture_namespace_and_partial_size_claims_are_consistent() -> Result<()> {
        let mut manifest = valid_manifest();
        manifest.resources = vec![
            json!({"id":1,"output_path":"resources/a","body_bytes":4}),
            json!({"id":2,"output_path":"resources/a","sha256":"digest-a"}),
            json!({"id":3,"output_path":"resources/a-other","body_bytes":0}),
        ];
        manifest.inline_scripts = vec![
            json!({"parent_resource_id":1,"ordinal":1,"output_path":"resources/a","body_bytes":4,"sha256":"digest-a"}),
        ];
        validate_manifest(&manifest, "consistent claims")?;
        manifest.inline_scripts[0]["body_bytes"] = json!(5);
        assert!(validate_manifest(&manifest, "conflicting size").is_err());
        manifest.inline_scripts[0]["body_bytes"] = Value::Null;
        validate_manifest(&manifest, "unknown size")?;
        manifest.resources[2]["output_path"] = json!("resources/a/b");
        assert!(validate_manifest(&manifest, "file-directory conflict").is_err());
        manifest.resources.reverse();
        assert!(validate_manifest(&manifest, "reversed conflict").is_err());
        manifest.resources[0]["output_path"] = json!("resources/a-other");
        manifest.resources[1]["sha256"] = json!(42);
        assert!(validate_manifest(&manifest, "nonstring hash").is_err());
        Ok(())
    }

    #[test]
    fn pages_and_inline_occurrences_have_record_and_identity_contracts() -> Result<()> {
        let mut manifest = valid_manifest();
        manifest.pages.push(Value::Null);
        assert!(validate_manifest(&manifest, "invalid page record").is_err());
        manifest.pages[0] = json!({"id":"page"});
        manifest.resources = vec![json!({"id":7}), json!({"id":9})];
        manifest.inline_scripts = vec![
            json!({"parent_resource_id":7,"ordinal":1}),
            json!({"parent_resource_id":9,"ordinal":1}),
        ];
        validate_manifest(&manifest, "separate occurrences")?;
        manifest.inline_scripts[1]["parent_resource_id"] = json!(7);
        assert!(validate_manifest(&manifest, "duplicate ordinal").is_err());
        for ordinal in [json!(0), json!(-1), json!("1"), Value::Null] {
            manifest.inline_scripts[1]["ordinal"] = ordinal;
            assert!(validate_manifest(&manifest, "invalid ordinal").is_err());
        }
        Ok(())
    }

    #[test]
    fn rejects_inline_parent_outside_resource_range() {
        let mut manifest = valid_manifest();
        manifest.resources = vec![json!({"id": 7, "output_path": "resources/a.js"})];
        manifest.inline_scripts = vec![
            json!({"parent_resource_id": 7, "ordinal": 1, "output_path": "resources/inline.js"}),
        ];
        assert!(validate_manifest(&manifest, "test").is_ok());
        manifest.inline_scripts[0]["parent_resource_id"] = json!(9);
        assert!(validate_manifest(&manifest, "test").is_err());
    }
}
