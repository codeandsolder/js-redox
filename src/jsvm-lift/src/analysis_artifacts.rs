use anyhow::{bail, Context, Result};
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArtifactSpec {
    pub name: &'static str,
    pub relative_path: &'static str,
    pub schema: &'static str,
    pub array_fields: &'static [&'static str],
    pub object_fields: &'static [&'static str],
}

macro_rules! artifact {
    ($name:ident, $label:literal, $path:literal, $schema:literal $(, arrays = [$($array:literal),* $(,)?])? $(, objects = [$($object:literal),* $(,)?])? ) => {
        pub const $name: ArtifactSpec = ArtifactSpec {
            name: $label,
            relative_path: $path,
            schema: $schema,
            array_fields: &[$($($array),*)?],
            object_fields: &[$($($object),*)?],
        };
    };
}

artifact!(
    SOURCE_INDEX,
    "source index",
    "analysis/source-index.json",
    "capture-source-index/v1",
    arrays = ["units"],
    objects = ["summary"]
);
artifact!(
    SOURCEMAPS,
    "source-map recovery",
    "analysis/sourcemaps.json",
    "capture-sourcemap-recovery/v1",
    arrays = ["source_maps"]
);
artifact!(
    IMPORT_MAPS,
    "import maps",
    "analysis/import-maps.json",
    "capture-import-maps/v1",
    arrays = ["maps"],
    objects = ["documents", "summary"]
);
artifact!(
    JS_REFERENCES,
    "JavaScript references",
    "analysis/js-references.json",
    "capture-js-references/v1",
    arrays = ["code_units"],
    objects = ["summary"]
);
artifact!(
    STRING_RECOVERY,
    "static string recovery",
    "analysis/string-recovery.json",
    "capture-static-string-recovery/v1",
    arrays = ["units"],
    objects = ["summary"]
);
artifact!(
    DEOBFUSCATION,
    "safe deobfuscation",
    "analysis/deobfuscation.json",
    "capture-safe-deobfuscation/v1",
    arrays = ["units"],
    objects = ["summary"]
);
artifact!(
    BUNDLES,
    "bundle modules",
    "analysis/bundles.json",
    "capture-bundle-modules/v1",
    arrays = ["bundles", "modules", "failures"],
    objects = ["summary"]
);
artifact!(
    WASM_INDEX,
    "WASM capture index",
    "analysis/wasm/index.json",
    "wasm-redox/capture-v1",
    arrays = ["modules"],
    objects = ["summary"]
);
artifact!(
    WASM_JS_BOUNDARY,
    "WASM/JavaScript boundary correlation",
    "analysis/wasm-js-boundary.json",
    "wasm-js-boundary-correlation/v7",
    arrays = ["host_effect_rows", "copied_input_rows", "skipped_modules"],
    objects = ["summary"]
);
artifact!(
    WASM_RESOURCE_PROVENANCE,
    "WASM runtime resource provenance",
    "analysis/wasm-resource-provenance.json",
    "wasm-runtime-resource-provenance/v2",
    arrays = ["observations", "unmatched", "ignored_non_body"],
    objects = ["summary"]
);
artifact!(
    GENERATED_RECOVERY,
    "generated-code recovery",
    "analysis/generated-recovery.json",
    "generated-code-safe-recovery/v1",
    arrays = ["units"],
    objects = ["summary"]
);
artifact!(
    JSVM_INDEX,
    "JS VM analysis",
    "analysis/jsvm/index.json",
    "capture-jsvm-analysis/v1",
    arrays = ["code_units", "dynamic_code_units"]
);
artifact!(
    SOURCE_GRAPH,
    "source graph",
    "analysis/source-graph.json",
    "source-graph/v2",
    arrays = ["nodes", "edges", "unresolved_edges"],
    objects = ["summary"]
);
artifact!(
    OBSERVED_SOURCE,
    "observed runtime source tree",
    "analysis/observed-source.json",
    "capture-observed-sources/v1",
    arrays = ["sources"],
    objects = ["summary"]
);
artifact!(
    EXECUTION_COVERAGE,
    "browser execution coverage with explicit observation mode",
    "analysis/execution-coverage.json",
    "capture-execution-coverage/v2",
    arrays = ["scripts"],
    objects = ["summary"]
);
artifact!(
    SELECTIVE_TRACE,
    "concrete debugger invocation witnesses",
    "analysis/selective-trace.json",
    "capture-selective-trace/v1",
    arrays = ["hits", "errors"],
    objects = ["summary"]
);
artifact!(
    RUNTIME_SCRIPTS,
    "runtime scripts",
    "analysis/runtime-scripts.json",
    "js-redox-runtime-scripts/v2",
    arrays = [
        "alpine_families",
        "gtm_families",
        "sources",
        "script_identity_conflicts"
    ],
    objects = ["summary"]
);
artifact!(
    API_SURFACE,
    "static API surface",
    "analysis/api-surface.json",
    "capture-api-surface/v10",
    arrays = ["callsites", "mutation_sites", "failures"],
    objects = ["summary"]
);

pub const ALL_ARTIFACTS: &[ArtifactSpec] = &[
    SOURCE_INDEX,
    SOURCEMAPS,
    IMPORT_MAPS,
    JS_REFERENCES,
    STRING_RECOVERY,
    DEOBFUSCATION,
    BUNDLES,
    WASM_INDEX,
    WASM_JS_BOUNDARY,
    WASM_RESOURCE_PROVENANCE,
    GENERATED_RECOVERY,
    JSVM_INDEX,
    SOURCE_GRAPH,
    RUNTIME_SCRIPTS,
    SELECTIVE_TRACE,
    EXECUTION_COVERAGE,
    OBSERVED_SOURCE,
    API_SURFACE,
];

#[must_use]
pub fn artifact_path(project: &Path, spec: ArtifactSpec) -> PathBuf {
    project.join(spec.relative_path)
}

/// Validate one artifact's root, schema and required field shapes.
///
/// # Errors
///
/// Fails when the root is not an object, its schema does not match the artifact contract, or a required array/object field is missing or incorrectly typed.
pub fn validate_artifact<'a>(
    document: &'a Value,
    spec: ArtifactSpec,
    label: &str,
) -> Result<&'a serde_json::Map<String, Value>> {
    let Some(object) = document.as_object() else {
        bail!("{label}: artifact root must be an object");
    };
    let schema = object.get("schema").and_then(Value::as_str);
    if schema != Some(spec.schema) {
        bail!(
            "{label}: expected schema {:?}, got {:?}",
            spec.schema,
            schema
        );
    }
    for &field in spec.array_fields {
        if !object.get(field).is_some_and(Value::is_array) {
            bail!("{label}: {field} must be an array");
        }
    }
    for &field in spec.object_fields {
        if !object.get(field).is_some_and(Value::is_object) {
            bail!("{label}: {field} must be an object");
        }
    }
    Ok(object)
}

/// Construct an artifact with a schema owned by its contract.
///
/// # Errors
///
/// Fails if the payload already defines the reserved `schema` field or if the completed artifact violates the required field shapes.
pub fn build_artifact(
    spec: ArtifactSpec,
    mut payload: serde_json::Map<String, Value>,
) -> Result<Value> {
    if payload.contains_key("schema") {
        bail!("{}: schema is owned by the artifact contract", spec.name);
    }
    payload.insert("schema".into(), Value::String(spec.schema.into()));
    let document = Value::Object(payload);
    validate_artifact(&document, spec, spec.name)?;
    Ok(document)
}

/// Read, decode and validate a schema-specific analysis artifact.
///
/// # Errors
///
/// Fails on file-read errors, invalid JSON, a mismatched schema or missing/incorrect required fields.
pub fn read_artifact(path: &Path, spec: ArtifactSpec) -> Result<Value> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("failed to read {} {}", spec.name, path.display()))?;
    let document: Value = serde_json::from_str(&text)
        .with_context(|| format!("failed to parse {} {}", spec.name, path.display()))?;
    validate_artifact(&document, spec, &path.display().to_string())?;
    Ok(document)
}

/// Load a project artifact, optionally accepting its absence.
///
/// # Errors
///
/// Propagates read, parse and validation failures; a missing optional artifact returns `Ok(None)`.
pub fn load_artifact(project: &Path, spec: ArtifactSpec, optional: bool) -> Result<Option<Value>> {
    match read_artifact(&artifact_path(project, spec), spec) {
        Ok(document) => Ok(Some(document)),
        Err(error)
            if optional
                && error
                    .downcast_ref::<std::io::Error>()
                    .is_some_and(|cause| cause.kind() == std::io::ErrorKind::NotFound) =>
        {
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// Stage a validated artifact without replacing its published file.
pub(crate) fn stage_artifact(
    project: &Path,
    spec: ArtifactSpec,
    document: &Value,
) -> Result<crate::report_file::StagedReport> {
    let path = artifact_path(project, spec);
    validate_artifact(document, spec, &path.display().to_string())?;
    crate::report_file::stage_json(&path, document)
}

/// Write a validated analysis artifact at its project-relative path.
/// # Errors
/// Propagates validation, serialization and filesystem errors.
pub fn write_artifact(project: &Path, spec: ArtifactSpec, document: &Value) -> Result<()> {
    stage_artifact(project, spec, document)?.publish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::collections::BTreeSet;

    #[test]
    fn optional_artifact_ignores_missing_file_not_other_read_failures() -> Result<()> {
        let temp = tempfile::TempDir::new()?;
        let project = temp.path();
        assert!(load_artifact(project, SOURCE_INDEX, true)?.is_none());
        assert!(load_artifact(project, SOURCE_INDEX, false).is_err());
        // A non-directory path component makes the requested artifact
        // inaccessible, rather than an optional missing artifact.
        let directory = project.join("analysis");
        fs::write(&directory, "not a directory")?;
        assert!(load_artifact(project, SOURCE_INDEX, true).is_err());
        fs::remove_file(&directory)?;
        fs::create_dir(&directory)?;
        fs::write(artifact_path(project, SOURCE_INDEX), "invalid JSON")?;
        assert!(load_artifact(project, SOURCE_INDEX, true).is_err());
        Ok(())
    }

    #[test]
    fn artifact_contracts_are_unique_and_fail_closed() -> Result<()> {
        let paths = ALL_ARTIFACTS
            .iter()
            .map(|spec| spec.relative_path)
            .collect::<BTreeSet<_>>();
        let schemas = ALL_ARTIFACTS
            .iter()
            .map(|spec| spec.schema)
            .collect::<BTreeSet<_>>();
        assert_eq!(paths.len(), ALL_ARTIFACTS.len());
        assert_eq!(schemas.len(), ALL_ARTIFACTS.len());
        assert!(ALL_ARTIFACTS
            .iter()
            .all(|spec| !spec.schema.starts_with("har-")));

        let good = json!({"schema": SOURCE_INDEX.schema, "units": [], "summary": {"units": 0}});
        validate_artifact(&good, SOURCE_INDEX, "test")?;
        assert!(validate_artifact(
            &json!({"schema": "capture-source-index/v0", "units": [], "summary": {}}),
            SOURCE_INDEX,
            "test"
        )
        .is_err());
        assert!(validate_artifact(
            &json!({"schema": SOURCE_INDEX.schema, "summary": {}}),
            SOURCE_INDEX,
            "test"
        )
        .is_err());
        assert!(validate_artifact(
            &json!({"schema": SOURCE_INDEX.schema, "units": [], "summary": []}),
            SOURCE_INDEX,
            "test"
        )
        .is_err());
        Ok(())
    }
}
