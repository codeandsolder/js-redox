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
    "wasm-js-boundary-correlation/v6",
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
    "source-graph/v1",
    arrays = ["nodes", "edges"],
    objects = ["summary"]
);
artifact!(
    RUNTIME_SCRIPTS,
    "runtime scripts",
    "analysis/runtime-scripts.json",
    "js-redox-runtime-scripts/v1",
    arrays = ["alpine_families", "gtm_families", "sources"],
    objects = ["summary"]
);
artifact!(
    API_SURFACE,
    "static API surface",
    "analysis/api-surface.json",
    "capture-api-surface/v2",
    arrays = ["callsites", "failures"],
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
    API_SURFACE,
];

#[must_use]
pub fn artifact_path(project: &Path, spec: ArtifactSpec) -> PathBuf {
    project.join(spec.relative_path)
}

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

pub fn read_artifact(path: &Path, spec: ArtifactSpec) -> Result<Value> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("failed to read {} {}", spec.name, path.display()))?;
    let document: Value = serde_json::from_str(&text)
        .with_context(|| format!("failed to parse {} {}", spec.name, path.display()))?;
    validate_artifact(&document, spec, &path.display().to_string())?;
    Ok(document)
}

pub fn load_artifact(project: &Path, spec: ArtifactSpec, optional: bool) -> Result<Option<Value>> {
    let path = artifact_path(project, spec);
    if optional && !path.exists() {
        return Ok(None);
    }
    read_artifact(&path, spec).map(Some)
}

pub fn write_artifact_path(path: &Path, spec: ArtifactSpec, document: &Value) -> Result<()> {
    validate_artifact(document, spec, &path.display().to_string())?;
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    let mut encoded = serde_json::to_string_pretty(document)?;
    encoded.push('\n');
    fs::write(path, encoded).with_context(|| format!("writing {}", path.display()))
}

pub fn write_artifact(project: &Path, spec: ArtifactSpec, document: &Value) -> Result<()> {
    write_artifact_path(&artifact_path(project, spec), spec, document)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::collections::BTreeSet;

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
