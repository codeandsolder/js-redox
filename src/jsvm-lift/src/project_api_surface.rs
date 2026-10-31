use crate::{
    analysis_artifacts::{load_artifact, write_artifact, API_SURFACE, DEOBFUSCATION, SOURCE_INDEX},
    api_surface::analyze_api_surface,
};
use anyhow::{Context, Result};
use serde_json::{json, Map, Value};
use std::{collections::BTreeMap, fs, path::Path};
use url::Url;

fn absolute_network_url(value: Option<&Value>) -> bool {
    let Some(raw) = value.and_then(Value::as_str) else {
        return false;
    };
    let Ok(url) = Url::parse(raw) else {
        return false;
    };
    matches!(url.scheme(), "http" | "https" | "ws" | "wss") && url.host().is_some()
}

fn string_field<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

/// Analyze every selected JavaScript view in a capture project and persist the
/// canonical `capture-api-surface/v2` artifact.
pub fn analyze_project_api_surface(project: &Path) -> Result<Value> {
    let source_index = load_artifact(project, SOURCE_INDEX, false)?
        .context("source index is required for API-surface analysis")?;
    let deobfuscation = load_artifact(project, DEOBFUSCATION, true)?;

    let mut deob_by_raw = BTreeMap::<String, Value>::new();
    if let Some(rows) = deobfuscation
        .as_ref()
        .and_then(|document| document.get("units"))
        .and_then(Value::as_array)
    {
        for row in rows {
            let Some(raw_path) = string_field(row, "raw_path") else {
                continue;
            };
            let exit = row.get("exit").and_then(Value::as_i64).unwrap_or_default();
            if exit == 0 && string_field(row, "output_path").is_some() {
                deob_by_raw.insert(raw_path.to_owned(), row.clone());
            }
        }
    }

    let units = source_index
        .get("units")
        .and_then(Value::as_array)
        .context("source index units must be an array")?;
    let mut callsites = Vec::new();
    let mut failures = Vec::new();
    let mut analyzed_units = 0_usize;

    for (source_index_ordinal, unit) in units.iter().enumerate() {
        if string_field(unit, "kind") != Some("javascript")
            || string_field(unit, "source_path").is_none()
        {
            continue;
        }
        let raw_path = string_field(unit, "raw_path");
        let deob = raw_path.and_then(|raw| deob_by_raw.get(raw));
        let analysis_path = deob
            .and_then(|row| string_field(row, "output_path"))
            .or_else(|| string_field(unit, "source_path"));
        let Some(analysis_path) = analysis_path else {
            continue;
        };
        analyzed_units += 1;
        let source_path = project.join(analysis_path);
        if !source_path.is_file() {
            failures.push(json!({
                "source_index_ordinal": source_index_ordinal,
                "resource_id": unit.get("resource_id").cloned().unwrap_or(Value::Null),
                "raw_path": raw_path,
                "analysis_path": analysis_path,
                "error": "selected analysis source is missing",
            }));
            continue;
        }

        let source = match fs::read_to_string(&source_path) {
            Ok(source) => source,
            Err(error) => {
                failures.push(json!({
                    "source_index_ordinal": source_index_ordinal,
                    "resource_id": unit.get("resource_id").cloned().unwrap_or(Value::Null),
                    "raw_path": raw_path,
                    "analysis_path": analysis_path,
                    "error": format!("failed to read selected analysis source: {error}"),
                }));
                continue;
            }
        };
        let rows = match analyze_api_surface(&source) {
            Ok(rows) => rows,
            Err(error) => {
                failures.push(json!({
                    "source_index_ordinal": source_index_ordinal,
                    "resource_id": unit.get("resource_id").cloned().unwrap_or(Value::Null),
                    "raw_path": raw_path,
                    "analysis_path": analysis_path,
                    "error": error.to_string(),
                }));
                continue;
            }
        };

        for (callsite_ordinal, row) in rows.into_iter().enumerate() {
            let value = serde_json::to_value(row)?;
            let mut object = match value {
                Value::Object(object) => object,
                _ => Map::new(),
            };
            object.insert("source_index_ordinal".into(), json!(source_index_ordinal));
            object.insert("callsite_ordinal".into(), json!(callsite_ordinal));
            object.insert(
                "resource_id".into(),
                unit.get("resource_id").cloned().unwrap_or(Value::Null),
            );
            object.insert(
                "resource_url".into(),
                unit.get("url").cloned().unwrap_or(Value::Null),
            );
            object.insert(
                "raw_path".into(),
                raw_path.map_or(Value::Null, |v| json!(v)),
            );
            object.insert(
                "source_path".into(),
                unit.get("source_path").cloned().unwrap_or(Value::Null),
            );
            object.insert("analysis_path".into(), json!(analysis_path));
            object.insert(
                "deobfuscation_ordinal".into(),
                deob.and_then(|row| row.get("ordinal"))
                    .cloned()
                    .unwrap_or(Value::Null),
            );
            let absolute = absolute_network_url(object.get("url"));
            object.insert("absolute_network_url".into(), Value::Bool(absolute));
            callsites.push(Value::Object(object));
        }
    }

    let mut kinds = BTreeMap::<String, usize>::new();
    for row in &callsites {
        if let Some(kind) = string_field(row, "kind") {
            *kinds.entry(kind.to_owned()).or_default() += 1;
        }
    }
    let summary = json!({
        "units": analyzed_units,
        "callsites": callsites.len(),
        "failures": failures.len(),
        "kinds": kinds,
        "static_urls": callsites.iter().filter(|row| string_field(row, "url").is_some()).count(),
        "absolute_network_urls": callsites.iter().filter(|row| row.get("absolute_network_url").and_then(Value::as_bool) == Some(true)).count(),
        "static_methods": callsites.iter().filter(|row| string_field(row, "method").is_some()).count(),
        "invalid_methods": callsites.iter().filter(|row| string_field(row, "method_status") == Some("invalid")).count(),
    });
    let document = json!({
        "schema": API_SURFACE.schema,
        "callsites": callsites,
        "failures": failures,
        "summary": summary,
    });
    write_artifact(project, API_SURFACE, &document)?;
    Ok(document
        .get("summary")
        .cloned()
        .unwrap_or_else(|| json!({})))
}

#[cfg(test)]
mod tests {
    use super::analyze_project_api_surface;
    use crate::analysis_artifacts::{
        read_artifact, write_artifact, API_SURFACE, DEOBFUSCATION, SOURCE_INDEX,
    };
    use serde_json::json;
    use std::{
        fs,
        path::PathBuf,
        process,
        sync::atomic::{AtomicU64, Ordering},
    };

    static NEXT_TEST: AtomicU64 = AtomicU64::new(0);

    fn temp_project() -> PathBuf {
        let ordinal = NEXT_TEST.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!("jsvm-api-surface-{}-{ordinal}", process::id()))
    }

    #[test]
    fn project_mode_prefers_deobfuscated_sources_and_records_failures() -> anyhow::Result<()> {
        let project = temp_project();
        if project.exists() {
            fs::remove_dir_all(&project)?;
        }
        fs::create_dir_all(project.join("src/_deobfuscated"))?;
        fs::write(
            project.join("src/_deobfuscated/app.js"),
            "fetch('https://api.example.test/v1');\n",
        )?;

        let source_index = json!({
            "schema": SOURCE_INDEX.schema,
            "units": [
                {
                    "kind": "javascript",
                    "resource_id": 7,
                    "url": "https://example.test/missing.js",
                    "raw_path": "resources/missing.js",
                    "source_path": "src/missing.js"
                },
                {
                    "kind": "javascript",
                    "resource_id": 11,
                    "url": "https://example.test/app.js",
                    "raw_path": "resources/app.js",
                    "source_path": "src/app.js"
                },
                {
                    "kind": "text",
                    "resource_id": 13,
                    "source_path": "src/data.txt"
                }
            ],
            "summary": {}
        });
        write_artifact(&project, SOURCE_INDEX, &source_index)?;
        let deobfuscation = json!({
            "schema": DEOBFUSCATION.schema,
            "units": [{
                "ordinal": 3,
                "raw_path": "resources/app.js",
                "output_path": "src/_deobfuscated/app.js",
                "exit": 0
            }],
            "summary": {}
        });
        write_artifact(&project, DEOBFUSCATION, &deobfuscation)?;

        let summary = analyze_project_api_surface(&project)?;
        assert_eq!(summary["units"], 2);
        assert_eq!(summary["callsites"], 1);
        assert_eq!(summary["failures"], 1);
        assert_eq!(summary["absolute_network_urls"], 1);
        let artifact = read_artifact(&project.join(API_SURFACE.relative_path), API_SURFACE)?;
        let call = &artifact["callsites"][0];
        assert_eq!(call["resource_id"], 11);
        assert_eq!(call["source_index_ordinal"], 1);
        assert_eq!(call["deobfuscation_ordinal"], 3);
        assert_eq!(call["analysis_path"], "src/_deobfuscated/app.js");
        assert_eq!(call["url"], "https://api.example.test/v1");
        assert_eq!(artifact["failures"][0]["source_index_ordinal"], 0);

        fs::remove_dir_all(project)?;
        Ok(())
    }
}
