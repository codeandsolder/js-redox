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
    use anyhow::Context;
    use serde_json::{json, Map};
    use std::{
        collections::BTreeMap,
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

    #[test]
    fn api_surface_graph_and_readme_remain_consistent() -> anyhow::Result<()> {
        use crate::{
            capture_project::{write_manifest, CaptureManifest, CaptureSource, MANIFEST_NAME},
            project_readme::refresh_project_readme,
            source_graph::build_source_graph,
        };

        let temp = tempfile::tempdir()?;
        let project = temp.path().join("project");
        fs::create_dir_all(project.join("resources"))?;
        fs::create_dir_all(project.join("src/_deobfuscated"))?;

        let source = r#"
const apiOrigin = "https://api.example.test";
const usersUrl = apiOrigin + "/v1/users";
const writeMethod = "POST";
fetch(usersUrl);
fetch("/relative");
fetch("/unknown-method", opts);
fetch(apiOrigin + "/write", { ...opts, method: writeMethod });
fetch("https://api.example.test/forbidden", { method: "trace" });
navigator.sendBeacon("https://api.example.test/beacon", body);
const xhr = new XMLHttpRequest();
xhr.open("PATCH", "https://api.example.test/items");
new WebSocket("wss://socket.example.test/ws");
function shadow(fetch) { fetch("https://fake.invalid/"); }
"#;
        let rejected = "with (scope) { fetch(\"https://rejected.invalid/\"); }\n";
        fs::write(project.join("resources/app.js"), source)?;
        fs::write(project.join("resources/rejected.js"), rejected)?;
        fs::write(project.join("src/app.js"), source)?;
        fs::write(project.join("src/rejected.js"), rejected)?;
        fs::write(project.join("src/_deobfuscated/app.js"), source)?;

        write_manifest(
            &project.join(MANIFEST_NAME),
            &CaptureManifest {
                schema: "capture-project/v1".into(),
                source: CaptureSource {
                    kind: "synthetic".into(),
                    input: "synthetic-api-surface.js".into(),
                    salvaged: false,
                    extra: Map::new(),
                },
                pages: Vec::new(),
                resources: vec![
                    json!({
                        "id": 0,
                        "url": "https://app.example.test/app.js",
                        "kind": "javascript",
                        "output_path": "resources/app.js",
                        "body_present": true,
                        "references": [],
                        "response_headers": [],
                    }),
                    json!({
                        "id": 1,
                        "url": "https://app.example.test/rejected.js",
                        "kind": "javascript",
                        "output_path": "resources/rejected.js",
                        "body_present": true,
                        "references": [],
                        "response_headers": [],
                    }),
                ],
                inline_scripts: Vec::new(),
                counts: BTreeMap::new(),
                extra: Map::new(),
            },
        )?;
        write_artifact(
            &project,
            SOURCE_INDEX,
            &json!({
                "schema": SOURCE_INDEX.schema,
                "units": [
                    {"kind":"html","resource_id":0,"source_path":"src/page.html"},
                    {"kind":"javascript","raw_path":"resources/app.js","resource_id":0,"url":"https://app.example.test/app.js","source_path":"src/app.js"},
                    {"kind":"javascript","raw_path":"resources/rejected.js","resource_id":1,"url":"https://app.example.test/rejected.js","source_path":"src/rejected.js"}
                ],
                "summary": {}
            }),
        )?;
        write_artifact(
            &project,
            DEOBFUSCATION,
            &json!({
                "schema": DEOBFUSCATION.schema,
                "units": [{
                    "ordinal": 0,
                    "resource_id": 0,
                    "raw_path": "resources/app.js",
                    "output_path": "src/_deobfuscated/app.js",
                    "exit": 0
                }],
                "summary": {}
            }),
        )?;

        let summary = analyze_project_api_surface(&project)?;
        assert_eq!(summary["units"], 2);
        assert_eq!(summary["callsites"], 8);
        assert_eq!(summary["failures"], 1);
        assert_eq!(summary["static_urls"], 8);
        assert_eq!(summary["kinds"]["fetch"], 5);
        assert_eq!(summary["kinds"]["send_beacon"], 1);
        assert_eq!(summary["kinds"]["websocket"], 1);
        assert_eq!(summary["kinds"]["xhr_open"], 1);
        assert_eq!(summary["absolute_network_urls"], 6);
        assert_eq!(summary["static_methods"], 5);
        assert_eq!(summary["invalid_methods"], 1);

        let artifact = read_artifact(&project.join(API_SURFACE.relative_path), API_SURFACE)?;
        let callsites = artifact["callsites"]
            .as_array()
            .context("api-surface callsites must be an array")?;
        assert!(callsites.iter().all(|row| row["source_index_ordinal"] == 1));
        assert!(callsites
            .iter()
            .all(|row| !row.to_string().contains("fake.invalid")));
        assert_eq!(artifact["failures"][0]["source_index_ordinal"], 2);
        let users = callsites
            .iter()
            .find(|row| row["url"] == "https://api.example.test/v1/users")
            .context("missing users callsite")?;
        assert_eq!(users["url_expression"], "usersUrl");
        assert_eq!(users["method"], "GET");
        let relative = callsites
            .iter()
            .find(|row| row["url"] == "/relative")
            .context("missing relative callsite")?;
        assert_eq!(relative["absolute_network_url"], false);
        let write = callsites
            .iter()
            .find(|row| row["url"] == "https://api.example.test/write")
            .context("missing write callsite")?;
        assert_eq!(write["method"], "POST");
        assert_eq!(write["url_expression"], r#"apiOrigin + "/write""#);
        assert_eq!(write["method_expression"], "writeMethod");
        let forbidden = callsites
            .iter()
            .find(|row| row["url"] == "https://api.example.test/forbidden")
            .context("missing forbidden-method callsite")?;
        assert_eq!(forbidden["method_status"], "invalid");
        assert!(forbidden
            .get("method")
            .is_none_or(serde_json::Value::is_null));

        let graph_summary = build_source_graph(&project)?;
        assert!(graph_summary.nodes >= 8);
        let graph = read_artifact(
            &project.join(crate::analysis_artifacts::SOURCE_GRAPH.relative_path),
            crate::analysis_artifacts::SOURCE_GRAPH,
        )?;
        let api_nodes = graph["nodes"]
            .as_array()
            .context("source graph nodes must be an array")?
            .iter()
            .filter(|node| node["type"] == "api_callsite")
            .count();
        let target_edges = graph["edges"]
            .as_array()
            .context("source graph edges must be an array")?
            .iter()
            .filter(|edge| edge["kind"] == "api_target")
            .count();
        assert_eq!(api_nodes, 8);
        assert_eq!(target_edges, 5);
        assert!(graph["nodes"].as_array().is_some_and(|nodes| {
            nodes.iter().any(|node| {
                node["type"] == "external_url" && node["url"] == "wss://socket.example.test/ws"
            })
        }));
        assert!(!graph["nodes"].as_array().is_some_and(|nodes| {
            nodes.iter().any(|node| {
                node["type"] == "external_url"
                    && node["url"] == "https://api.example.test/forbidden"
            })
        }));

        refresh_project_readme(&project)?;
        let readme = fs::read_to_string(project.join("README.md"))?;
        assert!(readme.contains("[analysis/api-surface.json](analysis/api-surface.json)"));
        assert!(readme.contains("Static browser API callsites: **8**"));
        assert!(readme.contains("callsites with exact absolute network URLs: **6**"));
        assert!(readme.contains("proven invalid methods: **1**"));
        assert!(readme.contains("failed source units: **1**"));
        Ok(())
    }
}
