use crate::{
    analysis_artifacts::{write_artifact, SOURCE_INDEX},
    browser_script_types::{inline_script_kind, InlineScriptKind},
    capture_project::load_manifest,
    content_dedup::{default_jobs, link_or_copy, sha256_path, Materialization},
    js_format::format_source,
};
use anyhow::{bail, Context, Result};
use encoding_rs::{Encoding, WINDOWS_1252};
use rayon::{prelude::*, ThreadPoolBuilder};
use regex::Regex;
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceMaterializeSummary {
    pub units: usize,
    pub javascript_units: usize,
    pub unique_javascript_inputs: usize,
    pub incomplete_units: usize,
    pub jobs: usize,
}

#[derive(Debug, Clone)]
struct Unit {
    kind: String,
    captured_kind: String,
    transport_kind: String,
    raw_path: String,
    resource_id: u64,
    url: String,
    resource: Option<Value>,
}

#[derive(Debug, Clone)]
struct JsTask {
    row_index: usize,
    source: PathBuf,
    dest: PathBuf,
    raw_path: String,
    resource: Option<Value>,
}

#[derive(Debug, Clone)]
struct DecodeResult {
    text: String,
    encoding: String,
    fallback: bool,
}

#[derive(Debug, Clone)]
struct JsGroupResult {
    transform: &'static str,
    formatted: bool,
    format_error: Option<String>,
    source_encoding: String,
    encoding_fallback: bool,
    output: String,
}

fn src_path(raw_path: &str) -> String {
    raw_path
        .strip_prefix("resources/")
        .map_or_else(|| format!("src/{raw_path}"), |rest| format!("src/{rest}"))
}

fn declared_charset(resource: Option<&Value>) -> Option<String> {
    let resource = resource?.as_object()?;
    let charset = Regex::new(r#"(?i)charset\s*=\s*['\"]?([^;'\"\s]+)"#).ok()?;
    let mut candidates = Vec::new();
    if let Some(mime) = resource.get("mime_type").and_then(Value::as_str) {
        candidates.push(mime);
    }
    if let Some(headers) = resource.get("response_headers").and_then(Value::as_array) {
        for header in headers {
            let Some(header) = header.as_object() else {
                continue;
            };
            if header
                .get("name")
                .and_then(Value::as_str)
                .is_some_and(|name| name.eq_ignore_ascii_case("content-type"))
            {
                if let Some(value) = header.get("value").and_then(Value::as_str) {
                    candidates.push(value);
                }
            }
        }
    }
    for value in candidates {
        if let Some(found) = charset.captures(value).and_then(|captures| captures.get(1)) {
            let label = found.as_str().trim().to_ascii_lowercase();
            return Some(match label.as_str() {
                "iso-8859-1" | "iso8859-1" | "latin1" | "latin-1" | "windows-1252" => {
                    "cp1252".to_owned()
                }
                "utf8" => "utf-8".to_owned(),
                _ => label,
            });
        }
    }
    None
}

fn decode_with_label(raw: &[u8], label: &str) -> Option<String> {
    match label {
        "utf-8" => std::str::from_utf8(raw).ok().map(ToOwned::to_owned),
        "cp1252" => {
            if raw
                .iter()
                .any(|byte| matches!(*byte, 0x81 | 0x8d | 0x8f | 0x90 | 0x9d))
            {
                return None;
            }
            let (decoded, _, had_errors) = WINDOWS_1252.decode(raw);
            (!had_errors).then(|| decoded.into_owned())
        }
        "latin1" => Some(raw.iter().map(|byte| char::from(*byte)).collect()),
        _ => {
            let encoding = Encoding::for_label(label.as_bytes())?;
            encoding
                .decode_without_bom_handling_and_without_replacement(raw)
                .map(|decoded| decoded.into_owned())
        }
    }
}

fn decode_text_bytes(raw: &[u8], resource: Option<&Value>) -> Result<DecodeResult> {
    let declared = declared_charset(resource);
    let mut encodings = Vec::new();
    if let Some(declared) = declared {
        encodings.push(declared);
    }
    for fallback in ["utf-8", "cp1252", "latin1"] {
        if !encodings.iter().any(|encoding| encoding == fallback) {
            encodings.push(fallback.to_owned());
        }
    }
    for (index, encoding) in encodings.iter().enumerate() {
        if let Some(text) = decode_with_label(raw, encoding) {
            return Ok(DecodeResult {
                text,
                encoding: encoding.clone(),
                fallback: index > 0,
            });
        }
    }
    bail!("no usable text decoding")
}

fn strip_xssi_prefix(text: &str) -> (&str, Option<&'static str>) {
    let stripped = text.trim_start_matches(['\u{feff}', ' ', '\t', '\r', '\n']);
    for prefix in ["for (;;);", "for(;;);", "while (1);", "while(1);", ")]}'"] {
        if let Some(rest) = stripped.strip_prefix(prefix) {
            return (
                rest.trim_start_matches(['\r', '\n', ' ', '\t']),
                Some(prefix),
            );
        }
    }
    (stripped, None)
}

fn materialize_text(
    source: &Path,
    dest: &Path,
    kind: &str,
    resource: Option<&Value>,
) -> Result<Map<String, Value>> {
    let raw = fs::read(source).with_context(|| format!("reading {}", source.display()))?;
    let decoded = decode_text_bytes(&raw, resource)?;
    let mut text = decoded.text;
    let mut transform = if decoded.encoding == "utf-8" && !decoded.fallback {
        "identity_utf8"
    } else {
        "text_transcoded_utf8"
    };
    let mut formatted = false;
    if kind == "json" {
        let (candidate, prefix) = strip_xssi_prefix(&text);
        if let Ok(value) = serde_json::from_str::<Value>(candidate) {
            text = serde_json::to_string_pretty(&value)?;
            text.push('\n');
            transform = if prefix.is_some() {
                "json_xssi_unwrapped"
            } else {
                "json_pretty"
            };
            formatted = true;
        }
    }
    if let Some(parent) = dest.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    fs::write(dest, text).with_context(|| format!("writing {}", dest.display()))?;
    Ok(Map::from_iter([
        ("transform".into(), Value::String(transform.into())),
        ("formatted".into(), Value::Bool(formatted)),
        ("source_encoding".into(), Value::String(decoded.encoding)),
        ("encoding_fallback".into(), Value::Bool(decoded.fallback)),
    ]))
}

fn format_javascript(source: &Path, resource: Option<&Value>) -> Result<JsGroupResult> {
    let raw = fs::read(source).with_context(|| format!("reading {}", source.display()))?;
    let decoded = decode_text_bytes(&raw, resource)?;
    match format_source(&decoded.text) {
        Ok(output) => Ok(JsGroupResult {
            transform: "oxc_parse_codegen",
            formatted: true,
            format_error: None,
            source_encoding: decoded.encoding,
            encoding_fallback: decoded.fallback,
            output,
        }),
        Err(error) => Ok(JsGroupResult {
            transform: "utf8_raw_fallback",
            formatted: false,
            format_error: Some(error.to_string()),
            source_encoding: decoded.encoding,
            encoding_fallback: decoded.fallback,
            output: decoded.text,
        }),
    }
}

fn object_string(value: &Value, key: &str) -> Option<String> {
    value
        .get(key)
        .and_then(Value::as_str)
        .map(ToOwned::to_owned)
}

fn object_u64(value: &Value, key: &str) -> Result<u64> {
    value
        .get(key)
        .and_then(Value::as_u64)
        .with_context(|| format!("{key} must be a non-negative integer"))
}

fn materialization_name(value: Materialization) -> &'static str {
    match value {
        Materialization::HardLink => "hardlink",
        Materialization::Copy => "copy",
    }
}

pub fn materialize_capture_source(
    project: &Path,
    jobs: Option<usize>,
) -> Result<SourceMaterializeSummary> {
    let jobs = jobs.unwrap_or_else(|| default_jobs(8)).max(1);
    let manifest = load_manifest(project)?;
    let mut resources_by_id = BTreeMap::<u64, &Value>::new();
    for resource in &manifest.resources {
        let id = object_u64(resource, "id")?;
        resources_by_id.insert(id, resource);
    }

    let mut units = Vec::<Unit>::new();
    let mut seen = BTreeSet::<String>::new();
    for resource in &manifest.resources {
        let Some(raw_path) = object_string(resource, "output_path") else {
            continue;
        };
        if !seen.insert(raw_path.clone()) {
            continue;
        }
        let kind = object_string(resource, "kind").context("resource.kind must be a string")?;
        if !matches!(
            kind.as_str(),
            "javascript" | "html" | "json" | "css" | "text"
        ) {
            continue;
        }
        let resource_id = object_u64(resource, "id")?;
        let url = object_string(resource, "url").unwrap_or_default();
        let transport_kind =
            object_string(resource, "transport_kind").unwrap_or_else(|| kind.clone());
        if resource.get("body_complete").and_then(Value::as_bool) == Some(false) {
            units.push(Unit {
                kind: "incomplete".into(),
                captured_kind: kind,
                transport_kind,
                raw_path,
                resource_id,
                url,
                resource: None,
            });
            continue;
        }
        units.push(Unit {
            kind: kind.clone(),
            captured_kind: kind,
            transport_kind,
            raw_path,
            resource_id,
            url,
            resource: Some(resource.clone()),
        });
    }

    for script in &manifest.inline_scripts {
        let Some(raw_path) = object_string(script, "output_path") else {
            continue;
        };
        if !seen.insert(raw_path.clone()) {
            continue;
        }
        let parent_id = object_u64(script, "parent_resource_id")?;
        let parent = resources_by_id
            .get(&parent_id)
            .with_context(|| format!("inline script parent resource id {parent_id} is missing"))?;
        let script_type = script.get("script_type").and_then(Value::as_str);
        let kind = match inline_script_kind(script_type) {
            InlineScriptKind::JavaScript => "javascript",
            InlineScriptKind::Json => "json",
            InlineScriptKind::Text => "text",
        };
        units.push(Unit {
            kind: kind.into(),
            captured_kind: kind.into(),
            transport_kind: "inline_script".into(),
            raw_path,
            resource_id: parent_id,
            url: object_string(parent, "url").unwrap_or_default(),
            resource: None,
        });
    }

    let mut rows = Vec::<Value>::new();
    let mut groups = BTreeMap::<(String, Option<String>), Vec<JsTask>>::new();
    for unit in units {
        if unit.kind == "incomplete" {
            rows.push(json!({
                "kind": "incomplete", "captured_kind": unit.captured_kind,
                "transport_kind": unit.transport_kind, "raw_path": unit.raw_path,
                "source_path": Value::Null, "resource_id": unit.resource_id, "url": unit.url,
                "transform": "skipped_incomplete_network_response", "formatted": false,
            }));
            continue;
        }
        let source = project.join(&unit.raw_path);
        let dest_rel = src_path(&unit.raw_path);
        let dest = project.join(&dest_rel);
        let mut row = json!({
            "kind": unit.kind, "captured_kind": unit.captured_kind,
            "transport_kind": unit.transport_kind, "raw_path": unit.raw_path,
            "resource_id": unit.resource_id, "url": unit.url, "source_path": dest_rel,
        });
        let row_index = rows.len();
        if unit.kind == "javascript" {
            let digest = sha256_path(&source)?;
            row.as_object_mut()
                .context("source row must be an object")?
                .insert("input_sha256".into(), Value::String(digest.clone()));
            let charset = declared_charset(unit.resource.as_ref());
            groups.entry((digest, charset)).or_default().push(JsTask {
                row_index,
                source,
                dest,
                raw_path: unit.raw_path,
                resource: unit.resource,
            });
        } else {
            let extra = materialize_text(&source, &dest, &unit.kind, unit.resource.as_ref())?;
            row.as_object_mut()
                .context("source row must be an object")?
                .extend(extra);
        }
        rows.push(row);
    }

    for group in groups.values() {
        for task in group {
            match fs::symlink_metadata(&task.dest) {
                Ok(_) => fs::remove_file(&task.dest)
                    .with_context(|| format!("removing {}", task.dest.display()))?,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => {
                    return Err(error)
                        .with_context(|| format!("inspecting {}", task.dest.display()))
                }
            }
        }
    }

    let pool = ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .context("building source-materialization thread pool")?;
    let group_refs = groups.iter().collect::<Vec<_>>();
    let results = pool.install(|| {
        group_refs
            .par_iter()
            .map(|(key, group)| {
                let canonical = group.first().context("empty JavaScript content group")?;
                let result = format_javascript(&canonical.source, canonical.resource.as_ref())?;
                Ok::<_, anyhow::Error>(((*key).clone(), result))
            })
            .collect::<Vec<_>>()
    });
    let results = results
        .into_iter()
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .collect::<BTreeMap<_, _>>();

    for (key, group) in &groups {
        let result = results
            .get(key)
            .context("missing JavaScript group result")?;
        let canonical = group.first().context("empty JavaScript content group")?;
        if let Some(parent) = canonical.dest.parent() {
            fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
        }
        fs::write(&canonical.dest, &result.output)
            .with_context(|| format!("writing {}", canonical.dest.display()))?;
        let (digest, charset_hint) = key;
        for (occurrence, task) in group.iter().enumerate() {
            let row = rows
                .get_mut(task.row_index)
                .and_then(Value::as_object_mut)
                .context("source row missing")?;
            row.insert("transform".into(), Value::String(result.transform.into()));
            row.insert("formatted".into(), Value::Bool(result.formatted));
            row.insert(
                "source_encoding".into(),
                Value::String(result.source_encoding.clone()),
            );
            row.insert(
                "encoding_fallback".into(),
                Value::Bool(result.encoding_fallback),
            );
            row.insert(
                "declared_charset".into(),
                charset_hint.clone().map_or(Value::Null, Value::String),
            );
            row.insert("content_sha256".into(), Value::String(digest.clone()));
            row.insert("content_group_size".into(), Value::from(group.len()));
            row.insert("deduplicated".into(), Value::Bool(occurrence > 0));
            row.insert(
                "deduplicated_from".into(),
                if occurrence > 0 {
                    Value::String(canonical.raw_path.clone())
                } else {
                    Value::Null
                },
            );
            if let Some(error) = &result.format_error {
                row.insert("format_error".into(), Value::String(error.clone()));
                row.insert("kind".into(), Value::String("javascript_unparsed".into()));
            }
            if occurrence == 0 {
                row.insert("materialization".into(), Value::String("canonical".into()));
            } else {
                let materialization = link_or_copy(&canonical.dest, &task.dest)?;
                row.insert(
                    "materialization".into(),
                    Value::String(materialization_name(materialization).into()),
                );
            }
        }
    }

    let js_units = rows
        .iter()
        .filter(|row| row.get("kind").and_then(Value::as_str) == Some("javascript"))
        .count();
    let unparsed_js_units = rows
        .iter()
        .filter(|row| row.get("kind").and_then(Value::as_str) == Some("javascript_unparsed"))
        .count();
    let captured_js_units = js_units + unparsed_js_units;
    let unique_js_inputs = rows
        .iter()
        .filter(|row| {
            row.get("kind").and_then(Value::as_str) == Some("javascript")
                && row.get("materialization").and_then(Value::as_str) == Some("canonical")
        })
        .count();
    let incomplete_units = rows
        .iter()
        .filter(|row| row.get("kind").and_then(Value::as_str) == Some("incomplete"))
        .count();
    let summary = json!({
        "units": rows.len(), "javascript_units": js_units, "captured_javascript_units": captured_js_units,
        "unparsed_javascript_units": unparsed_js_units, "unique_javascript_inputs": unique_js_inputs,
        "captured_unique_javascript_inputs": groups.len(),
        "deduplicated_javascript_units": js_units.saturating_sub(unique_js_inputs),
        "incomplete_network_units": incomplete_units, "formatter_jobs": jobs,
    });
    let document = json!({"schema": SOURCE_INDEX.schema, "units": rows, "summary": summary});
    write_artifact(project, SOURCE_INDEX, &document)?;
    Ok(SourceMaterializeSummary {
        units: document["units"].as_array().map_or(0, Vec::len),
        javascript_units: js_units,
        unique_javascript_inputs: unique_js_inputs,
        incomplete_units,
        jobs,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capture_project::{validate_manifest_value, write_manifest};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn test_project() -> Result<PathBuf> {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let path =
            std::env::temp_dir().join(format!("source-materialize-{}-{nonce}", std::process::id()));
        fs::create_dir_all(path.join("resources"))?;
        Ok(path)
    }

    #[test]
    fn materializes_sparse_ids_deduplicates_and_normalizes_text() -> Result<()> {
        let project = test_project()?;
        let result = (|| -> Result<()> {
            fs::write(project.join("resources/a.js"), "const x = 1;\n")?;
            fs::write(project.join("resources/b.js"), "const x = 1;\n")?;
            fs::write(
                project.join("resources/legacy.js"),
                b"// Copyright \xa9 2012\nconst y = 2;\n",
            )?;
            fs::write(project.join("resources/bad.js"), "const = ;\n")?;
            fs::write(
                project.join("resources/latin1.js"),
                b"const marker = '\x81';\n",
            )?;
            fs::write(
                project.join("resources/data.json"),
                ")]}'\n{\"payload\":{\"value\":42}}",
            )?;
            fs::write(
                project.join("resources/inline.json"),
                "{\"hello\":\"world\"}",
            )?;
            let raw = json!({
                "schema": "capture-project/v1",
                "source": {"kind": "synthetic", "input": "test", "salvaged": false},
                "pages": [],
                "resources": [
                    {"id": 42, "kind": "javascript", "url": "https://x/a.js", "output_path": "resources/a.js"},
                    {"id": 7, "kind": "javascript", "url": "https://x/b.js", "output_path": "resources/b.js"},
                    {"id": 90, "kind": "javascript", "url": "https://x/legacy.js", "output_path": "resources/legacy.js", "mime_type": "text/javascript; charset=iso-8859-1"},
                    {"id": 91, "kind": "javascript", "url": "https://x/bad.js", "output_path": "resources/bad.js"},
                    {"id": 92, "kind": "javascript", "url": "https://x/latin1.js", "output_path": "resources/latin1.js"},
                    {"id": 5, "kind": "json", "url": "https://x/data", "output_path": "resources/data.json"},
                    {"id": 99, "kind": "javascript", "url": "https://x/incomplete.js", "output_path": "resources/missing.js", "body_complete": false}
                ],
                "inline_scripts": [{"parent_resource_id": 42, "output_path": "resources/inline.json", "script_type": "application/json"}],
                "counts": {}
            });
            let manifest = validate_manifest_value(&raw, "test")?;
            write_manifest(&project.join("capture-manifest.json"), &manifest)?;
            let summary = materialize_capture_source(&project, Some(2))?;
            assert_eq!(summary.incomplete_units, 1);
            let index: Value = serde_json::from_str(&fs::read_to_string(
                project.join("analysis/source-index.json"),
            )?)?;
            let rows = index
                .get("units")
                .and_then(Value::as_array)
                .context("units missing")?;
            assert_eq!(index["summary"]["captured_unique_javascript_inputs"], 4);
            assert_eq!(index["summary"]["deduplicated_javascript_units"], 1);
            let legacy = rows
                .iter()
                .find(|row| row["resource_id"] == 90)
                .context("legacy row missing")?;
            assert_eq!(legacy["source_encoding"], "cp1252");
            assert!(fs::read_to_string(
                project.join(
                    legacy["source_path"]
                        .as_str()
                        .context("legacy source path missing")?
                )
            )?
            .contains('©'));
            let xssi = rows
                .iter()
                .find(|row| row["resource_id"] == 5)
                .context("json row missing")?;
            assert_eq!(xssi["transform"], "json_xssi_unwrapped");
            let inline = rows
                .iter()
                .find(|row| row["raw_path"] == "resources/inline.json")
                .context("inline row missing")?;
            assert_eq!(inline["kind"], "json");
            assert_eq!(inline["resource_id"], 42);
            let latin1 = rows
                .iter()
                .find(|row| row["resource_id"] == 92)
                .context("latin1 row missing")?;
            assert_eq!(latin1["source_encoding"], "latin1");
            let bad = rows
                .iter()
                .find(|row| row["resource_id"] == 91)
                .context("bad row missing")?;
            assert_eq!(bad["kind"], "javascript_unparsed");
            assert!(bad.get("format_error").is_some());
            let duplicate = rows
                .iter()
                .find(|row| row["resource_id"] == 7)
                .context("duplicate row missing")?;
            assert_eq!(duplicate["deduplicated"], true);
            assert!(matches!(
                duplicate["materialization"].as_str(),
                Some("hardlink" | "copy")
            ));
            Ok(())
        })();
        let cleanup = fs::remove_dir_all(&project);
        result?;
        cleanup?;
        Ok(())
    }
}
