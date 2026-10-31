use crate::{
    analysis_artifacts::{write_artifact, SOURCEMAPS},
    capture_project::load_manifest,
    sha256_hex,
    source_directive::source_directives,
};
use anyhow::{bail, Context, Result};
use base64::{engine::general_purpose::STANDARD, Engine as _};
use rolldown_redox::sourcemap::{compose_sourcemap_source, OwnedSourceMap};
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};
use url::Url;

const MAX_CHAIN_DEPTH: usize = 16;
const MAX_SOURCE_MAP_BYTES: usize = 64 * 1024 * 1024;
const MAX_SOURCE_MAP_BYTES_U64: u64 = 64 * 1024 * 1024;

#[derive(Debug, Clone)]
struct LoadedMap {
    document: Value,
    raw_bytes: Vec<u8>,
    map_url: Option<String>,
    map_resource_id: Option<u64>,
    map_origin: &'static str,
    base_url: String,
    identity: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectSourcemapSummary {
    pub referenced: usize,
    pub direct_recovered: usize,
    pub composed_links: usize,
    pub final_recovered: usize,
    pub missing_resources: usize,
}

fn value_text(value: &Value) -> String {
    value
        .as_str()
        .map_or_else(|| value.to_string(), ToOwned::to_owned)
}

fn safe_component(value: &str) -> String {
    let mut out = String::with_capacity(value.len().min(120));
    let mut last_was_underscore = false;
    for character in value.chars() {
        if out.len() >= 120 {
            break;
        }
        if character.is_ascii_alphanumeric() || matches!(character, '.' | '_' | '-') {
            out.push(character);
            last_was_underscore = false;
        } else if !last_was_underscore {
            out.push('_');
            last_was_underscore = true;
        }
    }
    let trimmed = out.trim_matches(['.', '_']);
    if trimmed.is_empty() {
        "_".into()
    } else {
        trimmed.to_owned()
    }
}

fn safe_source_path(raw: &str, ordinal: usize) -> PathBuf {
    let mut components = Vec::new();
    if let Ok(url) = Url::parse(raw) {
        components.push(safe_component(url.scheme()));
        components.push(safe_component(url.host_str().unwrap_or("_")));
        components.extend(
            url.path_segments()
                .into_iter()
                .flatten()
                .filter(|part| !part.is_empty() && !matches!(*part, "." | ".."))
                .map(safe_component),
        );
    } else {
        components.extend(
            raw.split('/')
                .filter(|part| !part.is_empty() && !matches!(*part, "." | ".."))
                .map(safe_component),
        );
    }
    if components.is_empty() {
        components.push(format!("source-{ordinal:04}.js"));
    }
    if components.last().is_some_and(|last| !last.contains('.')) {
        if let Some(last) = components.last_mut() {
            last.push_str(".js");
        }
    }
    components.into_iter().collect()
}

fn hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn percent_decode_bytes(data: &str) -> Vec<u8> {
    let bytes = data.as_bytes();
    let mut output = Vec::with_capacity(bytes.len());
    let mut index = 0usize;
    while index < bytes.len() {
        if bytes[index] == b'%' && index + 2 < bytes.len() {
            if let (Some(high), Some(low)) =
                (hex_value(bytes[index + 1]), hex_value(bytes[index + 2]))
            {
                output.push((high << 4) | low);
                index += 3;
                continue;
            }
        }
        output.push(bytes[index]);
        index += 1;
    }
    output
}

fn parse_data_url(raw: &str) -> Result<Vec<u8>> {
    let Some((header, data)) = raw.split_once(',') else {
        bail!("malformed data URL");
    };
    if data.len() > MAX_SOURCE_MAP_BYTES * 2 {
        bail!("inline source map exceeds size limit");
    }
    let decoded = if header.to_ascii_lowercase().contains(";base64") {
        STANDARD
            .decode(data.as_bytes())
            .context("invalid base64 source map data URL")?
    } else {
        percent_decode_bytes(data)
    };
    if decoded.len() > MAX_SOURCE_MAP_BYTES {
        bail!("inline source map exceeds size limit");
    }
    Ok(decoded)
}

fn join_relative_path(base: &str, reference: &str) -> String {
    let fake = Url::parse("https://logical.invalid/");
    let Ok(fake) = fake else {
        return reference.to_owned();
    };
    let base = fake.join(base).unwrap_or(fake.clone());
    let joined = base.join(reference).unwrap_or(base);
    let mut output = joined.path().to_owned();
    if let Some(query) = joined.query() {
        output.push('?');
        output.push_str(query);
    }
    if let Some(fragment) = joined.fragment() {
        output.push('#');
        output.push_str(fragment);
    }
    output
}

fn join_logical(base: &str, reference: &str) -> String {
    if Url::parse(reference).is_ok() {
        return reference.to_owned();
    }
    if let Ok(parsed) = Url::parse(base) {
        if matches!(parsed.scheme(), "http" | "https" | "file") {
            return parsed
                .join(reference)
                .map_or_else(|_| reference.to_owned(), |url| url.to_string());
        }
        let prefix = base
            .rsplit_once('/')
            .map_or_else(|| format!("{base}/"), |(prefix, _)| format!("{prefix}/"));
        return format!("{prefix}{reference}");
    }
    join_relative_path(base, reference)
}

fn logical_source_url(base_url: &str, source_root: &str, raw_source: &str) -> String {
    if Url::parse(raw_source).is_ok() {
        return raw_source.to_owned();
    }
    if source_root.is_empty() {
        return join_logical(base_url, raw_source);
    }
    let mut root = join_logical(base_url, source_root);
    if !root.ends_with('/') {
        root.push('/');
    }
    join_logical(&root, raw_source)
}

fn normalize_map_document(loaded: &LoadedMap) -> Result<Value> {
    let Some(source) = loaded.document.as_object() else {
        bail!("source map root is not an object");
    };
    let mut document = source.clone();
    let source_root = document
        .get("sourceRoot")
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_owned();
    let sources = document
        .get("sources")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default()
        .into_iter()
        .map(|source| {
            Value::String(logical_source_url(
                &loaded.base_url,
                &source_root,
                &value_text(&source),
            ))
        })
        .collect();
    document.insert("sources".into(), Value::Array(sources));
    document.remove("sourceRoot");
    Ok(Value::Object(document))
}

fn resource_id(resource: &Value) -> Option<u64> {
    resource.get("id").and_then(Value::as_u64)
}

fn resource_output_path(resource: &Value) -> Option<&str> {
    resource.get("output_path").and_then(Value::as_str)
}

fn problem(
    status: &str,
    fields: impl IntoIterator<Item = (&'static str, Value)>,
) -> Map<String, Value> {
    let mut object = Map::new();
    object.insert("status".into(), Value::String(status.into()));
    for (name, value) in fields {
        object.insert(name.into(), value);
    }
    object
}

fn load_map(
    raw_reference: &str,
    code_url: &str,
    by_url: &BTreeMap<String, Value>,
    project: &Path,
) -> std::result::Result<LoadedMap, Map<String, Value>> {
    let (bytes, map_url, map_resource_id, map_origin, base_url) =
        if raw_reference.starts_with("data:") {
            let bytes = parse_data_url(raw_reference).map_err(|error| {
                problem(
                    "decode_error",
                    [("error", Value::String(error.to_string()))],
                )
            })?;
            (bytes, None, None, "inline_data_url", code_url.to_owned())
        } else {
            let map_url = join_logical(code_url, raw_reference);
            let Some(linked) = by_url.get(&map_url) else {
                return Err(problem(
                    "missing_map_resource",
                    [("map_url", Value::String(map_url))],
                ));
            };
            let map_resource_id = resource_id(linked);
            let Some(output_path) = resource_output_path(linked) else {
                return Err(problem(
                    "missing_map_resource",
                    [("map_url", Value::String(map_url))],
                ));
            };
            let path = project.join(output_path);
            let metadata = fs::metadata(&path).map_err(|error| {
                problem(
                    "map_read_error",
                    [
                        ("map_url", Value::String(map_url.clone())),
                        (
                            "map_resource_id",
                            map_resource_id.map_or(Value::Null, Value::from),
                        ),
                        ("error", Value::String(error.to_string())),
                    ],
                )
            })?;
            if metadata.len() > MAX_SOURCE_MAP_BYTES_U64 {
                return Err(problem(
                    "map_too_large",
                    [
                        ("map_url", Value::String(map_url)),
                        (
                            "map_resource_id",
                            map_resource_id.map_or(Value::Null, Value::from),
                        ),
                    ],
                ));
            }
            let bytes = fs::read(&path).map_err(|error| {
                problem(
                    "map_read_error",
                    [
                        ("map_url", Value::String(map_url.clone())),
                        (
                            "map_resource_id",
                            map_resource_id.map_or(Value::Null, Value::from),
                        ),
                        ("error", Value::String(error.to_string())),
                    ],
                )
            })?;
            (
                bytes,
                Some(map_url.clone()),
                map_resource_id,
                "har_resource",
                map_url,
            )
        };

    let document = serde_json::from_slice::<Value>(&bytes).map_err(|error| {
        problem(
            "invalid_source_map",
            [
                (
                    "map_url",
                    map_url.clone().map_or(Value::Null, Value::String),
                ),
                (
                    "map_resource_id",
                    map_resource_id.map_or(Value::Null, Value::from),
                ),
                ("error", Value::String(error.to_string())),
            ],
        )
    })?;
    if !document.is_object() {
        return Err(problem(
            "invalid_source_map",
            [
                (
                    "map_url",
                    map_url.clone().map_or(Value::Null, Value::String),
                ),
                (
                    "map_resource_id",
                    map_resource_id.map_or(Value::Null, Value::from),
                ),
                (
                    "error",
                    Value::String("source map root is not an object".into()),
                ),
            ],
        ));
    }
    let digest = sha256_hex(&bytes);
    let identity = map_url
        .clone()
        .unwrap_or_else(|| format!("inline:{digest}"));
    Ok(LoadedMap {
        document,
        raw_bytes: bytes,
        map_url,
        map_resource_id,
        map_origin,
        base_url,
        identity,
    })
}

fn last_source_map_directive(source: &str) -> Option<String> {
    source_directives(source)
        .into_iter()
        .filter(|directive| directive.kind == "source_map")
        .map(|directive| directive.raw)
        .last()
}

fn manifest_source_map_reference(resource: &Value) -> Option<String> {
    resource
        .get("references")
        .and_then(Value::as_array)?
        .iter()
        .filter(|reference| reference.get("kind").and_then(Value::as_str) == Some("source_map"))
        .filter_map(|reference| reference.get("raw").and_then(Value::as_str))
        .map(ToOwned::to_owned)
        .last()
}

fn source_code(
    document: &Value,
    ordinal: usize,
    logical_source: &str,
    by_url: &BTreeMap<String, Value>,
    project: &Path,
) -> Option<(String, &'static str, Option<u64>)> {
    if let Some(content) = document
        .get("sourcesContent")
        .and_then(Value::as_array)
        .and_then(|contents| contents.get(ordinal))
        .and_then(Value::as_str)
    {
        return Some((content.to_owned(), "sources_content", None));
    }
    let linked = by_url.get(logical_source)?;
    let output_path = resource_output_path(linked)?;
    let text = fs::read_to_string(project.join(output_path)).ok()?;
    Some((text, "har_resource", resource_id(linked)))
}

pub fn compose_sourcemap_json(
    downstream_json: &str,
    upstream_json: &str,
    source_id: u32,
) -> Result<String> {
    let downstream = OwnedSourceMap::from_json_string(downstream_json)
        .context("parsing downstream source map")?;
    let upstream =
        OwnedSourceMap::from_json_string(upstream_json).context("parsing upstream source map")?;
    Ok(compose_sourcemap_source(
        downstream.as_source_map(),
        source_id,
        upstream.as_source_map(),
    )
    .to_json_string())
}

fn compose_documents(downstream: &Value, upstream: &Value, source_id: usize) -> Result<Value> {
    let source_id = u32::try_from(source_id).context("source-map source ordinal exceeds u32")?;
    let downstream = serde_json::to_string(downstream)?;
    let upstream = serde_json::to_string(upstream)?;
    let composed = compose_sourcemap_json(&downstream, &upstream, source_id)?;
    serde_json::from_str(&composed).context("parsing composed source map")
}

fn insert_problem(row: &mut Map<String, Value>, values: Map<String, Value>) {
    row.extend(values);
}

fn expand_map(
    loaded: &LoadedMap,
    by_url: &BTreeMap<String, Value>,
    project: &Path,
    stack: &BTreeSet<String>,
    depth: usize,
) -> Result<(Value, Vec<Value>, usize)> {
    let normalized = normalize_map_document(loaded)?;
    let sources = normalized
        .get("sources")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut composed = normalized.clone();
    let mut links = Vec::new();
    let mut compositions = 0usize;
    if depth >= MAX_CHAIN_DEPTH {
        return Ok((composed, links, compositions));
    }

    for ordinal in (0..sources.len()).rev() {
        let logical_source = value_text(&sources[ordinal]);
        let Some((code, code_origin, code_resource_id)) =
            source_code(&normalized, ordinal, &logical_source, by_url, project)
        else {
            continue;
        };
        let Some(raw_reference) = last_source_map_directive(&code) else {
            continue;
        };
        let mut row = Map::new();
        row.insert("depth".into(), Value::from(depth + 1));
        row.insert("source_ordinal".into(), Value::from(ordinal));
        row.insert(
            "logical_source".into(),
            Value::String(logical_source.clone()),
        );
        row.insert("code_origin".into(), Value::String(code_origin.into()));
        row.insert(
            "code_resource_id".into(),
            code_resource_id.map_or(Value::Null, Value::from),
        );
        row.insert("raw_reference".into(), Value::String(raw_reference.clone()));

        let upstream = match load_map(&raw_reference, &logical_source, by_url, project) {
            Ok(upstream) => upstream,
            Err(values) => {
                insert_problem(&mut row, values);
                links.push(Value::Object(row));
                continue;
            }
        };
        row.insert(
            "map_url".into(),
            upstream.map_url.clone().map_or(Value::Null, Value::String),
        );
        row.insert(
            "map_resource_id".into(),
            upstream.map_resource_id.map_or(Value::Null, Value::from),
        );
        row.insert(
            "map_origin".into(),
            Value::String(upstream.map_origin.into()),
        );
        if stack.contains(&upstream.identity) {
            row.insert("status".into(), Value::String("cycle".into()));
            links.push(Value::Object(row));
            continue;
        }

        let mut nested_stack = stack.clone();
        nested_stack.insert(upstream.identity.clone());
        let (expanded_upstream, nested_links, nested_compositions) =
            expand_map(&upstream, by_url, project, &nested_stack, depth + 1)?;
        let upstream_sources = expanded_upstream
            .get("sources")
            .and_then(Value::as_array)
            .map_or(0, Vec::len);
        row.insert("upstream_sources".into(), Value::from(upstream_sources));
        match compose_documents(&composed, &expanded_upstream, ordinal) {
            Ok(next) => {
                composed = next;
                row.insert("status".into(), Value::String("composed".into()));
                compositions += 1 + nested_compositions;
            }
            Err(error) => {
                row.insert("status".into(), Value::String("compose_error".into()));
                row.insert("error".into(), Value::String(error.to_string()));
            }
        }
        links.push(Value::Object(row));
        links.extend(nested_links);
    }
    Ok((composed, links, compositions))
}

fn materialize_sources(document: &Value, root: &Path, project: &Path) -> Result<Vec<Value>> {
    let sources = document
        .get("sources")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let contents = document
        .get("sourcesContent")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let mut recovered = Vec::with_capacity(sources.len());
    for (ordinal, source) in sources.iter().enumerate() {
        let source_text = value_text(source);
        let content = contents.get(ordinal).filter(|content| !content.is_null());
        let Some(content) = content else {
            recovered.push(json!({
                "ordinal": ordinal,
                "source": source,
                "logical_source": source,
                "status": "no_sources_content",
            }));
            continue;
        };
        let relative = safe_source_path(&source_text, ordinal);
        let destination = root.join(&relative);
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent)?;
        }
        let encoded = if let Some(text) = content.as_str() {
            text.to_owned()
        } else {
            let mut text = serde_json::to_string_pretty(content)?;
            text.push('\n');
            text
        };
        fs::write(&destination, encoded.as_bytes())?;
        let source_path = destination
            .strip_prefix(project)
            .with_context(|| {
                format!(
                    "recovered source outside project: {}",
                    destination.display()
                )
            })?
            .to_string_lossy()
            .into_owned();
        recovered.push(json!({
            "ordinal": ordinal,
            "source": source,
            "logical_source": source,
            "status": "recovered",
            "bytes": encoded.len(),
            "source_path": source_path,
        }));
    }
    Ok(recovered)
}

fn recovered_count(rows: &[Value]) -> usize {
    rows.iter()
        .filter(|row| row.get("status").and_then(Value::as_str) == Some("recovered"))
        .count()
}

pub fn recover_project_sourcemaps(project: &Path) -> Result<ProjectSourcemapSummary> {
    let project = project
        .canonicalize()
        .with_context(|| format!("resolving project {}", project.display()))?;
    let manifest = load_manifest(&project)?;
    let mut by_url = BTreeMap::new();
    for resource in &manifest.resources {
        if let Some(url) = resource.get("url").and_then(Value::as_str) {
            by_url.insert(url.to_owned(), resource.clone());
        }
    }

    let mut results = Vec::new();
    for resource in &manifest.resources {
        if resource.get("kind").and_then(Value::as_str) != Some("javascript") {
            continue;
        }
        let Some(raw_reference) = manifest_source_map_reference(resource) else {
            continue;
        };
        let Some(code_url) = resource.get("url").and_then(Value::as_str) else {
            continue;
        };
        let Some(resource_id) = resource_id(resource) else {
            continue;
        };
        let loaded = match load_map(&raw_reference, code_url, &by_url, &project) {
            Ok(loaded) => loaded,
            Err(values) => {
                let mut row = Map::new();
                row.insert("resource_id".into(), Value::from(resource_id));
                row.insert("url".into(), Value::String(code_url.into()));
                row.insert("raw_reference".into(), Value::String(raw_reference));
                row.extend(values);
                results.push(Value::Object(row));
                continue;
            }
        };

        let direct_document = normalize_map_document(&loaded)?;
        let digest = &sha256_hex(&loaded.raw_bytes)[..12];
        let source_root = project
            .join("src/_sourcemap")
            .join(format!("{resource_id:04}-{digest}"));
        let recovered = materialize_sources(&direct_document, &source_root, &project)?;
        let mut stack = BTreeSet::new();
        stack.insert(loaded.identity.clone());
        let (composed, links, compositions) = expand_map(&loaded, &by_url, &project, &stack, 0)?;

        let mut composed_recovered = Vec::new();
        let mut composed_map_path = Value::Null;
        if compositions > 0 {
            let composed_root = project.join("analysis/sourcemap-composed");
            fs::create_dir_all(&composed_root)?;
            let map_destination = composed_root.join(format!("{resource_id:04}-{digest}.map"));
            let mut encoded = serde_json::to_string(&composed)?;
            encoded.push('\n');
            fs::write(&map_destination, encoded)?;
            composed_map_path = Value::String(
                map_destination
                    .strip_prefix(&project)?
                    .to_string_lossy()
                    .into_owned(),
            );
            composed_recovered =
                materialize_sources(&composed, &source_root.join("final"), &project)?;
        }
        let composition_status = if links.is_empty() {
            "not_needed"
        } else if links
            .iter()
            .all(|link| link.get("status").and_then(Value::as_str) == Some("composed"))
        {
            "composed"
        } else {
            "partial"
        };
        let source_root_value = loaded
            .document
            .get("sourceRoot")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let direct_sources = direct_document
            .get("sources")
            .and_then(Value::as_array)
            .map_or(0, Vec::len);
        let direct_contents = direct_document
            .get("sourcesContent")
            .and_then(Value::as_array)
            .map_or(0, |contents| {
                contents.iter().filter(|value| !value.is_null()).count()
            });
        let composed_sources = composed
            .get("sources")
            .and_then(Value::as_array)
            .map_or(0, Vec::len);
        let composed_contents = composed
            .get("sourcesContent")
            .and_then(Value::as_array)
            .map_or(0, |contents| {
                contents.iter().filter(|value| !value.is_null()).count()
            });
        let status = if recovered_count(&recovered) > 0 {
            "recovered"
        } else {
            "no_sources_content"
        };
        results.push(json!({
            "resource_id": resource_id,
            "url": code_url,
            "raw_reference": raw_reference,
            "map_url": loaded.map_url,
            "map_resource_id": loaded.map_resource_id,
            "map_origin": loaded.map_origin,
            "source_root": source_root_value,
            "sources": direct_sources,
            "sources_content": direct_contents,
            "recovered": recovered,
            "composition": {
                "status": composition_status,
                "links": links,
                "composed_links": compositions,
                "composed_sources": composed_sources,
                "composed_sources_content": composed_contents,
                "composed_map_path": composed_map_path,
            },
            "composed_recovered": composed_recovered,
            "status": status,
        }));
    }

    let direct_recovered = results
        .iter()
        .filter_map(|map| map.get("recovered").and_then(Value::as_array))
        .map(|rows| recovered_count(rows))
        .sum();
    let final_recovered = results
        .iter()
        .filter_map(|map| map.get("composed_recovered").and_then(Value::as_array))
        .map(|rows| recovered_count(rows))
        .sum();
    let composed_links = results
        .iter()
        .filter_map(|map| map.get("composition"))
        .filter_map(|composition| composition.get("composed_links"))
        .filter_map(Value::as_u64)
        .filter_map(|count| usize::try_from(count).ok())
        .sum();
    let missing_resources = results
        .iter()
        .filter(|map| map.get("status").and_then(Value::as_str) == Some("missing_map_resource"))
        .count();
    let document = json!({
        "schema": SOURCEMAPS.schema,
        "source_maps": results,
    });
    write_artifact(&project, SOURCEMAPS, &document)?;
    Ok(ProjectSourcemapSummary {
        referenced: document["source_maps"].as_array().map_or(0, Vec::len),
        direct_recovered,
        composed_links,
        final_recovered,
        missing_resources,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn data_urls_are_bounded_and_percent_decoded_without_form_semantics() -> Result<()> {
        assert_eq!(
            parse_data_url("data:application/json,%7B%22x%22%3A1%7D")?,
            br#"{"x":1}"#
        );
        assert_eq!(parse_data_url("data:text/plain,a+b")?, b"a+b");
        Ok(())
    }

    #[test]
    fn safe_source_paths_drop_parent_components() {
        assert_eq!(
            safe_source_path("../src/../app-original.ts", 0),
            PathBuf::from("src/app-original.ts")
        );
        assert_eq!(
            safe_source_path("https://example.test/a/b", 1),
            PathBuf::from("https/example.test/a/b.js")
        );
    }

    #[test]
    fn logical_urls_resolve_nested_http_sources() {
        assert_eq!(
            logical_source_url(
                "https://fixture.invalid/assets/app.js.map",
                "src",
                "../original/app.ts",
            ),
            "https://fixture.invalid/assets/original/app.ts"
        );
    }
}
