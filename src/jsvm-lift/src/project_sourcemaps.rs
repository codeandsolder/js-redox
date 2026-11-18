use crate::{
    analysis_artifacts::{write_artifact, SOURCEMAPS},
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
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
    io::Read,
    path::{Path, PathBuf},
};
use url::Url;
use work_budget::{BudgetExceeded, WorkBudget};

const MAX_CHAIN_DEPTH: usize = 16;
const MAX_SOURCE_MAP_BYTES: usize = 64 * 1024 * 1024;
const MAX_SOURCE_MAP_BYTES_U64: u64 = 64 * 1024 * 1024;

#[derive(Debug, Clone)]
struct LoadedMap {
    document: Value,
    raw_bytes: Vec<u8>,
    map_url: Option<String>,
    map_resource_id: Option<u64>,
    map_resource_ids: Vec<u64>,
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

const fn hex_value(byte: u8) -> Option<u8> {
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
    let base = fake.join(base).unwrap_or(fake);
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

type CapturedByUrl = BTreeMap<String, Vec<Value>>;
#[derive(Debug)]
enum CapturedLookupError {
    Resource(Map<String, Value>),
    Budget(BudgetExceeded),
}

impl From<Map<String, Value>> for CapturedLookupError {
    fn from(problem: Map<String, Value>) -> Self {
        Self::Resource(problem)
    }
}

impl From<BudgetExceeded> for CapturedLookupError {
    fn from(error: BudgetExceeded) -> Self {
        Self::Budget(error)
    }
}

// Capture metadata failures are evidence; exhausted budgets abort analysis.
type CapturedLookup<T> = std::result::Result<Option<T>, CapturedLookupError>;

/// A URL can denote multiple HTTP responses. Only common, verified bytes
/// justify parsing the body; they never establish a unique response identity.
fn captured_bytes_for_url(
    url: &str,
    by_url: &CapturedByUrl,
    project: &Path,
    budget: &WorkBudget,
) -> CapturedLookup<(Vec<u8>, Vec<u64>)> {
    let Some(candidates) = by_url.get(url) else {
        return Ok(None);
    };
    let ids = candidates
        .iter()
        .filter_map(resource_id)
        .collect::<Vec<_>>();
    let mut reference = None::<Vec<u8>>;
    let mut hashes = BTreeSet::new();
    // Captures can share a physical output path. Hash it once while validating
    // every HTTP record's claimed digest independently. Retain only one body:
    // caching all candidates could consume N * 64 MiB for a single URL.
    let mut path_hashes = BTreeMap::<PathBuf, String>::new();
    for candidate in candidates {
        budget.consume(1)?;
        let Some(path) = resource_output_path(candidate) else {
            return Err(problem(
                "unavailable_captured_resource",
                [("url", json!(url)), ("candidate_resource_ids", json!(ids))],
            )
            .into());
        };
        let file = project.join(path);
        let digest = if let Some(digest) = path_hashes.get(&file) {
            digest.clone()
        } else {
            let read_error = |error: std::io::Error| {
                problem(
                    "captured_resource_read_error",
                    [
                        ("url", json!(url)),
                        ("candidate_resource_ids", json!(ids)),
                        ("error", json!(error.to_string())),
                    ],
                )
            };
            let file_handle = fs::File::open(&file).map_err(read_error)?;
            if file_handle.metadata().map_err(read_error)?.len() > MAX_SOURCE_MAP_BYTES_U64 {
                return Err(problem(
                    "captured_resource_too_large",
                    [("url", json!(url)), ("candidate_resource_ids", json!(ids))],
                )
                .into());
            }
            // A capture file may grow after stat: bound the actual read too.
            let mut bytes = Vec::new();
            file_handle
                .take(MAX_SOURCE_MAP_BYTES_U64 + 1)
                .read_to_end(&mut bytes)
                .map_err(read_error)?;
            if bytes.len() > MAX_SOURCE_MAP_BYTES {
                return Err(problem(
                    "captured_resource_too_large",
                    [("url", json!(url)), ("candidate_resource_ids", json!(ids))],
                )
                .into());
            }
            let digest = sha256_hex(&bytes);
            path_hashes.insert(file, digest.clone());
            if reference.is_none() {
                reference = Some(bytes);
            }
            digest
        };
        if candidate
            .get("sha256")
            .and_then(Value::as_str)
            .is_some_and(|sha| sha != digest)
        {
            return Err(problem(
                "captured_resource_sha_mismatch",
                [
                    ("url", json!(url)),
                    ("candidate_resource_ids", json!(ids)),
                    ("resource_id", json!(resource_id(candidate))),
                    ("actual_sha256", json!(digest)),
                ],
            )
            .into());
        }
        hashes.insert(digest);
    }
    if hashes.len() > 1 {
        return Err(problem(
            "ambiguous_captured_resource",
            [
                ("url", json!(url)),
                ("candidate_resource_ids", json!(ids)),
                ("candidate_sha256s", json!(hashes)),
            ],
        )
        .into());
    }
    Ok(reference.map(|bytes| (bytes, ids)))
}

fn load_map(
    raw_reference: &str,
    code_url: &str,
    by_url: &CapturedByUrl,
    project: &Path,
    budget: &WorkBudget,
) -> std::result::Result<LoadedMap, CapturedLookupError> {
    let (bytes, map_url, map_resource_id, map_resource_ids, map_origin, base_url) = if raw_reference
        .starts_with("data:")
    {
        let bytes = parse_data_url(raw_reference).map_err(|error| {
            problem(
                "decode_error",
                [("error", Value::String(error.to_string()))],
            )
        })?;
        (
            bytes,
            None,
            None,
            Vec::new(),
            "inline_data_url",
            code_url.to_owned(),
        )
    } else {
        let map_url = join_logical(code_url, raw_reference);
        let resolved = captured_bytes_for_url(&map_url, by_url, project, budget).map_err(
            |error| match error {
                CapturedLookupError::Resource(mut fields) => {
                    fields.insert("map_url".into(), json!(map_url));
                    fields.remove("url");
                    CapturedLookupError::Resource(fields)
                }
                error => error,
            },
        )?;
        let Some((bytes, resource_ids)) = resolved else {
            return Err(problem("missing_map_resource", [("map_url", json!(map_url))]).into());
        };
        let id = (resource_ids.len() == 1).then(|| resource_ids[0]);
        let origin = if id.is_some() {
            "har_resource"
        } else {
            "har_shared_bytes"
        };
        (
            bytes,
            Some(map_url.clone()),
            id,
            resource_ids,
            origin,
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
                ("map_url", map_url.map_or(Value::Null, Value::String)),
                (
                    "map_resource_id",
                    map_resource_id.map_or(Value::Null, Value::from),
                ),
                (
                    "error",
                    Value::String("source map root is not an object".into()),
                ),
            ],
        )
        .into());
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
        map_resource_ids,
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
        .next_back()
}

fn manifest_source_map_reference(resource: &Value) -> Option<String> {
    resource
        .get("references")
        .and_then(Value::as_array)?
        .iter()
        .filter(|reference| reference.get("kind").and_then(Value::as_str) == Some("source_map"))
        .filter_map(|reference| reference.get("raw").and_then(Value::as_str))
        .map(ToOwned::to_owned)
        .next_back()
}

fn source_code(
    document: &Value,
    ordinal: usize,
    logical_source: &str,
    by_url: &CapturedByUrl,
    project: &Path,
    budget: &WorkBudget,
) -> CapturedLookup<(String, &'static str, Option<u64>, Vec<u64>)> {
    if let Some(content) = document
        .get("sourcesContent")
        .and_then(Value::as_array)
        .and_then(|contents| contents.get(ordinal))
        .and_then(Value::as_str)
    {
        return Ok(Some((
            content.to_owned(),
            "sources_content",
            None,
            Vec::new(),
        )));
    }
    let Some((bytes, ids)) = captured_bytes_for_url(logical_source, by_url, project, budget)?
    else {
        return Ok(None);
    };
    let code = String::from_utf8(bytes).map_err(|error| {
        problem(
            "captured_source_encoding_error",
            [
                ("url", json!(logical_source)),
                ("candidate_resource_ids", json!(ids)),
                ("error", json!(error.to_string())),
            ],
        )
    })?;
    let resource = (ids.len() == 1).then(|| ids[0]);
    Ok(Some((code, "har_resource", resource, ids)))
}

/// Compose two parsed source maps at the specified downstream source ordinal.
///
/// # Errors
///
/// Fails if either input is not a valid source map or the work budget is exhausted during
/// parsing or composition.
pub fn compose_sourcemap_json(
    downstream_json: &str,
    upstream_json: &str,
    source_id: u32,
    budget: &WorkBudget,
) -> Result<String> {
    budget.checkpoint()?;
    let downstream = OwnedSourceMap::from_json_string(downstream_json)
        .context("parsing downstream source map")?;
    let upstream =
        OwnedSourceMap::from_json_string(upstream_json).context("parsing upstream source map")?;
    budget.checkpoint()?;
    let composed = compose_sourcemap_source(
        downstream.as_source_map(),
        source_id,
        upstream.as_source_map(),
    )
    .to_json_string();
    budget.checkpoint()?;
    Ok(composed)
}

fn compose_documents(
    downstream: &Value,
    upstream: &Value,
    source_id: usize,
    budget: &WorkBudget,
) -> Result<Value> {
    let source_id = u32::try_from(source_id).context("source-map source ordinal exceeds u32")?;
    let downstream = serde_json::to_string(downstream)?;
    let upstream = serde_json::to_string(upstream)?;
    let composed = compose_sourcemap_json(&downstream, &upstream, source_id, budget)?;
    serde_json::from_str(&composed).context("parsing composed source map")
}

fn insert_problem(row: &mut Map<String, Value>, values: Map<String, Value>) {
    row.extend(values);
}

fn expand_map(
    loaded: &LoadedMap,
    by_url: &CapturedByUrl,
    project: &Path,
    stack: &BTreeSet<String>,
    depth: usize,
    budget: &WorkBudget,
) -> Result<(Value, Vec<Value>, usize)> {
    budget.checkpoint()?;
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
        budget.checkpoint()?;
        let logical_source = value_text(&sources[ordinal]);
        let (code, code_origin, code_resource_id, code_resource_ids) = match source_code(
            &normalized,
            ordinal,
            &logical_source,
            by_url,
            project,
            budget,
        ) {
            Ok(Some(source)) => source,
            Ok(None) => continue,
            Err(CapturedLookupError::Budget(error)) => return Err(error.into()),
            Err(CapturedLookupError::Resource(mut values)) => {
                let mut row = Map::new();
                row.insert("depth".into(), json!(depth + 1));
                row.insert("source_ordinal".into(), json!(ordinal));
                row.insert("logical_source".into(), json!(logical_source));
                row.insert("code_url".into(), json!(logical_source));
                if let Some(ids) = values.remove("candidate_resource_ids") {
                    values.insert("candidate_code_resource_ids".into(), ids);
                }
                insert_problem(&mut row, values);
                links.push(Value::Object(row));
                continue;
            }
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
        row.insert("code_resource_ids".into(), json!(code_resource_ids));
        row.insert("raw_reference".into(), Value::String(raw_reference.clone()));

        let upstream = match load_map(&raw_reference, &logical_source, by_url, project, budget) {
            Ok(upstream) => upstream,
            Err(CapturedLookupError::Budget(error)) => return Err(error.into()),
            Err(CapturedLookupError::Resource(values)) => {
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
        row.insert("map_resource_ids".into(), json!(upstream.map_resource_ids));
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
            expand_map(&upstream, by_url, project, &nested_stack, depth + 1, budget)?;
        let upstream_sources = expanded_upstream
            .get("sources")
            .and_then(Value::as_array)
            .map_or(0, Vec::len);
        row.insert("upstream_sources".into(), Value::from(upstream_sources));
        match compose_documents(&composed, &expanded_upstream, ordinal, budget) {
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

fn materialize_sources(
    document: &Value,
    root: &Path,
    project: &Path,
    budget: &WorkBudget,
) -> Result<Vec<Value>> {
    budget.checkpoint()?;
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
        budget.checkpoint()?;
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

/// Recover and compose chained source maps for the capture project.
///
/// # Errors
///
/// Fails when the project cannot be resolved, its manifest/maps cannot be read or parsed,
/// source-map composition or serialization fails, output files cannot be written, or the
/// analysis budget is exhausted.
pub fn recover_project_sourcemaps(
    project: &Path,
    budgets: &AnalysisBudgets,
) -> Result<ProjectSourcemapSummary> {
    let project = project
        .canonicalize()
        .with_context(|| format!("resolving project {}", project.display()))?;
    let stage_budget = budgets.operation(
        AnalysisOperation::SourcemapRecovery,
        project.display().to_string(),
    );
    stage_budget.checkpoint()?;
    let manifest = load_manifest(&project)?;
    let mut by_url = CapturedByUrl::new();
    for resource in &manifest.resources {
        if let Some(url) = resource.get("url").and_then(Value::as_str) {
            by_url
                .entry(url.to_owned())
                .or_default()
                .push(resource.clone());
        }
    }

    let mut results = Vec::new();
    for resource in &manifest.resources {
        stage_budget.checkpoint()?;
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
        let budget = budgets.operation_under(
            &stage_budget,
            AnalysisOperation::SourcemapRecovery,
            format!("{resource_id}:{code_url}"),
        );
        budget.checkpoint()?;
        let loaded = match load_map(&raw_reference, code_url, &by_url, &project, &budget) {
            Ok(loaded) => loaded,
            Err(CapturedLookupError::Budget(error)) => return Err(error.into()),
            Err(CapturedLookupError::Resource(values)) => {
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
        let recovered = materialize_sources(&direct_document, &source_root, &project, &budget)?;
        let mut stack = BTreeSet::new();
        stack.insert(loaded.identity.clone());
        let (composed, links, compositions) =
            expand_map(&loaded, &by_url, &project, &stack, 0, &budget)?;

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
                materialize_sources(&composed, &source_root.join("final"), &project, &budget)?;
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
            "map_resource_ids": loaded.map_resource_ids,
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

    fn shared_map_fixture(project: &Path, second: &str, root_map: &str) -> Result<()> {
        use crate::capture_project::{write_manifest, CaptureManifest, CaptureSource, SCHEMA};
        fs::create_dir_all(project.join("resources"))?;
        let script = "console.log(1);\n//# sourceMappingURL=app.js.map";
        let map_a = root_map;
        for (path, bytes) in [("app.js", script), ("map-a", map_a), ("map-b", second)] {
            fs::write(project.join("resources").join(path), bytes)?;
        }
        let resources = vec![
            json!({
                "id":1,"kind":"javascript","url":"https://fixture.invalid/app.js",
                "output_path":"resources/app.js","sha256":sha256_hex(script.as_bytes()),
                "references":[{"kind":"source_map","raw":"app.js.map"}],
            }),
            json!({
                "id":2,"kind":"other","url":"https://fixture.invalid/app.js.map",
                "output_path":"resources/map-a","sha256":sha256_hex(map_a.as_bytes()),
            }),
            json!({
                "id":3,"kind":"other","url":"https://fixture.invalid/app.js.map",
                "output_path":"resources/map-b","sha256":sha256_hex(second.as_bytes()),
            }),
        ];
        write_manifest(
            &project.join("capture-manifest.json"),
            &CaptureManifest {
                schema: SCHEMA.into(),
                source: CaptureSource {
                    kind: "har".into(),
                    input: "source-map-alias-test".into(),
                    salvaged: false,
                    extra: Map::new(),
                },
                resources,
                pages: Vec::new(),
                inline_scripts: Vec::new(),
                counts: BTreeMap::new(),
                extra: Map::new(),
            },
        )?;
        Ok(())
    }

    fn alias_map_document(content: &str) -> String {
        json!({
            "version":3,"file":"app.js","sources":["original.ts"],
            "sourcesContent":[content],"names":[],"mappings":"",
        })
        .to_string()
    }

    fn read_fixture_artifact(project: &Path, path: &str) -> Result<Value> {
        serde_json::from_slice(&fs::read(project.join(path))?).map_err(Into::into)
    }

    #[test]
    fn duplicate_capture_path_preserves_all_ids_and_checks_each_claim() -> Result<()> {
        let temp = tempfile::tempdir()?;
        fs::create_dir_all(temp.path().join("resources"))?;
        let content = b"shared body";
        fs::write(temp.path().join("resources/shared.js"), content)?;
        let url = "https://fixture.invalid/shared.js";
        let candidate = |id, sha: String| {
            json!({
                "id": id, "output_path": "resources/shared.js", "sha256": sha
            })
        };
        let correct_sha = sha256_hex(content);
        let mut by_url = CapturedByUrl::from([(
            url.to_owned(),
            vec![
                candidate(2, correct_sha.clone()),
                candidate(3, correct_sha.clone()),
                candidate(4, correct_sha.clone()),
            ],
        )]);
        let budget = WorkBudget::new("shared-path-test", work_budget::BudgetLimits::unlimited());
        let Ok(Some((bytes, ids))) = captured_bytes_for_url(url, &by_url, temp.path(), &budget)
        else {
            bail!("shared stored body should resolve");
        };
        assert_eq!(bytes, content);
        assert_eq!(ids, vec![2, 3, 4]);

        // A cached digest must not accidentally bless a second record's
        // incorrect manifest claim for the same file.
        let candidates = by_url.get_mut(url).context("URL not indexed")?;
        candidates[1]["sha256"] = json!("wrong");
        let Err(error) = captured_bytes_for_url(url, &by_url, temp.path(), &budget) else {
            bail!("each captured record must validate its SHA-256");
        };
        let CapturedLookupError::Resource(error) = error else {
            anyhow::bail!("expected a per-capture SHA mismatch");
        };
        assert_eq!(error["status"], "captured_resource_sha_mismatch");
        assert_eq!(error["resource_id"], 3);
        assert_eq!(error["actual_sha256"], correct_sha);
        assert_eq!(error["candidate_resource_ids"], json!([2, 3, 4]));
        Ok(())
    }

    #[test]
    fn oversized_capture_is_rejected_before_reading() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let path = temp.path().join("oversized");
        let file = fs::File::create(&path)?;
        file.set_len(MAX_SOURCE_MAP_BYTES_U64 + 1)?;
        let url = "https://fixture.invalid/map";
        let by_url = CapturedByUrl::from([(
            url.to_owned(),
            vec![json!({"id": 9, "output_path": "oversized"})],
        )]);
        let budget = WorkBudget::new("oversized-test", work_budget::BudgetLimits::unlimited());
        let Err(error) = captured_bytes_for_url(url, &by_url, temp.path(), &budget) else {
            bail!("oversized resource must be rejected");
        };
        let CapturedLookupError::Resource(error) = error else {
            anyhow::bail!("expected a per-capture size failure");
        };
        assert_eq!(error["status"], "captured_resource_too_large");
        assert_eq!(error["candidate_resource_ids"], json!([9]));
        Ok(())
    }

    #[test]
    fn captured_response_candidates_consume_work_budget() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path();
        let map = alias_map_document("export const version = 1;");
        shared_map_fixture(project, &map, &map)?;
        let budgets = AnalysisBudgets::new(
            "capture-candidate-budget-test",
            work_budget::BudgetLimits::work(1),
        );
        let Err(error) = recover_project_sourcemaps(project, &budgets) else {
            bail!("the second matching response must exhaust the budget");
        };
        assert!(work_budget::find_budget_exceeded(error.as_ref()).is_some());
        assert!(!project.join("analysis/sourcemaps.json").exists());
        Ok(())
    }

    #[test]
    fn distinct_captured_responses_at_one_map_url_remain_ambiguous() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path();
        let first = alias_map_document("export const version = 1;");
        let second = alias_map_document("export const version = 2;");
        shared_map_fixture(project, &second, &first)?;
        let budget = AnalysisBudgets::standard("conflicting-source-map-responses");
        let result = recover_project_sourcemaps(project, &budget)?;
        assert_eq!(result.referenced, 1);
        assert_eq!(result.direct_recovered, 0);
        let rows = read_fixture_artifact(project, "analysis/sourcemaps.json")?;
        let source_map = &rows["source_maps"][0];
        assert_eq!(source_map["status"], "ambiguous_captured_resource");
        assert_eq!(source_map["map_url"], "https://fixture.invalid/app.js.map");
        assert_eq!(source_map["candidate_resource_ids"], json!([2, 3]));
        assert_eq!(
            source_map["candidate_sha256s"].as_array().map(Vec::len),
            Some(2)
        );
        crate::source_graph::build_source_graph(project, &budget)?;
        let graph = read_fixture_artifact(project, "analysis/source-graph.json")?;
        let edges = graph["edges"].as_array().context("missing edges")?;
        let candidates = edges
            .iter()
            .filter(|edge| {
                edge["from"] == "sourcemap-reference:1"
                    && edge["kind"] == "source_map_resource_candidate"
            })
            .collect::<Vec<_>>();
        assert_eq!(candidates.len(), 2);
        assert_eq!(
            candidates
                .iter()
                .filter_map(|edge| edge["to"].as_str())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["resource:2", "resource:3"]),
        );
        assert!(edges.iter().all(|edge| edge["kind"] != "source_map_source"));
        Ok(())
    }

    #[test]
    fn same_map_bytes_preserve_candidates_without_selecting_a_parent() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path();
        let map = alias_map_document("export const version = 1;");
        shared_map_fixture(project, &map, &map)?;
        let budget = AnalysisBudgets::standard("identical-source-map-responses");
        let result = recover_project_sourcemaps(project, &budget)?;
        assert_eq!(result.direct_recovered, 1);
        let rows = read_fixture_artifact(project, "analysis/sourcemaps.json")?;
        let source_map = &rows["source_maps"][0];
        assert_eq!(source_map["status"], "recovered");
        assert!(source_map["map_resource_id"].is_null());
        assert_eq!(source_map["map_resource_ids"], json!([2, 3]));
        assert_eq!(source_map["map_origin"], "har_shared_bytes");
        assert_eq!(source_map["recovered"][0]["status"], "recovered");
        crate::source_graph::build_source_graph(project, &budget)?;
        let graph = read_fixture_artifact(project, "analysis/source-graph.json")?;
        let edges = graph["edges"].as_array().context("missing graph edges")?;
        let from_reference = edges
            .iter()
            .filter(|edge| edge["from"] == "sourcemap-reference:1")
            .collect::<Vec<_>>();
        assert_eq!(
            from_reference
                .iter()
                .filter(|edge| edge["kind"] == "source_map_resource_candidate")
                .count(),
            2
        );
        let recovered = from_reference
            .iter()
            .filter(|edge| edge["kind"] == "source_map_source")
            .collect::<Vec<_>>();
        assert_eq!(recovered.len(), 1);
        assert_eq!(recovered[0]["to"], "sourcemap-source:1:0");
        assert!(edges
            .iter()
            .all(|edge| !(edge["kind"] == "source_map" && edge["from"] == "resource:1")));
        Ok(())
    }

    #[test]
    fn nested_map_with_reused_url_and_different_bodies_does_not_compose() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path();
        let nested_source = "console.log(1);\n//# sourceMappingURL=child.map";
        let map = alias_map_document(nested_source);
        shared_map_fixture(project, &map, &map)?;
        let map_a = alias_map_document("source A");
        let map_b = alias_map_document("source B");
        fs::write(project.join("resources/child-a"), &map_a)?;
        fs::write(project.join("resources/child-b"), &map_b)?;
        let mut manifest = crate::capture_project::load_manifest(project)?;
        for (id, path, body) in [
            (4, "resources/child-a", &map_a),
            (5, "resources/child-b", &map_b),
        ] {
            manifest.resources.push(json!({
                "id":id,"kind":"other","url":"https://fixture.invalid/child.map",
                "output_path":path,"sha256":sha256_hex(body.as_bytes()),
            }));
        }
        crate::capture_project::write_manifest(&project.join("capture-manifest.json"), &manifest)?;
        let budget = AnalysisBudgets::standard("ambiguous-nested-source-map");
        let result = recover_project_sourcemaps(project, &budget)?;
        assert_eq!(result.composed_links, 0);
        let rows = read_fixture_artifact(project, "analysis/sourcemaps.json")?;
        let link = &rows["source_maps"][0]["composition"]["links"][0];
        assert_eq!(link["status"], "ambiguous_captured_resource");
        assert_eq!(link["map_url"], "https://fixture.invalid/child.map");
        assert_eq!(link["candidate_resource_ids"], json!([4, 5]));
        crate::source_graph::build_source_graph(project, &budget)?;
        let graph = read_fixture_artifact(project, "analysis/source-graph.json")?;
        let edges = graph["edges"].as_array().context("missing graph edges")?;
        let candidates = edges
            .iter()
            .filter(|edge| {
                edge["from"] == "sourcemap-chain:1:0"
                    && edge["kind"] == "source_map_chain_resource_candidate"
            })
            .collect::<Vec<_>>();
        assert_eq!(candidates.len(), 2);
        assert_eq!(
            candidates
                .iter()
                .filter_map(|edge| edge["to"].as_str())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["resource:4", "resource:5"]),
        );
        Ok(())
    }

    #[test]
    fn chained_source_code_url_ambiguity_is_not_misclassified_as_map_identity() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path();
        let root_map = json!({
            "version":3,"file":"app.js","sources":["source.js"],
            "sourcesContent":[],"names":[],"mappings":"",
        })
        .to_string();
        shared_map_fixture(project, &root_map, &root_map)?;
        let first = "console.log('first');\n//# sourceMappingURL=first.map";
        let second = "console.log('second');\n//# sourceMappingURL=second.map";
        for (path, bytes) in [
            ("resources/source-a", first),
            ("resources/source-b", second),
        ] {
            fs::write(project.join(path), bytes)?;
        }
        let mut manifest = crate::capture_project::load_manifest(project)?;
        for (id, path, bytes) in [
            (4, "resources/source-a", first),
            (5, "resources/source-b", second),
        ] {
            manifest.resources.push(json!({
                "id":id,"kind":"javascript","url":"https://fixture.invalid/source.js",
                "output_path":path,"sha256":sha256_hex(bytes.as_bytes()),
            }));
        }
        crate::capture_project::write_manifest(&project.join("capture-manifest.json"), &manifest)?;
        let budget = AnalysisBudgets::standard("ambiguous-chained-source-code");
        let summary = recover_project_sourcemaps(project, &budget)?;
        assert_eq!(summary.composed_links, 0);
        let map = read_fixture_artifact(project, "analysis/sourcemaps.json")?;
        let link = &map["source_maps"][0]["composition"]["links"][0];
        assert_eq!(link["status"], "ambiguous_captured_resource");
        assert_eq!(link["code_url"], "https://fixture.invalid/source.js");
        assert_eq!(link["candidate_code_resource_ids"], json!([4, 5]));
        assert!(link["candidate_resource_ids"].is_null());
        crate::source_graph::build_source_graph(project, &budget)?;
        let graph = read_fixture_artifact(project, "analysis/source-graph.json")?;
        let edges = graph["edges"].as_array().context("missing graph edges")?;
        let candidates = edges
            .iter()
            .filter(|edge| {
                edge["from"] == "sourcemap-chain:1:0"
                    && edge["kind"] == "source_map_chain_code_candidate"
            })
            .collect::<Vec<_>>();
        assert_eq!(candidates.len(), 2);
        assert_eq!(
            candidates
                .iter()
                .filter_map(|edge| edge["to"].as_str())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["resource:4", "resource:5"]),
        );
        assert!(edges
            .iter()
            .all(|edge| edge["from"] != "sourcemap-chain:1:0"
                || edge["kind"] != "source_map_chain_resource_candidate"));
        Ok(())
    }

    #[test]
    fn chained_source_code_shared_bytes_retain_both_capture_ids() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path();
        let root_map = json!({
            "version":3,"file":"app.js","sources":["source.js"],
            "sourcesContent":[],"names":[],"mappings":"",
        })
        .to_string();
        shared_map_fixture(project, &root_map, &root_map)?;
        let code = "console.log('same');\n//# sourceMappingURL=child.map";
        let child_map = alias_map_document("export const child = 1;");
        for (path, bytes) in [
            ("resources/source-a", code),
            ("resources/source-b", code),
            ("resources/child.map", &child_map),
        ] {
            fs::write(project.join(path), bytes)?;
        }
        let mut manifest = crate::capture_project::load_manifest(project)?;
        for (id, path, url, bytes) in [
            (
                4,
                "resources/source-a",
                "https://fixture.invalid/source.js",
                code,
            ),
            (
                5,
                "resources/source-b",
                "https://fixture.invalid/source.js",
                code,
            ),
            (
                6,
                "resources/child.map",
                "https://fixture.invalid/child.map",
                &child_map,
            ),
        ] {
            manifest.resources.push(json!({
                "id":id,"kind":"javascript","url":url,
                "output_path":path,"sha256":sha256_hex(bytes.as_bytes()),
            }));
        }
        crate::capture_project::write_manifest(&project.join("capture-manifest.json"), &manifest)?;
        let budget = AnalysisBudgets::standard("shared-chained-source-code");
        recover_project_sourcemaps(project, &budget)?;
        let maps = read_fixture_artifact(project, "analysis/sourcemaps.json")?;
        let link = &maps["source_maps"][0]["composition"]["links"][0];
        assert_eq!(link["code_resource_ids"], json!([4, 5]));
        assert!(link["code_resource_id"].is_null());
        assert_eq!(link["map_resource_id"], 6);
        assert_ne!(link["status"], "ambiguous_captured_resource");
        crate::source_graph::build_source_graph(project, &budget)?;
        let graph = read_fixture_artifact(project, "analysis/source-graph.json")?;
        let edges = graph["edges"].as_array().context("missing graph edges")?;
        let code_candidates = edges
            .iter()
            .filter(|edge| {
                edge["from"] == "sourcemap-chain:1:0"
                    && edge["kind"] == "source_map_chain_code_candidate"
            })
            .collect::<Vec<_>>();
        assert_eq!(code_candidates.len(), 2);
        assert_eq!(
            code_candidates
                .iter()
                .filter_map(|edge| edge["to"].as_str())
                .collect::<BTreeSet<_>>(),
            BTreeSet::from(["resource:4", "resource:5"]),
        );
        assert!(edges
            .iter()
            .any(|edge| edge["from"] == "sourcemap-chain:1:0"
                && edge["kind"] == "source_map_chain_resource"
                && edge["to"] == "resource:6"));
        Ok(())
    }

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
