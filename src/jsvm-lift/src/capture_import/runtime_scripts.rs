use crate::{
    analysis_artifacts::{write_artifact, RUNTIME_SCRIPTS},
    capture_project::CaptureManifest,
    har_project::html::{find_tag_end, parse_attrs},
    sha256_hex,
};
use anyhow::{bail, Context, Result};
use regex::Regex;
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::{Path, PathBuf},
};

const ALPINE_PREFIX: &str =
    "(async function anonymous(__self,scope\n) {\nwith (scope) { __self.result = ";
const ALPINE_SUFFIX: &str = " }; __self.finished = true; return __self.result;\n})";

struct RuntimePatterns {
    single_string: Regex,
    double_string: Regex,
    whitespace: Regex,
    xfor: Regex,
}

impl RuntimePatterns {
    fn new() -> Result<Self> {
        Ok(Self {
            single_string: Regex::new(r"'(?:\\.|[^'\\])*'")?,
            double_string: Regex::new(r#""(?:\\.|[^"\\])*""#)?,
            whitespace: Regex::new(r"\s+")?,
            xfor: Regex::new(r"(?i)\s+(?:in|of)\s+")?,
        })
    }

    fn normalize_expression_shape(&self, expression: &str) -> String {
        let single = self.single_string.replace_all(expression, "'<str>'");
        let double = self.double_string.replace_all(&single, "\"<str>\"");
        let numbers = normalize_numeric_literals(&double);
        self.whitespace.replace_all(&numbers, " ").trim().to_owned()
    }
}

fn normalize_numeric_literals(input: &str) -> String {
    let chars = input.chars().collect::<Vec<_>>();
    let mut out = String::with_capacity(input.len());
    let mut index = 0usize;
    while index < chars.len() {
        let current = chars[index];
        let previous_blocks = index
            .checked_sub(1)
            .and_then(|previous| chars.get(previous))
            .is_some_and(|ch| ch.is_alphanumeric() || matches!(ch, '_' | '$'));
        if !current.is_ascii_digit() || previous_blocks {
            out.push(current);
            index += 1;
            continue;
        }

        let start = index;
        while index < chars.len() && chars[index].is_ascii_digit() {
            index += 1;
        }
        if index + 1 < chars.len() && chars[index] == '.' && chars[index + 1].is_ascii_digit() {
            index += 1;
            while index < chars.len() && chars[index].is_ascii_digit() {
                index += 1;
            }
        }
        let next_blocks = chars
            .get(index)
            .is_some_and(|ch| ch.is_alphanumeric() || matches!(ch, '_' | '$'));
        if next_blocks {
            for ch in &chars[start..index] {
                out.push(*ch);
            }
        } else {
            out.push_str("<num>");
        }
    }
    out
}

fn text(value: Option<&Value>) -> Option<&str> {
    value.and_then(Value::as_str)
}

fn stringish(value: Option<&Value>) -> String {
    match value {
        Some(Value::String(value)) => value.clone(),
        Some(Value::Number(value)) => value.to_string(),
        Some(Value::Bool(value)) => value.to_string(),
        _ => String::new(),
    }
}

fn truthy(value: Option<&Value>) -> bool {
    match value {
        None | Some(Value::Null) => false,
        Some(Value::Bool(value)) => *value,
        Some(Value::Number(value)) => value.as_i64().is_none_or(|number| number != 0),
        Some(Value::String(value)) => !value.is_empty(),
        Some(Value::Array(value)) => !value.is_empty(),
        Some(Value::Object(value)) => !value.is_empty(),
    }
}

fn event_session(event: &Map<String, Value>) -> String {
    let session = stringish(event.get("cdpSession"));
    if session.is_empty() {
        "main".into()
    } else {
        session
    }
}

fn sorted_unique_values<'a>(values: impl Iterator<Item = &'a Value>) -> Vec<Value> {
    let mut unique = BTreeMap::<String, Value>::new();
    for value in values {
        let key = match value {
            Value::String(text) => format!("s:{text}"),
            Value::Number(number) => format!("n:{number}"),
            Value::Bool(boolean) => format!("b:{boolean}"),
            Value::Null => "z:null".into(),
            other => format!("j:{other}"),
        };
        unique.entry(key).or_insert_with(|| value.clone());
    }
    unique.into_values().collect()
}

fn captured_javascript_digest(event: &Map<String, Value>) -> Option<&str> {
    let captured = event.get("captured")?.as_object()?;
    (text(captured.get("kind")) == Some("javascript"))
        .then(|| text(captured.get("sha256")))
        .flatten()
}

fn inline_origins(manifest: &CaptureManifest) -> HashMap<String, Vec<Value>> {
    let mut by_hash = HashMap::<String, Vec<Value>>::new();
    for script in &manifest.inline_scripts {
        let Some(script) = script.as_object() else {
            continue;
        };
        let Some(digest) = text(script.get("sha256")) else {
            continue;
        };
        by_hash.entry(digest.to_owned()).or_default().push(json!({
            "source": "capture_manifest",
            "parent_resource_id": script.get("parent_resource_id").cloned().unwrap_or(Value::Null),
            "ordinal": script.get("ordinal").cloned().unwrap_or(Value::Null),
            "script_type": script.get("script_type").cloned().unwrap_or(Value::Null),
            "output_path": script.get("output_path").cloned().unwrap_or(Value::Null),
        }));
    }
    by_hash
}

fn captured_resource_identity(manifest: &CaptureManifest) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut body_hashes = BTreeSet::new();
    let mut urls = BTreeSet::new();
    for resource in &manifest.resources {
        let Some(resource) = resource.as_object() else {
            continue;
        };
        if let Some(url) = text(resource.get("url")) {
            if !url.is_empty() {
                urls.insert(url.to_owned());
            }
        }
        if resource
            .get("body_present")
            .and_then(Value::as_bool)
            .unwrap_or(false)
        {
            if let Some(digest) = text(resource.get("sha256")) {
                body_hashes.insert(digest.to_owned());
            }
        }
    }
    (body_hashes, urls)
}

fn start_tag_directives(html: &str) -> Vec<(usize, String, String, String)> {
    let bytes = html.as_bytes();
    let lower = html.to_ascii_lowercase();
    let mut output = Vec::new();
    let mut offset = 0usize;
    let mut ordinal = 0usize;
    while offset < bytes.len() {
        let Some(relative) = html[offset..].find('<') else {
            break;
        };
        let start = offset + relative;
        let mut name_start = start + 1;
        while name_start < bytes.len() && bytes[name_start].is_ascii_whitespace() {
            name_start += 1;
        }
        if name_start >= bytes.len() || matches!(bytes[name_start], b'/' | b'!' | b'?') {
            offset = start + 1;
            continue;
        }
        let mut name_end = name_start;
        while name_end < bytes.len()
            && !bytes[name_end].is_ascii_whitespace()
            && !matches!(bytes[name_end], b'>' | b'/')
        {
            name_end += 1;
        }
        let Some(end) = find_tag_end(bytes, name_end) else {
            break;
        };
        let tag = html[name_start..name_end].to_ascii_lowercase();
        ordinal += 1;
        let attrs = parse_attrs(&html[start..=end]);
        let mut attrs = attrs.into_iter().collect::<Vec<_>>();
        attrs.sort_by(|left, right| left.0.cmp(&right.0));
        for (attribute, value) in attrs {
            if attribute.starts_with("x-")
                || attribute.starts_with('@')
                || attribute.starts_with(':')
            {
                output.push((ordinal, tag.clone(), attribute, value));
            }
        }
        if tag == "script" {
            if let Some(relative_close) = lower[end + 1..].find("</script") {
                let close_start = end + 1 + relative_close;
                offset = lower[close_start..]
                    .find('>')
                    .map_or(bytes.len(), |relative_end| close_start + relative_end + 1);
                continue;
            }
        }
        offset = end + 1;
    }
    output
}

fn frame_directives(capture: &Path) -> Result<BTreeMap<String, Vec<Value>>> {
    let frames = capture.join("frames");
    if !frames.is_dir() {
        return Ok(BTreeMap::new());
    }
    let mut paths = fs::read_dir(&frames)?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.is_file()
                && path
                    .extension()
                    .and_then(|extension| extension.to_str())
                    .is_some_and(|extension| extension.eq_ignore_ascii_case("html"))
        })
        .collect::<Vec<_>>();
    paths.sort();

    let mut by_value = BTreeMap::<String, Vec<Value>>::new();
    for path in paths {
        let bytes = fs::read(&path)?;
        let html = String::from_utf8_lossy(&bytes);
        let relative = path
            .strip_prefix(capture)
            .with_context(|| format!("frame outside capture: {}", path.display()))?
            .to_string_lossy()
            .into_owned();
        for (tag_ordinal, tag, attribute, value) in start_tag_directives(&html) {
            by_value.entry(value).or_default().push(json!({
                "source": "final_frame",
                "path": relative,
                "tag_ordinal": tag_ordinal,
                "tag": tag,
                "attribute": attribute,
            }));
        }
    }
    Ok(by_value)
}

fn recover_alpine_expression(source: &str) -> Option<(String, String)> {
    let compiled = source
        .strip_prefix(ALPINE_PREFIX)?
        .strip_suffix(ALPINE_SUFFIX)?;
    let original = compiled
        .strip_prefix("(async()=>{ ")
        .and_then(|value| value.strip_suffix(" })()"))
        .unwrap_or(compiled);
    Some((compiled.to_owned(), original.to_owned()))
}

fn recover_gtm_custom_javascript(source: &str, patterns: &RuntimePatterns) -> Option<String> {
    let value = source.trim();
    if !(value.starts_with("(function(){") || value.starts_with("(function () {")) {
        return None;
    }
    if !value.contains("google_tag_manager")
        && !value.to_ascii_lowercase().contains("googletagmanager")
    {
        return None;
    }
    Some(patterns.normalize_expression_shape(value))
}

fn match_directives(
    expression: &str,
    directives: &BTreeMap<String, Vec<Value>>,
    patterns: &RuntimePatterns,
) -> (&'static str, Vec<Value>) {
    if let Some(exact) = directives.get(expression) {
        return ("exact", exact.clone());
    }
    const PLACEHOLDER: &str = " = __placeholder";
    if let Some(target) = expression.strip_suffix(PLACEHOLDER) {
        let matches = directives
            .get(target)
            .into_iter()
            .flatten()
            .filter(|row| text(row.get("attribute")) == Some("x-model"))
            .cloned()
            .collect::<Vec<_>>();
        if !matches.is_empty() {
            return ("x-model-setter", matches);
        }
    }

    let mut matches = Vec::new();
    for (value, rows) in directives {
        let Some(separator) = patterns.xfor.find(value) else {
            continue;
        };
        if value[separator.end()..].trim() != expression.trim() {
            continue;
        }
        matches.extend(
            rows.iter()
                .filter(|row| text(row.get("attribute")) == Some("x-for"))
                .cloned(),
        );
    }
    if matches.is_empty() {
        ("unmatched", matches)
    } else {
        ("x-for-rhs", matches)
    }
}

fn generation_origins(
    event_rows: &[usize],
    events: &[Value],
    events_by_script_id: &HashMap<(String, String), usize>,
) -> Vec<Value> {
    let mut output = Vec::new();
    let mut seen = BTreeSet::new();
    for event_index in event_rows {
        let Some(event) = events.get(*event_index).and_then(Value::as_object) else {
            continue;
        };
        let session = event_session(event);
        let child_script_id = stringish(event.get("scriptId"));
        let mut current_index = *event_index;
        let mut visited = BTreeSet::new();
        if !child_script_id.is_empty() {
            visited.insert(child_script_id.clone());
        }
        let mut chain = Vec::new();
        for _ in 0..32 {
            let Some(current) = events.get(current_index).and_then(Value::as_object) else {
                break;
            };
            let Some(frame) = current
                .get("stackTrace")
                .and_then(Value::as_object)
                .and_then(|stack| stack.get("callFrames"))
                .and_then(Value::as_array)
                .and_then(|frames| frames.first())
                .and_then(Value::as_object)
            else {
                break;
            };
            let parent_script_id = stringish(frame.get("scriptId"));
            if parent_script_id.is_empty() || !visited.insert(parent_script_id.clone()) {
                break;
            }
            let parent_index = events_by_script_id
                .get(&(session.clone(), parent_script_id.clone()))
                .copied();
            let parent = parent_index
                .and_then(|index| events.get(index))
                .and_then(Value::as_object);
            let captured = parent
                .and_then(|parent| parent.get("captured"))
                .and_then(Value::as_object);
            let parent_url = parent
                .and_then(|parent| text(parent.get("url")))
                .filter(|url| !url.is_empty())
                .or_else(|| text(frame.get("url")))
                .unwrap_or_default();
            chain.push(json!({
                "cdp_session": session,
                "script_id": parent_script_id,
                "sha256": captured.and_then(|value| value.get("sha256")).cloned().unwrap_or(Value::Null),
                "url": parent_url,
                "function_name": text(frame.get("functionName")).unwrap_or_default(),
                "line_number": frame.get("lineNumber").cloned().unwrap_or(Value::Null),
                "column_number": frame.get("columnNumber").cloned().unwrap_or(Value::Null),
            }));
            let Some(parent_index) = parent_index else {
                break;
            };
            current_index = parent_index;
        }
        if chain.is_empty() {
            continue;
        }
        let origin = json!({
            "cdp_session": session,
            "child_script_id": child_script_id,
            "chain": chain,
        });
        if let Ok(key) = serde_json::to_string(&origin) {
            if seen.insert(key) {
                output.push(origin);
            }
        }
    }
    output
}

fn document_inline_origins(event_rows: &[usize], events: &[Value]) -> Vec<Value> {
    let mut output = Vec::new();
    for event_index in event_rows {
        let Some(event) = events.get(*event_index).and_then(Value::as_object) else {
            continue;
        };
        let url = text(event.get("url")).unwrap_or_default();
        if !(matches!(url, "about:blank" | "about:srcdoc") || url.starts_with("data:text/html")) {
            continue;
        }
        if truthy(event.get("stackTrace")) {
            continue;
        }
        let Some(aux) = event
            .get("executionContextAuxData")
            .and_then(Value::as_object)
        else {
            continue;
        };
        if aux.get("isDefault").and_then(Value::as_bool) != Some(true) {
            continue;
        }
        let start_line = event
            .get("startLine")
            .and_then(Value::as_i64)
            .unwrap_or_default();
        let start_column = event
            .get("startColumn")
            .and_then(Value::as_i64)
            .unwrap_or_default();
        if url != "about:srcdoc" && start_line == 0 && start_column == 0 {
            continue;
        }
        output.push(json!({
            "cdp_session": event_session(event),
            "script_id": event.get("scriptId").cloned().unwrap_or(Value::Null),
            "url": url,
            "frame_id": aux.get("frameId").cloned().unwrap_or(Value::Null),
            "start_line": event.get("startLine").cloned().unwrap_or(Value::Null),
            "start_column": event.get("startColumn").cloned().unwrap_or(Value::Null),
            "end_line": event.get("endLine").cloned().unwrap_or(Value::Null),
            "end_column": event.get("endColumn").cloned().unwrap_or(Value::Null),
            "embedder_name": event.get("embedderName").cloned().unwrap_or(Value::Null),
        }));
    }
    output
}

fn instrumentation_kind(source: &str) -> Option<&'static str> {
    if source.contains("// packages/injected/src/utilityScript.ts")
        || source.contains("utilityScript.evaluate")
    {
        return Some("playwright-utility");
    }
    if source.contains("// packages/injected/src/storageScript.ts") {
        return Some("playwright-storage");
    }
    if source.trim_start().starts_with("(phrases) => {")
        && source.contains("document.querySelectorAll")
    {
        return Some("recorder-consent-fallback");
    }
    if source.contains("detectedCmps") && source.contains("heuristicPatterns") {
        return Some("recorder-autoconsent-probe");
    }
    if source.contains("localStorage: dump(localStorage)")
        && source.contains("sessionStorage: dump(sessionStorage)")
    {
        return Some("recorder-storage-dump");
    }
    if source.contains("XMLSerializer().serializeToString(document.doctype)") {
        return Some("recorder-html-snapshot");
    }
    if source.len() <= 4096
        && source.contains("document.documentElement.scrollHeight")
        && (source.contains("scrollY")
            || source.contains("scrollTo({ top:")
            || source.trim_start().starts_with("() => Math.max("))
    {
        return Some("recorder-scroll");
    }
    None
}

fn families(shapes: &BTreeMap<String, Vec<String>>) -> Vec<Value> {
    let mut rows = shapes
        .iter()
        .map(|(shape, hashes)| {
            json!({
                "shape": shape,
                "source_count": hashes.len(),
                "source_hashes": hashes,
            })
        })
        .collect::<Vec<_>>();
    rows.sort_by(|left, right| {
        let left_count = left
            .get("source_count")
            .and_then(Value::as_u64)
            .unwrap_or_default();
        let right_count = right
            .get("source_count")
            .and_then(Value::as_u64)
            .unwrap_or_default();
        right_count
            .cmp(&left_count)
            .then_with(|| text(left.get("shape")).cmp(&text(right.get("shape"))))
    });
    rows
}

pub(super) fn analyze_recorder_runtime_scripts(
    capture: &Path,
    project: &Path,
    manifest: &CaptureManifest,
) -> Result<()> {
    let runtime_manifest = capture.join("runtime-scripts.json");
    let runtime_dir = capture.join("runtime-scripts");
    if !runtime_manifest.is_file() || !runtime_dir.is_dir() {
        bail!(
            "not a recorder runtime-script bundle: {}",
            capture.display()
        );
    }
    let events_value: Value = serde_json::from_slice(&fs::read(&runtime_manifest)?)
        .with_context(|| format!("parsing {}", runtime_manifest.display()))?;
    let events = events_value
        .as_array()
        .context("runtime-scripts.json must contain an array")?;
    let patterns = RuntimePatterns::new()?;
    let directives = frame_directives(capture)?;
    let inline_by_hash = inline_origins(manifest);
    let (body_hashes, network_urls) = captured_resource_identity(manifest);

    let mut events_by_hash = HashMap::<String, Vec<usize>>::new();
    let mut events_by_script_id = HashMap::<(String, String), usize>::new();
    for (index, event) in events.iter().enumerate() {
        let Some(event) = event.as_object() else {
            continue;
        };
        if !event.get("scriptId").is_none_or(Value::is_null) {
            events_by_script_id.insert(
                (event_session(event), stringish(event.get("scriptId"))),
                index,
            );
        }
        if let Some(digest) = captured_javascript_digest(event) {
            events_by_hash
                .entry(digest.to_owned())
                .or_default()
                .push(index);
        }
    }

    let mut source_paths = fs::read_dir(&runtime_dir)?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.is_file()
                && path
                    .extension()
                    .and_then(|extension| extension.to_str())
                    .is_some_and(|extension| extension.eq_ignore_ascii_case("js"))
        })
        .collect::<Vec<PathBuf>>();
    source_paths.sort();

    let mut sources = Vec::new();
    let mut class_counts = BTreeMap::<String, usize>::new();
    let mut class_bytes = BTreeMap::<String, usize>::new();
    let mut instrumentation_counts = BTreeMap::<String, usize>::new();
    let mut alpine_shapes = BTreeMap::<String, Vec<String>>::new();
    let mut gtm_shapes = BTreeMap::<String, Vec<String>>::new();
    let mut alpine_dom_mapped = 0usize;
    let mut alpine_dom_matches = 0usize;

    for source_path in source_paths {
        let raw_source = fs::read(&source_path)?;
        let digest = sha256_hex(&raw_source);
        let source = String::from_utf8_lossy(&raw_source);
        let event_rows = events_by_hash.get(&digest).cloned().unwrap_or_default();
        let mut urls = BTreeSet::new();
        let mut sessions = BTreeSet::new();
        let mut script_ids = Vec::new();
        let mut execution_context_values = Vec::new();
        let mut script_instances = Vec::new();
        for event_index in &event_rows {
            let Some(event) = events.get(*event_index).and_then(Value::as_object) else {
                continue;
            };
            if let Some(url) = text(event.get("url")).filter(|url| !url.is_empty()) {
                urls.insert(url.to_owned());
            }
            sessions.insert(event_session(event));
            script_ids.push(event.get("scriptId").cloned().unwrap_or(Value::Null));
            if let Some(value) = event.get("executionContextId") {
                execution_context_values.push(value);
            }
            script_instances.push(json!({
                "cdp_session": event_session(event),
                "script_id": event.get("scriptId").cloned().unwrap_or(Value::Null),
                "execution_context_id": event.get("executionContextId").cloned().unwrap_or(Value::Null),
            }));
        }

        let origins = generation_origins(&event_rows, events, &events_by_script_id);
        let document_origins = document_inline_origins(&event_rows, events);
        let relative_path = source_path
            .strip_prefix(capture)
            .with_context(|| format!("runtime source outside capture: {}", source_path.display()))?
            .to_string_lossy()
            .into_owned();
        let mut row = Map::new();
        row.insert("sha256".into(), json!(digest));
        row.insert("size".into(), json!(raw_source.len()));
        row.insert("path".into(), json!(relative_path));
        row.insert("event_count".into(), json!(event_rows.len()));
        row.insert("script_ids".into(), Value::Array(script_ids));
        row.insert("cdp_sessions".into(), json!(sessions));
        row.insert(
            "execution_context_ids".into(),
            Value::Array(sorted_unique_values(execution_context_values.into_iter())),
        );
        row.insert("script_instances".into(), Value::Array(script_instances));
        row.insert("urls".into(), json!(urls));
        if !document_origins.is_empty() {
            row.insert(
                "document_inline_origins".into(),
                Value::Array(document_origins),
            );
        }
        if !origins.is_empty() {
            let mut root_hashes = BTreeSet::new();
            let mut root_urls = BTreeSet::new();
            let mut max_depth = 0usize;
            for origin in &origins {
                let chain = origin
                    .get("chain")
                    .and_then(Value::as_array)
                    .map(Vec::as_slice)
                    .unwrap_or_default();
                max_depth = max_depth.max(chain.len());
                if let Some(root) = chain.last() {
                    if let Some(digest) = text(root.get("sha256")) {
                        root_hashes.insert(digest.to_owned());
                    }
                    if let Some(url) = text(root.get("url")).filter(|url| !url.is_empty()) {
                        root_urls.insert(url.to_owned());
                    }
                }
            }
            row.insert(
                "generated".into(),
                json!({
                    "origins": origins,
                    "root_sha256s": root_hashes,
                    "root_urls": root_urls,
                    "max_depth": max_depth,
                }),
            );
        }

        let classification = if body_hashes.contains(&digest) {
            "network_response"
        } else if let Some(origins) = inline_by_hash.get(&digest) {
            row.insert("inline_origins".into(), Value::Array(origins.clone()));
            "inline_script"
        } else if urls.iter().any(|url| network_urls.contains(url)) {
            "network_observed"
        } else if row.contains_key("document_inline_origins") {
            "document_inline_script"
        } else if let Some((compiled, expression)) = recover_alpine_expression(&source) {
            let (mapping_kind, matches) = match_directives(&expression, &directives, &patterns);
            let shape = patterns.normalize_expression_shape(&expression);
            alpine_shapes
                .entry(shape.clone())
                .or_default()
                .push(digest.clone());
            if !matches.is_empty() {
                alpine_dom_mapped += 1;
                alpine_dom_matches += matches.len();
            }
            row.insert(
                "alpine".into(),
                json!({
                    "compiled_expression": compiled,
                    "expression": expression,
                    "shape": shape,
                    "dom_mapping_kind": mapping_kind,
                    "dom_matches": matches,
                }),
            );
            "alpine_expression"
        } else if let Some(shape) = recover_gtm_custom_javascript(&source, &patterns) {
            gtm_shapes
                .entry(shape.clone())
                .or_default()
                .push(digest.clone());
            row.insert("gtm".into(), json!({"shape": shape}));
            "gtm_custom_javascript"
        } else if let Some(kind) = instrumentation_kind(&source) {
            *instrumentation_counts.entry(kind.into()).or_default() += 1;
            row.insert("instrumentation_kind".into(), json!(kind));
            "capture_instrumentation"
        } else if row.contains_key("generated") {
            "generated_runtime"
        } else {
            "anonymous_runtime"
        };
        row.insert("classification".into(), json!(classification));
        *class_counts.entry(classification.into()).or_default() += 1;
        *class_bytes.entry(classification.into()).or_default() += raw_source.len();
        sources.push(Value::Object(row));
    }

    let class_count = |name: &str| class_counts.get(name).copied().unwrap_or_default();
    let document = json!({
        "schema": RUNTIME_SCRIPTS.schema,
        "capture": capture.display().to_string(),
        "summary": {
            "script_parsed_events": events.len(),
            "captured_javascript_events": events_by_hash.values().map(Vec::len).sum::<usize>(),
            "unique_javascript_sources": sources.len(),
            "unique_javascript_bytes": sources.iter().filter_map(|row| row.get("size").and_then(Value::as_u64)).sum::<u64>(),
            "classifications": class_counts,
            "classification_bytes": class_bytes,
            "alpine_dom_mapped_sources": alpine_dom_mapped,
            "alpine_dom_match_occurrences": alpine_dom_matches,
            "alpine_expression_shapes": alpine_shapes.len(),
            "gtm_expression_shapes": gtm_shapes.len(),
            "capture_instrumentation_kinds": instrumentation_counts,
            "generated_runtime_sources": class_count("generated_runtime"),
            "anonymous_runtime_sources": class_count("anonymous_runtime"),
        },
        "alpine_families": families(&alpine_shapes),
        "gtm_families": families(&gtm_shapes),
        "sources": sources,
    });
    write_artifact(project, RUNTIME_SCRIPTS, &document)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn event(
        session: &str,
        script_id: &str,
        digest: &str,
        url: &str,
        parent: Option<&str>,
    ) -> Value {
        let mut row = json!({
            "cdpSession": session,
            "scriptId": script_id,
            "url": url,
            "executionContextId": 1,
            "captured": {"kind": "javascript", "sha256": digest},
        });
        if let Some(parent) = parent {
            row["stackTrace"] = json!({
                "callFrames": [{
                    "functionName": "eval",
                    "scriptId": parent,
                    "url": "",
                    "lineNumber": 0,
                    "columnNumber": 0,
                }]
            });
        }
        row
    }

    #[test]
    fn instrumentation_classifier_bounds_scroll_probe() {
        let probe = "() => ({ y: scrollY, height: document.documentElement.scrollHeight })";
        assert_eq!(instrumentation_kind(probe), Some("recorder-scroll"));
        let page = format!(
            "const app = '{}'; const h = document.documentElement.scrollHeight; console.log(scrollY, h);",
            "x".repeat(5000)
        );
        assert_eq!(instrumentation_kind(&page), None);
        assert_eq!(
            instrumentation_kind("((utilityScript, ...args) => utilityScript.evaluate(...args))"),
            Some("playwright-utility")
        );
    }

    #[test]
    fn generated_script_ids_are_session_scoped() -> Result<()> {
        let events = vec![
            event(
                "main",
                "1",
                "main-parent",
                "https://main.invalid/root.js",
                None,
            ),
            event("main", "2", "main-child", "", Some("1")),
            event(
                "oopif-1",
                "1",
                "frame-parent",
                "https://frame.invalid/root.js",
                None,
            ),
            event("oopif-1", "2", "frame-child", "", Some("1")),
        ];
        let mut by_id = HashMap::new();
        for (index, event) in events.iter().enumerate() {
            let object = event.as_object().context("fixture event must be object")?;
            by_id.insert(
                (event_session(object), stringish(object.get("scriptId"))),
                index,
            );
        }
        let main = generation_origins(&[1], &events, &by_id);
        let frame = generation_origins(&[3], &events, &by_id);
        assert_eq!(main[0]["chain"][0]["sha256"], "main-parent");
        assert_eq!(frame[0]["chain"][0]["sha256"], "frame-parent");
        assert_eq!(main[0]["cdp_session"], "main");
        assert_eq!(frame[0]["cdp_session"], "oopif-1");
        Ok(())
    }

    #[test]
    fn srcdoc_default_context_is_document_inline_provenance() {
        let row = json!({
            "cdpSession": "oopif-2",
            "scriptId": "1",
            "url": "about:srcdoc",
            "startLine": 0,
            "startColumn": 17,
            "endLine": 0,
            "endColumn": 45,
            "executionContextAuxData": {"isDefault": true, "frameId": "fixture-frame"},
            "embedderName": "about:srcdoc",
        });
        let origins = document_inline_origins(&[0], &[row]);
        assert_eq!(origins.len(), 1);
        assert_eq!(origins[0]["cdp_session"], "oopif-2");
        assert_eq!(origins[0]["frame_id"], "fixture-frame");
        assert_eq!(origins[0]["start_column"], 17);
    }

    #[test]
    fn alpine_directive_mapping_keeps_exact_model_and_for_rhs() -> Result<()> {
        let patterns = RuntimePatterns::new()?;
        let mut directives = BTreeMap::new();
        directives.insert("app.foo".into(), vec![json!({"attribute": "x-text"})]);
        directives.insert("form.name".into(), vec![json!({"attribute": "x-model"})]);
        directives.insert("item in items".into(), vec![json!({"attribute": "x-for"})]);
        assert_eq!(
            match_directives("app.foo", &directives, &patterns).0,
            "exact"
        );
        assert_eq!(
            match_directives("form.name = __placeholder", &directives, &patterns).0,
            "x-model-setter"
        );
        assert_eq!(
            match_directives("items", &directives, &patterns).0,
            "x-for-rhs"
        );
        Ok(())
    }
}
