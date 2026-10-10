use anyhow::{bail, ensure, Context, Result};
use base64::Engine;
use clap::Parser as ClapParser;
use jsvm_lift::source_directive::source_directives;
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, HashMap},
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
};
use url::Url;

#[derive(ClapParser, Debug)]
#[command(about = "Turn a browser HAR into a provenance-preserving source project")]
struct Args {
    har: PathBuf,
    #[arg(short, long)]
    output: PathBuf,
    #[arg(long)]
    overwrite: bool,
}

#[derive(Debug, Deserialize)]
struct Har {
    log: HarLog,
}

#[derive(Debug, Deserialize)]
struct HarLog {
    #[serde(default)]
    version: String,
    #[serde(default)]
    pages: Vec<HarPage>,
    entries: Vec<HarEntry>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HarPage {
    #[serde(default)]
    id: String,
    #[serde(default)]
    title: String,
    #[serde(default)]
    started_date_time: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HarEntry {
    #[serde(default)]
    pageref: Option<String>,
    #[serde(default)]
    started_date_time: String,
    #[serde(default)]
    time: f64,
    request: HarRequest,
    response: HarResponse,
    #[serde(default, rename = "_resourceType")]
    resource_type: Option<String>,
    #[serde(default, rename = "_failure")]
    failure: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
struct HarRequest {
    #[serde(default)]
    method: String,
    #[serde(default)]
    url: String,
    #[serde(default)]
    headers: Vec<NameValue>,
}

#[derive(Debug, Deserialize)]
struct HarResponse {
    #[serde(default)]
    status: i64,
    #[serde(default)]
    status_text: String,
    #[serde(default)]
    headers: Vec<NameValue>,
    content: HarContent,
    #[serde(default, rename = "_jsRedoxBody")]
    js_redox_body: Option<JsRedoxBodyRef>,
    #[serde(default, rename = "_jsRedoxBodyCapture")]
    js_redox_body_capture: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
struct JsRedoxBodyRef {
    path: String,
    sha256: String,
    size: usize,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HarContent {
    #[serde(default)]
    size: i64,
    #[serde(default)]
    mime_type: String,
    #[serde(default)]
    text: Option<String>,
    #[serde(default)]
    encoding: Option<String>,
}

#[derive(Debug, Deserialize)]
struct NameValue {
    #[serde(default)]
    name: String,
    #[serde(default)]
    value: String,
}

#[derive(Debug, Clone, Serialize)]
struct PageMeta {
    id: String,
    title: String,
    started_date_time: String,
}

#[derive(Debug, Clone, Serialize)]
struct HeaderMeta {
    name: String,
    value: String,
}

#[derive(Debug, Clone, Serialize)]
struct Reference {
    kind: String,
    raw: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    resolved_url: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct ResourceMeta {
    id: usize,
    pageref: Option<String>,
    started_date_time: String,
    time_ms: f64,
    method: String,
    url: String,
    status: i64,
    status_text: String,
    mime_type: String,
    resource_type: Option<String>,
    declared_size: i64,
    encoding: Option<String>,
    body_present: bool,
    body_complete: bool,
    body_bytes: usize,
    sha256: Option<String>,
    transport_kind: String,
    kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    network_failure: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    body_capture: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    output_path: Option<String>,
    reused_body: bool,
    request_headers: Vec<HeaderMeta>,
    response_headers: Vec<HeaderMeta>,
    references: Vec<Reference>,
}

#[derive(Debug, Clone, Serialize)]
struct InlineScriptMeta {
    parent_resource_id: usize,
    ordinal: usize,
    script_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    src: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    resolved_src: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    output_path: Option<String>,
    body_bytes: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    sha256: Option<String>,
}

#[derive(Debug, Serialize)]
struct CaptureSource {
    kind: &'static str,
    input: String,
    har_version: String,
    salvaged: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    parse_error: Option<String>,
}

#[derive(Debug, Serialize)]
struct ProjectManifest {
    schema: &'static str,
    source: CaptureSource,
    pages: Vec<PageMeta>,
    resources: Vec<ResourceMeta>,
    inline_scripts: Vec<InlineScriptMeta>,
    counts: BTreeMap<String, usize>,
}

#[derive(Debug)]
struct ScriptTag {
    attrs: HashMap<String, String>,
    body: String,
}

fn headers(src: &[NameValue]) -> Vec<HeaderMeta> {
    src.iter()
        .map(|h| HeaderMeta {
            name: h.name.clone(),
            value: h.value.clone(),
        })
        .collect()
}

fn sha256_hex(bytes: &[u8]) -> String {
    jsvm_lift::sha256_hex(bytes)
}

fn short_hash(text: &str) -> String {
    sha256_hex(text.as_bytes())[..10].to_string()
}

fn sanitize_component(raw: &str) -> String {
    let mut out = String::new();
    for c in raw.chars() {
        if c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-') {
            out.push(c);
        } else {
            out.push('_');
        }
    }
    while out.contains("__") {
        out = out.replace("__", "_");
    }
    let out = out.trim_matches('_');
    if out.is_empty() {
        "_".into()
    } else {
        out.chars().take(120).collect()
    }
}

fn mime_base(mime: &str) -> &str {
    mime.split(';').next().unwrap_or(mime).trim()
}

fn resource_kind(url: &str, mime: &str) -> &'static str {
    let m = mime_base(mime).to_ascii_lowercase();
    let path = Url::parse(url)
        .ok()
        .map(|u| u.path().to_ascii_lowercase())
        .unwrap_or_default();
    if m == "application/wasm" || path.ends_with(".wasm") {
        "wasm"
    } else if m.contains("javascript")
        || m.contains("ecmascript")
        || path.ends_with(".js")
        || path.ends_with(".mjs")
        || path.ends_with(".cjs")
    {
        "javascript"
    } else if m == "text/html" || m == "application/xhtml+xml" || path.ends_with(".html") {
        "html"
    } else if m.contains("json") || path.ends_with(".json") || path.ends_with(".map") {
        "json"
    } else if m == "text/css" || path.ends_with(".css") {
        "css"
    } else if m.starts_with("text/") || m.contains("xml") || m.contains("svg") {
        "text"
    } else {
        "binary"
    }
}

fn extension_for(kind: &str, mime: &str) -> &'static str {
    match kind {
        "javascript" => "js",
        "wasm" => "wasm",
        "html" => "html",
        "json" => "json",
        "css" => "css",
        "text" if mime_base(mime).contains("xml") => "xml",
        "text" => "txt",
        _ => "bin",
    }
}

fn has_plausible_extension(name: &str, kind: &str) -> bool {
    let extension = Path::new(name)
        .extension()
        .and_then(|extension| extension.to_str())
        .map(str::to_ascii_lowercase);
    let Some(extension) = extension.as_deref() else {
        return false;
    };
    match kind {
        "javascript" => matches!(extension, "js" | "mjs" | "cjs"),
        "wasm" => extension == "wasm",
        "html" => matches!(extension, "html" | "htm" | "xhtml"),
        "json" => matches!(extension, "json" | "map"),
        "css" => extension == "css",
        "text" => matches!(extension, "txt" | "xml" | "svg" | "csv" | "md"),
        // Binary assets have a much wider extension vocabulary. A numeric-only
        // suffix is far more likely to be a package/version component than a
        // file extension (for example `typography@2.0.0`).
        _ => extension.bytes().any(|byte| byte.is_ascii_alphabetic()),
    }
}

fn insert_suffix(path: &str, suffix: &str) -> String {
    let p = Path::new(path);
    let parent = p.parent().unwrap_or_else(|| Path::new(""));
    let stem = p.file_stem().and_then(|x| x.to_str()).unwrap_or("resource");
    let ext = p.extension().and_then(|x| x.to_str());
    let name = match ext {
        Some(ext) => format!("{stem}{suffix}.{ext}"),
        None => format!("{stem}{suffix}"),
    };
    parent
        .join(name)
        .to_string_lossy()
        .replace(std::path::MAIN_SEPARATOR, "/")
}

fn output_path_for(url: &str, kind: &str, mime: &str) -> String {
    let Ok(parsed) = Url::parse(url) else {
        return format!(
            "resources/_invalid_url/resource-{}.{}",
            short_hash(url),
            extension_for(kind, mime)
        );
    };
    let scheme = sanitize_component(parsed.scheme());
    let host = sanitize_component(parsed.host_str().unwrap_or("_no_host"));
    let mut parts: Vec<String> = parsed
        .path_segments()
        .map(|it| {
            it.filter(|s| !s.is_empty())
                .map(sanitize_component)
                .collect()
        })
        .unwrap_or_default();
    if parts.is_empty() {
        parts.push(format!("index.{}", extension_for(kind, mime)));
    } else if let Some(last) = parts.last_mut() {
        if !has_plausible_extension(last, kind) {
            last.push('.');
            last.push_str(extension_for(kind, mime));
        }
    }
    let mut path = format!("resources/{scheme}/{host}/{}", parts.join("/"));
    if let Some(query) = parsed.query() {
        path = insert_suffix(&path, &format!("~q-{}", short_hash(query)));
    }
    path
}

fn decode_body(
    content: &HarContent,
    recorder_body: Option<&JsRedoxBodyRef>,
    har_root: &Path,
) -> Result<Option<Vec<u8>>> {
    if let Some(reference) = recorder_body {
        let root = fs::canonicalize(har_root)
            .with_context(|| format!("canonicalizing HAR root {}", har_root.display()))?;
        let path = fs::canonicalize(har_root.join(&reference.path)).with_context(|| {
            format!(
                "resolving recorder body {}",
                har_root.join(&reference.path).display()
            )
        })?;
        ensure!(
            path.starts_with(&root),
            "recorder body escapes HAR root: {}",
            reference.path
        );
        let bytes = fs::read(&path).with_context(|| format!("reading {}", path.display()))?;
        ensure!(
            bytes.len() == reference.size,
            "recorder body size mismatch for {}: manifest={} actual={}",
            reference.path,
            reference.size,
            bytes.len()
        );
        ensure!(
            sha256_hex(&bytes) == reference.sha256,
            "recorder body SHA-256 mismatch for {}",
            reference.path
        );
        return Ok(Some(bytes));
    }

    let Some(text) = content.text.as_ref() else {
        return Ok(None);
    };
    if content.encoding.as_deref() == Some("base64") {
        Ok(Some(
            base64::engine::general_purpose::STANDARD
                .decode(text.as_bytes())
                .context("decoding HAR base64 body")?,
        ))
    } else {
        Ok(Some(text.as_bytes().to_vec()))
    }
}

fn trim_transport_prefix(text: &str) -> (&str, bool) {
    let mut text = text.trim_start_matches(|c: char| c == '\u{feff}' || c.is_ascii_whitespace());
    for prefix in ["for (;;);", "for(;;);", "while (1);", "while(1);", ")]}'"] {
        if let Some(rest) = text.strip_prefix(prefix) {
            text = rest.trim_start_matches(|c: char| c.is_ascii_whitespace());
            return (text, true);
        }
    }
    (text, false)
}

fn looks_like_plain_text_error(text: &str) -> bool {
    let text = text.trim();
    if text.is_empty()
        || text.len() > 512
        || !text
            .chars()
            .all(|c| !c.is_control() || c.is_ascii_whitespace())
    {
        return false;
    }
    if (16..=128).contains(&text.len()) && text.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return true;
    }
    let has_js_structure = text
        .bytes()
        .any(|byte| matches!(byte, b'{' | b'}' | b'[' | b']' | b'(' | b')' | b';' | b'='));
    !has_js_structure && text.split_ascii_whitespace().count() >= 2
}

fn refine_resource_kind(
    transport_kind: &str,
    resource_type: Option<&str>,
    mime: &str,
    body: &[u8],
) -> String {
    if transport_kind != "javascript" {
        return transport_kind.to_string();
    }
    let Ok(text) = std::str::from_utf8(body) else {
        return transport_kind.to_string();
    };
    let (candidate, had_xssi_prefix) = trim_transport_prefix(text);
    let lower_prefix = candidate
        .chars()
        .take(256)
        .collect::<String>()
        .to_ascii_lowercase();
    if lower_prefix.starts_with("<!doctype")
        || lower_prefix.starts_with("<html")
        || lower_prefix.starts_with("<head")
        || lower_prefix.starts_with("<body")
        || lower_prefix.starts_with("<script")
    {
        return "html".into();
    }
    if lower_prefix.starts_with("<?xml") || lower_prefix.starts_with("<svg") {
        return "text".into();
    }
    if (had_xssi_prefix || matches!(candidate.as_bytes().first(), Some(b'{') | Some(b'[')))
        && serde_json::from_str::<serde_json::Value>(candidate).is_ok()
    {
        return "json".into();
    }
    if matches!(
        resource_type.map(str::to_ascii_lowercase).as_deref(),
        Some("xhr" | "fetch" | "ping" | "eventsource")
    ) {
        return "text".into();
    }
    if mime_base(mime).eq_ignore_ascii_case("text/plain") && looks_like_plain_text_error(candidate)
    {
        return "text".into();
    }
    if looks_like_plain_text_error(candidate) {
        return "text".into();
    }
    transport_kind.to_string()
}

fn format_json_if_possible(bytes: &[u8]) -> Vec<u8> {
    let Ok(value) = serde_json::from_slice::<serde_json::Value>(bytes) else {
        return bytes.to_vec();
    };
    let Ok(mut pretty) = serde_json::to_vec_pretty(&value) else {
        return bytes.to_vec();
    };
    pretty.push(10);
    pretty
}

const fn find_tag_end(bytes: &[u8], mut i: usize) -> Option<usize> {
    let mut quote = None;
    while i < bytes.len() {
        let b = bytes[i];
        if let Some(q) = quote {
            if b == q {
                quote = None;
            }
        } else if b == b'\'' || b == b'"' {
            quote = Some(b);
        } else if b == b'>' {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn parse_attrs(tag: &str) -> HashMap<String, String> {
    let bytes = tag.as_bytes();
    let mut out = HashMap::new();
    let mut i = tag.to_ascii_lowercase().find("script").map_or(0, |x| x + 6);
    while i < bytes.len() {
        while i < bytes.len() && (bytes[i].is_ascii_whitespace() || bytes[i] == b'/') {
            i += 1;
        }
        if i >= bytes.len() || bytes[i] == b'>' {
            break;
        }
        let start = i;
        while i < bytes.len()
            && !bytes[i].is_ascii_whitespace()
            && !matches!(bytes[i], b'=' | b'>' | b'/')
        {
            i += 1;
        }
        if i == start {
            i += 1;
            continue;
        }
        let key = tag[start..i].to_ascii_lowercase();
        while i < bytes.len() && bytes[i].is_ascii_whitespace() {
            i += 1;
        }
        let mut value = String::new();
        if i < bytes.len() && bytes[i] == b'=' {
            i += 1;
            while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                i += 1;
            }
            if i < bytes.len() && (bytes[i] == b'\'' || bytes[i] == b'"') {
                let quote = bytes[i];
                i += 1;
                let vstart = i;
                while i < bytes.len() && bytes[i] != quote {
                    i += 1;
                }
                value = tag[vstart..i.min(bytes.len())].to_string();
                i += usize::from(i < bytes.len());
            } else {
                let vstart = i;
                while i < bytes.len()
                    && !bytes[i].is_ascii_whitespace()
                    && !matches!(bytes[i], b'>' | b'/')
                {
                    i += 1;
                }
                value = tag[vstart..i].to_string();
            }
        }
        out.insert(key, value);
    }
    out
}

fn extract_script_tags(html: &str) -> Vec<ScriptTag> {
    let lower = html.to_ascii_lowercase();
    let bytes = html.as_bytes();
    let mut out = Vec::new();
    let mut from = 0usize;
    while let Some(rel) = lower[from..].find("<script") {
        let start = from + rel;
        let Some(open_end) = find_tag_end(bytes, start + 7) else {
            break;
        };
        let attrs = parse_attrs(&html[start..=open_end]);
        let body_start = open_end + 1;
        let Some(close_rel) = lower[body_start..].find("</script") else {
            break;
        };
        let close_start = body_start + close_rel;
        let body = html[body_start..close_start].to_string();
        let close_end = lower[close_start..]
            .find('>')
            .map_or(close_start + 8, |x| close_start + x + 1);
        out.push(ScriptTag { attrs, body });
        from = close_end.min(html.len());
    }
    out
}

fn script_type(attrs: &HashMap<String, String>) -> String {
    attrs
        .get("type")
        .map(|s| {
            s.split_once(';')
                .map_or(s.as_str(), |(essence, _)| essence)
                .trim()
                .to_ascii_lowercase()
        })
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "text/javascript".into())
}

fn is_standard_executable_script_type(ty: &str) -> bool {
    matches!(
        ty,
        "module"
            | "text/javascript"
            | "application/javascript"
            | "application/ecmascript"
            | "text/ecmascript"
            | "application/x-ecmascript"
            | "application/x-javascript"
            | "text/javascript1.0"
            | "text/javascript1.1"
            | "text/javascript1.2"
            | "text/javascript1.3"
            | "text/javascript1.4"
            | "text/javascript1.5"
            | "text/jscript"
            | "text/livescript"
            | "text/x-ecmascript"
            | "text/x-javascript"
    )
}

fn is_executable_script_type(ty: &str) -> bool {
    if is_standard_executable_script_type(ty) {
        return true;
    }
    let Some((prefix, suffix)) = ty.split_once('-') else {
        return false;
    };
    prefix.len() >= 16
        && prefix.bytes().all(|byte| byte.is_ascii_hexdigit())
        && is_standard_executable_script_type(suffix)
}

fn is_json_script_type(ty: &str) -> bool {
    matches!(ty, "importmap" | "speculationrules") || ty.contains("json")
}

fn inline_script_extension(ty: &str) -> &'static str {
    if is_executable_script_type(ty) {
        "js"
    } else if is_json_script_type(ty) {
        "json"
    } else {
        "txt"
    }
}

fn resolve_ref(base: &str, raw: &str) -> Option<String> {
    Url::parse(base).ok()?.join(raw).ok().map(|u| u.to_string())
}

fn source_refs(source: &str, base: &str) -> Vec<Reference> {
    source_directives(source)
        .into_iter()
        .filter_map(|directive| {
            if directive.raw.starts_with("data:") {
                return None;
            }
            Some(Reference {
                kind: directive.kind,
                resolved_url: resolve_ref(base, &directive.raw),
                raw: directive.raw,
            })
        })
        .collect()
}

fn write_resource(
    root: &Path,
    desired: String,
    bytes: &[u8],
    seen: &mut HashMap<String, String>,
) -> Result<(String, bool)> {
    let digest = sha256_hex(bytes);
    let mut path = desired;
    let mut reused = false;
    if let Some(existing) = seen.get(&path) {
        if existing == &digest {
            reused = true;
        } else {
            let mut n = 2usize;
            loop {
                let candidate = insert_suffix(&path, &format!("~v{n}"));
                match seen.get(&candidate) {
                    Some(h) if h == &digest => {
                        path = candidate;
                        reused = true;
                        break;
                    }
                    Some(_) => n += 1,
                    None => {
                        path = candidate;
                        break;
                    }
                }
            }
        }
    }
    if !reused {
        let full = root.join(&path);
        if let Some(parent) = full.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&full, bytes).with_context(|| format!("writing {}", full.display()))?;
        seen.insert(path.clone(), digest);
    }
    Ok((path, reused))
}

fn salvage_har(raw: &[u8]) -> Result<Har> {
    let text = std::str::from_utf8(raw).context("HAR is not valid UTF-8")?;
    let marker = text
        .find("\"entries\"")
        .context("could not locate HAR log.entries for salvage")?;
    let array_rel = text[marker..]
        .find('[')
        .context("could not locate HAR log.entries array")?;
    let array_start = marker + array_rel;
    let bytes = text.as_bytes();

    let mut entries = Vec::new();
    let mut in_string = false;
    let mut escaped = false;
    let mut object_depth = 0usize;
    let mut array_depth = 1usize;
    let mut entry_start = None;

    for i in (array_start + 1)..bytes.len() {
        let byte = bytes[i];
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            continue;
        }

        match byte {
            b'"' => in_string = true,
            b'{' => {
                if object_depth == 0 && array_depth == 1 {
                    entry_start = Some(i);
                }
                object_depth += 1;
            }
            b'}' => {
                if object_depth == 0 {
                    continue;
                }
                object_depth -= 1;
                if object_depth == 0 && array_depth == 1 {
                    if let Some(start) = entry_start.take() {
                        match serde_json::from_str::<HarEntry>(&text[start..=i]) {
                            Ok(entry) => entries.push(entry),
                            Err(error) => {
                                eprintln!(
                                    "warning: skipping malformed salvaged HAR entry at bytes {start}..={i}: {error}"
                                );
                            }
                        }
                    }
                }
            }
            b'[' => array_depth += 1,
            b']' => {
                if array_depth == 1 && object_depth == 0 {
                    break;
                }
                array_depth = array_depth.saturating_sub(1);
            }
            _ => {}
        }
    }

    if entries.is_empty() {
        bail!("no complete HAR entries could be salvaged");
    }

    Ok(Har {
        log: HarLog {
            version: "1.2-salvaged".into(),
            pages: Vec::new(),
            entries,
        },
    })
}

fn prepare_output(args: &Args) -> Result<()> {
    if args.output.exists() {
        if !args.overwrite {
            bail!(
                "output directory already exists: {} (use --overwrite)",
                args.output.display()
            );
        }
        fs::remove_dir_all(&args.output)?;
    }
    fs::create_dir_all(&args.output)?;
    Ok(())
}

fn read_har(path: &Path) -> Result<(Har, bool, Option<String>)> {
    let raw = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
    let first = raw.iter().copied().find(|byte| !byte.is_ascii_whitespace());
    if first != Some(b'{') {
        bail!(
            "{} is not HAR JSON (first non-whitespace byte {:?})",
            path.display(),
            first
        );
    }
    let parsed = match serde_json::from_slice::<Har>(&raw) {
        Ok(har) => (har, false, None),
        Err(error) => {
            let message = error.to_string();
            eprintln!("warning: full HAR JSON parse failed; salvaging complete entries: {message}");
            (
                salvage_har(&raw)
                    .with_context(|| format!("salvaging truncated HAR {}", path.display()))?,
                true,
                Some(message),
            )
        }
    };
    if parsed.0.log.entries.is_empty() {
        bail!("HAR contains no log.entries");
    }
    Ok(parsed)
}

fn page_metadata(har: &Har) -> Vec<PageMeta> {
    har.log
        .pages
        .iter()
        .map(|page| PageMeta {
            id: page.id.clone(),
            title: page.title.clone(),
            started_date_time: page.started_date_time.clone(),
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn materialize_inline_scripts(
    parent_resource_id: usize,
    base_url: &str,
    html: &str,
    written: &str,
    output_root: &Path,
    seen: &mut HashMap<String, String>,
    counts: &mut BTreeMap<String, usize>,
    references: &mut Vec<Reference>,
    inline_scripts: &mut Vec<InlineScriptMeta>,
) -> Result<()> {
    for (ordinal0, script) in extract_script_tags(html).into_iter().enumerate() {
        let ordinal = ordinal0 + 1;
        let ty = script_type(&script.attrs);
        let src = script.attrs.get("src").cloned();
        let resolved_src = src.as_deref().and_then(|src| resolve_ref(base_url, src));
        if let Some(raw_src) = src.as_ref() {
            if is_executable_script_type(&ty) {
                references.push(Reference {
                    kind: "script_src".into(),
                    raw: raw_src.clone(),
                    resolved_url: resolved_src.clone(),
                });
            }
            inline_scripts.push(InlineScriptMeta {
                parent_resource_id,
                ordinal,
                script_type: ty,
                src,
                resolved_src,
                output_path: None,
                body_bytes: 0,
                sha256: None,
            });
            continue;
        }

        let body = if is_json_script_type(&ty) {
            format_json_if_possible(script.body.as_bytes())
        } else {
            script.body.into_bytes()
        };
        if body.iter().all(u8::is_ascii_whitespace) {
            continue;
        }
        let ext = inline_script_extension(&ty);
        let desired = format!("{written}.inline/script-{ordinal:03}.{ext}");
        let (script_path, _) = write_resource(output_root, desired, &body, seen)?;
        *counts.entry("inline_scripts".into()).or_insert(0) += 1;
        inline_scripts.push(InlineScriptMeta {
            parent_resource_id,
            ordinal,
            script_type: ty,
            src: None,
            resolved_src: None,
            output_path: Some(script_path),
            body_bytes: body.len(),
            sha256: Some(sha256_hex(&body)),
        });
    }
    Ok(())
}

fn materialize_entry(
    id: usize,
    entry: &HarEntry,
    har_root: &Path,
    output_root: &Path,
    seen: &mut HashMap<String, String>,
    counts: &mut BTreeMap<String, usize>,
    inline_scripts: &mut Vec<InlineScriptMeta>,
) -> Result<ResourceMeta> {
    let transport_kind =
        resource_kind(&entry.request.url, &entry.response.content.mime_type).to_string();
    let body = decode_body(
        &entry.response.content,
        entry.response.js_redox_body.as_ref(),
        har_root,
    )
    .with_context(|| format!("entry {id}: {}", entry.request.url))?;
    let body_present = body.is_some();
    let body_complete = entry.failure.is_none();
    let mut kind = transport_kind.clone();
    let mut output_path = None;
    let mut body_bytes = 0;
    let mut sha256 = None;
    let mut reused_body = false;
    let mut references = Vec::new();

    if let Some(body) = body {
        body_bytes = body.len();
        sha256 = Some(sha256_hex(&body));
        kind = refine_resource_kind(
            &transport_kind,
            entry.resource_type.as_deref(),
            &entry.response.content.mime_type,
            &body,
        );
        if kind != transport_kind {
            *counts
                .entry("resources_content_reclassified".into())
                .or_insert(0) += 1;
        }
        if kind == "javascript" && body_complete {
            if let Ok(source) = std::str::from_utf8(&body) {
                references.extend(source_refs(source, &entry.request.url));
            }
        }
        let desired = output_path_for(&entry.request.url, &kind, &entry.response.content.mime_type);
        let (written, reused) = write_resource(output_root, desired, &body, seen)?;
        output_path = Some(written.clone());
        reused_body = reused;
        if kind == "html" && body_complete {
            if let Ok(html) = std::str::from_utf8(&body) {
                materialize_inline_scripts(
                    id,
                    &entry.request.url,
                    html,
                    &written,
                    output_root,
                    seen,
                    counts,
                    &mut references,
                    inline_scripts,
                )?;
            }
        }
    } else {
        *counts.entry("resources_without_body".into()).or_insert(0) += 1;
    }
    *counts.entry(format!("resource_{kind}")).or_insert(0) += 1;
    if !body_complete {
        *counts.entry("resources_incomplete".into()).or_insert(0) += 1;
    }

    Ok(ResourceMeta {
        id,
        pageref: entry.pageref.clone(),
        started_date_time: entry.started_date_time.clone(),
        time_ms: entry.time,
        method: entry.request.method.clone(),
        url: entry.request.url.clone(),
        status: entry.response.status,
        status_text: entry.response.status_text.clone(),
        mime_type: entry.response.content.mime_type.clone(),
        resource_type: entry.resource_type.clone(),
        declared_size: entry.response.content.size,
        encoding: entry.response.content.encoding.clone(),
        body_present,
        body_complete,
        body_bytes,
        sha256,
        transport_kind,
        kind,
        network_failure: entry.failure.clone(),
        body_capture: entry.response.js_redox_body_capture.clone(),
        output_path,
        reused_body,
        request_headers: headers(&entry.request.headers),
        response_headers: headers(&entry.response.headers),
        references,
    })
}

fn build_manifest(
    args: &Args,
    har: Har,
    salvaged: bool,
    parse_error: Option<String>,
) -> Result<ProjectManifest> {
    let pages = page_metadata(&har);
    let mut seen = HashMap::new();
    let mut counts = BTreeMap::new();
    let mut inline_scripts = Vec::new();
    let mut resources = Vec::with_capacity(har.log.entries.len());
    let har_root = args.har.parent().unwrap_or_else(|| Path::new("."));
    for (id, entry) in har.log.entries.iter().enumerate() {
        resources.push(materialize_entry(
            id,
            entry,
            har_root,
            &args.output,
            &mut seen,
            &mut counts,
            &mut inline_scripts,
        )?);
    }
    counts.insert("resources_total".into(), resources.len());
    counts.insert("pages".into(), pages.len());
    Ok(ProjectManifest {
        schema: "capture-project/v1",
        source: CaptureSource {
            kind: "har",
            input: args.har.display().to_string(),
            har_version: har.log.version,
            salvaged,
            parse_error,
        },
        pages,
        resources,
        inline_scripts,
        counts,
    })
}

fn write_project_metadata(args: &Args, manifest: &ProjectManifest) -> Result<()> {
    fs::write(
        args.output.join("capture-manifest.json"),
        format!("{}\n", serde_json::to_string_pretty(manifest)?),
    )?;
    fs::create_dir_all(args.output.join(".vscode"))?;
    fs::write(
        args.output.join(".vscode/settings.json"),
        "{\n  \"editor.maxTokenizationLineLength\": 200000\n}\n",
    )?;
    let mut summary = String::new();
    for (kind, count) in &manifest.counts {
        let _ = writeln!(summary, "- {kind}: {count}");
    }
    fs::write(
        args.output.join("README.md"),
        format!(
            "# Capture source project\n\nGenerated from {}.\n\nResponse bodies are preserved by URL under resources/. Inline script bodies are extracted beside their parent HTML. capture-manifest.json keeps capture provenance and discovered script/source-map references.\n\n## Counts\n\n{}",
            args.har.display(),
            summary
        ),
    )?;
    Ok(())
}

fn print_summary(args: &Args, manifest: &ProjectManifest) {
    println!(
        "HAR project: {} resources, {} script records -> {}",
        manifest.resources.len(),
        manifest.inline_scripts.len(),
        args.output.display()
    );
    for (kind, count) in &manifest.counts {
        println!("{kind}\t{count}");
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    prepare_output(&args)?;
    let (har, salvaged, parse_error) = read_har(&args.har)?;
    let manifest = build_manifest(&args, har, salvaged, parse_error)?;
    write_project_metadata(&args, &manifest)?;
    print_summary(&args, &manifest);
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::output_path_for;

    #[test]
    fn version_like_url_component_gets_resource_extension() {
        assert_eq!(
            output_path_for(
                "https://esm.glass.adidas.com/@adl/typography@2.0.0",
                "javascript",
                "application/javascript",
            ),
            "resources/https/esm.glass.adidas.com/adl/typography_2.0.0.js"
        );
        assert_eq!(
            output_path_for(
                "https://esm.glass.adidas.com/@adl/typography@2.0.0/fonts/AdihausDIN-Regular.woff2",
                "binary",
                "font/woff2",
            ),
            "resources/https/esm.glass.adidas.com/adl/typography_2.0.0/fonts/AdihausDIN-Regular.woff2"
        );
    }
}
