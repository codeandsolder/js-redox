use anyhow::{bail, Context, Result};
use base64::Engine;
use clap::Parser as ClapParser;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, HashMap},
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
    declared_size: i64,
    encoding: Option<String>,
    body_present: bool,
    body_bytes: usize,
    sha256: Option<String>,
    kind: String,
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
struct ProjectManifest {
    schema: &'static str,
    source_har: String,
    har_version: String,
    salvaged: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    parse_error: Option<String>,
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
    let mut h = Sha256::new();
    h.update(bytes);
    format!("{:x}", h.finalize())
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
    if m.contains("javascript")
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
        "html" => "html",
        "json" => "json",
        "css" => "css",
        "text" if mime_base(mime).contains("xml") => "xml",
        "text" => "txt",
        _ => "bin",
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
    } else {
        let last = parts.last_mut().unwrap();
        if !last.contains('.') {
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

fn decode_body(content: &HarContent) -> Result<Option<Vec<u8>>> {
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

fn find_tag_end(bytes: &[u8], mut i: usize) -> Option<usize> {
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
    let mut i = tag
        .to_ascii_lowercase()
        .find("script")
        .map(|x| x + 6)
        .unwrap_or(0);
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
            .map(|x| close_start + x + 1)
            .unwrap_or(close_start + 8);
        out.push(ScriptTag { attrs, body });
        from = close_end.min(html.len());
    }
    out
}

fn script_type(attrs: &HashMap<String, String>) -> String {
    attrs
        .get("type")
        .map(|s| s.trim().to_ascii_lowercase())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "text/javascript".into())
}

fn resolve_ref(base: &str, raw: &str) -> Option<String> {
    Url::parse(base).ok()?.join(raw).ok().map(|u| u.to_string())
}

fn source_refs(source: &str, base: &str) -> Vec<Reference> {
    let mut out = Vec::new();
    for (marker, kind) in [
        ("sourceMappingURL=", "source_map"),
        ("sourceURL=", "source_url"),
    ] {
        let mut from = 0usize;
        while let Some(rel) = source[from..].find(marker) {
            let start = from + rel + marker.len();
            let tail = &source[start..];
            let end = tail
                .find(|c: char| c.is_whitespace() || matches!(c, '*' | '\'' | '"' | '<' | '>'))
                .unwrap_or(tail.len());
            let raw = tail[..end].trim().trim_end_matches(';');
            if !raw.is_empty() && !raw.starts_with("data:") {
                out.push(Reference {
                    kind: kind.into(),
                    raw: raw.into(),
                    resolved_url: resolve_ref(base, raw),
                });
            }
            from = start + end.max(1);
        }
    }
    out
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

fn main() -> Result<()> {
    let args = Args::parse();
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

    let raw = fs::read(&args.har).with_context(|| format!("reading {}", args.har.display()))?;
    let first = raw.iter().copied().find(|b| !b.is_ascii_whitespace());
    if first != Some(b'{') {
        bail!(
            "{} is not HAR JSON (first non-whitespace byte {:?})",
            args.har.display(),
            first
        );
    }
    let (har, salvaged, parse_error) = match serde_json::from_slice::<Har>(&raw) {
        Ok(har) => (har, false, None),
        Err(error) => {
            let message = error.to_string();
            eprintln!("warning: full HAR JSON parse failed; salvaging complete entries: {message}");
            (
                salvage_har(&raw)
                    .with_context(|| format!("salvaging truncated HAR {}", args.har.display()))?,
                true,
                Some(message),
            )
        }
    };
    if har.log.entries.is_empty() {
        bail!("HAR contains no log.entries");
    }

    let pages = har
        .log
        .pages
        .iter()
        .map(|p| PageMeta {
            id: p.id.clone(),
            title: p.title.clone(),
            started_date_time: p.started_date_time.clone(),
        })
        .collect::<Vec<_>>();

    let mut seen = HashMap::new();
    let mut resources = Vec::new();
    let mut inline_scripts = Vec::new();
    let mut counts = BTreeMap::new();

    for (id, entry) in har.log.entries.iter().enumerate() {
        let kind = resource_kind(&entry.request.url, &entry.response.content.mime_type).to_string();
        *counts.entry(format!("resource_{kind}")).or_insert(0) += 1;

        let body = decode_body(&entry.response.content)
            .with_context(|| format!("entry {id}: {}", entry.request.url))?;
        let mut output_path = None;
        let mut body_bytes = 0usize;
        let mut sha256 = None;
        let mut reused_body = false;
        let mut references = Vec::new();

        if let Some(mut body) = body {
            body_bytes = body.len();
            sha256 = Some(sha256_hex(&body));
            if kind == "json" {
                body = format_json_if_possible(&body);
            }
            if kind == "javascript" {
                if let Ok(source) = std::str::from_utf8(&body) {
                    references.extend(source_refs(source, &entry.request.url));
                }
            }
            let desired =
                output_path_for(&entry.request.url, &kind, &entry.response.content.mime_type);
            let (written, reused) = write_resource(&args.output, desired, &body, &mut seen)?;
            output_path = Some(written.clone());
            reused_body = reused;

            if kind == "html" {
                if let Ok(html) = std::str::from_utf8(&body) {
                    for (ordinal0, script) in extract_script_tags(html).into_iter().enumerate() {
                        let ordinal = ordinal0 + 1;
                        let ty = script_type(&script.attrs);
                        let src = script.attrs.get("src").cloned();
                        let resolved_src = src
                            .as_deref()
                            .and_then(|s| resolve_ref(&entry.request.url, s));
                        if let Some(raw_src) = src.as_ref() {
                            references.push(Reference {
                                kind: "script_src".into(),
                                raw: raw_src.clone(),
                                resolved_url: resolved_src.clone(),
                            });
                            inline_scripts.push(InlineScriptMeta {
                                parent_resource_id: id,
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

                        let structured_json = ty.contains("json") || ty == "importmap";
                        let body = if structured_json {
                            format_json_if_possible(script.body.as_bytes())
                        } else {
                            script.body.into_bytes()
                        };
                        if body.iter().all(|b| b.is_ascii_whitespace()) {
                            continue;
                        }
                        let ext = if structured_json { "json" } else { "js" };
                        let desired = format!("{written}.inline/script-{ordinal:03}.{ext}");
                        let (script_path, _) =
                            write_resource(&args.output, desired, &body, &mut seen)?;
                        *counts.entry("inline_scripts".into()).or_insert(0) += 1;
                        inline_scripts.push(InlineScriptMeta {
                            parent_resource_id: id,
                            ordinal,
                            script_type: ty,
                            src: None,
                            resolved_src: None,
                            output_path: Some(script_path),
                            body_bytes: body.len(),
                            sha256: Some(sha256_hex(&body)),
                        });
                    }
                }
            }
        } else {
            *counts.entry("resources_without_body".into()).or_insert(0) += 1;
        }

        resources.push(ResourceMeta {
            id,
            pageref: entry.pageref.clone(),
            started_date_time: entry.started_date_time.clone(),
            time_ms: entry.time,
            method: entry.request.method.clone(),
            url: entry.request.url.clone(),
            status: entry.response.status,
            status_text: entry.response.status_text.clone(),
            mime_type: entry.response.content.mime_type.clone(),
            declared_size: entry.response.content.size,
            encoding: entry.response.content.encoding.clone(),
            body_present: entry.response.content.text.is_some(),
            body_bytes,
            sha256,
            kind,
            output_path,
            reused_body,
            request_headers: headers(&entry.request.headers),
            response_headers: headers(&entry.response.headers),
            references,
        });
    }

    counts.insert("resources_total".into(), resources.len());
    counts.insert("pages".into(), pages.len());

    let manifest = ProjectManifest {
        schema: "har-project/v0",
        source_har: args.har.display().to_string(),
        har_version: har.log.version,
        salvaged,
        parse_error,
        pages,
        resources,
        inline_scripts,
        counts,
    };

    fs::write(
        args.output.join("har-manifest.json"),
        format!("{}\n", serde_json::to_string_pretty(&manifest)?),
    )?;
    fs::create_dir_all(args.output.join(".vscode"))?;
    fs::write(
        args.output.join(".vscode/settings.json"),
        "{\n  \"editor.maxTokenizationLineLength\": 200000\n}\n",
    )?;

    let mut summary = String::new();
    for (kind, count) in &manifest.counts {
        summary.push_str(&format!("- {kind}: {count}\n"));
    }
    fs::write(
        args.output.join("README.md"),
        format!(
            "# HAR source project\n\nGenerated from {}.\n\nResponse bodies are preserved by URL under resources/. Inline script bodies are extracted beside their parent HTML. har-manifest.json keeps request/response provenance and discovered script/source-map references.\n\n## Counts\n\n{}",
            args.har.display(),
            summary
        ),
    )?;

    println!(
        "HAR project: {} resources, {} script records -> {}",
        manifest.resources.len(),
        manifest.inline_scripts.len(),
        args.output.display()
    );
    for (kind, count) in &manifest.counts {
        println!("{kind}\t{count}");
    }
    Ok(())
}
