use super::parse::{HarContent, JsRedoxBodyRef};
use crate::sha256_hex;
use anyhow::{ensure, Context, Result};
use base64::Engine;
use std::{collections::HashMap, fs, path::Path};
use url::Url;

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

pub(crate) fn resource_kind(url: &str, mime: &str) -> &'static str {
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

pub(super) fn output_path_for(url: &str, kind: &str, mime: &str) -> String {
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

pub(super) fn decode_body(
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

pub(super) fn refine_resource_kind(
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

pub(super) fn format_json_if_possible(bytes: &[u8]) -> Vec<u8> {
    let Ok(value) = serde_json::from_slice::<serde_json::Value>(bytes) else {
        return bytes.to_vec();
    };
    let Ok(mut pretty) = serde_json::to_vec_pretty(&value) else {
        return bytes.to_vec();
    };
    pretty.push(10);
    pretty
}

pub(super) fn write_resource(
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
