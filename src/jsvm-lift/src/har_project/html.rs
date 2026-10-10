use super::{Reference, ScriptTag};
use crate::source_directive::source_directives;
use std::collections::HashMap;
use url::Url;

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

pub(super) fn extract_script_tags(html: &str) -> Vec<ScriptTag> {
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

pub(super) fn script_type(attrs: &HashMap<String, String>) -> String {
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

pub(super) fn is_executable_script_type(ty: &str) -> bool {
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

pub(super) fn is_json_script_type(ty: &str) -> bool {
    matches!(ty, "importmap" | "speculationrules") || ty.contains("json")
}

pub(super) fn inline_script_extension(ty: &str) -> &'static str {
    if is_executable_script_type(ty) {
        "js"
    } else if is_json_script_type(ty) {
        "json"
    } else {
        "txt"
    }
}

pub(super) fn resolve_ref(base: &str, raw: &str) -> Option<String> {
    Url::parse(base).ok()?.join(raw).ok().map(|u| u.to_string())
}

pub(super) fn source_refs(source: &str, base: &str) -> Vec<Reference> {
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
