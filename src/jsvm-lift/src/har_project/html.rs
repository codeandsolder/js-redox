use super::materialize::Reference;
use crate::{
    browser_script_types::{
        inline_script_extension as shared_inline_script_extension, is_executable_script,
        is_json_script, script_type_essence,
    },
    source_directive::source_directives,
};
use html_escape::decode_html_entities;
use std::collections::HashMap;
use url::Url;

#[derive(Debug)]
pub(crate) struct ScriptTag {
    pub(crate) attrs: HashMap<String, String>,
    pub(crate) body: String,
}

pub(crate) const fn find_tag_end(bytes: &[u8], mut i: usize) -> Option<usize> {
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

pub(crate) fn parse_attrs(tag: &str) -> HashMap<String, String> {
    let bytes = tag.as_bytes();
    let mut out = HashMap::new();
    let mut i = 0usize;
    while i < bytes.len() && (bytes[i].is_ascii_whitespace() || matches!(bytes[i], b'<' | b'/')) {
        i += 1;
    }
    while i < bytes.len() && !bytes[i].is_ascii_whitespace() && !matches!(bytes[i], b'>' | b'/') {
        i += 1;
    }
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
            let (value_start, value_end) = if i < bytes.len() && matches!(bytes[i], b'\'' | b'"') {
                let quote = bytes[i];
                i += 1;
                let value_start = i;
                while i < bytes.len() && bytes[i] != quote {
                    i += 1;
                }
                let value_end = i;
                i += usize::from(i < bytes.len());
                (value_start, value_end)
            } else {
                let value_start = i;
                while i < bytes.len()
                    && !bytes[i].is_ascii_whitespace()
                    && !matches!(bytes[i], b'>' | b'/')
                {
                    i += 1;
                }
                (value_start, i)
            };
            value = decode_html_entities(&tag[value_start..value_end]).into_owned();
        }
        out.insert(key, value);
    }
    out
}

pub(crate) fn extract_script_tags(html: &str) -> Vec<ScriptTag> {
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

pub(crate) fn script_type(attrs: &HashMap<String, String>) -> String {
    script_type_essence(attrs.get("type").map(String::as_str))
}

pub(super) fn is_executable_script_type(ty: &str) -> bool {
    is_executable_script(Some(ty))
}

pub(super) fn is_json_script_type(ty: &str) -> bool {
    is_json_script(Some(ty))
}

pub(super) fn inline_script_extension(ty: &str) -> &'static str {
    shared_inline_script_extension(Some(ty))
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
