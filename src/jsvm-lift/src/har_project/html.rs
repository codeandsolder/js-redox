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

pub(crate) fn document_base(html: &str, final_url: &Url) -> Url {
    let lower = html.to_ascii_lowercase();
    let mut from = 0;
    while let Some(relative) = lower[from..].find("<base") {
        let start = from + relative;
        if !html
            .as_bytes()
            .get(start + 5)
            .is_some_and(|c| c.is_ascii_whitespace() || *c == b'>')
        {
            from = start + 5;
            continue;
        }
        let Some(end) = find_tag_end(html.as_bytes(), start + 5) else {
            break;
        };
        let attrs = parse_attrs(&html[start..=end]);
        if let Some(href) = attrs.get("href") {
            if let Ok(candidate) = final_url.join(href) {
                if matches!(candidate.scheme(), "http" | "https") {
                    return candidate;
                }
            }
        }
        from = end + 1;
    }
    final_url.clone()
}

pub(crate) fn script_preload_links(html: &str) -> Vec<(String, &'static str)> {
    let lower = html.to_ascii_lowercase();
    let mut from = 0;
    let mut urls = Vec::new();
    while let Some(relative) = lower[from..].find("<link") {
        let start = from + relative;
        if !html
            .as_bytes()
            .get(start + 5)
            .is_some_and(|c| c.is_ascii_whitespace() || *c == b'>')
        {
            from = start + 5;
            continue;
        }
        let Some(end) = find_tag_end(html.as_bytes(), start + 5) else {
            break;
        };
        let attrs = parse_attrs(&html[start..=end]);
        let rel = attrs.get("rel").map(String::as_str).unwrap_or_default();
        let modulepreload = rel
            .split_ascii_whitespace()
            .any(|word| word.eq_ignore_ascii_case("modulepreload"));
        let script_preload = rel
            .split_ascii_whitespace()
            .any(|word| word.eq_ignore_ascii_case("preload"))
            && attrs
                .get("as")
                .is_some_and(|value| value.eq_ignore_ascii_case("script"));
        if modulepreload || script_preload {
            if let Some(url) = attrs.get("href") {
                urls.push((
                    url.clone(),
                    if modulepreload {
                        "modulepreload"
                    } else {
                        "script_preload"
                    },
                ));
            }
        }
        from = end + 1;
    }
    urls
}

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

#[cfg(test)]
mod tests {
    use super::script_preload_links;

    #[test]
    fn collects_module_and_classic_script_preloads() {
        let html = r#"<!doctype html>
            <link rel="stylesheet" href="not-a-script.css">
            <link rel="ModulePreload" href="./a.js">
            <LINK REL="preload stylesheet" AS="SCRIPT" HREF="./b.js">
            <link rel="preload" as="font" href="not-a-script.woff2">
            <linker href="not-a-tag.js">
        "#;
        assert_eq!(
            script_preload_links(html),
            vec![
                ("./a.js".to_owned(), "modulepreload"),
                ("./b.js".to_owned(), "script_preload"),
            ]
        );
    }
}
