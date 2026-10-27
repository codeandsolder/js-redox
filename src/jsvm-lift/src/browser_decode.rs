//! Browser-compatible JavaScript byte decoding.
//!
//! Raw HTTP response bytes are provenance, not ECMAScript source text. Browsers
//! decode those bytes before parsing. This module keeps that boundary explicit
//! and uses `encoding_rs` for WHATWG-compatible decoding instead of assuming
//! every captured body is a Rust UTF-8 `String`.

use encoding_rs::{Encoding, UTF_16BE, UTF_16LE, UTF_8, WINDOWS_1252};
use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScriptKind {
    Module,
    Classic,
    ClassicWorker,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum DecodeSource {
    Bom,
    ModuleUtf8,
    ScriptCharset,
    DocumentEncoding,
    WorkerResponseEncoding,
    Utf8Default,
    Utf8Fallback,
    AlreadyUnicode,
    HtmlTransport,
    HtmlMeta,
    HtmlFallback,
}

impl DecodeSource {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Bom => "bom",
            Self::ModuleUtf8 => "module-utf8",
            Self::ScriptCharset => "script-charset",
            Self::DocumentEncoding => "document-encoding",
            Self::WorkerResponseEncoding => "worker-response-encoding",
            Self::Utf8Default => "utf8-default",
            Self::Utf8Fallback => "utf8-fallback",
            Self::AlreadyUnicode => "already-unicode",
            Self::HtmlTransport => "html-transport",
            Self::HtmlMeta => "html-meta",
            Self::HtmlFallback => "html-fallback",
        }
    }
}



#[derive(Debug, Clone, Serialize)]
pub struct DecodedHtml {
    pub source: String,
    pub encoding: String,
    pub decode_source: DecodeSource,
    pub had_errors: bool,
    pub uncertain: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bom_encoding: Option<String>,
}

fn html_compatible_encoding(encoding: &'static Encoding) -> &'static Encoding {
    if encoding == UTF_16LE || encoding == UTF_16BE {
        UTF_8
    } else if encoding.name().eq_ignore_ascii_case("x-user-defined") {
        WINDOWS_1252
    } else {
        encoding
    }
}

fn content_type_charset(value: &str) -> Option<&'static Encoding> {
    for parameter in value.split(';').skip(1) {
        let Some((name, raw_value)) = parameter.split_once('=') else {
            continue;
        };
        if !name.trim().eq_ignore_ascii_case("charset") {
            continue;
        }
        let label = raw_value.trim().trim_matches(|ch| ch == '\'' || ch == '"');
        return label_encoding(Some(label)).map(html_compatible_encoding);
    }
    None
}

fn ascii_eq_ignore_case(bytes: &[u8], expected: &[u8]) -> bool {
    bytes.len() == expected.len()
        && bytes
            .iter()
            .zip(expected)
            .all(|(a, b)| a.eq_ignore_ascii_case(b))
}

fn ascii_prefix_ignore_case(bytes: &[u8], expected: &[u8]) -> bool {
    bytes.len() >= expected.len() && ascii_eq_ignore_case(&bytes[..expected.len()], expected)
}

const fn is_html_space(byte: u8) -> bool {
    matches!(byte, b'\t' | b'\n' | 0x0c | b'\r' | b' ')
}

fn parse_ascii_attrs(tag: &[u8]) -> Vec<(String, String)> {
    let mut attrs = Vec::new();
    let mut i = 0usize;
    while i < tag.len() {
        while i < tag.len() && (is_html_space(tag[i]) || tag[i] == b'/') {
            i += 1;
        }
        if i >= tag.len() || tag[i] == b'>' {
            break;
        }
        let name_start = i;
        while i < tag.len()
            && !is_html_space(tag[i])
            && !matches!(tag[i], b'=' | b'>' | b'/')
        {
            i += 1;
        }
        if name_start == i {
            i += 1;
            continue;
        }
        let name = String::from_utf8_lossy(&tag[name_start..i]).to_ascii_lowercase();
        while i < tag.len() && is_html_space(tag[i]) {
            i += 1;
        }
        let mut value = String::new();
        if i < tag.len() && tag[i] == b'=' {
            i += 1;
            while i < tag.len() && is_html_space(tag[i]) {
                i += 1;
            }
            let (start, end) = if i < tag.len() && matches!(tag[i], b'\'' | b'"') {
                let quote = tag[i];
                i += 1;
                let start = i;
                while i < tag.len() && tag[i] != quote {
                    i += 1;
                }
                let end = i;
                if i < tag.len() {
                    i += 1;
                }
                (start, end)
            } else {
                let start = i;
                while i < tag.len() && !is_html_space(tag[i]) && !matches!(tag[i], b'>' | b'/') {
                    i += 1;
                }
                (start, i)
            };
            value = String::from_utf8_lossy(&tag[start..end]).into_owned();
        }
        if !attrs.iter().any(|(existing, _)| existing == &name) {
            attrs.push((name, value));
        }
    }
    attrs
}

fn charset_from_meta_content(value: &str) -> Option<&'static Encoding> {
    let lower = value.to_ascii_lowercase();
    let mut offset = 0usize;
    while let Some(index) = lower[offset..].find("charset") {
        offset += index + "charset".len();
        let rest = lower[offset..].trim_start_matches(|ch: char| ch.is_ascii_whitespace());
        let Some(after_eq) = rest.strip_prefix('=') else {
            continue;
        };
        let after_eq = after_eq.trim_start_matches(|ch: char| ch.is_ascii_whitespace());
        let label = after_eq
            .trim_start_matches(['\'', '"'])
            .split(|ch: char| ch.is_ascii_whitespace() || matches!(ch, '\'' | '"' | ';'))
            .next()
            .unwrap_or_default();
        if let Some(encoding) = label_encoding(Some(label)) {
            return Some(html_compatible_encoding(encoding));
        }
    }
    None
}

fn sniff_html_meta_encoding(bytes: &[u8]) -> Option<&'static Encoding> {
    let bytes = &bytes[..bytes.len().min(1024)];
    let mut i = 0usize;
    while i + 5 <= bytes.len() {
        if ascii_prefix_ignore_case(&bytes[i..], b"<!--") {
            if let Some(end) = bytes[i + 4..].windows(3).position(|window| window == b"-->") {
                i += 4 + end + 3;
                continue;
            }
            return None;
        }
        if bytes[i] != b'<' || !ascii_prefix_ignore_case(&bytes[i + 1..], b"meta") {
            i += 1;
            continue;
        }
        let after_name = i + 5;
        if after_name < bytes.len() && !is_html_space(bytes[after_name]) && bytes[after_name] != b'/' {
            i += 1;
            continue;
        }
        let mut end = after_name;
        let mut quote = None;
        while end < bytes.len() {
            let byte = bytes[end];
            if let Some(active) = quote {
                if byte == active {
                    quote = None;
                }
            } else if matches!(byte, b'\'' | b'"') {
                quote = Some(byte);
            } else if byte == b'>' {
                break;
            }
            end += 1;
        }
        if end >= bytes.len() {
            return None;
        }
        let attrs = parse_ascii_attrs(&bytes[after_name..end]);
        let mut got_pragma = false;
        let mut need_pragma = None;
        let mut charset = None;
        for (name, value) in attrs {
            match name.as_str() {
                "http-equiv" if value.eq_ignore_ascii_case("content-type") => got_pragma = true,
                "content" if charset.is_none() => {
                    if let Some(encoding) = charset_from_meta_content(&value) {
                        charset = Some(encoding);
                        need_pragma = Some(true);
                    }
                }
                "charset" => {
                    charset = label_encoding(Some(&value)).map(html_compatible_encoding);
                    need_pragma = Some(false);
                }
                _ => {}
            }
        }
        if let (Some(encoding), Some(needs_pragma)) = (charset, need_pragma) {
            if !needs_pragma || got_pragma {
                return Some(encoding);
            }
        }
        i = end + 1;
    }
    None
}

/// Decode an HTML byte stream before extracting inline scripts.
///
/// Priority follows the browser HTML encoding sniffing model: BOM, transport
/// charset, early meta declaration, then a caller-supplied/default browser
/// fallback. The fallback is explicitly marked uncertain because real browser
/// defaults are locale/container dependent.
#[must_use]
pub fn decode_html(
    bytes: &[u8],
    transport_content_type: Option<&str>,
    default_encoding: Option<&str>,
) -> DecodedHtml {
    let bom_encoding = Encoding::for_bom(bytes).map(|(encoding, _)| encoding);
    let (selected, decode_source, uncertain) = if let Some(encoding) = bom_encoding {
        (encoding, DecodeSource::Bom, false)
    } else if let Some(encoding) = transport_content_type.and_then(content_type_charset) {
        (encoding, DecodeSource::HtmlTransport, false)
    } else if let Some(encoding) = sniff_html_meta_encoding(bytes) {
        (encoding, DecodeSource::HtmlMeta, false)
    } else {
        let encoding = label_encoding(default_encoding).unwrap_or(WINDOWS_1252);
        (html_compatible_encoding(encoding), DecodeSource::HtmlFallback, true)
    };
    let (source, actual_encoding, had_errors) = selected.decode(bytes);
    DecodedHtml {
        source: source.into_owned(),
        encoding: actual_encoding.name().to_string(),
        decode_source,
        had_errors,
        uncertain,
        bom_encoding: bom_encoding.map(|encoding| encoding.name().to_string()),
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ScriptDecodeContext<'a> {
    pub kind: ScriptKind,
    pub script_charset: Option<&'a str>,
    pub document_encoding: Option<&'a str>,
    pub response_encoding: Option<&'a str>,
}

impl ScriptDecodeContext<'_> {
    #[must_use]
    pub const fn module() -> Self {
        Self {
            kind: ScriptKind::Module,
            script_charset: None,
            document_encoding: None,
            response_encoding: None,
        }
    }

    #[must_use]
    pub const fn classic_unknown() -> Self {
        Self {
            kind: ScriptKind::Classic,
            script_charset: None,
            document_encoding: None,
            response_encoding: None,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct DecodedScript {
    pub source: String,
    pub encoding: String,
    pub decode_source: DecodeSource,
    pub had_errors: bool,
    pub uncertain: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bom_encoding: Option<String>,
}

fn label_encoding(label: Option<&str>) -> Option<&'static Encoding> {
    label.and_then(|label| Encoding::for_label(label.trim().as_bytes()))
}

fn selected_encoding(context: ScriptDecodeContext<'_>) -> (&'static Encoding, DecodeSource, bool) {
    match context.kind {
        ScriptKind::Module => (UTF_8, DecodeSource::ModuleUtf8, false),
        ScriptKind::Classic => {
            if let Some(encoding) = label_encoding(context.script_charset) {
                return (encoding, DecodeSource::ScriptCharset, false);
            }
            if let Some(encoding) = label_encoding(context.document_encoding) {
                return (encoding, DecodeSource::DocumentEncoding, false);
            }
            // A detached corpus body does not carry the classic script's
            // embedding document encoding. UTF-8 replacement is useful for
            // analysis, but explicitly mark it uncertain rather than claiming
            // this is necessarily what the browser saw.
            (UTF_8, DecodeSource::Utf8Fallback, true)
        }
        ScriptKind::ClassicWorker => {
            if let Some(encoding) = label_encoding(context.response_encoding) {
                return (encoding, DecodeSource::WorkerResponseEncoding, false);
            }
            (UTF_8, DecodeSource::Utf8Default, false)
        }
    }
}

/// Decode raw script bytes with browser-oriented WHATWG encoding behavior.
///
/// A BOM is allowed to override the context-selected encoding, matching the
/// decoder behavior browsers apply before JavaScript parsing. Malformed byte
/// sequences become replacement characters and are reported through
/// `had_errors`; they never turn into a process-level failure.
#[must_use]
pub fn decode_script(bytes: &[u8], context: ScriptDecodeContext<'_>) -> DecodedScript {
    let (selected, selected_source, uncertain) = selected_encoding(context);
    let bom_encoding = Encoding::for_bom(bytes).map(|(encoding, _)| encoding.name().to_string());
    let (source, actual_encoding, had_errors) = selected.decode(bytes);
    DecodedScript {
        source: source.into_owned(),
        encoding: actual_encoding.name().to_string(),
        decode_source: if bom_encoding.is_some() {
            DecodeSource::Bom
        } else {
            selected_source
        },
        had_errors,
        uncertain,
        bom_encoding,
    }
}

#[cfg(test)]
mod tests {
    use super::{decode_script, DecodeSource, ScriptDecodeContext, ScriptKind};

    #[test]
    fn module_invalid_utf8_uses_replacement_without_failing() {
        let decoded = decode_script(b"let x='\x80';", ScriptDecodeContext::module());
        assert_eq!(decoded.source, "let x='\u{fffd}';");
        assert!(decoded.had_errors);
        assert!(!decoded.uncertain);
        assert_eq!(decoded.encoding, "UTF-8");
        assert_eq!(decoded.decode_source, DecodeSource::ModuleUtf8);
    }

    #[test]
    fn classic_document_encoding_uses_whatwg_windows_1252_alias() {
        let decoded = decode_script(
            b"// Copyright \xa9\nlet x=1;",
            ScriptDecodeContext {
                kind: ScriptKind::Classic,
                script_charset: None,
                document_encoding: Some("iso-8859-1"),
                response_encoding: None,
            },
        );
        assert_eq!(decoded.source, "// Copyright ©\nlet x=1;");
        assert!(!decoded.had_errors);
        assert!(!decoded.uncertain);
        assert_eq!(decoded.encoding, "windows-1252");
        assert_eq!(decoded.decode_source, DecodeSource::DocumentEncoding);
    }

    #[test]
    fn detached_classic_source_is_explicitly_uncertain() {
        let decoded = decode_script(b"// \xa9", ScriptDecodeContext::classic_unknown());
        assert_eq!(decoded.source, "// \u{fffd}");
        assert!(decoded.had_errors);
        assert!(decoded.uncertain);
        assert_eq!(decoded.decode_source, DecodeSource::Utf8Fallback);
    }

    #[test]
    fn bom_overrides_selected_legacy_encoding() {
        let decoded = decode_script(
            b"\xef\xbb\xbflet x=1;",
            ScriptDecodeContext {
                kind: ScriptKind::Classic,
                script_charset: Some("windows-1252"),
                document_encoding: None,
                response_encoding: None,
            },
        );
        assert_eq!(decoded.source, "let x=1;");
        assert_eq!(decoded.encoding, "UTF-8");
        assert_eq!(decoded.decode_source, DecodeSource::Bom);
        assert_eq!(decoded.bom_encoding.as_deref(), Some("UTF-8"));
    }

    #[test]
    fn html_transport_charset_precedes_meta() {
        let decoded = super::decode_html(
            b"<meta charset=utf-8><script>// \xa9</script>",
            Some("text/html; charset=windows-1252"),
            None,
        );
        assert_eq!(decoded.encoding, "windows-1252");
        assert_eq!(decoded.decode_source, DecodeSource::HtmlTransport);
        assert!(decoded.source.contains("// ©"));
        assert!(!decoded.uncertain);
    }

    #[test]
    fn html_meta_charset_decodes_before_inline_script_extraction() {
        let decoded = super::decode_html(
            b"<meta charset=windows-1252><script>const copyright='\xa9';</script>",
            None,
            None,
        );
        assert_eq!(decoded.encoding, "windows-1252");
        assert_eq!(decoded.decode_source, DecodeSource::HtmlMeta);
        assert!(decoded.source.contains("const copyright='©';"));
        assert!(!decoded.uncertain);
    }

    #[test]
    fn html_fallback_is_explicitly_uncertain() {
        let decoded = super::decode_html(b"<script>// \xa9</script>", None, None);
        assert_eq!(decoded.encoding, "windows-1252");
        assert_eq!(decoded.decode_source, DecodeSource::HtmlFallback);
        assert!(decoded.uncertain);
    }

}
