//! Literal-data rendering for generated Markdown browsing views.
use std::fmt::Write as _;

/// Keep source line boundaries and controls visible instead of allowing a
/// captured label or expression to introduce a new Markdown block.
fn single_line(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    for ch in value.chars() {
        match ch {
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() || matches!(ch, '\u{2028}' | '\u{2029}') => {
                let _ = write!(out, "\\u{:04x}", u32::from(ch));
            }
            ch => out.push(ch),
        }
    }
    out
}

/// Literal inline text, also safe inside a GFM table cell or link label.
/// These are presentation escapes, not changes to the source or its spans.
pub(crate) fn literal_text(value: &str) -> String {
    let safe = single_line(value);
    let mut chars = safe.chars().peekable();
    let mut out = String::with_capacity(safe.len());
    while let Some(ch) = chars.next() {
        match ch {
            '&' if chars
                .peek()
                .is_some_and(|next| next.is_ascii_alphabetic() || *next == '#') =>
            {
                out.push_str("&amp;")
            }
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '\\' | '`' | '*' | '_' | '~' | '[' | ']' | '|' | '#' => {
                out.push('\\');
                out.push(ch);
            }
            ch => out.push(ch),
        }
    }
    out
}

/// A CommonMark code span with an unambiguous delimiter and padding.
pub(crate) fn code_span(value: &str) -> String {
    let safe = single_line(value);
    if safe.is_empty() {
        return "`\"\"`".to_owned();
    }
    let longest = safe
        .split(|ch| ch != '`')
        .map(str::len)
        .max()
        .unwrap_or_default();
    let delimiter = "`".repeat(longest + 1);
    // CommonMark removes one surrounding space when both ends contain a
    // space and the contents are not all spaces. Preserve intentional spaces.
    let padding = longest != 0
        || (safe.starts_with(' ') && safe.ends_with(' ') && !safe.bytes().all(|b| b == b' '));
    if padding {
        format!("{delimiter} {safe} {delimiter}")
    } else {
        format!("{delimiter}{safe}{delimiter}")
    }
}

/// GitHub-flavored Markdown removes exactly the extra backslash before a
/// pipe during table parsing, including in code spans. Existing backslashes
/// remain part of the displayed source fragment.
pub(crate) fn table_code(value: &str) -> String {
    code_span(&value.replace('|', "\\|"))
}

/// URL-encode a path that its caller has already established is local.
/// A literal filename must not be parsed as a query, fragment or URL scheme.
pub(crate) fn link_destination(path: &str) -> String {
    let mut output = String::with_capacity(path.len());
    for byte in path.bytes() {
        if byte.is_ascii_alphanumeric() || b"/-_.~".contains(&byte) {
            output.push(char::from(byte));
        } else {
            let _ = write!(output, "%{byte:02X}");
        }
    }
    output
}

/// Fence is always longer than any backtick run in the supplied content.
/// The language is a fixed report-format identifier, never a captured value.
pub(crate) fn fenced_code(value: &str, language: &str) -> String {
    let longest = value
        .split(|ch| ch != '`')
        .map(str::len)
        .max()
        .unwrap_or_default();
    let fence = "`".repeat(3.max(longest + 1));
    format!("{fence}{language}\n{value}\n{fence}\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn code_spans_handle_delimiters_empty_text_and_padding() {
        for (source, expected) in [
            ("simple", "`simple`"),
            ("", "`\"\"`"),
            ("object`name", "`` object`name ``"),
            ("``", "``` `` ```"),
            (" a ", "`  a  `"),
            (" ", "` `"),
            ("\r\n\t\u{2028}\u{2029}", "`\\r\\n\\t\\u2028\\u2029`"),
        ] {
            assert_eq!(code_span(source), expected);
        }
    }

    #[test]
    fn literal_markup_and_local_paths_do_not_change_report_structure() {
        assert_eq!(
            literal_text("a\\|b\n[link](url)<tag>&amp;"),
            r"a\\\|b\\n\[link\](url)&lt;tag&gt;&amp;amp;"
        );
        assert_eq!(table_code("a||b"), r"`a\|\|b`");
        assert_eq!(table_code(r"a\|b"), r"`a\\|b`");
        assert_eq!(table_code("a+b"), "`a+b`");
        assert_eq!(
            link_destination("../name #?% (💡).js"),
            "../name%20%23%3F%25%20%28%F0%9F%92%A1%29.js"
        );
        assert_eq!(fenced_code("x\n```\ny", "js"), "````js\nx\n```\ny\n````\n");
    }
}
