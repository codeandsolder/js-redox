#[must_use]
pub fn preview(source: &str, start: u32, end: u32, cap: usize) -> String {
    let start = start as usize;
    let end = (end as usize).min(source.len());
    let raw = source.get(start..end).unwrap_or_default();
    collect_byte_prefix(
        raw.chars()
            .map(|ch| if ch.is_whitespace() { ' ' } else { ch }),
        cap,
    )
}

/// Return a borrowed prefix of at most cap Unicode scalar values and
/// whether content was omitted. Do not count or allocate the remaining text.
pub(crate) fn clip_chars(text: &str, cap: usize) -> (&str, bool) {
    if text.len() <= cap {
        return (text, false);
    }
    match text.char_indices().nth(cap) {
        Some((end, _)) => (&text[..end], true),
        None => (text, false),
    }
}

/// A lazy equivalent of joining `split_whitespace()` with single spaces.
/// Leading/trailing whitespace is omitted; inner runs become one ASCII space.
pub(crate) fn collapsed_whitespace(text: &str) -> impl Iterator<Item = char> + '_ {
    let mut chars = text.trim_start().chars().peekable();
    std::iter::from_fn(move || {
        let ch = chars.next()?;
        if !ch.is_whitespace() {
            return Some(ch);
        }
        while chars.next_if(|ch| ch.is_whitespace()).is_some() {}
        chars.peek().map(|_| ' ')
    })
}

/// Collect only complete scalar values fitting a UTF-8 byte cap. The prefix
/// remains valid even when the next scalar spans the limit.
pub(crate) fn collect_byte_prefix(chars: impl Iterator<Item = char>, cap: usize) -> String {
    let mut out = String::with_capacity(chars.size_hint().0.min(cap));
    if cap == 0 {
        return out;
    }
    for ch in chars {
        if ch.len_utf8() > cap - out.len() {
            break;
        }
        out.push(ch);
        if out.len() == cap {
            break;
        }
    }
    out
}

/// ECMAScript line boundaries, expressed in original UTF-8 byte offsets.
/// CRLF is one terminator; empty source and final empty lines are retained.
pub(crate) fn js_line_ranges(source: &str) -> impl Iterator<Item = std::ops::Range<usize>> + '_ {
    let mut remaining = Some((0, source));
    std::iter::from_fn(move || {
        let (start, text) = remaining.take()?;
        let Some(end) = text.find(['\r', '\n', '\u{2028}', '\u{2029}']) else {
            return Some(start..source.len());
        };
        let terminator = &text[end..];
        let width = if terminator.starts_with("\r\n") {
            2
        } else {
            terminator.chars().next()?.len_utf8()
        };
        let next = end + width;
        remaining = Some((start + next, &text[next..]));
        Some(start..start + end)
    })
}

/// Shared index for AST byte positions and original debugger coordinates.
#[derive(Debug)]
pub(crate) struct SourceLineIndex {
    starts: Vec<usize>,
}

impl SourceLineIndex {
    pub(crate) fn new(source: &str) -> Self {
        Self {
            starts: js_line_ranges(source).map(|range| range.start).collect(),
        }
    }

    pub(crate) const fn retained_bytes(&self) -> usize {
        self.starts
            .capacity()
            .saturating_mul(std::mem::size_of::<usize>())
    }

    pub(crate) fn line_text<'a>(&self, source: &'a str, local_line: usize) -> Option<&'a str> {
        let start = *self.starts.get(local_line)?;
        if let Some(&next) = self.starts.get(local_line + 1) {
            let terminated = source.get(start..next)?;
            terminated
                .strip_suffix("\r\n")
                .or_else(|| terminated.strip_suffix(['\r', '\n', '\u{2028}', '\u{2029}']))
        } else {
            source.get(start..)
        }
    }

    /// One-based line, zero-based UTF-8 byte column (not a CDP column).
    pub(crate) fn byte_line_column(&self, offset: usize) -> (usize, usize) {
        let index = self
            .starts
            .partition_point(|start| *start <= offset)
            .saturating_sub(1);
        (index + 1, offset - self.starts[index])
    }

    /// One-based line and Unicode scalar column for human-readable navigation.
    pub(crate) fn character_line_column(
        &self,
        source: &str,
        offset: usize,
    ) -> Option<(usize, usize)> {
        let (line, _) = self.byte_line_column(offset);
        let prefix = source.get(self.starts[line - 1]..offset)?;
        Some((line, prefix.chars().count() + 1))
    }

    /// CDP uses UTF-16 columns relative to document coordinates; the recorded
    /// script origin column applies only to the first local line. Reject
    /// surrogate midpoints, terminator interiors and out-of-range columns.
    pub(crate) fn cdp_byte_offset(
        &self,
        source: &str,
        line: u64,
        column: u64,
        start_line: u64,
        start_column: u64,
    ) -> Option<usize> {
        let local_line = usize::try_from(line.checked_sub(start_line)?).ok()?;
        let units =
            usize::try_from(column.checked_sub(if local_line == 0 { start_column } else { 0 })?)
                .ok()?;
        let text = self.line_text(source, local_line)?;
        Some(self.starts[local_line] + utf16_byte_offset(text, units).ok()?)
    }
}

/// Exact boundary conversion, including EOF and rejecting surrogate midpoints.
pub(crate) fn utf16_byte_offset(text: &str, offset: usize) -> anyhow::Result<usize> {
    let mut remaining = offset;
    for (index, ch) in text.char_indices() {
        if remaining == 0 {
            return Ok(index);
        }
        remaining = remaining
            .checked_sub(ch.len_utf16())
            .ok_or_else(|| anyhow::anyhow!("UTF-16 offset falls inside a surrogate pair"))?;
    }
    anyhow::ensure!(remaining == 0, "UTF-16 offset exceeds source length");
    Ok(text.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn previews_respect_byte_and_character_limits_without_splitting_scalars() {
        let source = "x💡é\u{2028}z";
        let end = u32::try_from(source.len()).unwrap_or_default();
        for (cap, expected) in [
            (0, ""),
            (1, "x"),
            (4, "x"),
            (5, "x💡"),
            (6, "x💡"),
            (7, "x💡é"),
            (8, "x💡é "),
            (9, "x💡é z"),
        ] {
            let result = preview(source, 0, end, cap);
            assert_eq!(result, expected);
            assert!(result.len() <= cap);
        }
        assert_eq!(clip_chars(source, 2), ("x💡", true));
        assert_eq!(clip_chars(source, 5), (source, false));
        assert_eq!(clip_chars("", 0), ("", false));
        assert_eq!(clip_chars("💡", 0), ("", true));
        assert_eq!(preview(source, 2, end, 99), "");
    }

    #[test]
    fn lazy_whitespace_collapse_matches_full_normalization() {
        for raw in ["", "   ", "  x  y  ", "💡\u{2028}\t\rñ\n", "one two three"] {
            let expected = raw.split_whitespace().collect::<Vec<_>>().join(" ");
            assert_eq!(collapsed_whitespace(raw).collect::<String>(), expected);
            for cap in 0..=expected.len() + 1 {
                let prefix = &expected[..expected.floor_char_boundary(cap.min(expected.len()))];
                assert_eq!(collect_byte_prefix(collapsed_whitespace(raw), cap), prefix);
            }
        }
    }

    #[test]
    fn javascript_line_positions_agree_across_byte_and_utf16_coordinates() {
        let source = "💡x\r\ny\rz\u{2028}💡\u{2029}";
        let index = SourceLineIndex::new(source);
        let lines = js_line_ranges(source)
            .map(|range| &source[range])
            .collect::<Vec<_>>();
        assert_eq!(lines, ["💡x", "y", "z", "💡", ""]);
        for (line, text) in lines.iter().enumerate() {
            assert_eq!(index.line_text(source, line), Some(*text));
        }
        assert_eq!(index.line_text(source, lines.len()), None);
        for (row, col, expected) in [
            (0, 0, Some(0)),
            (0, 1, None),
            (0, 2, Some(4)),
            (0, 3, Some(5)),
            (0, 4, None),
            (1, 0, Some(7)),
            (2, 0, Some(9)),
            (3, 0, Some(13)),
            (3, 1, None),
            (3, 2, Some(17)),
            (4, 0, Some(20)),
            (4, 1, None),
            (5, 0, None),
        ] {
            assert_eq!(index.cdp_byte_offset(source, row, col, 0, 0), expected);
            if let Some(offset) = expected {
                assert_eq!(
                    u64::try_from(index.byte_line_column(offset).0).ok(),
                    Some(row + 1)
                );
            }
        }
        assert_eq!(index.character_line_column(source, 4), Some((1, 2)));
        assert_eq!(index.byte_line_column(4), (1, 4));
        assert_eq!(index.character_line_column(source, 1), None);
        assert_eq!(index.character_line_column(source, 20), Some((5, 1)));
        assert_eq!(index.cdp_byte_offset(source, 5, 17, 5, 17), Some(0));
        assert_eq!(index.cdp_byte_offset(source, 5, 16, 5, 17), None);
        assert_eq!(index.cdp_byte_offset(source, 6, 0, 5, 17), Some(7));
        assert_eq!(index.cdp_byte_offset(source, 5, 0, 5, u64::MAX), None);
        assert_eq!(
            index.cdp_byte_offset(source, u64::MAX, u64::MAX, 0, 0),
            None
        );
        assert_eq!(
            SourceLineIndex::new("").cdp_byte_offset("", 0, 0, 0, 0),
            Some(0)
        );
    }
}
