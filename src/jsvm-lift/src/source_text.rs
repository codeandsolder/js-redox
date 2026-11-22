#[must_use]
pub fn preview(source: &str, start: u32, end: u32, cap: usize) -> String {
    let start = start as usize;
    let end = (end as usize).min(source.len());
    let raw = source.get(start..end).unwrap_or_default();
    let mut out = String::with_capacity(cap.min(raw.len()));
    for c in raw.chars() {
        if out.len() >= cap {
            break;
        }
        out.push(if c.is_whitespace() { ' ' } else { c });
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
    ranges: Vec<std::ops::Range<usize>>,
}

impl SourceLineIndex {
    pub(crate) fn new(source: &str) -> Self {
        Self {
            ranges: js_line_ranges(source).collect(),
        }
    }

    /// One-based line, zero-based UTF-8 byte column (not a CDP column).
    pub(crate) fn byte_line_column(&self, offset: usize) -> (usize, usize) {
        let index = self
            .ranges
            .partition_point(|range| range.start <= offset)
            .saturating_sub(1);
        (index + 1, offset - self.ranges[index].start)
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
        let range = self.ranges.get(local_line)?;
        let text = source.get(range.clone())?;
        Some(range.start + utf16_byte_offset(text, units)?)
    }
}

/// Exact boundary conversion, including EOF and rejecting surrogate midpoints.
fn utf16_byte_offset(text: &str, offset: usize) -> Option<usize> {
    let mut remaining = offset;
    for (index, ch) in text.char_indices() {
        if remaining == 0 {
            return Some(index);
        }
        remaining = remaining.checked_sub(ch.len_utf16())?;
    }
    (remaining == 0).then_some(text.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn javascript_line_positions_agree_across_byte_and_utf16_coordinates() {
        let source = "💡x\r\ny\rz\u{2028}💡\u{2029}";
        let index = SourceLineIndex::new(source);
        let lines = js_line_ranges(source)
            .map(|range| &source[range])
            .collect::<Vec<_>>();
        assert_eq!(lines, ["💡x", "y", "z", "💡", ""]);
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
                assert_eq!(index.byte_line_column(offset).0, row as usize + 1);
            }
        }
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
