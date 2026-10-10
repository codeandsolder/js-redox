use oxc_allocator::Allocator;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceDirective {
    pub kind: String,
    pub raw: String,
    pub start: u32,
    pub end: u32,
}

fn directive_from_comment(source: &str, start: u32, end: u32) -> Option<SourceDirective> {
    let text = source.get(start as usize..end as usize)?.trim();
    let text = text
        .strip_prefix('#')
        .or_else(|| text.strip_prefix('@'))?
        .trim_start();

    let (kind, rest) = if let Some(rest) = text.strip_prefix("sourceMappingURL") {
        ("source_map", rest)
    } else {
        let rest = text.strip_prefix("sourceURL")?;
        ("source_url", rest)
    };

    let rest = rest.trim_start();
    let raw = rest.strip_prefix('=')?.trim_start();
    let raw = raw.split_whitespace().next().unwrap_or_default();
    let raw = raw.trim_matches(|character: char| matches!(character, '\'' | '"' | ';'));
    if raw.is_empty() {
        return None;
    }

    Some(SourceDirective {
        kind: kind.to_string(),
        raw: raw.to_string(),
        start,
        end,
    })
}

#[must_use]
pub fn source_directives(source: &str) -> Vec<SourceDirective> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    parsed
        .program
        .comments
        .iter()
        .filter_map(|comment| {
            let span = comment.content_span();
            directive_from_comment(source, span.start, span.end)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::source_directives;

    #[test]
    fn source_directives_are_comments_not_string_contents() {
        let source = r#"
            const fake_line = "//# sourceMappingURL=fake-line.js.map";
            const fake_block = `/*# sourceURL=https://fake.invalid/original.js */`;
            //# sourceMappingURL=real.js.map
            /*@ sourceURL=https://example.test/original.js */
        "#;
        let directives = source_directives(source);
        assert_eq!(directives.len(), 2);
        assert_eq!(directives[0].kind, "source_map");
        assert_eq!(directives[0].raw, "real.js.map");
        assert_eq!(directives[1].kind, "source_url");
        assert_eq!(directives[1].raw, "https://example.test/original.js");
    }

    #[test]
    fn source_directives_preserve_inline_data_urls() {
        let source = "//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozfQ==\n";
        let directives = source_directives(source);
        assert_eq!(directives.len(), 1);
        assert_eq!(
            directives[0].raw,
            "data:application/json;base64,eyJ2ZXJzaW9uIjozfQ=="
        );
    }
}
