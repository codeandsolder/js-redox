use oxc_allocator::Allocator;
use oxc_ast::ast::{Expression, Statement};
use oxc_parser::Parser;
use oxc_span::SourceType;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BrowserLegacyOpaqueSpan {
    pub start: u32,
    pub end: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BrowserLegacyCallAssignmentRecovery {
    pub source: String,
    pub opaque_spans: Vec<BrowserLegacyOpaqueSpan>,
}

fn expression_is_call(source: &str) -> bool {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, SourceType::cjs()).parse();
    if parsed.fatal_error || !parsed.diagnostics.is_empty() || parsed.program.body.len() != 1 {
        return false;
    }
    let Statement::ExpressionStatement(statement) = &parsed.program.body[0] else {
        return false;
    };
    fn is_call(expression: &Expression<'_>) -> bool {
        match expression {
            Expression::CallExpression(_) => true,
            Expression::ParenthesizedExpression(parenthesized) => {
                is_call(&parenthesized.expression)
            }
            _ => false,
        }
    }
    is_call(&statement.expression)
}

/// Build an offset-preserving parser view for the legacy web syntax where a
/// call expression appears as an assignment target (`callee() = value`). V8
/// still accepts this syntax and raises at runtime if the invalid reference is
/// actually assigned. Oxc intentionally rejects it because it is not a modern
/// ECMAScript AssignmentTarget.
///
/// The returned source is analysis-only: each invalid target is replaced by an
/// identifier of exactly the same byte length, and the replaced spans are
/// reported explicitly. Callers must never publish or execute the masked view.
#[must_use]
pub fn recover_browser_legacy_call_assignments(
    source: &str,
    source_type: SourceType,
) -> Option<BrowserLegacyCallAssignmentRecovery> {
    let mut masked = source.to_string();
    let mut opaque_spans = Vec::new();

    for _ in 0..64 {
        let allocator = Allocator::default();
        let parsed = Parser::new(&allocator, &masked, source_type).parse();
        if !parsed.fatal_error {
            return (!opaque_spans.is_empty()).then_some(BrowserLegacyCallAssignmentRecovery {
                source: masked,
                opaque_spans,
            });
        }
        if parsed.diagnostics.len() != 1 {
            return None;
        }
        let diagnostic = &parsed.diagnostics[0];
        if diagnostic.message.as_ref() != "Cannot assign to this expression" {
            return None;
        }
        let label = diagnostic.labels.first()?;
        let start = usize::try_from(label.offset()).ok()?;
        let len = usize::try_from(label.len()).ok()?;
        let end = start.checked_add(len)?;
        if len == 0
            || end > source.len()
            || !source.is_char_boundary(start)
            || !source.is_char_boundary(end)
        {
            return None;
        }
        if opaque_spans.iter().any(|span: &BrowserLegacyOpaqueSpan| {
            let span_start = span.start as usize;
            let span_end = span.end as usize;
            start < span_end && span_start < end
        }) {
            return None;
        }
        if !expression_is_call(&source[start..end]) {
            return None;
        }
        masked.replace_range(start..end, &"_".repeat(len));
        opaque_spans.push(BrowserLegacyOpaqueSpan {
            start: u32::try_from(start).ok()?,
            end: u32::try_from(end).ok()?,
        });
    }
    None
}

#[cfg(test)]
mod tests {
    use super::recover_browser_legacy_call_assignments;
    use oxc_span::SourceType;

    #[test]
    fn recovers_only_call_assignment_targets_without_moving_offsets() {
        let source = "before(); target(1) = value; after();";
        let recovery = recover_browser_legacy_call_assignments(source, SourceType::cjs()).unwrap();
        assert_eq!(recovery.source.len(), source.len());
        assert_eq!(recovery.opaque_spans.len(), 1);
        let span = recovery.opaque_spans[0];
        assert_eq!(&source[span.start as usize..span.end as usize], "target(1)");
        assert_eq!(
            &recovery.source[span.start as usize..span.end as usize],
            "_________"
        );
    }

    #[test]
    fn rejects_non_call_invalid_assignment_targets() {
        assert!(
            recover_browser_legacy_call_assignments("(1 + 2) = 3;", SourceType::cjs()).is_none()
        );
    }
}
