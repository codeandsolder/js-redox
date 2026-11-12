//! Structural outline for deeply nested calls in original lexical helpers.
//!
//! This is a source-navigation aid, not a proposed evaluation order or a
//! semantics-changing transformation. Nested callback bodies belong to their
//! own lexical function and never extend an enclosing call spine.
use oxc_allocator::Allocator;
use oxc_ast::ast::{ArrowFunctionExpression, CallExpression, Function};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::scope::ScopeFlags;
use rolldown_redox::ecmascript::parse_program;

const MIN_DEPTH: usize = 8;

struct Call {
    span: Span,
    callee: String,
    argument_spans: Vec<Span>,
    parent: Option<usize>,
    nesting: usize,
}

#[derive(Default)]
struct Collector<'s> {
    source: &'s str,
    calls: Vec<Call>,
    ancestors: Vec<usize>,
}

impl Collector<'_> {
    fn slot(&self, parent: usize, child: Span) -> String {
        self.calls[parent]
            .argument_spans
            .iter()
            .position(|span| span.start <= child.start && child.end <= span.end)
            .map_or_else(
                || "callee expression".to_owned(),
                |index| format!("argument {}", index + 1),
            )
    }
}

impl<'a> Visit<'a> for Collector<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        let parent = self.ancestors.last().copied();
        let index = self.calls.len();
        let callee = self
            .source
            .get(call.callee.span().start as usize..call.callee.span().end as usize)
            .unwrap_or("<unknown>");
        let nesting = parent.map_or(1, |id| self.calls[id].nesting + 1);
        self.calls.push(Call {
            span: call.span,
            callee: callee.to_owned(),
            argument_spans: call.arguments.iter().map(GetSpan::span).collect(),
            parent,
            nesting,
        });
        self.ancestors.push(index);
        walk::walk_call_expression(self, call);
        self.ancestors.pop();
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        let ancestors = std::mem::take(&mut self.ancestors);
        walk::walk_function(self, function, flags);
        self.ancestors = ancestors;
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        let ancestors = std::mem::take(&mut self.ancestors);
        walk::walk_arrow_function_expression(self, arrow);
        self.ancestors = ancestors;
    }
}

fn line_col(source: &str, byte: usize) -> (usize, usize) {
    let prefix = source.get(..byte).unwrap_or("");
    let line = prefix.bytes().filter(|b| *b == b'\n').count() + 1;
    let column = prefix.rsplit('\n').next().unwrap_or("").chars().count() + 1;
    (line, column)
}

fn label(raw: &str) -> String {
    if raw.len() > 80 || raw.contains('\n') || raw.contains('`') {
        "<computed callee>".to_owned()
    } else {
        raw.replace('|', "\\|")
    }
}

/// The deepest call ancestry in a parsed helper. Only sufficiently deep
/// chains get a Markdown sidecar, never replacing source or implying that
/// nested calls are unconditional or execute in the printed order.
pub fn deepest_call_spine(source: &str, helper_path: &str) -> Option<String> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    if !parsed.is_clean() {
        return None;
    }
    let mut collector = Collector {
        source,
        ..Collector::default()
    };
    collector.visit_program(&parsed.program);
    let deepest = collector
        .calls
        .iter()
        .enumerate()
        .max_by_key(|(_, call)| call.nesting)?;
    if deepest.1.nesting < MIN_DEPTH {
        return None;
    }
    let mut path = Vec::new();
    let mut cursor = Some(deepest.0);
    while let Some(index) = cursor {
        path.push(index);
        cursor = collector.calls[index].parent;
    }
    path.reverse();
    let mut markdown = format!(
        r"# Deep call nesting — {helper_path}

[Open the readable lexical helper](../{helper_path}). This is the
**deepest AST call-containment chain**, not an execution trace or a
suggested rewrite. Calls inside separate callback functions start
independent chains. Conditions, argument evaluation, computed
property access, and receiver binding retain their meanings only
in the original JavaScript. Byte ranges refer to that readable helper.

| Depth | Callee | Location | Nested within |
|---:|---|---|---|
"
    );
    for (depth, index) in path.into_iter().enumerate() {
        let call = &collector.calls[index];
        let (line, column) = line_col(source, call.span.start as usize);
        let slot = call.parent.map_or_else(
            || "root of this chain".to_owned(),
            |parent| collector.slot(parent, call.span),
        );
        markdown.push_str(&format!(
            "| {} | `{}` | line {line}:{column}, bytes {}–{} | {slot} |\n",
            depth + 1,
            label(&call.callee),
            call.span.start,
            call.span.end,
        ));
    }
    Some(markdown)
}

#[cfg(test)]
mod tests {
    use super::deepest_call_spine;

    #[test]
    fn shows_deep_argument_chain_with_exact_offsets() {
        let source = "function f(){return a(b(c(d(e(f(g(h(1))))))));}";
        let outline = deepest_call_spine(source, "helpers/f.js");
        assert!(outline.is_some());
        let outline = outline.unwrap_or_default();
        assert!(outline.contains("| 8 | `h`"), "{outline}");
        assert!(outline.contains("argument 1"), "{outline}");
        assert!(outline.contains("bytes "), "{outline}");
        assert!(outline.contains("../helpers/f.js"), "{outline}");
    }

    #[test]
    fn does_not_join_calls_across_callback_function_boundaries() {
        let source =
            "function f(){return outer(inner(function(){return a(b(c(d(e(f(g(1)))))));}));}";
        assert!(deepest_call_spine(source, "helpers/f.js").is_none());
    }

    #[test]
    fn ignores_short_calls_and_invalid_javascript() {
        assert!(deepest_call_spine("function f(){return a(b(c(1)));}", "helpers/f.js").is_none());
        assert!(deepest_call_spine("function f({", "helpers/f.js").is_none());
    }
}
