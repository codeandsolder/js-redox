//! Structural source-navigation views for original lexical helpers.
//!
//! A deep-call spine and optional whitespace-only expression layout are
//! derived independently. Neither represents a proposed evaluation order or
//! a semantics-changing transformation. Nested callback bodies never extend
//! an enclosing call spine.
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    ArrowFunctionExpression, AssignmentExpression, BinaryExpression, CallExpression,
    ConditionalExpression, Expression, Function, LogicalExpression, SequenceExpression,
};
use oxc_ast_visit::{walk, Visit};
use oxc_codegen::Codegen;
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::scope::ScopeFlags;
use rolldown_redox::ecmascript::parse_program;
use std::collections::BTreeMap;

const MIN_DEPTH: usize = 8;
const MAX_INDENT_DEPTH: usize = 18;
const LONG_EXPRESSION_BYTES: usize = 160;
/// Keep inline assignments inspectable without repeating a giant RHS into
/// every ancestor row; the byte range still identifies its exact source.
const MAX_INLINE_ASSIGNMENT_RHS_BYTES: usize = 96;

/// Independent, non-executable navigation projections of the same original
/// lexical helper. The layout only inserts whitespace between AST tokens.
#[derive(Default)]
pub struct HelperNavigation {
    pub call_spine_markdown: Option<String>,
    pub assignment_outline_markdown: Option<String>,
    pub layout: String,
}

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

/// A source-backed containment tree of writes inside long expressions.
/// This is *not* execution order. Assignment target references form before
/// the RHS is evaluated; nested RHS writes may also be conditional.
struct AssignmentNode {
    span: Span,
    target_span: Span,
    target: String,
    operator: String,
    rhs: String,
    parent: Option<usize>,
    in_target_reference: bool,
    guard_depth: usize,
    nearest_guard: Option<String>,
}

#[derive(Default)]
struct AssignmentOutlineCollector<'s> {
    source: &'s str,
    nodes: Vec<AssignmentNode>,
    ancestors: Vec<usize>,
    guards: Vec<String>,
}

fn assignment_rhs_summary(source: &str, right: &Expression<'_>) -> String {
    let span = right.span();
    let length = span.end.saturating_sub(span.start) as usize;
    let fragment = source.get(span.start as usize..span.end as usize);
    if let Some(value) = fragment.filter(|value| {
        value.len() <= MAX_INLINE_ASSIGNMENT_RHS_BYTES
            && !value.contains(char::from(10))
            && !value.contains(char::from(13))
            && !value.contains(char::from(96))
    }) {
        // Code spans preserve JS operators (especially the pipe character)
        // without interpreting them as Markdown table delimiters.
        return format!(
            "{}{}{}",
            char::from(96),
            value.replace('|', "\\|"),
            char::from(96)
        );
    }
    let kind = match right {
        Expression::AssignmentExpression(_) => "assignment",
        Expression::SequenceExpression(_) => "sequence",
        Expression::BinaryExpression(_) => "binary",
        Expression::LogicalExpression(_) => "logical",
        Expression::ConditionalExpression(_) => "conditional",
        Expression::CallExpression(_) => "call",
        Expression::NewExpression(_) => "constructor",
        Expression::ArrayExpression(_) => "array",
        Expression::ObjectExpression(_) => "object",
        Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_) => "function",
        _ => "expression",
    };
    format!("*{kind} ({length} bytes; see source range)*")
}

impl<'a> Visit<'a> for AssignmentOutlineCollector<'_> {
    fn visit_assignment_expression(&mut self, expression: &AssignmentExpression<'a>) {
        let target_span = expression.left.span();
        let parent = self.ancestors.last().copied();
        let in_target_reference = parent.is_some_and(|index| {
            let parent_target = self.nodes[index].target_span;
            expression.span.start >= parent_target.start && expression.span.end <= parent_target.end
        });
        let target = self
            .source
            .get(target_span.start as usize..target_span.end as usize)
            .unwrap_or("<unavailable target>")
            .to_owned();
        let index = self.nodes.len();
        self.nodes.push(AssignmentNode {
            span: expression.span,
            target_span,
            target,
            operator: expression.operator.as_str().to_owned(),
            rhs: assignment_rhs_summary(self.source, &expression.right),
            parent,
            in_target_reference,
            guard_depth: self.guards.len(),
            nearest_guard: self.guards.last().cloned(),
        });
        self.ancestors.push(index);
        walk::walk_assignment_expression(self, expression);
        self.ancestors.pop();
    }

    fn visit_logical_expression(&mut self, expression: &LogicalExpression<'a>) {
        self.visit_expression(&expression.left);
        self.guards.push(format!(
            "logical {} right operand",
            expression.operator.as_str()
        ));
        self.visit_expression(&expression.right);
        self.guards.pop();
    }

    fn visit_conditional_expression(&mut self, expression: &ConditionalExpression<'a>) {
        self.visit_expression(&expression.test);
        self.guards.push("conditional true arm".to_owned());
        self.visit_expression(&expression.consequent);
        self.guards.pop();
        self.guards.push("conditional false arm".to_owned());
        self.visit_expression(&expression.alternate);
        self.guards.pop();
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        // A nested function body is deferred and must not be listed as part
        // of the enclosing initializer. It can have independent root writes.
        let ancestors = std::mem::take(&mut self.ancestors);
        let guards = std::mem::take(&mut self.guards);
        walk::walk_function(self, function, flags);
        self.ancestors = ancestors;
        self.guards = guards;
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        let ancestors = std::mem::take(&mut self.ancestors);
        let guards = std::mem::take(&mut self.guards);
        walk::walk_arrow_function_expression(self, arrow);
        self.ancestors = ancestors;
        self.guards = guards;
    }
}

fn assignment_outline(source: &str, program: &oxc_ast::ast::Program<'_>) -> Option<String> {
    let mut collector = AssignmentOutlineCollector {
        source,
        ..AssignmentOutlineCollector::default()
    };
    collector.visit_program(program);
    let nodes = &collector.nodes;
    let mut children = vec![Vec::new(); nodes.len()];
    for (index, node) in nodes.iter().enumerate() {
        if let Some(parent) = node.parent {
            children[parent].push(index);
        }
    }
    let roots = nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| {
            (node.parent.is_none()
                && node.span.end.saturating_sub(node.span.start) as usize > LONG_EXPRESSION_BYTES
                && !children[index].is_empty())
            .then_some(index)
        })
        .collect::<Vec<_>>();
    if roots.is_empty() {
        return None;
    }
    let mut output = String::from(
        r"# Nested assignment structure in long expressions

These are AST containment relationships, **not an execution trace** or a
proposed rewrite. Assignment references are resolved before their RHS.
Computed keys, getters and conversions may have effects. Logical and
conditional operands can be skipped, and functions created inside an
RHS have independent, deferred bodies. Guard annotations report only
the nearest enclosing guard and the total guard nesting depth.
Byte locations refer to the readable lexical helper. The assigned RHS is
quoted verbatim when short; long or multiline RHS expressions are described
by AST type and byte length, not evaluated or silently truncated.

",
    );
    fn emit(
        nodes: &[AssignmentNode],
        children: &[Vec<usize>],
        source: &str,
        index: usize,
        depth: usize,
        output: &mut String,
    ) {
        let node = &nodes[index];
        let (line, col) = line_col(source, node.span.start as usize);
        let target = if node.target.len() > 80
            || node.target.contains(char::from(96))
            || node.target.contains(char::from(10))
        {
            "<complex target>".to_owned()
        } else {
            node.target.replace('|', r"\|")
        };
        let role = if node.parent.is_none() {
            "root"
        } else if node.in_target_reference {
            "target reference"
        } else {
            "assignment value"
        };
        let guard = node.nearest_guard.as_ref().map_or_else(
            || "none".to_owned(),
            |guard| format!("{} ({} total)", guard, node.guard_depth),
        );
        output.push_str(&format!(
            "| {} | {} | {} {} | {} | {} | {} | {}:{} ({}–{}) |\n",
            depth,
            index + 1,
            target,
            node.operator,
            node.rhs,
            role,
            guard,
            line,
            col,
            node.span.start,
            node.span.end,
        ));
        for &child in &children[index] {
            emit(nodes, children, source, child, depth + 1, output);
        }
    }
    for root in roots {
        let node = &nodes[root];
        let (line, col) = line_col(source, node.span.start as usize);
        output.push_str(&format!(
            "\n## Long assignment at {line}:{col} ({} source bytes)\n\n",
            node.span.end - node.span.start,
        ));
        output.push_str("| Depth | ID | Assignment target/operator | Assigned RHS | Containment | Nearest guard | Source location |\n|---:|---:|---|---|---|---|---|\n");
        emit(nodes, &children, source, root, 0, &mut output);
        output.push(char::from(10));
    }
    Some(output)
}

/// Line-break opportunities at AST-verified operand boundaries. These are
/// *not* expression rewrites: every original byte is copied verbatim.
struct ExpressionBreaks<'s> {
    source: &'s str,
    depth: usize,
    positions: BTreeMap<usize, usize>,
}

impl ExpressionBreaks<'_> {
    fn operand(&mut self, parent: Span, operand: Span) {
        let Some(fragment) = self.source.get(parent.start as usize..parent.end as usize) else {
            return;
        };
        // Only unfold an expression that's too long *on the same source
        // line*. Existing multiline syntax, including comments, is retained.
        if fragment.len() <= LONG_EXPRESSION_BYTES || fragment.contains('\n') {
            return;
        }
        let position = operand.start as usize;
        if position <= parent.start as usize
            || position >= parent.end as usize
            || !self.source.is_char_boundary(position)
        {
            return;
        }
        let indent = self.depth.min(MAX_INDENT_DEPTH);
        self.positions
            .entry(position)
            .and_modify(|value| *value = (*value).max(indent))
            .or_insert(indent);
    }
}

impl<'a> Visit<'a> for ExpressionBreaks<'_> {
    fn visit_expression(&mut self, expression: &Expression<'a>) {
        self.depth += 1;
        walk::walk_expression(self, expression);
        self.depth -= 1;
    }

    fn visit_assignment_expression(&mut self, expr: &AssignmentExpression<'a>) {
        self.operand(expr.span, expr.right.span());
        walk::walk_assignment_expression(self, expr);
    }

    fn visit_logical_expression(&mut self, expr: &LogicalExpression<'a>) {
        self.operand(expr.span, expr.right.span());
        walk::walk_logical_expression(self, expr);
    }

    fn visit_binary_expression(&mut self, expr: &BinaryExpression<'a>) {
        self.operand(expr.span, expr.right.span());
        walk::walk_binary_expression(self, expr);
    }

    fn visit_conditional_expression(&mut self, expr: &ConditionalExpression<'a>) {
        self.operand(expr.span, expr.consequent.span());
        self.operand(expr.span, expr.alternate.span());
        walk::walk_conditional_expression(self, expr);
    }

    fn visit_sequence_expression(&mut self, expr: &SequenceExpression<'a>) {
        for item in expr.expressions.iter().skip(1) {
            self.operand(expr.span, item.span());
        }
        walk::walk_sequence_expression(self, expr);
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        let parent_depth = std::mem::replace(&mut self.depth, 0);
        walk::walk_function(self, function, flags);
        self.depth = parent_depth;
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        let parent_depth = std::mem::replace(&mut self.depth, 0);
        walk::walk_arrow_function_expression(self, arrow);
        self.depth = parent_depth;
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

/// Two independent navigational projections. A deep call chain supplies an
/// optional Markdown outline, while any long expression can receive a layout
/// even if the helper has no deeply nested calls.
pub fn helper_navigation(source: &str, helper_path: &str) -> Option<HelperNavigation> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    if !parsed.is_clean() {
        return None;
    }
    let assignment_outline_markdown = assignment_outline(source, &parsed.program);
    let mut collector = Collector {
        source,
        ..Collector::default()
    };
    collector.visit_program(&parsed.program);
    let deepest = collector
        .calls
        .iter()
        .enumerate()
        .max_by_key(|(_, call)| call.nesting)
        .filter(|(_, call)| call.nesting >= MIN_DEPTH);
    let mut path = Vec::new();
    if let Some((index, _)) = deepest {
        let mut cursor = Some(index);
        while let Some(index) = cursor {
            path.push(index);
            cursor = collector.calls[index].parent;
        }
        path.reverse();
    }
    // Insert whitespace only at parsed argument boundaries or immediately
    // before a call's closing paren. In particular, never rewrite callee
    // expressions, so direct eval and receiver identity remain unchanged.
    let mut expressions = ExpressionBreaks {
        source,
        depth: 0,
        positions: BTreeMap::new(),
    };
    expressions.visit_program(&parsed.program);
    let mut breaks = expressions.positions;
    if path.is_empty() && breaks.is_empty() && assignment_outline_markdown.is_none() {
        return None;
    }
    for &index in &path {
        let call = &collector.calls[index];
        if call.argument_spans.is_empty() {
            continue;
        }
        let end = usize::try_from(call.span.end).ok()?;
        let close = end.checked_sub(1)?;
        if source.as_bytes().get(close) != Some(&b')') {
            return None;
        }
        let depth = call.nesting.min(MAX_INDENT_DEPTH);
        for argument in &call.argument_spans {
            let start = usize::try_from(argument.start).ok()?;
            if !source.is_char_boundary(start) {
                return None;
            }
            breaks
                .entry(start)
                .and_modify(|d| *d = (*d).max(depth))
                .or_insert(depth);
        }
        breaks
            .entry(close)
            .and_modify(|d| *d = (*d).max(depth.saturating_sub(1)))
            .or_insert(depth.saturating_sub(1));
    }
    let mut layout = String::with_capacity(source.len() + breaks.len() * 40);
    let mut previous = 0;
    for (position, depth) in breaks {
        layout.push_str(source.get(previous..position)?);
        layout.push('\n');
        layout.push_str(&"  ".repeat(depth));
        previous = position;
    }
    layout.push_str(source.get(previous..)?);
    // Formatting is analyst-only, but it still must parse identically. The
    // source bytes are all retained; reject unexpected lexical consequences.
    let layout_arena = Allocator::default();
    let layout_parsed = parse_program(&layout_arena, &layout, SourceType::unambiguous());
    if !layout_parsed.is_clean()
        || Codegen::new().build(&parsed.program).code
            != Codegen::new().build(&layout_parsed.program).code
    {
        return None;
    }
    let layout_path = helper_path.trim_start_matches("helpers/");
    let call_spine_markdown = if path.is_empty() {
        None
    } else {
        let mut markdown = format!(
            r"# Deep call nesting — {helper_path}

[Open the readable lexical helper](../{helper_path}) or
[view its whitespace-only nested-call layout](../expression-layouts/{layout_path}).
Both preserve the original tokens; the layout is an analyst view, not the
original executable or a valid replacement for byte-sensitive JavaScript.
In addition to the deepest call chain, long single-line assignments,
sequences, comparisons, short-circuits and conditional operands are
indented at their original AST boundaries. No expression is hoisted.

This is the
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
    };
    Some(HelperNavigation {
        call_spine_markdown,
        assignment_outline_markdown,
        layout,
    })
}

#[cfg(test)]
mod tests {
    use super::helper_navigation;

    #[test]
    fn shows_deep_argument_chain_with_exact_offsets() {
        let source = "function f(){return a(b(c(d(e(f(g(h(1))))))));}";
        let outline = helper_navigation(source, "helpers/f.js");
        assert!(outline.is_some());
        let view = outline.unwrap_or_default();
        let markdown = view.call_spine_markdown.as_deref().unwrap_or_default();
        assert!(markdown.contains("| 8 | `h`"), "{markdown}");
        assert!(markdown.contains("argument 1"), "{markdown}");
        assert!(markdown.contains("bytes "), "{markdown}");
        assert!(markdown.contains("../helpers/f.js"), "{markdown}");
        assert!(
            markdown.contains("../expression-layouts/f.js"),
            "{markdown}"
        );
        assert!(view.layout.lines().count() > 10, "{}", view.layout);
        assert_eq!(
            source
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>(),
            view.layout
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>(),
        );
    }

    #[test]
    fn unfolds_long_effectful_expression_without_hoisting() {
        let source = "function f(U,H){((Hm=((U.a=1,U.b=2,U.c=3,U.d=4,U.e=5,U.f=6,U.g=7,U.h=8,U.i=9,U.j=10,U.k=11,U.l=12,U.m=13,U.n=14,U.o=15,U.p=16,U.q=17,U.r=18,U.s=19,U.t=20,U.u=21,U.v=22,U.w=23,U.x=24,U.y=25,U.z=26),H.length<2&&H)));return a(b(c(d(e(f(g(h(Hm))))))));}";
        let view = helper_navigation(source, "helpers/f.js").unwrap_or_default();
        assert!(view.layout.contains("U.q=17"), "{}", view.layout);
        assert!(view.layout.lines().count() > 20, "{}", view.layout);
        assert!(view.layout.contains("U.m=13"), "{}", view.layout);
        assert_eq!(
            source
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>(),
            view.layout
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>(),
        );
    }

    #[test]
    fn long_expression_without_deep_calls_still_gets_layout() {
        let source = "function init(U){return (U.a=1,U.b=2,U.c=3,U.d=4,U.e=5,U.f=6,U.g=7,U.h=8,U.i=9,U.j=10,U.k=11,U.l=12,U.m=13,U.n=14,U.o=15,U.p=16,U.q=17,U.r=18,U.s=19,U.t=20,U.u=21,U.v=22,U.w=23,U.x=24,U.y=25,U.z=26);}";
        let view = helper_navigation(source, "helpers/init.js").unwrap_or_default();
        assert!(view.call_spine_markdown.is_none());
        assert!(view.layout.lines().count() > 10, "{}", view.layout);
        assert_eq!(
            source
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>(),
            view.layout
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect::<String>(),
        );
    }

    #[test]
    fn does_not_join_calls_across_callback_function_boundaries() {
        let source =
            "function f(){return outer(inner(function(){return a(b(c(d(e(f(g(1)))))));}));}";
        assert!(helper_navigation(source, "helpers/f.js").is_none());
    }

    #[test]
    fn outlines_nested_writes_with_guards_without_merging_callback_bodies() {
        let source = "function f(U,flag){let result;result=(U.a=1,flag&&(U.b=2),U.c=(U.d=3),U.e=4,U.f=5,U.g=6,U.h=7,U.i=8,U.j=9,U.k=10,U.l=11,U.m=12,U.n=13,U.o=14,U.p=15,U.q=16,U.r=17,U.s=18,U.t=19,U.fn=function(){hidden=123;},U.u=20);return result;}";
        let view = helper_navigation(source, "helpers/f.js").unwrap_or_default();
        let outline = view.assignment_outline_markdown.unwrap_or_default();
        assert!(outline.contains("result ="), "{outline}");
        assert!(outline.contains("U.b ="), "{outline}");
        assert!(outline.contains("logical && right operand"), "{outline}");
        assert!(outline.contains("U.d ="), "{outline}");
        assert!(
            !outline.contains("hidden ="),
            "nested function assignments are deferred: {outline}"
        );
        assert!(outline.contains("not an execution trace"), "{outline}");
        assert!(outline.contains("Source location"), "{outline}");
    }

    #[test]
    fn describes_real_assigned_values_and_bounded_complex_expression_rhs() {
        let source = "function f(U){Hm=(U.a=void 0,U.b=[],U.c=false,U.d=0,U.e=(U.f=1,2),U.g=(U.h=1,U.i=2,U.j=3,U.k=4,U.l=5,U.m=6,U.n=7,U.o=8,U.p=9,U.q=10,U.r=11,U.s=12,U.t=13,U.u=14,U.v=15,U.w=16,U.x=17,U.y=18,U.z=19));return Hm;}";
        let view = helper_navigation(source, "helpers/f.js").unwrap_or_default();
        let outline = view.assignment_outline_markdown.unwrap_or_default();
        for (target, expected) in [
            ("U.a", "void 0"),
            ("U.b", "[]"),
            ("U.c", "false"),
            ("U.d", "0"),
        ] {
            let text = format!(
                "{target} = | {}{expected}{}",
                char::from(96),
                char::from(96)
            );
            assert!(
                outline.contains(&text),
                "missing exact assigned value {text}: {outline}"
            );
        }
        assert!(outline.contains("Assigned RHS"), "{outline}");
        assert!(outline.contains("bytes; see source range"), "{outline}");
        assert!(outline.contains("U.f ="), "{outline}");
    }

    #[test]
    fn ignores_short_calls_and_invalid_javascript() {
        assert!(helper_navigation("function f(){return a(b(c(1)));}", "helpers/f.js").is_none());
        assert!(helper_navigation("function f({", "helpers/f.js").is_none());
    }
}
