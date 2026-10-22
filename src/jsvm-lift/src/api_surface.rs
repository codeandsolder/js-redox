use anyhow::{anyhow, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, CallExpression, Expression, NewExpression, Program, VariableDeclarator,
    WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::symbol::SymbolId;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::collections::BTreeSet;

const STANDARD_BROWSER_API_ASSUMPTION: &str = "standard_browser_api_binding_semantics";

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Serialize)]
pub struct ApiCallsite {
    pub kind: String,
    pub start: u32,
    pub end: u32,
    pub line: usize,
    pub column: usize,
    pub callee: String,
    pub proof: String,
    pub standard_browser_api_semantics_required: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub method: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub method_expression: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub url: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub url_expression: Option<String>,
}

fn unparenthesized<'a>(mut expression: &'a Expression<'a>) -> &'a Expression<'a> {
    while let Expression::ParenthesizedExpression(parenthesized) = expression {
        expression = &parenthesized.expression;
    }
    expression
}

fn expression_symbol(scoping: &Scoping, expression: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()
}

fn symbol_is_stable(scoping: &Scoping, symbol: SymbolId) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| {
            let reference = scoping.get_reference(*reference_id);
            !reference.is_write() && !reference.flags().is_member_write_target()
        })
}

fn global_path(scoping: &Scoping, expression: &Expression<'_>) -> Option<String> {
    match unparenthesized(expression) {
        Expression::Identifier(identifier) => {
            let reference = scoping.get_reference(identifier.reference_id.get()?);
            reference
                .symbol_id()
                .is_none()
                .then(|| identifier.name.to_string())
        }
        Expression::StaticMemberExpression(member) if !member.optional => Some(format!(
            "{}.{}",
            global_path(scoping, &member.object)?,
            member.property.name
        )),
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            Some(format!(
                "{}.{}",
                global_path(scoping, &member.object)?,
                property.value
            ))
        }
        _ => None,
    }
}

fn static_string(expression: &Expression<'_>) -> Option<String> {
    match unparenthesized(expression) {
        Expression::StringLiteral(value) => Some(value.value.to_string()),
        Expression::TemplateLiteral(value) if value.expressions.is_empty() => {
            value.quasis.first().map(|quasi| {
                quasi
                    .value
                    .cooked
                    .as_ref()
                    .unwrap_or(&quasi.value.raw)
                    .to_string()
            })
        }
        Expression::BinaryExpression(binary) if binary.operator.as_str() == "+" => {
            let mut left = static_string(&binary.left)?;
            left.push_str(&static_string(&binary.right)?);
            Some(left)
        }
        _ => None,
    }
}

fn source_fragment(source: &str, span: Span) -> String {
    source
        .get(span.start as usize..(span.end as usize).min(source.len()))
        .unwrap_or_default()
        .to_string()
}

#[derive(Debug)]
struct LineIndex {
    starts: Vec<usize>,
}

impl LineIndex {
    fn new(source: &str) -> Self {
        let mut starts = vec![0];
        starts.extend(
            source
                .bytes()
                .enumerate()
                .filter_map(|(index, byte)| (byte == b'\n').then_some(index + 1)),
        );
        Self { starts }
    }

    fn line_column(&self, offset: u32) -> (usize, usize) {
        let offset = offset as usize;
        let index = self
            .starts
            .partition_point(|start| *start <= offset)
            .saturating_sub(1);
        (index + 1, offset.saturating_sub(self.starts[index]))
    }
}

fn allowed_fetch_path(path: &str) -> bool {
    matches!(
        path,
        "fetch" | "window.fetch" | "globalThis.fetch" | "self.fetch"
    )
}

fn allowed_send_beacon_path(path: &str) -> bool {
    matches!(
        path,
        "navigator.sendBeacon"
            | "window.navigator.sendBeacon"
            | "globalThis.navigator.sendBeacon"
            | "self.navigator.sendBeacon"
    )
}

fn allowed_websocket_path(path: &str) -> bool {
    matches!(
        path,
        "WebSocket" | "window.WebSocket" | "globalThis.WebSocket" | "self.WebSocket"
    )
}

fn allowed_xhr_path(path: &str) -> bool {
    matches!(
        path,
        "XMLHttpRequest"
            | "window.XMLHttpRequest"
            | "globalThis.XMLHttpRequest"
            | "self.XMLHttpRequest"
    )
}

fn exact_argument(
    source: &str,
    argument: Option<&oxc_ast::ast::Argument<'_>>,
) -> (Option<String>, Option<String>) {
    let Some(argument) = argument else {
        return (None, None);
    };
    let Some(expression) = argument.as_expression() else {
        return (None, Some(source_fragment(source, argument.span())));
    };
    (
        static_string(expression),
        Some(source_fragment(source, expression.span())),
    )
}

struct XhrBindingCollector<'c> {
    scoping: &'c Scoping,
    symbols: BTreeSet<SymbolId>,
}

impl<'a> Visit<'a> for XhrBindingCollector<'_> {
    fn visit_variable_declarator(&mut self, declarator: &VariableDeclarator<'a>) {
        if let (BindingPattern::BindingIdentifier(identifier), Some(initializer)) =
            (&declarator.id, declarator.init.as_ref())
        {
            let initializer = unparenthesized(initializer);
            if let Expression::NewExpression(new_expression) = initializer {
                if global_path(self.scoping, &new_expression.callee)
                    .as_deref()
                    .is_some_and(allowed_xhr_path)
                {
                    if let Some(symbol) = identifier.symbol_id.get() {
                        if symbol_is_stable(self.scoping, symbol) {
                            self.symbols.insert(symbol);
                        }
                    }
                }
            }
        }
        walk::walk_variable_declarator(self, declarator);
    }
}

struct Collector<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    xhr_symbols: &'c BTreeSet<SymbolId>,
    lines: LineIndex,
    callsites: BTreeSet<ApiCallsite>,
}

impl Collector<'_, '_> {
    fn push(
        &mut self,
        kind: &str,
        span: Span,
        callee: String,
        proof: &str,
        method: (Option<String>, Option<String>),
        url: (Option<String>, Option<String>),
    ) {
        let (method, method_expression) = method;
        let (url, url_expression) = url;
        let (line, column) = self.lines.line_column(span.start);
        self.callsites.insert(ApiCallsite {
            kind: kind.to_string(),
            start: span.start,
            end: span.end,
            line,
            column,
            callee,
            proof: proof.to_string(),
            standard_browser_api_semantics_required: true,
            method,
            method_expression,
            url,
            url_expression,
        });
    }

    fn xhr_receiver_symbol(&self, callee: &Expression<'_>) -> Option<SymbolId> {
        match unparenthesized(callee) {
            Expression::StaticMemberExpression(member)
                if !member.optional && member.property.name == "open" =>
            {
                expression_symbol(self.scoping, &member.object)
            }
            Expression::ComputedMemberExpression(member) if !member.optional => {
                let Expression::StringLiteral(property) = unparenthesized(&member.expression)
                else {
                    return None;
                };
                (property.value == "open")
                    .then(|| expression_symbol(self.scoping, &member.object))
                    .flatten()
            }
            _ => None,
        }
    }
}

impl<'a> Visit<'a> for Collector<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Some(path) = global_path(self.scoping, &call.callee) {
                if allowed_fetch_path(&path) {
                    let (url, url_expression) = exact_argument(self.source, call.arguments.first());
                    let method = (call.arguments.len() == 1
                        && call
                            .arguments
                            .first()
                            .is_some_and(|argument| argument.as_expression().is_some()))
                    .then(|| "GET".to_string());
                    self.push(
                        "fetch",
                        call.span,
                        path,
                        STANDARD_BROWSER_API_ASSUMPTION,
                        (method, None),
                        (url, url_expression),
                    );
                } else if allowed_send_beacon_path(&path) {
                    let (url, url_expression) = exact_argument(self.source, call.arguments.first());
                    self.push(
                        "send_beacon",
                        call.span,
                        path,
                        STANDARD_BROWSER_API_ASSUMPTION,
                        (Some("POST".to_string()), None),
                        (url, url_expression),
                    );
                }
            }

            if let Some(symbol) = self.xhr_receiver_symbol(&call.callee) {
                if self.xhr_symbols.contains(&symbol) {
                    let (method, method_expression) =
                        exact_argument(self.source, call.arguments.first());
                    let (url, url_expression) = exact_argument(self.source, call.arguments.get(1));
                    self.push(
                        "xhr_open",
                        call.span,
                        source_fragment(self.source, call.callee.span()),
                        "stable_symbol_initialized_from_standard_XMLHttpRequest",
                        (method, method_expression),
                        (url, url_expression),
                    );
                }
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &NewExpression<'a>) {
        if let Some(path) = global_path(self.scoping, &expression.callee) {
            if allowed_websocket_path(&path) {
                let (url, url_expression) =
                    exact_argument(self.source, expression.arguments.first());
                self.push(
                    "websocket",
                    expression.span,
                    path,
                    STANDARD_BROWSER_API_ASSUMPTION,
                    (None, None),
                    (url, url_expression),
                );
            }
        }
        walk::walk_new_expression(self, expression);
    }
}

fn parse_clean<'a>(
    allocator: &'a Allocator,
    source: &'a str,
    source_type: SourceType,
) -> Option<Program<'a>> {
    let parsed = parse_program(allocator, source, source_type);
    parsed.is_clean().then_some(parsed.program)
}

#[derive(Default)]
struct WithStatementDetector {
    found: bool,
}

impl<'a> Visit<'a> for WithStatementDetector {
    fn visit_with_statement(&mut self, _statement: &WithStatement<'a>) {
        self.found = true;
    }
}

fn contains_with_statement(program: &Program<'_>) -> bool {
    let mut detector = WithStatementDetector::default();
    detector.visit_program(program);
    detector.found
}

pub fn analyze_api_surface(source: &str) -> Result<Vec<ApiCallsite>> {
    for source_type in [SourceType::unambiguous(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let Some(program) = parse_clean(&allocator, source, source_type) else {
            continue;
        };
        if contains_with_statement(&program) {
            return Err(anyhow!(
                "with statement makes browser API identifier resolution environment-dependent"
            ));
        }

        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if !semantic.diagnostics.is_empty() {
            continue;
        }
        let scoping = semantic.semantic.scoping();

        let mut xhr = XhrBindingCollector {
            scoping,
            symbols: BTreeSet::new(),
        };
        xhr.visit_program(&program);

        let mut collector = Collector {
            source,
            scoping,
            xhr_symbols: &xhr.symbols,
            lines: LineIndex::new(source),
            callsites: BTreeSet::new(),
        };
        collector.visit_program(&program);
        let mut callsites = collector.callsites.into_iter().collect::<Vec<_>>();
        callsites.sort_by(|left, right| {
            (left.start, left.end, left.kind.as_str()).cmp(&(
                right.start,
                right.end,
                right.kind.as_str(),
            ))
        });
        return Ok(callsites);
    }

    Err(anyhow!(
        "Oxc could not semantically validate source as browser JavaScript"
    ))
}

#[cfg(test)]
mod tests {
    use super::analyze_api_surface;
    use anyhow::Result;

    #[test]
    fn records_exact_browser_api_calls_and_preserves_unresolved_arguments() -> Result<()> {
        let source = r#"
fetch("https://api.example.test/v1" + "/users");
fetch(`/relative`);
fetch("/unknown-method", options);
navigator.sendBeacon("https://api.example.test/beacon", body);
new WebSocket("wss://socket.example.test/ws");
const xhr = new XMLHttpRequest();
xhr.open("POST", "https://api.example.test/items");
xhr.send(payload);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 6, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(
            rows[0].url.as_deref(),
            Some("https://api.example.test/v1/users")
        );
        assert_eq!(rows[0].method.as_deref(), Some("GET"));
        assert_eq!(rows[1].url.as_deref(), Some("/relative"));
        assert_eq!(rows[2].method, None);
        assert_eq!(rows[2].url.as_deref(), Some("/unknown-method"));
        assert_eq!(rows[3].kind, "send_beacon");
        assert_eq!(rows[3].method.as_deref(), Some("POST"));
        assert_eq!(rows[4].kind, "websocket");
        assert_eq!(rows[5].kind, "xhr_open");
        assert_eq!(rows[5].method.as_deref(), Some("POST"));
        assert_eq!(rows[5].line, 8);
        Ok(())
    }

    #[test]
    fn rejects_shadowed_or_mutated_browser_bindings() -> Result<()> {
        let source = r#"
function fakeFetch(fetch) { fetch("https://fake.invalid/"); }
function fakeWindow(window) { window.fetch("https://fake.invalid/window"); }
function fakeSocket(WebSocket) { new WebSocket("wss://fake.invalid/"); }
let xhr = new XMLHttpRequest();
xhr = replacement;
xhr.open("GET", "https://fake.invalid/xhr");
fetch("https://real.example.test/");
fetch(...args);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 2, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(rows[0].url.as_deref(), Some("https://real.example.test/"));
        assert_eq!(rows[1].method, None);
        assert_eq!(rows[1].url, None);
        Ok(())
    }

    #[test]
    fn classic_script_semantics_fall_back_without_losing_global_sinks() -> Result<()> {
        let source = r#"
function duplicate() { return 1; }
function duplicate() { return 2; }
fetch("https://classic.example.test/");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 1, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(
            rows[0].url.as_deref(),
            Some("https://classic.example.test/")
        );
        Ok(())
    }

    #[test]
    fn with_statement_fails_closed() {
        let source = r#"with (scope) { fetch("https://ambiguous.example.test/"); }"#;
        assert!(analyze_api_surface(source).is_err());
    }

    #[test]
    fn xhr_symbols_are_scope_aware() -> Result<()> {
        let source = r#"
const xhr = new XMLHttpRequest();
function nested() {
    const xhr = { open() {} };
    xhr.open("GET", "https://fake.invalid/");
}
xhr.open("PUT", "https://real.example.test/value");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 1, "{rows:#?}");
        assert_eq!(rows[0].kind, "xhr_open");
        assert_eq!(rows[0].method.as_deref(), Some("PUT"));
        assert_eq!(
            rows[0].url.as_deref(),
            Some("https://real.example.test/value")
        );
        Ok(())
    }
}
