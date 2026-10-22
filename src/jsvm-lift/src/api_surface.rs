use anyhow::{anyhow, Result};
use jsvm_safe_core::ProvenConstantEnvironment;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, CallExpression, ComputedMemberExpression, Expression, NewExpression,
    ObjectPropertyKind, Program, PropertyKind, StaticMemberExpression, VariableDeclarator,
    WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping, SemanticBuilder};
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

fn symbol_is_safe_xhr_receiver(
    scoping: &Scoping,
    symbol: SymbolId,
    safe_member_refs: &BTreeSet<ReferenceId>,
) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| {
            let reference = scoping.get_reference(*reference_id);
            safe_member_refs.contains(reference_id)
                && !reference.is_write()
                && !reference.flags().is_member_write_target()
        })
}

fn direct_reference_id(expression: &Expression<'_>) -> Option<ReferenceId> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    identifier.reference_id.get()
}

fn safe_xhr_member_name(name: &str) -> bool {
    !matches!(name, "constructor" | "__proto__" | "prototype")
}

#[derive(Default)]
struct SafeMemberReferenceCollector {
    refs: BTreeSet<ReferenceId>,
}

impl<'a> Visit<'a> for SafeMemberReferenceCollector {
    fn visit_static_member_expression(&mut self, member: &StaticMemberExpression<'a>) {
        if !member.optional && safe_xhr_member_name(member.property.name.as_str()) {
            if let Some(reference_id) = direct_reference_id(&member.object) {
                self.refs.insert(reference_id);
            }
        }
        walk::walk_static_member_expression(self, member);
    }

    fn visit_computed_member_expression(&mut self, member: &ComputedMemberExpression<'a>) {
        if !member.optional {
            if let Expression::StringLiteral(property) = unparenthesized(&member.expression) {
                if safe_xhr_member_name(property.value.as_str()) {
                    if let Some(reference_id) = direct_reference_id(&member.object) {
                        self.refs.insert(reference_id);
                    }
                }
            }
        }
        walk::walk_computed_member_expression(self, member);
    }
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

fn static_string(
    expression: &Expression<'_>,
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
) -> Option<String> {
    constants.exact_string(expression, scoping)
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

fn allowed_request_init_method_prototype_path(path: &str) -> bool {
    matches!(
        path,
        "Object.prototype.method"
            | "window.Object.prototype.method"
            | "globalThis.Object.prototype.method"
            | "self.Object.prototype.method"
    )
}

fn sink_family(path: &str) -> Option<&'static str> {
    if allowed_fetch_path(path) {
        Some("fetch")
    } else if allowed_send_beacon_path(path) {
        Some("send_beacon")
    } else if allowed_websocket_path(path) {
        Some("websocket")
    } else if allowed_xhr_path(path) {
        Some("xhr")
    } else if allowed_request_init_method_prototype_path(path) {
        Some("request_init_method_prototype")
    } else {
        None
    }
}

fn assignment_global_path(
    scoping: &Scoping,
    target: &oxc_ast::ast::AssignmentTarget<'_>,
) -> Option<String> {
    match target {
        oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(identifier) => {
            let reference = scoping.get_reference(identifier.reference_id.get()?);
            reference
                .symbol_id()
                .is_none()
                .then(|| identifier.name.to_string())
        }
        oxc_ast::ast::AssignmentTarget::StaticMemberExpression(member) if !member.optional => {
            Some(format!(
                "{}.{}",
                global_path(scoping, &member.object)?,
                member.property.name
            ))
        }
        oxc_ast::ast::AssignmentTarget::ComputedMemberExpression(member) if !member.optional => {
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

fn simple_assignment_global_path(
    scoping: &Scoping,
    target: &oxc_ast::ast::SimpleAssignmentTarget<'_>,
) -> Option<String> {
    match target {
        oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) => {
            let reference = scoping.get_reference(identifier.reference_id.get()?);
            reference
                .symbol_id()
                .is_none()
                .then(|| identifier.name.to_string())
        }
        oxc_ast::ast::SimpleAssignmentTarget::StaticMemberExpression(member)
            if !member.optional =>
        {
            Some(format!(
                "{}.{}",
                global_path(scoping, &member.object)?,
                member.property.name
            ))
        }
        oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member)
            if !member.optional =>
        {
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

struct SinkMutationCollector<'c> {
    scoping: &'c Scoping,
    mutated: BTreeSet<&'static str>,
}

impl SinkMutationCollector<'_> {
    fn record(&mut self, path: Option<String>) {
        if let Some(family) = path.as_deref().and_then(sink_family) {
            self.mutated.insert(family);
        }
    }
}

impl<'a> Visit<'a> for SinkMutationCollector<'_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        self.record(assignment_global_path(self.scoping, &assignment.left));
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_update_expression(&mut self, update: &oxc_ast::ast::UpdateExpression<'a>) {
        self.record(simple_assignment_global_path(
            self.scoping,
            &update.argument,
        ));
        walk::walk_update_expression(self, update);
    }

    fn visit_unary_expression(&mut self, unary: &oxc_ast::ast::UnaryExpression<'a>) {
        if unary.operator.as_str() == "delete" {
            self.record(global_path(self.scoping, &unary.argument));
        }
        walk::walk_unary_expression(self, unary);
    }
}

fn exact_argument(
    source: &str,
    argument: Option<&oxc_ast::ast::Argument<'_>>,
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
) -> (Option<String>, Option<String>) {
    let Some(argument) = argument else {
        return (None, None);
    };
    let Some(expression) = argument.as_expression() else {
        return (None, Some(source_fragment(source, argument.span())));
    };
    (
        static_string(expression, scoping, constants),
        Some(source_fragment(source, expression.span())),
    )
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum FetchInitMethod {
    Missing,
    NoOwnMethod,
    Exact { value: String, expression: String },
    Unknown,
}

fn fetch_init_method(
    source: &str,
    argument: Option<&oxc_ast::ast::Argument<'_>>,
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
) -> FetchInitMethod {
    let Some(argument) = argument else {
        return FetchInitMethod::Missing;
    };
    let Some(expression) = argument.as_expression() else {
        return FetchInitMethod::Unknown;
    };
    let Expression::ObjectExpression(object) = unparenthesized(expression) else {
        return FetchInitMethod::Unknown;
    };

    let mut state = FetchInitMethod::NoOwnMethod;
    for item in &object.properties {
        let ObjectPropertyKind::ObjectProperty(property) = item else {
            state = FetchInitMethod::Unknown;
            continue;
        };

        let static_name = property.key.static_name();
        if property.computed && static_name.is_none() {
            state = FetchInitMethod::Unknown;
            continue;
        }
        let Some(name) = static_name else {
            state = FetchInitMethod::Unknown;
            continue;
        };

        let prototype_setter = name == "__proto__"
            && !property.computed
            && !property.method
            && !property.shorthand
            && property.kind == PropertyKind::Init;
        if prototype_setter {
            if !matches!(state, FetchInitMethod::Exact { .. }) {
                state = FetchInitMethod::Unknown;
            }
            continue;
        }

        if name != "method" {
            continue;
        }

        if property.kind != PropertyKind::Init || property.method {
            state = FetchInitMethod::Unknown;
            continue;
        }

        state = if let Some(value) = static_string(&property.value, scoping, constants) {
            FetchInitMethod::Exact {
                value,
                expression: source_fragment(source, property.value.span()),
            }
        } else {
            FetchInitMethod::Unknown
        };
    }
    state
}

fn fetch_method(
    source: &str,
    arguments: &[oxc_ast::ast::Argument<'_>],
    input_is_static_string: bool,
    request_init_method_prototype_mutated: bool,
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
) -> (Option<String>, Option<String>) {
    if arguments
        .first()
        .is_some_and(|argument| argument.as_expression().is_none())
    {
        return (None, None);
    }

    match fetch_init_method(source, arguments.get(1), scoping, constants) {
        FetchInitMethod::Exact { value, expression } => (Some(value), Some(expression)),
        FetchInitMethod::Missing if input_is_static_string => (Some("GET".to_string()), None),
        FetchInitMethod::NoOwnMethod
            if input_is_static_string && !request_init_method_prototype_mutated =>
        {
            (Some("GET".to_string()), None)
        }
        FetchInitMethod::Missing | FetchInitMethod::NoOwnMethod | FetchInitMethod::Unknown => {
            (None, None)
        }
    }
}

struct XhrBindingCollector<'c> {
    scoping: &'c Scoping,
    safe_member_refs: &'c BTreeSet<ReferenceId>,
    standard_xhr_available: bool,
    symbols: BTreeSet<SymbolId>,
}

impl<'a> Visit<'a> for XhrBindingCollector<'_> {
    fn visit_variable_declarator(&mut self, declarator: &VariableDeclarator<'a>) {
        if let (BindingPattern::BindingIdentifier(identifier), Some(initializer)) =
            (&declarator.id, declarator.init.as_ref())
        {
            let initializer = unparenthesized(initializer);
            if let Expression::NewExpression(new_expression) = initializer {
                if self.standard_xhr_available
                    && global_path(self.scoping, &new_expression.callee)
                        .as_deref()
                        .is_some_and(allowed_xhr_path)
                {
                    if let Some(symbol) = identifier.symbol_id.get() {
                        if symbol_is_safe_xhr_receiver(self.scoping, symbol, self.safe_member_refs)
                        {
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
    constants: &'c ProvenConstantEnvironment,
    mutated_sinks: &'c BTreeSet<&'static str>,
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
                if allowed_fetch_path(&path) && !self.mutated_sinks.contains("fetch") {
                    let (url, url_expression) = exact_argument(
                        self.source,
                        call.arguments.first(),
                        self.scoping,
                        self.constants,
                    );
                    let method = fetch_method(
                        self.source,
                        &call.arguments,
                        url.is_some(),
                        self.mutated_sinks.contains("request_init_method_prototype"),
                        self.scoping,
                        self.constants,
                    );
                    self.push(
                        "fetch",
                        call.span,
                        path,
                        STANDARD_BROWSER_API_ASSUMPTION,
                        method,
                        (url, url_expression),
                    );
                } else if allowed_send_beacon_path(&path)
                    && !self.mutated_sinks.contains("send_beacon")
                {
                    let (url, url_expression) = exact_argument(
                        self.source,
                        call.arguments.first(),
                        self.scoping,
                        self.constants,
                    );
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
                    let (method, method_expression) = exact_argument(
                        self.source,
                        call.arguments.first(),
                        self.scoping,
                        self.constants,
                    );
                    let (url, url_expression) = exact_argument(
                        self.source,
                        call.arguments.get(1),
                        self.scoping,
                        self.constants,
                    );
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
            if allowed_websocket_path(&path) && !self.mutated_sinks.contains("websocket") {
                let (url, url_expression) = exact_argument(
                    self.source,
                    expression.arguments.first(),
                    self.scoping,
                    self.constants,
                );
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
        let constants = ProvenConstantEnvironment::collect(&program, scoping);

        let mut safe_member_refs = SafeMemberReferenceCollector::default();
        safe_member_refs.visit_program(&program);

        let mut mutations = SinkMutationCollector {
            scoping,
            mutated: BTreeSet::new(),
        };
        mutations.visit_program(&program);

        let mut xhr = XhrBindingCollector {
            scoping,
            safe_member_refs: &safe_member_refs.refs,
            standard_xhr_available: !mutations.mutated.contains("xhr"),
            symbols: BTreeSet::new(),
        };
        xhr.visit_program(&program);

        let mut collector = Collector {
            source,
            scoping,
            constants: &constants,
            mutated_sinks: &mutations.mutated,
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
    fn resolves_only_available_proven_const_strings() -> Result<()> {
        let source = r#"
const scheme = "https://";
const host = "api.example.test";
const url = scheme + host + "/v1";
const method = "PA" + "TCH";
fetch(url, { method });
navigator.sendBeacon(url, payload);
const xhr = new XMLHttpRequest();
xhr.open(method, url);
const socket = "wss://socket.example.test/ws";
new WebSocket(socket);
fetch(later);
const later = "https://later.example.test/";
let mutable = "https://mutable.example.test/";
fetch(mutable);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 6, "{rows:#?}");
        assert_eq!(rows[0].url.as_deref(), Some("https://api.example.test/v1"));
        assert_eq!(rows[0].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[0].url_expression.as_deref(), Some("url"));
        assert_eq!(rows[0].method_expression.as_deref(), Some("method"));
        assert_eq!(rows[1].url.as_deref(), Some("https://api.example.test/v1"));
        assert_eq!(rows[2].kind, "xhr_open");
        assert_eq!(rows[2].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[2].url.as_deref(), Some("https://api.example.test/v1"));
        assert_eq!(rows[3].kind, "websocket");
        assert_eq!(rows[3].url.as_deref(), Some("wss://socket.example.test/ws"));
        assert_eq!(rows[4].url, None, "TDZ/forward const must stay unresolved");
        assert_eq!(rows[4].url_expression.as_deref(), Some("later"));
        assert_eq!(rows[5].url, None, "mutable let must stay unresolved");
        assert_eq!(rows[5].url_expression.as_deref(), Some("mutable"));
        Ok(())
    }

    #[test]
    fn fetch_inline_init_method_respects_object_overwrite_order() -> Result<()> {
        let source = r#"
fetch("https://api.example.test/post", { method: "POST" });
fetch("https://api.example.test/default", { headers: { "x-test": "1" } });
fetch("https://api.example.test/later-exact", { ...opts, method: "PATCH" });
fetch("https://api.example.test/later-spread", { method: "DELETE", ...opts });
fetch("https://api.example.test/later-dynamic", { method: "PUT", [key]: "POST" });
fetch("https://api.example.test/later-method", { [key]: "POST", method: "PUT" });
const request = new Request("https://api.example.test/original", { method: "POST" });
fetch(request, { method: "PATCH" });
fetch(request, { headers: {} });
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 8, "{rows:#?}");

        assert_eq!(rows[0].method.as_deref(), Some("POST"));
        assert_eq!(rows[0].method_expression.as_deref(), Some(r#""POST""#));
        assert_eq!(rows[1].method.as_deref(), Some("GET"));
        assert_eq!(rows[2].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[3].method, None);
        assert_eq!(rows[4].method, None);
        assert_eq!(rows[5].method.as_deref(), Some("PUT"));
        assert_eq!(rows[6].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[6].url, None);
        assert_eq!(rows[7].method, None);
        assert_eq!(rows[7].url, None);
        Ok(())
    }

    #[test]
    fn fetch_inline_init_does_not_confuse_inherited_method_with_absence() -> Result<()> {
        let source = r#"
fetch("https://api.example.test/proto-only", { __proto__: { method: "POST" } });
fetch("https://api.example.test/own-before", { method: "PUT", __proto__: { method: "POST" } });
fetch("https://api.example.test/own-after", { __proto__: { method: "POST" }, method: "PATCH" });
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert_eq!(rows[0].method, None);
        assert_eq!(rows[1].method.as_deref(), Some("PUT"));
        assert_eq!(rows[2].method.as_deref(), Some("PATCH"));
        Ok(())
    }

    #[test]
    fn visible_object_prototype_method_mutation_only_blocks_inherited_default() -> Result<()> {
        let source = r#"
Object.prototype.method = "POST";
fetch("https://api.example.test/inline-empty", {});
fetch("https://api.example.test/no-init");
fetch("https://api.example.test/own", { method: "PATCH" });
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert_eq!(rows[0].method, None);
        assert_eq!(rows[1].method.as_deref(), Some("GET"));
        assert_eq!(rows[2].method.as_deref(), Some("PATCH"));
        Ok(())
    }

    #[test]
    fn fetch_request_object_does_not_claim_default_get() -> Result<()> {
        let source = r#"
const request = new Request("https://api.example.test/items", { method: "POST" });
fetch(request);
fetch("https://api.example.test/default-get");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 2, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(rows[0].method, None);
        assert_eq!(rows[0].url, None);
        assert_eq!(rows[1].method.as_deref(), Some("GET"));
        assert_eq!(
            rows[1].url.as_deref(),
            Some("https://api.example.test/default-get")
        );
        Ok(())
    }

    #[test]
    fn rejects_visibly_monkey_patched_standard_sink_families() -> Result<()> {
        let source = r#"
fetch = fakeFetch;
fetch("https://fake.invalid/fetch");
window["fetch"]("https://fake.invalid/window-fetch");
navigator.sendBeacon = fakeBeacon;
navigator.sendBeacon("https://fake.invalid/beacon", body);
WebSocket = FakeSocket;
new WebSocket("wss://fake.invalid/socket");
XMLHttpRequest = FakeXhr;
const xhr = new XMLHttpRequest();
xhr.open("GET", "https://fake.invalid/xhr");
"#;
        let rows = analyze_api_surface(source)?;
        assert!(rows.is_empty(), "{rows:#?}");

        let selective = r#"
window.fetch = fakeFetch;
window.fetch("https://fake.invalid/fetch");
navigator.sendBeacon("https://real.example.test/beacon", body);
"#;
        let rows = analyze_api_surface(selective)?;
        assert_eq!(rows.len(), 1, "{rows:#?}");
        assert_eq!(rows[0].kind, "send_beacon");
        assert_eq!(
            rows[0].url.as_deref(),
            Some("https://real.example.test/beacon")
        );
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
    fn xhr_receiver_must_not_escape_or_reach_prototype_mutation() -> Result<()> {
        let source = r#"
const aliased = new XMLHttpRequest();
const alias = aliased;
alias.open = fakeOpen;
aliased.open("GET", "https://fake.invalid/alias");
const passed = new XMLHttpRequest();
unknown(passed);
passed.open("GET", "https://fake.invalid/passed");
const prototype = new XMLHttpRequest();
prototype.constructor.prototype.open = fakeOpen;
prototype.open("GET", "https://fake.invalid/prototype");
const direct = new XMLHttpRequest();
direct.open("POST", "https://real.example.test/direct");
direct.send(payload);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 1, "{rows:#?}");
        assert_eq!(rows[0].kind, "xhr_open");
        assert_eq!(rows[0].method.as_deref(), Some("POST"));
        assert_eq!(
            rows[0].url.as_deref(),
            Some("https://real.example.test/direct")
        );
        Ok(())
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
