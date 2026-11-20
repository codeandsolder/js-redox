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

use work_budget::WorkBudget;

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Serialize)]
pub struct ApiCallsite {
    pub kind: String,
    pub start: u32,
    pub end: u32,
    pub line: usize,
    pub column: usize,
    pub callee: String,
    pub proof: String,
    /// "standard" means no relevant local mutation was identified;
    /// "candidate" retains syntax and arguments without proving the API binding.
    pub binding_status: String,
    pub standard_browser_api_semantics_required: bool,
    /// Stable ordinals into the same source unit's mutation_sites collection.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub mutation_site_ordinals: Vec<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub method: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub method_expression: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub method_status: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub url: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub url_expression: Option<String>,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Serialize)]
pub struct ApiMutationSite {
    pub start: u32,
    pub end: u32,
    pub line: usize,
    pub column: usize,
    pub operation: String,
    pub certainty: String,
    pub target_pattern: Vec<Option<String>>,
    pub affected_families: Vec<String>,
    pub expression: String,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct ApiSurfaceAnalysis {
    pub callsites: Vec<ApiCallsite>,
    pub mutation_sites: Vec<ApiMutationSite>,
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

// Binding reassignment can replace the XMLHttpRequest instance entirely. We
// still surface calls on escaped instances as candidates, but never calls on a
// binding whose value may have been overwritten.
fn xhr_binding_is_not_reassigned(scoping: &Scoping, symbol: SymbolId) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|id| !scoping.get_reference(*id).is_write())
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

struct SafeMemberReferenceCollector<'c> {
    scoping: &'c Scoping,
    constants: &'c ProvenConstantEnvironment,
    refs: BTreeSet<ReferenceId>,
}

impl<'a> Visit<'a> for SafeMemberReferenceCollector<'_> {
    fn visit_static_member_expression(&mut self, member: &StaticMemberExpression<'a>) {
        if !member.optional && safe_xhr_member_name(member.property.name.as_str()) {
            if let Some(reference_id) = direct_reference_id(&member.object) {
                self.refs.insert(reference_id);
            }
        }
        walk::walk_static_member_expression(self, member);
    }

    fn visit_computed_member_expression(&mut self, member: &ComputedMemberExpression<'a>) {
        if !member.optional
            && static_string(&member.expression, self.scoping, self.constants)
                .as_deref()
                .is_some_and(safe_xhr_member_name)
        {
            if let Some(reference_id) = direct_reference_id(&member.object) {
                self.refs.insert(reference_id);
            }
        }
        walk::walk_computed_member_expression(self, member);
    }
}

/// Recognize global-rooted member accesses while preserving computed keys
/// whose values cannot be proven. Unknown keys are never promoted to exact
/// callsite identities, but they can identify possibly overwritten API families.
fn global_path_pattern(
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
    expression: &Expression<'_>,
) -> Option<Vec<Option<String>>> {
    match unparenthesized(expression) {
        Expression::Identifier(identifier) => {
            let reference = scoping.get_reference(identifier.reference_id.get()?);
            reference
                .symbol_id()
                .is_none()
                .then(|| vec![Some(identifier.name.to_string())])
        }
        Expression::StaticMemberExpression(member) if !member.optional => {
            let mut path = global_path_pattern(scoping, constants, &member.object)?;
            path.push(Some(member.property.name.to_string()));
            Some(path)
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let mut path = global_path_pattern(scoping, constants, &member.object)?;
            path.push(static_string(&member.expression, scoping, constants));
            Some(path)
        }
        _ => None,
    }
}

/// A single computed key containing a dot is not a nested property access.
fn global_path(
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
    expression: &Expression<'_>,
) -> Option<String> {
    let segments = global_path_pattern(scoping, constants, expression)?;
    let path = segments
        .into_iter()
        .map(|segment| segment.filter(|value| !value.contains('.')))
        .collect::<Option<Vec<_>>>()?;
    Some(path.join("."))
}

fn static_string(
    expression: &Expression<'_>,
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
) -> Option<String> {
    constants.exact_string(expression, scoping)
}

fn effective_http_method(value: &str) -> Option<String> {
    if value.is_empty()
        || !value.as_bytes().iter().all(|byte| {
            byte.is_ascii_alphanumeric()
                || matches!(
                    byte,
                    b'!' | b'#'
                        | b'$'
                        | b'%'
                        | b'&'
                        | b'\''
                        | b'*'
                        | b'+'
                        | b'-'
                        | b'.'
                        | b'^'
                        | b'_'
                        | b'`'
                        | b'|'
                        | b'~'
                )
        })
    {
        return None;
    }
    if ["CONNECT", "TRACE", "TRACK"]
        .iter()
        .any(|forbidden| value.eq_ignore_ascii_case(forbidden))
    {
        return None;
    }
    for normalized in ["DELETE", "GET", "HEAD", "OPTIONS", "POST", "PUT"] {
        if value.eq_ignore_ascii_case(normalized) {
            return Some(normalized.to_string());
        }
    }
    Some(value.to_string())
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

/// Global aliases refer to the same object for property writes. Retain the
/// path components so an unknown key cannot masquerade as a known segment.
fn normalized_mutation_path(path: &[Option<String>]) -> &[Option<String>] {
    if path.len() > 1 && matches!(path[0].as_deref(), Some("window" | "globalThis" | "self")) {
        &path[1..]
    } else {
        path
    }
}

const MUTATION_TARGETS: &[(&str, &[&str])] = &[
    ("fetch", &["fetch"]),
    ("send_beacon", &["navigator", "sendBeacon"]),
    ("websocket", &["WebSocket"]),
    ("xhr", &["XMLHttpRequest"]),
    ("xhr_open_method", &["XMLHttpRequest", "prototype", "open"]),
    (
        "request_init_method_prototype",
        &["Object", "prototype", "method"],
    ),
];

#[derive(Default)]
struct SinkMutations {
    definite: BTreeSet<&'static str>,
    possible: BTreeSet<&'static str>,
    sites: BTreeSet<ApiMutationSite>,
}

impl SinkMutations {
    fn record(
        &mut self,
        path: &[Option<String>],
        span: Span,
        operation: &str,
        reflective: bool,
        source: &str,
        lines: &LineIndex,
    ) {
        let normalized = normalized_mutation_path(path);
        let mut affected = Vec::new();
        let possible = reflective || normalized.iter().any(Option::is_none);
        for &(family, target) in MUTATION_TARGETS {
            // An ancestor write may replace the entire API binding. A write
            // below that binding cannot replace the binding itself.
            if normalized.len() > target.len()
                || !normalized
                    .iter()
                    .zip(target)
                    .all(|(segment, name)| segment.as_deref().is_none_or(|value| value == *name))
            {
                continue;
            }
            affected.push(family.to_owned());
            if possible {
                self.possible.insert(family);
            } else {
                self.definite.insert(family);
            }
        }
        if affected.is_empty() {
            return;
        }
        let (line, column) = lines.line_column(span.start);
        self.sites.insert(ApiMutationSite {
            start: span.start,
            end: span.end,
            line,
            column,
            operation: operation.to_owned(),
            certainty: if possible { "possible" } else { "definite" }.to_owned(),
            target_pattern: path.to_vec(),
            affected_families: affected,
            expression: source_fragment(source, span),
        });
    }

    fn definitely(&self, family: &str) -> bool {
        self.definite.contains(family)
    }

    fn possibly(&self, family: &str) -> bool {
        self.possible.contains(family)
    }

    fn relevant_ordinals(&self, families: &[&str]) -> Vec<usize> {
        self.sites
            .iter()
            .enumerate()
            .filter_map(|(ordinal, site)| {
                site.affected_families
                    .iter()
                    .any(|family| families.contains(&family.as_str()))
                    .then_some(ordinal)
            })
            .collect()
    }
}

fn assignment_target_global_path_pattern(
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
    target: &oxc_ast::ast::SimpleAssignmentTarget<'_>,
) -> Option<Vec<Option<String>>> {
    match target {
        oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) => {
            let reference = scoping.get_reference(identifier.reference_id.get()?);
            reference
                .symbol_id()
                .is_none()
                .then(|| vec![Some(identifier.name.to_string())])
        }
        oxc_ast::ast::SimpleAssignmentTarget::StaticMemberExpression(member)
            if !member.optional =>
        {
            let mut path = global_path_pattern(scoping, constants, &member.object)?;
            path.push(Some(member.property.name.to_string()));
            Some(path)
        }
        oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member)
            if !member.optional =>
        {
            let mut path = global_path_pattern(scoping, constants, &member.object)?;
            path.push(static_string(&member.expression, scoping, constants));
            Some(path)
        }
        _ => None,
    }
}

struct SinkMutationCollector<'s, 'c> {
    source: &'s str,
    lines: LineIndex,
    scoping: &'c Scoping,
    constants: &'c ProvenConstantEnvironment,
    mutations: SinkMutations,
}

impl SinkMutationCollector<'_, '_> {
    fn record(
        &mut self,
        path: Option<Vec<Option<String>>>,
        span: Span,
        operation: &str,
        reflective: bool,
    ) {
        if let Some(path) = path {
            self.mutations
                .record(&path, span, operation, reflective, self.source, &self.lines);
        }
    }

    fn reflective_target(&self, call: &CallExpression<'_>) -> Option<Vec<Option<String>>> {
        let target = call.arguments.first()?.as_expression()?;
        global_path_pattern(self.scoping, self.constants, target)
    }

    fn reflective_key(&self, arg: Option<&oxc_ast::ast::Argument<'_>>) -> Option<String> {
        let expression = arg?.as_expression()?;
        static_string(expression, self.scoping, self.constants)
    }

    /// Object.assign copies own enumerable keys in source order; a spread or
    /// nonliteral source can introduce arbitrary keys. Traverse nested literal
    /// spreads instead of discarding their statically exposed property names.
    fn record_assign_source(
        &mut self,
        target: &[Option<String>],
        source: &Expression<'_>,
        call_span: Span,
    ) {
        if let Expression::ObjectExpression(object) = unparenthesized(source) {
            for property in &object.properties {
                match property {
                    ObjectPropertyKind::ObjectProperty(property) => {
                        let key = property
                            .key
                            .static_name()
                            .and_then(|name| name.into_cow_str().map(|text| text.into_owned()))
                            .or_else(|| {
                                property.key.as_expression().and_then(|expr| {
                                    static_string(expr, self.scoping, self.constants)
                                })
                            });
                        let mut path = target.to_vec();
                        path.push(key);
                        self.record(Some(path), call_span, "Object.assign", true);
                    }
                    ObjectPropertyKind::SpreadProperty(spread) => {
                        self.record_assign_source(target, &spread.argument, call_span);
                    }
                }
            }
        } else {
            let mut path = target.to_vec();
            path.push(None);
            self.record(Some(path), call_span, "Object.assign", true);
        }
    }
}

impl<'a> Visit<'a> for SinkMutationCollector<'_, '_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        self.record(
            assignment
                .left
                .as_simple_assignment_target()
                .and_then(|target| {
                    assignment_target_global_path_pattern(self.scoping, self.constants, target)
                }),
            assignment.span,
            "assignment",
            false,
        );
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_update_expression(&mut self, update: &oxc_ast::ast::UpdateExpression<'a>) {
        self.record(
            assignment_target_global_path_pattern(self.scoping, self.constants, &update.argument),
            update.span,
            "update",
            false,
        );
        walk::walk_update_expression(self, update);
    }

    fn visit_unary_expression(&mut self, unary: &oxc_ast::ast::UnaryExpression<'a>) {
        if unary.operator.as_str() == "delete" {
            self.record(
                global_path_pattern(self.scoping, self.constants, &unary.argument),
                unary.span,
                "delete",
                false,
            );
        }
        walk::walk_unary_expression(self, unary);
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            let method = global_path(self.scoping, self.constants, &call.callee);
            match method.as_deref() {
                Some("Object.defineProperty" | "Reflect.set") if call.arguments.len() >= 3 => {
                    if let Some(mut target) = self.reflective_target(call) {
                        target.push(self.reflective_key(call.arguments.get(1)));
                        self.record(
                            Some(target),
                            call.span,
                            method.as_deref().unwrap_or_default(),
                            true,
                        );
                    }
                }
                Some("Object.assign") if call.arguments.len() >= 2 => {
                    if let Some(target) = self.reflective_target(call) {
                        for source in &call.arguments[1..] {
                            if let Some(source) = source.as_expression() {
                                self.record_assign_source(&target, source, call.span);
                            } else {
                                let mut path = target.clone();
                                path.push(None);
                                self.record(Some(path), call.span, "Object.assign", true);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        walk::walk_call_expression(self, call);
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
    Literal {
        value: Option<String>,
        expression: String,
    },
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
            if matches!(state, FetchInitMethod::NoOwnMethod) {
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

        state = static_string(&property.value, scoping, constants).map_or(
            FetchInitMethod::Unknown,
            |value| FetchInitMethod::Literal {
                value: effective_http_method(&value),
                expression: source_fragment(source, property.value.span()),
            },
        );
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
) -> (Option<String>, Option<String>, Option<String>) {
    if arguments
        .first()
        .is_some_and(|argument| argument.as_expression().is_none())
    {
        return (None, None, Some("unknown".to_string()));
    }

    match fetch_init_method(source, arguments.get(1), scoping, constants) {
        FetchInitMethod::Literal { value, expression } => {
            let status = if value.is_some() { "exact" } else { "invalid" };
            (value, Some(expression), Some(status.to_owned()))
        }
        FetchInitMethod::Missing if input_is_static_string => {
            (Some("GET".to_string()), None, Some("exact".to_string()))
        }
        FetchInitMethod::NoOwnMethod
            if input_is_static_string && !request_init_method_prototype_mutated =>
        {
            (Some("GET".to_string()), None, Some("exact".to_string()))
        }
        FetchInitMethod::Missing | FetchInitMethod::NoOwnMethod | FetchInitMethod::Unknown => {
            (None, None, Some("unknown".to_string()))
        }
    }
}

struct XhrBindingCollector<'c> {
    scoping: &'c Scoping,
    constants: &'c ProvenConstantEnvironment,
    safe_member_refs: &'c BTreeSet<ReferenceId>,
    standard_xhr_available: bool,
    constructor_may_be_mutated: bool,
    symbols: BTreeSet<SymbolId>,
    candidate_symbols: BTreeSet<SymbolId>,
}

impl<'a> Visit<'a> for XhrBindingCollector<'_> {
    fn visit_variable_declarator(&mut self, declarator: &VariableDeclarator<'a>) {
        if let (BindingPattern::BindingIdentifier(identifier), Some(initializer)) =
            (&declarator.id, declarator.init.as_ref())
        {
            let initializer = unparenthesized(initializer);
            if let Expression::NewExpression(new_expression) = initializer {
                if self.standard_xhr_available
                    && global_path(self.scoping, self.constants, &new_expression.callee)
                        .as_deref()
                        .is_some_and(allowed_xhr_path)
                {
                    if let Some(symbol) = identifier.symbol_id.get() {
                        if xhr_binding_is_not_reassigned(self.scoping, symbol) {
                            if symbol_is_safe_xhr_receiver(
                                self.scoping,
                                symbol,
                                self.safe_member_refs,
                            ) && !self.constructor_may_be_mutated
                            {
                                self.symbols.insert(symbol);
                            } else {
                                self.candidate_symbols.insert(symbol);
                            }
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
    mutations: &'c SinkMutations,
    xhr_symbols: &'c BTreeSet<SymbolId>,
    xhr_candidate_symbols: &'c BTreeSet<SymbolId>,
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
        method: (Option<String>, Option<String>, Option<String>),
        url: (Option<String>, Option<String>),
    ) {
        let (method, method_expression, method_status) = method;
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
            binding_status: if kind.ends_with("_candidate") {
                "candidate".to_owned()
            } else {
                "standard".to_owned()
            },
            standard_browser_api_semantics_required: true,
            mutation_site_ordinals: self.mutations.relevant_ordinals(match kind {
                "fetch_candidate" | "fetch" => &["fetch", "request_init_method_prototype"],
                "send_beacon_candidate" => &["send_beacon"],
                "websocket_candidate" => &["websocket"],
                "xhr_open_candidate" => &["xhr", "xhr_open_method"],
                _ => &[],
            }),
            method,
            method_expression,
            method_status,
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
                (static_string(&member.expression, self.scoping, self.constants).as_deref()
                    == Some("open"))
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
            if let Some(path) = global_path(self.scoping, self.constants, &call.callee) {
                if allowed_fetch_path(&path) && !self.mutations.definitely("fetch") {
                    let (url, url_expression) = exact_argument(
                        self.source,
                        call.arguments.first(),
                        self.scoping,
                        self.constants,
                    );
                    let candidate = self.mutations.possibly("fetch");
                    let mut method = fetch_method(
                        self.source,
                        &call.arguments,
                        url.is_some(),
                        self.mutations.definitely("request_init_method_prototype")
                            || self.mutations.possibly("request_init_method_prototype"),
                        self.scoping,
                        self.constants,
                    );
                    if candidate && method.2.as_deref() == Some("exact") {
                        method.2 = Some("conditional".to_owned());
                    }
                    self.push(
                        if candidate {
                            "fetch_candidate"
                        } else {
                            "fetch"
                        },
                        call.span,
                        path,
                        if candidate {
                            "unresolved_global_member_mutation_may_replace_fetch"
                        } else {
                            STANDARD_BROWSER_API_ASSUMPTION
                        },
                        method,
                        (url, url_expression),
                    );
                } else if allowed_send_beacon_path(&path)
                    && !self.mutations.definitely("send_beacon")
                {
                    let (url, url_expression) = exact_argument(
                        self.source,
                        call.arguments.first(),
                        self.scoping,
                        self.constants,
                    );
                    let candidate = self.mutations.possibly("send_beacon");
                    self.push(
                        if candidate {
                            "send_beacon_candidate"
                        } else {
                            "send_beacon"
                        },
                        call.span,
                        path,
                        if candidate {
                            "unresolved_global_member_mutation_may_replace_sendBeacon"
                        } else {
                            STANDARD_BROWSER_API_ASSUMPTION
                        },
                        (
                            Some("POST".to_owned()),
                            None,
                            Some(if candidate { "conditional" } else { "exact" }.to_owned()),
                        ),
                        (url, url_expression),
                    );
                }
            }

            if let Some(symbol) = self.xhr_receiver_symbol(&call.callee) {
                let stable_receiver = self.xhr_symbols.contains(&symbol);
                let confirmed = stable_receiver
                    && !self.mutations.possibly("xhr_open_method")
                    && !self.mutations.definitely("xhr_open_method");
                let candidate = !self.mutations.definitely("xhr_open_method")
                    && (stable_receiver || self.xhr_candidate_symbols.contains(&symbol));
                if confirmed || candidate {
                    let (method, method_expression) = exact_argument(
                        self.source,
                        call.arguments.first(),
                        self.scoping,
                        self.constants,
                    );
                    let (method, method_status) = method.map_or_else(
                        || (None, Some("unknown".to_owned())),
                        |literal| {
                            let normalized = effective_http_method(&literal);
                            let status = if normalized.is_some() {
                                "exact"
                            } else {
                                "invalid"
                            };
                            (normalized, Some(status.to_owned()))
                        },
                    );
                    let (url, url_expression) = exact_argument(
                        self.source,
                        call.arguments.get(1),
                        self.scoping,
                        self.constants,
                    );
                    let dynamic_mutation = self.mutations.possibly("xhr")
                        || self.mutations.possibly("xhr_open_method");
                    self.push(
                        if confirmed { "xhr_open" } else { "xhr_open_candidate" },
                        call.span,
                        source_fragment(self.source, call.callee.span()),
                        if confirmed {
                            "stable_symbol_initialized_from_standard_XMLHttpRequest"
                        } else if dynamic_mutation {
                            "unresolved_global_member_mutation_may_replace_XMLHttpRequest_or_open"
                        } else {
                            "unreassigned_binding_initialized_from_standard_XMLHttpRequest_but_receiver_escapes_or_is_mutable"
                        },
                        (
                            method,
                            method_expression,
                            if dynamic_mutation && method_status.as_deref() == Some("exact") {
                                Some("conditional".to_owned())
                            } else {
                                method_status
                            },
                        ),
                        (url, url_expression),
                    );
                }
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &NewExpression<'a>) {
        if let Some(path) = global_path(self.scoping, self.constants, &expression.callee) {
            if allowed_websocket_path(&path) && !self.mutations.definitely("websocket") {
                let (url, url_expression) = exact_argument(
                    self.source,
                    expression.arguments.first(),
                    self.scoping,
                    self.constants,
                );
                let candidate = self.mutations.possibly("websocket");
                self.push(
                    if candidate {
                        "websocket_candidate"
                    } else {
                        "websocket"
                    },
                    expression.span,
                    path,
                    if candidate {
                        "unresolved_global_member_mutation_may_replace_WebSocket"
                    } else {
                        STANDARD_BROWSER_API_ASSUMPTION
                    },
                    (None, None, None),
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

/// Recover source-proven browser API call sites under a bounded analysis.
///
/// # Errors
///
/// Fails on work-budget exhaustion, a `with` statement that makes identifier resolution environment-dependent, or failure to parse and semantically validate the source in supported JavaScript modes.
pub fn analyze_api_surface(source: &str, budget: &WorkBudget) -> Result<ApiSurfaceAnalysis> {
    budget.checkpoint()?;
    for source_type in [SourceType::unambiguous(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let Some(program) = parse_clean(&allocator, source, source_type) else {
            budget.checkpoint()?;
            continue;
        };
        budget.checkpoint()?;
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
        budget.checkpoint()?;
        let constants = ProvenConstantEnvironment::collect(&program, scoping);
        budget.checkpoint()?;

        let mut safe_member_refs = SafeMemberReferenceCollector {
            scoping,
            constants: &constants,
            refs: BTreeSet::new(),
        };
        safe_member_refs.visit_program(&program);
        budget.checkpoint()?;

        let mut mutations = SinkMutationCollector {
            source,
            lines: LineIndex::new(source),
            scoping,
            constants: &constants,
            mutations: SinkMutations::default(),
        };
        mutations.visit_program(&program);
        budget.checkpoint()?;

        let mut xhr = XhrBindingCollector {
            scoping,
            constants: &constants,
            safe_member_refs: &safe_member_refs.refs,
            standard_xhr_available: !mutations.mutations.definitely("xhr"),
            constructor_may_be_mutated: mutations.mutations.possibly("xhr"),
            symbols: BTreeSet::new(),
            candidate_symbols: BTreeSet::new(),
        };
        xhr.visit_program(&program);
        budget.checkpoint()?;

        let mut collector = Collector {
            source,
            scoping,
            constants: &constants,
            mutations: &mutations.mutations,
            xhr_symbols: &xhr.symbols,
            xhr_candidate_symbols: &xhr.candidate_symbols,
            lines: LineIndex::new(source),
            callsites: BTreeSet::new(),
        };
        collector.visit_program(&program);
        budget.checkpoint()?;
        let mut callsites = collector.callsites.into_iter().collect::<Vec<_>>();
        callsites.sort_by(|left, right| {
            (left.start, left.end, left.kind.as_str()).cmp(&(
                right.start,
                right.end,
                right.kind.as_str(),
            ))
        });
        return Ok(ApiSurfaceAnalysis {
            callsites,
            mutation_sites: mutations.mutations.sites.into_iter().collect(),
        });
    }

    Err(anyhow!(
        "Oxc could not semantically validate source as browser JavaScript"
    ))
}

#[cfg(test)]
mod tests {
    use super::analyze_api_surface as analyze_api_surface_budgeted;
    use super::ApiCallsite;
    use anyhow::Result;
    use work_budget::WorkBudget;

    fn analyze_api_surface(source: &str) -> Result<Vec<ApiCallsite>> {
        Ok(
            analyze_api_surface_budgeted(source, &WorkBudget::unlimited("api-surface-test"))?
                .callsites,
        )
    }

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
    fn reflective_define_property_preserves_candidate_and_mutation_witness() -> Result<()> {
        let src = r#"
const key = "fe" + "tch";
Object.defineProperty(window, key, { value: replacement });
fetch("https://api.example.test/one", { method: "POST" });
navigator.sendBeacon("https://api.example.test/two", payload);
"#;
        let result =
            super::analyze_api_surface(src, &WorkBudget::unlimited("reflective-define-property"))?;
        assert_eq!(result.callsites.len(), 2);
        assert_eq!(result.mutation_sites.len(), 1, "{result:#?}");
        let site = &result.mutation_sites[0];
        assert_eq!(site.operation, "Object.defineProperty");
        assert_eq!(site.certainty, "possible");
        assert_eq!(
            site.target_pattern,
            vec![Some("window".into()), Some("fetch".into())]
        );
        assert_eq!(site.affected_families, ["fetch"]);
        assert!(site.expression.starts_with("Object.defineProperty"));
        assert_eq!(result.callsites[0].kind, "fetch_candidate");
        assert_eq!(
            result.callsites[0].method_status.as_deref(),
            Some("conditional")
        );
        assert_eq!(result.callsites[0].mutation_site_ordinals, [0]);
        assert_eq!(result.callsites[1].kind, "send_beacon");
        assert!(result.callsites[1].mutation_site_ordinals.is_empty());
        Ok(())
    }

    #[test]
    fn reflective_set_and_unknown_key_maintain_narrow_mutation_provenance() -> Result<()> {
        let src = r#"
const key = runtimeKey();
Reflect.set(navigator, key, replacement);
fetch("https://api.example.test/safe");
navigator.sendBeacon("https://api.example.test/uncertain", payload);
const xhr = new XMLHttpRequest();
xhr.open("GET", "https://api.example.test/xhr");
"#;
        let result = super::analyze_api_surface(src, &WorkBudget::unlimited("reflective-set"))?;
        assert_eq!(result.callsites.len(), 3);
        assert_eq!(result.mutation_sites.len(), 1);
        assert_eq!(result.mutation_sites[0].operation, "Reflect.set");
        assert_eq!(
            result.mutation_sites[0].target_pattern,
            vec![Some("navigator".into()), None,]
        );
        assert_eq!(result.mutation_sites[0].affected_families, ["send_beacon"]);
        assert_eq!(result.callsites[0].kind, "fetch");
        assert_eq!(result.callsites[1].kind, "send_beacon_candidate");
        assert_eq!(result.callsites[1].mutation_site_ordinals, [0]);
        assert_eq!(result.callsites[2].kind, "xhr_open");
        Ok(())
    }

    #[test]
    fn assign_literal_keys_and_spreads_emit_precise_mutation_sites() -> Result<()> {
        let src = r#"
const key = "Web" + "Socket";
Object.assign(window, {
    fetch: replacement,
    [key]: CustomSocket,
    ...{ navigator: alteredNavigator },
    ...external,
    irrelevant: 1
});
fetch("https://api.example.test/uncertain");
navigator.sendBeacon("https://api.example.test/uncertain", data);
new WebSocket("wss://api.example.test/uncertain");
const xhr = new XMLHttpRequest();
xhr.open("POST", "https://api.example.test/uncertain");
"#;
        let result =
            super::analyze_api_surface(src, &WorkBudget::unlimited("assign-literal-and-spread"))?;
        assert_eq!(result.callsites.len(), 4);
        assert_eq!(
            result
                .callsites
                .iter()
                .map(|row| row.kind.as_str())
                .collect::<Vec<_>>(),
            [
                "fetch_candidate",
                "send_beacon_candidate",
                "websocket_candidate",
                "xhr_open_candidate"
            ]
        );
        assert!(result.mutation_sites.len() >= 4, "{result:#?}");
        assert!(result
            .mutation_sites
            .iter()
            .all(|site| site.operation == "Object.assign" && site.certainty == "possible"));
        for (idx, row) in result.callsites.iter().enumerate() {
            assert!(!row.mutation_site_ordinals.is_empty(), "{idx}: {row:#?}");
            for &ordinal in &row.mutation_site_ordinals {
                assert!(ordinal < result.mutation_sites.len());
            }
        }
        assert!(result.mutation_sites.iter().any(|site| {
            site.target_pattern == [Some("window".into()), Some("WebSocket".into())]
        }));
        Ok(())
    }

    #[test]
    fn reflective_method_and_xhr_prototype_writes_keep_specific_inference_boundaries() -> Result<()>
    {
        let src = r#"
Object.defineProperty(Object.prototype, "method", {value: "DELETE"});
Object.assign(XMLHttpRequest.prototype, {open: customOpen});
fetch("https://api.example.test/implicit", {});
fetch("https://api.example.test/own", {method: "PATCH"});
fetch("https://api.example.test/omitted");
const xhr = new XMLHttpRequest();
xhr.open("POST", "https://api.example.test/xhr");
"#;
        let result =
            super::analyze_api_surface(src, &WorkBudget::unlimited("reflective-prototypes"))?;
        assert_eq!(result.callsites.len(), 4);
        assert_eq!(result.callsites[0].kind, "fetch");
        assert_eq!(
            result.callsites[0].method_status.as_deref(),
            Some("unknown")
        );
        assert_eq!(result.callsites[1].method.as_deref(), Some("PATCH"));
        assert_eq!(result.callsites[2].method.as_deref(), Some("GET"));
        assert_eq!(result.callsites[3].kind, "xhr_open_candidate");
        assert_eq!(
            result.callsites[3].method_status.as_deref(),
            Some("conditional")
        );
        assert!(result
            .mutation_sites
            .iter()
            .any(|site| { site.affected_families == ["xhr_open_method"] }));
        Ok(())
    }

    #[test]
    fn shadowed_reflective_names_and_unrelated_mutations_are_not_global_witnesses() -> Result<()> {
        let src = r#"
function local(Object, Reflect) {
    Object.defineProperty(window, "fetch", {value: fake});
    Reflect.set(window, "WebSocket", fake);
    Object.assign(window, {navigator: fake});
}
Object.defineProperty(window, "unrelated", {value: 1});
Reflect.set(globalThis.fetch, "unrelated", replacement);
Object.assign(window, {});
fetch("https://api.example.test/verified");
navigator.sendBeacon("https://api.example.test/verified", data);
new WebSocket("wss://api.example.test/verified");
"#;
        let result =
            super::analyze_api_surface(src, &WorkBudget::unlimited("reflective-shadowed"))?;
        assert_eq!(result.callsites.len(), 3);
        assert!(result
            .callsites
            .iter()
            .all(|row| row.binding_status == "standard"));
        assert!(result.mutation_sites.is_empty(), "{result:#?}");
        Ok(())
    }

    #[test]
    fn unknown_reflective_keys_and_unknown_assign_sources_retain_candidate_provenance() -> Result<()>
    {
        let src = r#"
let key = getKey();
Object.defineProperty(globalThis, key, {value: replacement});
Object.assign(navigator, unknownSource);
fetch("https://api.example.test/a");
navigator.sendBeacon("https://api.example.test/b", data);
new WebSocket("wss://api.example.test/c");
"#;
        let result = super::analyze_api_surface(src, &WorkBudget::unlimited("reflective-unknown"))?;
        assert_eq!(result.callsites.len(), 3);
        assert!(result
            .callsites
            .iter()
            .all(|row| row.binding_status == "candidate"));
        assert_eq!(result.mutation_sites.len(), 2);
        assert!(result.mutation_sites.iter().any(|site| {
            site.target_pattern == [Some("globalThis".into()), None]
                && site.affected_families.contains(&"fetch".to_string())
        }));
        assert!(result.mutation_sites.iter().any(|site| {
            site.target_pattern == [Some("navigator".into()), None]
                && site.affected_families == ["send_beacon"]
        }));
        Ok(())
    }

    #[test]
    fn dynamic_global_property_write_keeps_all_affected_api_calls_as_candidates() -> Result<()> {
        let source = r#"
let key = location.hash.slice(1);
globalThis[key] = replacement;
fetch("https://api.example.test/items", { method: "PATCH" });
navigator.sendBeacon("https://api.example.test/telemetry", data);
new WebSocket("wss://api.example.test/live");
const xhr = new XMLHttpRequest();
xhr.open("PUT", "https://api.example.test/form");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        assert_eq!(
            rows.iter().map(|row| row.kind.as_str()).collect::<Vec<_>>(),
            [
                "fetch_candidate",
                "send_beacon_candidate",
                "websocket_candidate",
                "xhr_open_candidate"
            ],
        );
        assert!(rows.iter().all(|row| row.binding_status == "candidate"));
        assert_eq!(
            rows[0].url.as_deref(),
            Some("https://api.example.test/items")
        );
        assert_eq!(
            rows[0].url_expression.as_deref(),
            Some(r#""https://api.example.test/items""#)
        );
        assert_eq!(rows[0].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[0].method_status.as_deref(), Some("conditional"));
        assert_eq!(rows[1].method.as_deref(), Some("POST"));
        assert_eq!(rows[1].method_status.as_deref(), Some("conditional"));
        assert_eq!(rows[2].url.as_deref(), Some("wss://api.example.test/live"));
        assert_eq!(rows[3].method.as_deref(), Some("PUT"));
        assert_eq!(rows[3].method_status.as_deref(), Some("conditional"));
        assert_eq!(
            rows[3].url.as_deref(),
            Some("https://api.example.test/form")
        );
        assert!(rows
            .iter()
            .all(|row| row.proof.contains("unresolved_global_member_mutation")));
        Ok(())
    }

    #[test]
    fn dynamic_nested_write_downgrades_only_matching_api_family() -> Result<()> {
        let source = r#"
let key = getKey();
window.navigator[key] = replacement;
fetch("https://api.example.test/known");
navigator.sendBeacon("https://api.example.test/maybe", data);
new WebSocket("wss://api.example.test/known");
const xhr = new XMLHttpRequest();
xhr.open("GET", "https://api.example.test/known");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(rows[1].kind, "send_beacon_candidate");
        assert_eq!(rows[2].kind, "websocket");
        assert_eq!(rows[3].kind, "xhr_open");
        assert!(rows.iter().enumerate().all(|(index, row)| {
            row.binding_status == if index == 1 { "candidate" } else { "standard" }
        }));
        assert_eq!(rows[0].method_status.as_deref(), Some("exact"));
        assert_eq!(rows[1].method_status.as_deref(), Some("conditional"));
        Ok(())
    }

    #[test]
    fn definite_namespace_replacements_invalidate_global_aliases_and_descendants() -> Result<()> {
        let source = r#"
window.fetch = customFetch;
self.navigator = customNavigator;
globalThis.WebSocket = CustomSocket;
globalThis.XMLHttpRequest = CustomXhr;
fetch("https://fake.invalid/fetch");
globalThis.fetch("https://fake.invalid/global-fetch");
navigator.sendBeacon("https://fake.invalid/beacon", data);
window.navigator.sendBeacon("https://fake.invalid/global-beacon", data);
new WebSocket("wss://fake.invalid/socket");
const xhr = new XMLHttpRequest();
xhr.open("POST", "https://fake.invalid/xhr");
"#;
        let rows = analyze_api_surface(source)?;
        assert!(rows.is_empty(), "{rows:#?}");
        Ok(())
    }

    #[test]
    fn inherited_method_and_xhr_prototype_dynamic_writes_preserve_uncertainty() -> Result<()> {
        let source = r#"
let key = getName();
Object.prototype[key] = "DELETE";
XMLHttpRequest.prototype[key] = customOpen;
fetch("https://api.example.test/inherited", {});
fetch("https://api.example.test/own", { method: "POST" });
fetch("https://api.example.test/no-init");
const xhr = new XMLHttpRequest();
xhr.open("PATCH", "https://api.example.test/record");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(rows[0].method, None);
        assert_eq!(rows[0].method_status.as_deref(), Some("unknown"));
        assert_eq!(rows[1].kind, "fetch");
        assert_eq!(rows[1].method.as_deref(), Some("POST"));
        assert_eq!(rows[1].method_status.as_deref(), Some("exact"));
        assert_eq!(rows[2].method.as_deref(), Some("GET"));
        assert_eq!(rows[3].kind, "xhr_open_candidate");
        assert_eq!(rows[3].binding_status, "candidate");
        assert_eq!(rows[3].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[3].method_status.as_deref(), Some("conditional"));
        Ok(())
    }

    #[test]
    fn dynamically_computed_subproperties_cannot_replace_parent_api_binding() -> Result<()> {
        let source = r#"
let unknown = getName();
globalThis[unknown].fetch = replacement;
globalThis.fetch[unknown] = replacement;
window["navigator.sendBeacon"] = fakeBeacon;
fetch("https://api.example.test/verified");
navigator.sendBeacon("https://api.example.test/verified", data);
new WebSocket("wss://api.example.test/verified");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert!(rows.iter().all(|row| row.binding_status == "standard"));
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(rows[1].kind, "send_beacon");
        assert_eq!(rows[2].kind, "websocket");
        Ok(())
    }

    #[test]
    fn shadowed_global_namespaces_and_unrelated_computed_writes_are_excluded() -> Result<()> {
        let source = r#"
function local(window, navigator) {
    let key = getName();
    window[key] = replacement;
    navigator[key] = replacement;
}
const fixed = "unrelated";
window[fixed] = replacement;
fetch("https://api.example.test/verified");
navigator.sendBeacon("https://api.example.test/verified", data);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 2, "{rows:#?}");
        assert!(rows.iter().all(|row| row.binding_status == "standard"));
        Ok(())
    }

    #[test]
    fn proven_computed_member_keys_recover_standard_api_calls_and_xhr_open() -> Result<()> {
        let source = r#"
const fetchKey = "fe" + "tch";
const beaconKey = "send" + "Beacon";
const socketKey = "Web" + "Socket";
const xhrKey = "XML" + "HttpRequest";
const openKey = "op" + "en";
const url = "https://api.example.test" + "/computed";
globalThis[fetchKey](url, { method: "post" });
window.navigator[beaconKey](url, payload);
new self[socketKey]("wss://api.example.test/ws");
const xhr = new globalThis[xhrKey]();
xhr[openKey]("PATCH", url);
xhr.send(payload);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(rows[0].method.as_deref(), Some("POST"));
        assert_eq!(
            rows[0].url.as_deref(),
            Some("https://api.example.test/computed")
        );
        assert_eq!(rows[0].callee, "globalThis.fetch");
        assert_eq!(rows[1].kind, "send_beacon");
        assert_eq!(rows[1].callee, "window.navigator.sendBeacon");
        assert_eq!(rows[1].method.as_deref(), Some("POST"));
        assert_eq!(rows[2].kind, "websocket");
        assert_eq!(rows[2].callee, "self.WebSocket");
        assert_eq!(rows[3].kind, "xhr_open");
        assert_eq!(rows[3].method.as_deref(), Some("PATCH"));
        assert_eq!(
            rows[3].url.as_deref(),
            Some("https://api.example.test/computed")
        );
        Ok(())
    }

    #[test]
    fn computed_member_mutations_invalidate_the_same_sinks_as_literal_writes() -> Result<()> {
        let source = r#"
const fetchKey = "fe" + "tch";
const beaconKey = "send" + "Beacon";
const socketKey = "Web" + "Socket";
const xhrKey = "XML" + "HttpRequest";
window[fetchKey] = customFetch;
navigator[beaconKey]++;
delete self[socketKey];
globalThis[xhrKey] = CustomXhr;
fetch("https://fake.invalid/fetch");
navigator.sendBeacon("https://fake.invalid/beacon", body);
new WebSocket("wss://fake.invalid/socket");
const xhr = new XMLHttpRequest();
xhr.open("GET", "https://fake.invalid/xhr");
"#;
        let rows = analyze_api_surface(source)?;
        assert!(
            rows.is_empty(),
            "computed mutations must not silently preserve sink proof: {rows:#?}"
        );

        let unrelated = r#"
const key = "WebSocket";
globalThis[key] = FakeWebSocket;
fetch("https://real.example.test/fetch");
navigator.sendBeacon("https://real.example.test/beacon", data);
"#;
        let rows = analyze_api_surface(unrelated)?;
        assert_eq!(rows.len(), 2, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(rows[1].kind, "send_beacon");
        Ok(())
    }

    #[test]
    fn computed_inherited_request_method_mutation_blocks_only_unknown_defaults() -> Result<()> {
        let source = r#"
const methodKey = "meth" + "od";
Object.prototype[methodKey] = "POST";
fetch("https://api.example.test/inherited", {});
fetch("https://api.example.test/explicit-default");
fetch("https://api.example.test/explicit-method", { method: "PUT" });
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert_eq!(rows[0].method, None);
        assert_eq!(rows[0].method_status.as_deref(), Some("unknown"));
        assert_eq!(rows[1].method.as_deref(), Some("GET"));
        assert_eq!(rows[2].method.as_deref(), Some("PUT"));
        Ok(())
    }

    #[test]
    fn unknown_or_shadowed_computed_keys_do_not_create_false_api_matches() -> Result<()> {
        let source = r#"
let changing = "fetch";
window[changing]("https://fake.invalid/ambiguous");
const localKey = "fetch";
function shadow(window) {
    window[localKey]("https://fake.invalid/shadowed-window");
}
const ctorKey = "XMLHttpRequest";
function shadowConstructor(XMLHttpRequest) {
    const xhr = new XMLHttpRequest();
    xhr.open("GET", "https://fake.invalid/xhr");
}
const openKey = "open";
let changingMethod = "open";
const confirmed = new XMLHttpRequest();
confirmed[changingMethod]("GET", "https://fake.invalid/unknown-open");
confirmed[openKey]("POST", "https://candidate.invalid/computed-open");
fetch("https://real.example.test/unshadowed");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 2, "{rows:#?}");
        assert_eq!(rows[0].kind, "xhr_open_candidate", "{rows:#?}");
        assert_eq!(
            rows[0].url.as_deref(),
            Some("https://candidate.invalid/computed-open")
        );
        assert_eq!(rows[1].kind, "fetch");
        assert_eq!(
            rows[1].url.as_deref(),
            Some("https://real.example.test/unshadowed")
        );
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
    fn normalizes_valid_methods_and_marks_proven_invalid_methods() -> Result<()> {
        let source = r#"
fetch("https://api.example.test/get", { method: "gEt" });
fetch("https://api.example.test/custom", { method: "eGg" });
fetch("https://api.example.test/forbidden", { method: "trace" });
fetch("https://api.example.test/bad-token", { method: "bad method" });
const xhr = new XMLHttpRequest();
xhr.open("pOsT", "https://api.example.test/xhr-ok");
const blocked = new XMLHttpRequest();
blocked.open("CONNECT", "https://api.example.test/xhr-blocked");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 6, "{rows:#?}");
        assert_eq!(rows[0].method.as_deref(), Some("GET"));
        assert_eq!(rows[0].method_status.as_deref(), Some("exact"));
        assert_eq!(rows[1].method.as_deref(), Some("eGg"));
        assert_eq!(rows[1].method_status.as_deref(), Some("exact"));
        assert_eq!(rows[2].method, None);
        assert_eq!(rows[2].method_expression.as_deref(), Some(r#""trace""#));
        assert_eq!(rows[2].method_status.as_deref(), Some("invalid"));
        assert_eq!(rows[3].method, None);
        assert_eq!(rows[3].method_status.as_deref(), Some("invalid"));
        assert_eq!(rows[4].method.as_deref(), Some("POST"));
        assert_eq!(rows[4].method_status.as_deref(), Some("exact"));
        assert_eq!(rows[5].method, None);
        assert_eq!(rows[5].method_status.as_deref(), Some("invalid"));
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
fetch("https://api.example.test/invalid-own", { method: "TRACE", __proto__: { method: "GET" } });
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        assert_eq!(rows[0].method, None);
        assert_eq!(rows[1].method.as_deref(), Some("PUT"));
        assert_eq!(rows[2].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[3].method, None);
        assert_eq!(rows[3].method_status.as_deref(), Some("invalid"));
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
        // Update expressions must invalidate the same recognized global sinks
        // as plain assignments, but unrelated sink families remain available.
        let updated = r#"
window["fetch"]++;
++navigator.sendBeacon;
new WebSocket("wss://real.example.test/remaining-sink");
"#;
        let updated_rows = analyze_api_surface(updated)?;
        assert_eq!(updated_rows.len(), 1, "{updated_rows:#?}");
        assert_eq!(updated_rows[0].kind, "websocket");
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
    fn escaped_xhr_receivers_remain_candidates_without_becoming_verified_calls() -> Result<()> {
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
        assert_eq!(rows.len(), 4, "{rows:#?}");
        for candidate in &rows[..3] {
            assert_eq!(candidate.kind, "xhr_open_candidate");
            assert!(candidate.proof.contains("escapes_or_is_mutable"));
        }
        assert_eq!(rows[0].url.as_deref(), Some("https://fake.invalid/alias"));
        assert_eq!(rows[1].url.as_deref(), Some("https://fake.invalid/passed"));
        assert_eq!(
            rows[2].url.as_deref(),
            Some("https://fake.invalid/prototype")
        );
        assert_eq!(rows[3].kind, "xhr_open");
        assert_eq!(rows[3].method.as_deref(), Some("POST"));
        assert_eq!(
            rows[3].url.as_deref(),
            Some("https://real.example.test/direct")
        );
        Ok(())
    }

    #[test]
    fn htmx_style_xhr_requests_keep_both_request_paths() -> Result<()> {
        let source = r#"
function loadHistoryFromServer(path) {
    const request = new XMLHttpRequest();
    const details = { path, xhr: request };
    request.open("GET", path, true);
    request.onload = function() { details.response = this.response; };
    triggerEvent(details);
    request.send();
}
function issueAjaxRequest(verb, finalPath, eltData) {
    const xhr = new XMLHttpRequest();
    eltData.xhr = xhr;
    xhr.open(verb.toUpperCase(), finalPath, true);
    xhr.onload = () => eltData.xhr = null;
    xhr.send(payload);
}
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 2, "{rows:#?}");
        assert!(rows.iter().all(|row| row.kind == "xhr_open_candidate"));
        assert_eq!(rows[0].callee, "request.open");
        assert_eq!(rows[0].method.as_deref(), Some("GET"));
        assert_eq!(rows[0].url_expression.as_deref(), Some("path"));
        assert_eq!(rows[1].callee, "xhr.open");
        assert_eq!(
            rows[1].method_expression.as_deref(),
            Some("verb.toUpperCase()")
        );
        assert_eq!(rows[1].url_expression.as_deref(), Some("finalPath"));
        Ok(())
    }

    #[test]
    fn xhr_binding_candidates_do_not_include_reassigned_or_shadowed_xhr() -> Result<()> {
        let source = r"
function falsePositive(XMLHttpRequest) {
    const fake = new XMLHttpRequest();
    const payload = {fake};
    fake.open('GET', 'https://fake.invalid/shadow');
}
let changed = new XMLHttpRequest();
changed = unrelated;
changed.open('POST', 'https://fake.invalid/reassigned');
const real = new XMLHttpRequest();
unknown(real);
real.open('PUT', 'https://candidate.invalid/path');
";
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 1, "{rows:#?}");
        assert_eq!(rows[0].kind, "xhr_open_candidate");
        assert_eq!(
            rows[0].url.as_deref(),
            Some("https://candidate.invalid/path")
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
