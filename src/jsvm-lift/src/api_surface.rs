use crate::source_text::SourceLineIndex;
use anyhow::{anyhow, Result};
use jsvm_safe_core::{
    exact_property_key, is_prototype_setter, ProvenConstantEnvironment, StaticPrimitiveValue,
};
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

mod callables;
mod forwarding;
use callables::{ApiArguments, ApiKind, Callable, CallableIndex};

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Serialize)]
pub struct ApiCallsite {
    pub kind: String,
    pub start: u32,
    pub end: u32,
    pub line: usize,
    pub column: usize,
    pub callee: String,
    pub api_origin: String,
    pub invocation_form: String,
    /// Final underlying sink expression when this row specializes a local
    /// wrapper invocation (not evidence that either expression executed).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub forwarded_sink_span: Option<[u32; 2]>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub binding_witnesses: Vec<ApiBindingWitness>,
    pub proof: String,
    /// "standard" means no relevant local mutation was identified;
    /// "candidate" retains syntax and arguments without proving the API binding.
    pub binding_status: String,
    pub standard_browser_api_semantics_required: bool,
    /// Stable ordinals into the same source unit's `mutation_sites` collection.
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
pub struct ApiBindingWitness {
    pub kind: String,
    pub start: u32,
    pub end: u32,
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bound_function_span: Option<[u32; 2]>,
    pub affected_families: Vec<String>,
    pub expression: String,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct ApiSurfaceAnalysis {
    pub callsites: Vec<ApiCallsite>,
    pub mutation_sites: Vec<ApiMutationSite>,
}

fn unparenthesized<'a, 'e>(mut expression: &'e Expression<'a>) -> &'e Expression<'a> {
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

struct SafeMemberReferenceCollector<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    constants: &'c ProvenConstantEnvironment,
    callables: &'c CallableIndex,
    mutations: &'c SinkMutations,
    refs: BTreeSet<ReferenceId>,
}

impl<'a> Visit<'a> for SafeMemberReferenceCollector<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        let resolved = self
            .callables
            .resolve_dispatch(call, self.source, self.scoping, self.constants)
            .map(|dispatch| (dispatch.callable, dispatch.receiver_ref))
            .or_else(|| {
                let bound =
                    self.callables
                        .resolve_bind(call, self.source, self.scoping, self.constants)?;
                let receiver_ref = call
                    .arguments
                    .first()
                    .and_then(|arg| arg.as_expression())
                    .filter(|expr| expression_symbol(self.scoping, expr) == bound.receiver)
                    .and_then(direct_reference_id);
                Some((bound, receiver_ref))
            });
        if let Some((callable, Some(reference_id))) = resolved {
            if callable.kind == ApiKind::XhrOpen
                && !callable
                    .dispatch_dependencies()
                    .iter()
                    .any(|key| self.mutations.any(key))
                && !self.mutations.any("xhr")
                && !self.mutations.any("xhr_open_method")
            {
                self.refs.insert(reference_id);
            }
        }
        walk::walk_call_expression(self, call);
    }

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

// The minimum depth distinguishes replacing a global binding from
// modifying an existing object's property. In particular, global
// XMLHttpRequest/Function/Object replacement does not itself mutate the
// original constructor's prototype object.
const MUTATION_TARGETS: &[(&str, &[&str], usize)] = &[
    ("namespace_window", &["window"], 1),
    ("namespace_self", &["self"], 1),
    ("namespace_globalThis", &["globalThis"], 1),
    ("fetch", &["fetch"], 1),
    ("send_beacon", &["navigator", "sendBeacon"], 1),
    ("websocket", &["WebSocket"], 1),
    ("xhr", &["XMLHttpRequest"], 1),
    (
        "xhr_open_method",
        &["XMLHttpRequest", "prototype", "open"],
        2,
    ),
    ("rest_iterator", &["Array", "prototype"], 2),
    ("function_bind", &["Function", "prototype", "bind"], 2),
    ("function_call", &["Function", "prototype", "call"], 2),
    ("function_apply", &["Function", "prototype", "apply"], 2),
    ("reflect_apply", &["Reflect", "apply"], 1),
    (
        "request_init_method_prototype",
        &["Object", "prototype", "method"],
        2,
    ),
];

const OWN_DISPATCH_TARGETS: &[(&str, &[&str])] = &[
    ("fetch", &["fetch"]),
    ("send_beacon", &["navigator", "sendBeacon"]),
    ("websocket", &["WebSocket"]),
    ("xhr", &["XMLHttpRequest"]),
    ("xhr_open_method", &["XMLHttpRequest", "prototype", "open"]),
];
const DISPATCH_MEMBERS: &[&str] = &["bind", "call", "apply"];

/// A mutation path is either global-rooted or relative to a specific
/// function object created by a native bind expression. Keep these domains
/// disjoint: an arbitrary JavaScript property name cannot collide with a
/// synthetic bound-function identity.
enum MutationPath {
    Global(Vec<Option<String>>),
    Bound {
        function_span: Span,
        members: Vec<Option<String>>,
    },
}

impl MutationPath {
    fn push(&mut self, key: Option<String>) {
        match self {
            Self::Global(path) | Self::Bound { members: path, .. } => path.push(key),
        }
    }

    fn with_key(&self, key: Option<String>) -> Self {
        let mut path = match self {
            Self::Global(path) => Self::Global(path.clone()),
            Self::Bound {
                function_span,
                members,
            } => Self::Bound {
                function_span: *function_span,
                members: members.clone(),
            },
        };
        path.push(key);
        path
    }
}

fn mutation_prefix_matches(path: &[Option<String>], target: &[&str]) -> bool {
    path.len() <= target.len()
        && path
            .iter()
            .zip(target)
            .all(|(segment, name)| segment.as_deref().is_none_or(|value| value == *name))
}

#[derive(Default)]
struct SinkMutations {
    wrapper_globals: std::collections::BTreeMap<String, String>,
    definite: BTreeSet<String>,
    possible: BTreeSet<String>,
    sites: BTreeSet<ApiMutationSite>,
}

impl SinkMutations {
    fn record(
        &mut self,
        path: &MutationPath,
        span: Span,
        operation: &str,
        reflective: bool,
        source: &str,
        lines: &SourceLineIndex,
    ) {
        let (target_pattern, bound_function_span) = match path {
            MutationPath::Global(path) => (path, None),
            MutationPath::Bound {
                function_span,
                members,
            } => (members, Some([function_span.start, function_span.end])),
        };
        let mut affected = Vec::new();
        let possible = reflective || target_pattern.iter().any(Option::is_none);
        match path {
            MutationPath::Global(path) => {
                let normalized = normalized_mutation_path(path);
                for &(family, target, minimum_depth) in MUTATION_TARGETS {
                    if normalized.len() >= minimum_depth
                        && mutation_prefix_matches(normalized, target)
                    {
                        affected.push(family.to_owned());
                    }
                }
                if let [Some(array), Some(prototype), None] = normalized {
                    if array == "Array" && prototype == "prototype" {
                        affected.push("rest_iterator".to_owned());
                    }
                }
                if let [key] = normalized {
                    if let Some(key) = key {
                        affected.extend(self.wrapper_globals.get(key).cloned());
                    } else {
                        affected.extend(self.wrapper_globals.values().cloned());
                    }
                }
                for &(family, target) in OWN_DISPATCH_TARGETS {
                    if let Some((key, object)) = normalized.split_last() {
                        if object.len() == target.len() && mutation_prefix_matches(object, target) {
                            for &operation in DISPATCH_MEMBERS {
                                if key.as_deref().is_none_or(|key| key == operation) {
                                    affected.push(format!("{family}_{operation}"));
                                }
                            }
                        }
                    }
                }
            }
            MutationPath::Bound {
                function_span,
                members,
            } => {
                if let [key] = members.as_slice() {
                    for &operation in DISPATCH_MEMBERS {
                        if key.as_deref().is_none_or(|key| key == operation) {
                            affected.push(format!(
                                "bound_{operation}:{}:{}",
                                function_span.start, function_span.end
                            ));
                        }
                    }
                }
            }
        }
        if possible {
            self.possible.extend(affected.iter().cloned());
        } else {
            self.definite.extend(affected.iter().cloned());
        }
        if affected.is_empty() {
            return;
        }
        let (line, column) = lines.byte_line_column(span.start as usize);
        self.sites.insert(ApiMutationSite {
            start: span.start,
            end: span.end,
            line,
            column,
            operation: operation.to_owned(),
            certainty: if possible { "possible" } else { "definite" }.to_owned(),
            target_pattern: target_pattern.clone(),
            bound_function_span,
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

    fn any(&self, family: &str) -> bool {
        self.definitely(family) || self.possibly(family)
    }

    fn relevant_ordinals(&self, families: &BTreeSet<String>) -> Vec<usize> {
        self.sites
            .iter()
            .enumerate()
            .filter_map(|(ordinal, site)| {
                site.affected_families
                    .iter()
                    .any(|family| families.contains(family))
                    .then_some(ordinal)
            })
            .collect()
    }
}

struct SinkMutationCollector<'s, 'c> {
    source: &'s str,
    lines: &'c SourceLineIndex,
    scoping: &'c Scoping,
    constants: &'c ProvenConstantEnvironment,
    callables: &'c CallableIndex,
    mutations: SinkMutations,
}

impl SinkMutationCollector<'_, '_> {
    fn object_path(&self, expression: &Expression<'_>) -> Option<MutationPath> {
        self.target_path(expression)
            .or_else(|| {
                self.callables
                    .namespace_path(expression, self.scoping, self.constants)
                    .map(MutationPath::Global)
            })
            .or_else(|| {
                self.callables
                    .resolve(expression, self.source, self.scoping, self.constants)
                    .map(|callable| callable.mutation_object_path())
            })
    }

    fn target_path(&self, expression: &Expression<'_>) -> Option<MutationPath> {
        if let Some(path) = global_path_pattern(self.scoping, self.constants, expression) {
            return Some(MutationPath::Global(path));
        }
        match unparenthesized(expression) {
            Expression::StaticMemberExpression(member) if !member.optional => {
                let mut path = self.object_path(&member.object)?;
                path.push(Some(member.property.name.to_string()));
                Some(path)
            }
            Expression::ComputedMemberExpression(member) if !member.optional => {
                let mut path = self.object_path(&member.object)?;
                path.push(static_string(
                    &member.expression,
                    self.scoping,
                    self.constants,
                ));
                Some(path)
            }
            _ => None,
        }
    }

    fn assignment_target_path_pattern(
        &self,
        target: &oxc_ast::ast::SimpleAssignmentTarget<'_>,
    ) -> Option<MutationPath> {
        match target {
            oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) => {
                let reference = self.scoping.get_reference(identifier.reference_id.get()?);
                reference
                    .symbol_id()
                    .is_none()
                    .then(|| MutationPath::Global(vec![Some(identifier.name.to_string())]))
            }
            oxc_ast::ast::SimpleAssignmentTarget::StaticMemberExpression(member)
                if !member.optional =>
            {
                let mut path = self.object_path(&member.object)?;
                path.push(Some(member.property.name.to_string()));
                Some(path)
            }
            oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member)
                if !member.optional =>
            {
                let mut path = self.object_path(&member.object)?;
                path.push(static_string(
                    &member.expression,
                    self.scoping,
                    self.constants,
                ));
                Some(path)
            }
            _ => None,
        }
    }

    fn record(
        &mut self,
        path: Option<MutationPath>,
        span: Span,
        operation: &str,
        reflective: bool,
    ) {
        if let Some(path) = path {
            self.mutations
                .record(&path, span, operation, reflective, self.source, self.lines);
        }
    }

    fn reflective_target(&self, call: &CallExpression<'_>) -> Option<MutationPath> {
        let target = call.arguments.first()?.as_expression()?;
        self.object_path(target)
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
        target: &MutationPath,
        source: &Expression<'_>,
        call_span: Span,
    ) {
        if let Expression::ObjectExpression(object) = unparenthesized(source) {
            for property in &object.properties {
                match property {
                    ObjectPropertyKind::ObjectProperty(property) => {
                        let key = exact_property_key(&property.key, property.computed, |expr| {
                            self.constants.exact_primitive(expr, self.scoping)
                        });
                        if key
                            .as_deref()
                            .is_some_and(|key| is_prototype_setter(property, key))
                        {
                            continue;
                        }
                        self.record(Some(target.with_key(key)), call_span, "Object.assign", true);
                    }
                    ObjectPropertyKind::SpreadProperty(spread) => {
                        self.record_assign_source(target, &spread.argument, call_span);
                    }
                }
            }
        } else {
            self.record(
                Some(target.with_key(None)),
                call_span,
                "Object.assign",
                true,
            );
        }
    }
}

impl<'a> Visit<'a> for SinkMutationCollector<'_, '_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        self.record(
            assignment
                .left
                .as_simple_assignment_target()
                .and_then(|target| self.assignment_target_path_pattern(target)),
            assignment.span,
            "assignment",
            false,
        );
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_update_expression(&mut self, update: &oxc_ast::ast::UpdateExpression<'a>) {
        self.record(
            self.assignment_target_path_pattern(&update.argument),
            update.span,
            "update",
            false,
        );
        walk::walk_update_expression(self, update);
    }

    fn visit_unary_expression(&mut self, unary: &oxc_ast::ast::UnaryExpression<'a>) {
        if unary.operator.as_str() == "delete" {
            self.record(
                self.target_path(&unary.argument),
                unary.span,
                "delete",
                false,
            );
        }
        walk::walk_unary_expression(self, unary);
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            let method = self
                .callables
                .intrinsic_path(&call.callee, self.scoping, self.constants);
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
                                self.record(
                                    Some(target.with_key(None)),
                                    call.span,
                                    "Object.assign",
                                    true,
                                );
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

fn literal_data_key(
    property: &oxc_ast::ast::ObjectProperty<'_>,
    primitive: impl FnOnce(&Expression<'_>) -> Option<StaticPrimitiveValue>,
) -> Option<String> {
    let name = exact_property_key(&property.key, property.computed, primitive)?;
    if property.kind != PropertyKind::Init
        || property.method
        || is_prototype_setter(property, &name)
    {
        return None;
    }
    Some(name)
}

fn literal_method_evidence(source: &str, literal: &str, span: Span) -> FetchInitMethod {
    FetchInitMethod::Literal {
        value: effective_http_method(literal),
        expression: source_fragment(source, span),
    }
}

fn method_value_evidence(
    source: &str,
    value: &Expression<'_>,
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
) -> FetchInitMethod {
    static_string(value, scoping, constants).map_or(FetchInitMethod::Unknown, |literal| {
        literal_method_evidence(source, &literal, value.span())
    })
}

fn fetch_init_method(
    source: &str,
    expression: &Expression<'_>,
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
) -> FetchInitMethod {
    let Expression::ObjectExpression(object) = unparenthesized(expression) else {
        return FetchInitMethod::Unknown;
    };

    let mut state = FetchInitMethod::NoOwnMethod;
    for item in &object.properties {
        let ObjectPropertyKind::ObjectProperty(property) = item else {
            state = FetchInitMethod::Unknown;
            continue;
        };

        let Some(name) = exact_property_key(&property.key, property.computed, |expr| {
            constants.exact_primitive(expr, scoping)
        }) else {
            state = FetchInitMethod::Unknown;
            continue;
        };

        if is_prototype_setter(property, &name) {
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

        state = method_value_evidence(source, &property.value, scoping, constants);
    }
    state
}

fn method_from_init(
    init: FetchInitMethod,
    input_is_static_string: bool,
    request_init_method_prototype_mutated: bool,
) -> (Option<String>, Option<String>, Option<String>) {
    match init {
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

struct Collector<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    constants: &'c ProvenConstantEnvironment,
    mutations: &'c SinkMutations,
    callables: &'c CallableIndex,
    safe_member_refs: &'c BTreeSet<ReferenceId>,
    lines: &'c SourceLineIndex,
    callsites: BTreeSet<ApiCallsite>,
}

type MethodEvidence = (Option<String>, Option<String>, Option<String>);

fn xhr_method(arguments: &ApiArguments) -> MethodEvidence {
    let (literal, expression) = arguments.exact(0);
    let (method, status) = literal.map_or((None, "unknown"), |literal| {
        let normalized = effective_http_method(&literal);
        let status = if normalized.is_some() {
            "exact"
        } else {
            "invalid"
        };
        (normalized, status)
    });
    (method, expression, Some(status.into()))
}

impl Collector<'_, '_> {
    fn visit_invocation(
        &mut self,
        callee: &Expression<'_>,
        arguments: &[oxc_ast::ast::Argument<'_>],
        span: Span,
        constructor: bool,
    ) {
        let Some(callable) =
            self.callables
                .resolve(callee, self.source, self.scoping, self.constants)
        else {
            return;
        };
        // Returned function invocations use the same positional value
        // builder as wrappers, retaining known spread origins.
        if callable.is_returned() || !callable.callable_as(constructor) {
            return;
        }
        let mut callable = callable;
        callable
            .prefix
            .append(arguments, self.source, self.scoping, self.constants);
        self.emit_invocation(callee, callable, span);
    }

    fn emit_invocation(&mut self, callee: &Expression<'_>, callable: Callable, span: Span) {
        self.emit_forwarded(callee, callable, span, &BTreeSet::new());
    }

    fn emit_forwarded(
        &mut self,
        callee: &Expression<'_>,
        callable: Callable,
        span: Span,
        forwarding_dependencies: &BTreeSet<String>,
    ) {
        if callable.kind == ApiKind::XhrConstructor {
            return;
        }
        let family = callable.kind.family();
        let mut affected = BTreeSet::new();
        let mut mutated = false;
        // Captured function values may outlive replacement of their original
        // global property. Do not discard their potentially real invocation.
        let mut binding_families =
            vec![(family, callable.captured || callable.constructor_captured)];
        if callable.kind == ApiKind::XhrOpen {
            binding_families.push(("xhr", callable.constructor_captured));
        }
        for (family, captured) in binding_families {
            if self.mutations.definitely(family) && !captured {
                return;
            }
            if self.mutations.any(family) {
                mutated = true;
                affected.insert(family.to_owned());
            }
        }
        for dependency in callable
            .dispatch_dependencies()
            .into_iter()
            .chain(forwarding_dependencies.iter().cloned())
        {
            if self.mutations.any(&dependency) {
                mutated = true;
                affected.insert(dependency);
            }
        }
        let escaped = callable.receiver.is_some_and(|symbol| {
            !symbol_is_safe_xhr_receiver(self.scoping, symbol, self.safe_member_refs)
        });
        let candidate = mutated || escaped;
        let arguments_evidence = &callable.prefix;
        let url = arguments_evidence.exact(usize::from(callable.kind == ApiKind::XhrOpen));
        let prototype_mutated = self.mutations.any("request_init_method_prototype");
        let mut method = match callable.kind {
            ApiKind::Fetch => arguments_evidence.fetch_method(url.0.is_some(), prototype_mutated),
            ApiKind::Beacon => (Some("POST".to_owned()), None, Some("exact".to_owned())),
            ApiKind::XhrOpen => xhr_method(arguments_evidence),
            ApiKind::WebSocket | ApiKind::XhrConstructor => (None, None, None),
        };
        if callable.kind == ApiKind::Fetch
            && prototype_mutated
            && method.2.as_deref() == Some("unknown")
        {
            affected.insert("request_init_method_prototype".into());
        }
        if candidate && method.2.as_deref() == Some("exact") {
            method.2 = Some("conditional".into());
        }
        let proof = if mutated {
            if callable.invocation_form() == "wrapper" {
                "forwarded_api_binding_or_local_wrapper_may_be_mutated"
            } else if callable.captured || callable.constructor_captured {
                "captured_api_binding_or_native_dispatch_may_be_mutated"
            } else {
                match callable.kind {
                    ApiKind::Fetch => "unresolved_global_member_mutation_may_replace_fetch",
                    ApiKind::Beacon => "unresolved_global_member_mutation_may_replace_sendBeacon",
                    ApiKind::WebSocket => "unresolved_global_member_mutation_may_replace_WebSocket",
                    ApiKind::XhrOpen => {
                        "unresolved_global_member_mutation_may_replace_XMLHttpRequest_or_open"
                    }
                    ApiKind::XhrConstructor => STANDARD_BROWSER_API_ASSUMPTION,
                }
            }
        } else if escaped {
            "unreassigned_binding_initialized_from_standard_XMLHttpRequest_but_receiver_escapes_or_is_mutable"
        } else if callable.invocation_form() == "wrapper" {
            "stable_local_wrapper_with_semantically_forwarded_arguments"
        } else if matches!(
            callable.invocation_form(),
            "call" | "apply" | "reflect_apply"
        ) {
            "native_api_dispatch_with_proven_receiver"
        } else if callable.bound {
            "native_bound_api_with_proven_receiver"
        } else if callable.captured {
            "immutable_lexical_api_alias"
        } else if callable.kind == ApiKind::XhrOpen {
            "stable_symbol_initialized_from_standard_XMLHttpRequest"
        } else {
            STANDARD_BROWSER_API_ASSUMPTION
        };
        let callee_text = global_path(self.scoping, self.constants, callee)
            .unwrap_or_else(|| source_fragment(self.source, callee.span()));
        let (line, column) = self.lines.byte_line_column(span.start as usize);
        self.callsites.insert(ApiCallsite {
            kind: callable.kind.callsite_kind(candidate).to_owned(),
            start: span.start,
            end: span.end,
            line,
            column,
            callee: callee_text,
            api_origin: callable.kind.canonical_path().to_owned(),
            invocation_form: callable.invocation_form().to_owned(),
            forwarded_sink_span: callable
                .forwarded_sink_span
                .or_else(|| callable.is_returned().then_some([span.start, span.end])),
            binding_witnesses: callable.witnesses(),
            proof: proof.to_owned(),
            binding_status: if candidate { "candidate" } else { "standard" }.to_owned(),
            standard_browser_api_semantics_required: true,
            mutation_site_ordinals: self.mutations.relevant_ordinals(&affected),
            method: method.0,
            method_expression: method.1,
            method_status: method.2,
            url: url.0,
            url_expression: url.1,
        });
    }
}

impl<'a> Visit<'a> for Collector<'_, '_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Some(dispatch) =
                self.callables
                    .resolve_dispatch(call, self.source, self.scoping, self.constants)
            {
                self.emit_invocation(&call.callee, dispatch.callable, call.span);
            } else {
                self.visit_invocation(&call.callee, &call.arguments, call.span, false);
            }
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &NewExpression<'a>) {
        self.visit_invocation(
            &expression.callee,
            &expression.arguments,
            expression.span,
            true,
        );
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
            .with_build_nodes(true)
            .with_cfg(true)
            .build(&program);
        if !semantic.diagnostics.is_empty() {
            continue;
        }
        let scoping = semantic.semantic.scoping();
        budget.checkpoint()?;
        let constants = ProvenConstantEnvironment::collect(&program, scoping);
        budget.checkpoint()?;

        let mut callables = CallableIndex::collect(&program, source, scoping, &constants);
        budget.checkpoint()?;

        let wrappers = forwarding::WrapperIndex::collect(&semantic.semantic, budget)?;
        forwarding::collect_returned_values(
            &semantic.semantic,
            &wrappers,
            &mut callables,
            source,
            &constants,
            budget,
        )?;
        let wrapper_globals = wrappers
            .root_mutation_targets()
            .map(|(name, family)| (name.to_owned(), family))
            .collect();

        let lines = SourceLineIndex::new(source);
        let mut mutations = SinkMutationCollector {
            source,
            lines: &lines,
            scoping,
            constants: &constants,
            callables: &callables,
            mutations: SinkMutations {
                wrapper_globals,
                ..SinkMutations::default()
            },
        };
        mutations.visit_program(&program);
        budget.checkpoint()?;

        let mut safe_member_refs = SafeMemberReferenceCollector {
            source,
            scoping,
            constants: &constants,
            callables: &callables,
            mutations: &mutations.mutations,
            refs: BTreeSet::new(),
        };
        safe_member_refs.visit_program(&program);
        budget.checkpoint()?;

        let mut collector = Collector {
            source,
            scoping,
            constants: &constants,
            mutations: &mutations.mutations,
            callables: &callables,
            safe_member_refs: &safe_member_refs.refs,
            lines: &lines,
            callsites: BTreeSet::new(),
        };
        collector.visit_program(&program);
        budget.checkpoint()?;
        for node in semantic.semantic.nodes().iter() {
            budget.consume(1)?;
            let site = match node.kind() {
                oxc_ast::AstKind::CallExpression(call) if !call.optional => {
                    forwarding::InvocationSite {
                        callee: &call.callee,
                        arguments: &call.arguments,
                        span: call.span,
                        constructor: false,
                    }
                }
                oxc_ast::AstKind::NewExpression(new) => forwarding::InvocationSite {
                    callee: &new.callee,
                    arguments: &new.arguments,
                    span: new.span,
                    constructor: true,
                },
                _ => continue,
            };
            forwarding::specialize(site, &semantic.semantic, &wrappers, &mut collector, budget)?;
        }
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
    use anyhow::{Context, Result};
    use work_budget::WorkBudget;

    fn analyze_api_surface(source: &str) -> Result<Vec<ApiCallsite>> {
        Ok(
            analyze_api_surface_budgeted(source, &WorkBudget::unlimited("api-surface-test"))?
                .callsites,
        )
    }

    #[test]
    fn api_callsites_use_ecmascript_lines_and_byte_columns() -> Result<()> {
        let source = "// comment\r/*💡*/fetch('/a');\r\nfetch('/b');\u{2028}fetch('/c');\u{2029}fetch('/d');";
        let rows = analyze_api_surface(source)?;
        assert_eq!(
            rows.iter()
                .map(|row| (row.line, row.column))
                .collect::<Vec<_>>(),
            [(2, 8), (3, 0), (4, 0), (5, 0)]
        );
        Ok(())
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
    fn frame_primitives_compose_urls_data_keys_and_request_methods() -> Result<()> {
        let source = r#"
const transport = (base, path, key, select) => {
    const endpoint = base + path;
    const verb = select ? "PATCH" : "DELETE";
    const init = {[key]: verb};
    return fetch(endpoint, init);
};
transport("https://example.test", "/one", "method", true);
transport("https://example.test", "/two", "method", false);
transport("https://example.test", "/three", "other", false);
"#;
        let rows = analyze_api_surface(source)?;
        let wrappers = rows
            .iter()
            .filter(|row| row.invocation_form == "wrapper")
            .collect::<Vec<_>>();
        let evidence = wrappers
            .iter()
            .map(|row| {
                (
                    row.url.as_deref(),
                    row.method.as_deref(),
                    row.method_status.as_deref(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            evidence,
            [
                (
                    Some("https://example.test/one"),
                    Some("PATCH"),
                    Some("exact")
                ),
                (
                    Some("https://example.test/two"),
                    Some("DELETE"),
                    Some("exact")
                ),
                (
                    Some("https://example.test/three"),
                    Some("GET"),
                    Some("exact")
                ),
            ],
            "{rows:#?}"
        );
        assert!(wrappers
            .iter()
            .all(|row| row.url_expression.as_deref() == Some("base + path")));
        assert_eq!(
            wrappers[0].method_expression.as_deref(),
            Some(r#"select ? "PATCH" : "DELETE""#)
        );
        Ok(())
    }

    #[test]
    fn cached_frame_requirements_are_independent_of_incoming_value_types() -> Result<()> {
        let source = r#"
const send = (base, path, options) => fetch(base + path, options);
send({toString() { sideEffect(); return "/object"; }}, "/unsafe", {method:"POST"});
send("/known", "/first", {method:"PUT"});
send(unknown, "/unresolved", {method:"DELETE"});
send("/known", "/second", {method:"PATCH"});
const spread = (url, options) => fetch(...[url, options]);
spread("/materialized", {method:"POST"});
"#;
        let rows = analyze_api_surface(source)?;
        let evidence = rows
            .iter()
            .filter(|row| row.invocation_form == "wrapper")
            .map(|row| (row.url.as_deref(), row.method.as_deref()))
            .collect::<Vec<_>>();
        assert_eq!(
            evidence,
            [
                (Some("/known/first"), Some("PUT")),
                (Some("/known/second"), Some("PATCH")),
                (Some("/materialized"), Some("POST")),
            ],
            "{rows:#?}"
        );
        Ok(())
    }

    #[test]
    fn frame_primitives_preserve_lexical_origins_and_missing_value_semantics() -> Result<()> {
        let source = r#"
const base = "https://example.test";
const relay = (suffix, verb) => {
    const path = base + suffix;
    return leaf(path, verb);
};
relay("/before-initialization", "POST");
const leaf = (base, choose) => {
    const url = base + "/data";
    return fetch(url, {method: choose ?? "PATCH"});
};
relay("/one", "PUT");
relay("/two");
const templated = (name, count) => fetch("https://api.test/" + name + "/" + count, {method: count === 0 ? "POST" : "DELETE"});
templated("widget", 0);
templated("other", 2);
"#;
        let rows = analyze_api_surface(source)?;
        let selected = rows
            .iter()
            .filter(|row| matches!(row.callee.as_str(), "relay" | "templated"))
            .collect::<Vec<_>>();
        assert_eq!(
            selected
                .iter()
                .map(|row| (row.url.as_deref(), row.method.as_deref()))
                .collect::<Vec<_>>(),
            [
                (Some("https://example.test/one/data"), Some("PUT")),
                (Some("https://example.test/two/data"), Some("PATCH")),
                (Some("https://api.test/widget/0"), Some("POST")),
                (Some("https://api.test/other/2"), Some("DELETE")),
            ],
            "{rows:#?}"
        );
        Ok(())
    }

    #[test]
    fn deferred_lookup_does_not_move_alias_initialization_to_invocation_time() -> Result<()> {
        let source = r#"
const invoke = url => alias(url);
const alias = later;
const later = url => fetch(url);
invoke("/initializer-in-tdz");
const early = url => future(url);
early("/before-initialization");
const future = url => fetch(url);
early("/after-initialization");
const validAlias = future;
const throughAlias = url => validAlias(url);
throughAlias("/initialized-alias");
"#;
        let rows = analyze_api_surface(source)?;
        let urls = rows
            .iter()
            .filter(|row| row.invocation_form == "wrapper")
            .filter_map(|row| row.url.as_deref())
            .collect::<Vec<_>>();
        assert_eq!(
            urls,
            ["/after-initialization", "/initialized-alias"],
            "{rows:#?}"
        );
        Ok(())
    }

    #[test]
    fn computed_apply_values_follow_native_nullish_and_primitive_rules() -> Result<()> {
        let source = r#"
const bound = fetch.bind(window, "/bound");
const invoke = (fn, empty) => fn.apply(empty ? null : 123, empty ? void 0 : 4);
invoke(bound, true);
invoke(bound, false);
const reflected = (fn, empty) => Reflect.apply(fn, null, empty ? null : 1);
reflected(bound, true);
reflected(bound, false);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 1, "{rows:#?}");
        assert_eq!(rows[0].url.as_deref(), Some("/bound"));
        assert_eq!(rows[0].method.as_deref(), Some("GET"));
        assert_eq!(rows[0].invocation_form, "wrapper");
        Ok(())
    }

    #[test]
    fn primitive_template_interpolation_reuses_ecmascript_coercion() -> Result<()> {
        let source = r#"
const render = (name, count, flag) => fetch(`/${name}/${count}/${flag}`);
render("name", 12, true);
render("other", -0, false);
"#;
        let rows = analyze_api_surface(source)?;
        let urls = rows
            .iter()
            .filter(|row| row.invocation_form == "wrapper")
            .map(|row| row.url.as_deref())
            .collect::<Vec<_>>();
        assert_eq!(
            urls,
            [Some("/name/12/true"), Some("/other/0/false")],
            "{rows:#?}"
        );
        Ok(())
    }

    #[test]
    fn wrapper_local_frames_propagate_aliases_and_private_record_fields() -> Result<()> {
        let source = r#"
function transport(fn, receiver, url, method) {
    const verb = method;
    const init = {method: "GET", ["me" + "thod"]: verb};
    const args = [url, init];
    const request = fn;
    return request.apply(receiver, args);
}
transport(fetch, window, "/local", "PATCH");
transport(fetch, window, "/other", "POST");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 2, "{rows:#?}");
        for (row, (url, method)) in rows.iter().zip([("/local", "PATCH"), ("/other", "POST")]) {
            assert_eq!(row.url.as_deref(), Some(url));
            assert_eq!(row.method.as_deref(), Some(method));
            assert_eq!(row.binding_status, "standard");
            assert_eq!(
                row.binding_witnesses
                    .iter()
                    .filter(|w| w.kind == "wrapper_local_binding")
                    .count(),
                4
            );
            let [start, end] = row
                .forwarded_sink_span
                .context("missing original invocation")?;
            assert_eq!(
                &source[start as usize..end as usize],
                "request.apply(receiver, args)"
            );
        }
        Ok(())
    }

    #[test]
    fn local_aliases_retain_rest_arrays_and_record_origins_across_wrappers() -> Result<()> {
        let source = r#"
const leaf = (fn, items) => {
    const copy = items;
    return Reflect.apply(fn, window, copy);
};
const relay = (url, ...args) => {
    const rest = args, list = [url, ...rest];
    return leaf(fetch, list);
};
relay("/first", {method: "PUT"});
relay("/second", ...unresolved, {method: "POST"});
"#;
        let rows = analyze_api_surface(source)?;
        let specialized = rows
            .iter()
            .filter(|row| row.callee == "relay")
            .collect::<Vec<_>>();
        assert_eq!(
            specialized
                .iter()
                .map(|row| (
                    row.url.as_deref(),
                    row.method.as_deref(),
                    row.method_status.as_deref()
                ))
                .collect::<Vec<_>>(),
            [
                (Some("/first"), Some("PUT"), Some("exact")),
                (Some("/second"), None, Some("unknown")),
            ],
            "{rows:#?}"
        );
        assert_eq!(
            specialized[0]
                .binding_witnesses
                .iter()
                .filter(|w| w.kind == "wrapper_local_binding")
                .count(),
            3
        );
        Ok(())
    }

    #[test]
    fn local_frame_proof_rejects_effectful_initializers_tdz_and_alias_escapes() -> Result<()> {
        let source = r#"
const escaped = (url, options) => {
    const alias = options;
    return fetch(url, options, mutate(alias));
};
escaped("/not-specialized", {method:"POST"});
const tdz = (url) => {
    const first = later, later = url;
    return fetch(first);
};
tdz("/not-initialized");
const sideEffect = (url, method) => {
    const init = {method, extra: arbitrary()};
    return fetch(url, init);
};
sideEffect("/not-proven", "PATCH");
const dynamic = (url) => {
    const init = {method:"POST"};
    return fetch(url, init, eval("init.method = 'DELETE'"));
};
dynamic("/not-proven");
const safe = (url, method) => {
    const key = "me";
    const init = {[key + "thod"]: method};
    return fetch(url, init);
};
safe("/safe", "PATCH");
"#;
        let rows = analyze_api_surface(source)?;
        let specialized = rows
            .iter()
            .filter(|row| row.invocation_form == "wrapper")
            .collect::<Vec<_>>();
        assert_eq!(specialized.len(), 1, "{rows:#?}");
        assert_eq!(specialized[0].callee, "safe");
        assert_eq!(specialized[0].url.as_deref(), Some("/safe"));
        assert_eq!(specialized[0].method.as_deref(), Some("PATCH"));
        Ok(())
    }

    #[test]
    fn native_bind_factories_capture_arguments_and_preserve_receivers() -> Result<()> {
        let source = r#"
const make = (fn, receiver, base, path) => {
    const url = base + path;
    return fn.bind(receiver, url);
};
const send = make(fetch, window, "/api", "/one");
send({method:"PATCH"});
make(navigator.sendBeacon, navigator, "/beacon", "/two")(payload);
make(navigator.sendBeacon, window, "/invalid", "/receiver")(payload);
const socket = make(WebSocket, null, "wss://example.test", "/socket");
new socket();
socket();
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(
            rows.iter()
                .map(|row| (row.kind.as_str(), row.url.as_deref(), row.method.as_deref()))
                .collect::<Vec<_>>(),
            [
                ("fetch", Some("/api/one"), Some("PATCH")),
                ("send_beacon", Some("/beacon/two"), Some("POST")),
                ("websocket", Some("wss://example.test/socket"), None),
            ],
            "{rows:#?}"
        );
        assert!(rows.iter().all(|row| row.invocation_form == "wrapper"
            && row.binding_witnesses.iter().any(|w| w.kind == "bind")));
        Ok(())
    }

    #[test]
    fn returned_native_values_support_all_explicit_dispatch_modes() -> Result<()> {
        let source = r#"
const identity = fn => fn;
const beacon = identity(navigator.sendBeacon);
beacon.call(navigator, "/call", payload);
beacon.apply(navigator, ["/apply", payload]);
Reflect.apply(identity(navigator.sendBeacon), navigator, ["/reflect", payload]);
identity(navigator.sendBeacon)("/detached", payload);
beacon.call(window, "/invalid", payload);
const bind = (fn, recv, ...args) => fn.bind(recv, ...args);
bind(fetch, window, "/bound").apply({}, [{method:"PUT"}]);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(
            rows.iter()
                .map(|row| row.url.as_deref())
                .collect::<Vec<_>>(),
            [
                Some("/call"),
                Some("/apply"),
                Some("/reflect"),
                Some("/bound")
            ],
            "{rows:#?}"
        );
        assert_eq!(rows[3].method.as_deref(), Some("PUT"));
        for (row, op) in rows.iter().zip(["call", "apply", "reflect_apply", "apply"]) {
            assert!(row.binding_witnesses.iter().any(|w| w.kind == op));
        }
        Ok(())
    }

    #[test]
    fn returned_bind_allocations_and_aliases_have_independent_mutation_identity() -> Result<()> {
        let source = r#"
const make = url => fetch.bind(window, url);
const one = make("/one");
const two = make("/two");
const alias = one;
alias.call = replacement;
one.call(window, {method:"POST"});
two.call(window, {method:"PUT"});
one();
"#;
        let analysis =
            super::analyze_api_surface(source, &WorkBudget::unlimited("factory-bound-mutations"))?;
        let rows = &analysis.callsites;
        assert_eq!(
            rows.iter()
                .map(|row| (row.kind.as_str(), row.url.as_deref()))
                .collect::<Vec<_>>(),
            [
                ("fetch_candidate", Some("/one")),
                ("fetch", Some("/two")),
                ("fetch", Some("/one")),
            ],
            "{analysis:#?}"
        );
        let site = &analysis.mutation_sites[rows[0].mutation_site_ordinals[0]];
        let [start, end] = site
            .bound_function_span
            .context("missing bound allocation")?;
        assert_eq!(&source[start as usize..end as usize], r#"make("/one")"#);
        assert!(rows[1..]
            .iter()
            .all(|row| row.mutation_site_ordinals.is_empty()));
        Ok(())
    }

    #[test]
    fn returned_callable_spreads_retain_positions_and_iterator_dependency() -> Result<()> {
        let source = r#"
const identity = fn => fn;
const send = identity(fetch);
send(...["/spread", {method:"POST"}]);
identity(fetch)(...["/inline", {method:"PUT"}]);
Array.prototype[Symbol.iterator] = replacement;
"#;
        let analysis =
            super::analyze_api_surface(source, &WorkBudget::unlimited("returned-spread"))?;
        assert_eq!(
            analysis
                .callsites
                .iter()
                .map(|row| (row.url.as_deref(), row.method.as_deref(), row.kind.as_str()))
                .collect::<Vec<_>>(),
            [
                (Some("/spread"), Some("POST"), "fetch_candidate"),
                (Some("/inline"), Some("PUT"), "fetch_candidate"),
            ],
            "{analysis:#?}"
        );
        assert!(analysis
            .callsites
            .iter()
            .all(|row| row.mutation_site_ordinals == [0]));
        Ok(())
    }

    #[test]
    fn factory_mutation_provenance_flows_through_returned_explicit_dispatch() -> Result<()> {
        let source = r#"
function make(fn, r, url) { return fn.bind(r, url); }
const send = make(fetch, window, "/candidate");
window.make = replacement;
send.apply(null, [{method:"POST"}]);
const identity = fn => fn;
const request = identity(fetch);
request.call = replacement;
Reflect.apply(request, window, ["/reflect"]);
request.call(window, "/call");
"#;
        let analysis = super::analyze_api_surface(
            source,
            &WorkBudget::unlimited("factory-dispatch-mutations"),
        )?;
        assert_eq!(
            analysis
                .callsites
                .iter()
                .map(|row| row.kind.as_str())
                .collect::<Vec<_>>(),
            ["fetch_candidate", "fetch", "fetch_candidate"],
            "{analysis:#?}"
        );
        assert!(analysis.callsites[0]
            .mutation_site_ordinals
            .iter()
            .any(|i| analysis.mutation_sites[*i]
                .affected_families
                .iter()
                .any(|family| family.starts_with("wrapper_global:"))));
        assert!(analysis.callsites[1].mutation_site_ordinals.is_empty());
        assert_eq!(
            analysis.callsites[2].method_status.as_deref(),
            Some("conditional")
        );
        Ok(())
    }

    #[test]
    fn synchronous_callable_returns_preserve_receiver_and_constructor_requirements() -> Result<()> {
        let source = r#"
const identity = (fn) => {const selected = fn; return selected;};
identity(fetch)("/inline", {method: "POST"});
const req = identity(identity(fetch));
const alias = req;
alias("/alias");
identity(navigator.sendBeacon)("/detached", payload);
new (identity(WebSocket))("wss://example.test/live");
identity(WebSocket)("wss://example.test/invalid");
const asyncIdentity = async fn => fn;
asyncIdentity(fetch)("/promise-not-function");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert_eq!(
            rows.iter()
                .map(|row| row.url.as_deref())
                .collect::<Vec<_>>(),
            [
                Some("/inline"),
                Some("/alias"),
                Some("wss://example.test/live")
            ]
        );
        assert_eq!(rows[0].method.as_deref(), Some("POST"));
        assert_eq!(rows[1].method.as_deref(), Some("GET"));
        assert_eq!(
            rows[1]
                .binding_witnesses
                .iter()
                .filter(|w| w.kind == "returned_callable")
                .count(),
            2
        );
        assert_eq!(rows[2].kind, "websocket");
        assert!(rows
            .iter()
            .all(|row| row.invocation_form == "wrapper" && row.binding_status == "standard"));
        Ok(())
    }

    #[test]
    fn returned_callable_keeps_factory_mutation_evidence() -> Result<()> {
        let source = r#"
function choose(fn) { return fn; }
const req = choose(fetch);
window.choose = replacement;
req("/candidate");
const safe = fn => fn;
safe(fetch)("/standard");
"#;
        let analysis = super::analyze_api_surface(
            source,
            &WorkBudget::unlimited("returned-callable-mutations"),
        )?;
        assert_eq!(analysis.callsites.len(), 2, "{analysis:#?}");
        assert_eq!(analysis.callsites[0].kind, "fetch_candidate");
        assert_eq!(
            analysis.callsites[0].method_status.as_deref(),
            Some("conditional")
        );
        assert_eq!(analysis.callsites[0].mutation_site_ordinals, [0]);
        assert!(analysis.mutation_sites[0]
            .affected_families
            .iter()
            .any(|family| family.starts_with("wrapper_global:")));
        assert_eq!(analysis.callsites[1].kind, "fetch");
        assert_eq!(
            analysis.callsites[1].mutation_site_ordinals,
            [] as [usize; 0]
        );
        Ok(())
    }

    #[test]
    fn computed_literal_method_keys_share_constant_proof_with_local_records() -> Result<()> {
        let source = r#"
const key = "me" + "thod";
fetch("/computed", {[key]: "PATCH"});
fetch("/overwrite", {method:"PATCH", ["me" + "thod"]:"POST"});
fetch("/unknown", {method:"PATCH", [dynamic()]: "POST"});
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 3);
        assert_eq!(rows[0].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[1].method.as_deref(), Some("POST"));
        assert_eq!(rows[2].method_status.as_deref(), Some("unknown"));
        Ok(())
    }

    #[test]
    fn forwarded_native_dispatch_recovers_receivers_and_bound_arguments() -> Result<()> {
        let source = r#"
const invoke = (fn, receiver, url, init) => fn.call(receiver, url, init);
const apply = (fn, receiver, list) => fn.apply(receiver, list);
const bound = fetch.bind(window, "/bound");
invoke(fetch, window, "/call", {method: "PATCH"});
invoke(navigator.sendBeacon, navigator, "/beacon", payload);
invoke(navigator.sendBeacon, window, "/invalid", payload);
apply(bound, {}, [{method: "PUT"}]);
apply(navigator.sendBeacon, navigator, ["/apply", payload]);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        assert!(rows
            .iter()
            .all(|row| row.invocation_form == "wrapper" && row.binding_status == "standard"));
        assert_eq!(
            rows.iter()
                .map(|row| row.url.as_deref())
                .collect::<Vec<_>>(),
            [
                Some("/call"),
                Some("/beacon"),
                Some("/bound"),
                Some("/apply")
            ]
        );
        assert_eq!(rows[0].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[2].method.as_deref(), Some("PUT"));
        for row in &rows {
            let [start, end] = row.forwarded_sink_span.context("missing forwarded span")?;
            let origin = &source[start as usize..end as usize];
            assert!(origin.starts_with("fn.call(") || origin.starts_with("fn.apply("));
            assert!(row
                .binding_witnesses
                .iter()
                .any(|w| matches!(w.kind.as_str(), "call" | "apply")));
        }
        Ok(())
    }

    #[test]
    fn forwarded_array_values_survive_multiple_wrapper_frames_and_reflect_namespace_aliases(
    ) -> Result<()> {
        let source = r#"
const dispatch = (R, fn, receiver, list) => R["ap" + "ply"](fn, receiver, list);
const relay = (init, url, fn) => dispatch(Reflect, fn, window, [url, init]);
relay({method: "POST"}, "https://example.test/data", fetch);
const uncertain = (fn, receiver, url, init) => Reflect.apply(fn, receiver, [url, ...unknown, init]);
uncertain(fetch, window, "/unknown-tail", {method: "DELETE"});
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 2, "{rows:#?}");
        assert_eq!(rows[0].url.as_deref(), Some("https://example.test/data"));
        assert_eq!(rows[0].method.as_deref(), Some("POST"));
        assert_eq!(
            rows[0]
                .binding_witnesses
                .iter()
                .filter(|w| w.kind == "wrapper_definition")
                .count(),
            2
        );
        assert!(rows[0]
            .binding_witnesses
            .iter()
            .any(|w| w.kind == "reflect_apply"));
        assert_eq!(rows[1].url.as_deref(), Some("/unknown-tail"));
        assert_eq!(rows[1].method_status.as_deref(), Some("unknown"));
        Ok(())
    }

    #[test]
    fn rest_array_indexing_does_not_depend_on_native_array_iteration() -> Result<()> {
        let source = r#"
const call = (fn, recv, ...args) => fn.call(recv, ...args);
const apply = (fn, recv, ...args) => fn.apply(recv, args);
const reflect = (fn, recv, ...args) => Reflect.apply(fn, recv, args);
Array.prototype[Symbol.iterator] = replacement;
call(fetch, window, "/call", {method: "POST"});
apply(fetch, window, "/apply", {method: "PUT"});
reflect(fetch, window, "/reflect", {method: "PATCH"});
"#;
        let analysis =
            super::analyze_api_surface(source, &WorkBudget::unlimited("forwarded-rest-dispatch"))?;
        let rows = &analysis.callsites;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch_candidate");
        assert_eq!(rows[0].method_status.as_deref(), Some("conditional"));
        assert_eq!(
            analysis.mutation_sites[rows[0].mutation_site_ordinals[0]].affected_families,
            ["rest_iterator"]
        );
        assert!(rows[1..]
            .iter()
            .all(|row| row.kind == "fetch" && row.mutation_site_ordinals.is_empty()));
        assert_eq!(rows[1].method.as_deref(), Some("PUT"));
        assert_eq!(rows[2].method.as_deref(), Some("PATCH"));
        Ok(())
    }

    #[test]
    fn forwarded_dispatch_respects_missing_and_invalid_array_like_inputs() -> Result<()> {
        let source = r#"
const bound = fetch.bind(window, "/bound");
const apply = (fn, args) => fn.apply(null, args);
const reflect = (fn, r, args) => Reflect.apply(fn, r, args);
apply(bound, null);
apply(bound, 12);
reflect(bound, window, null);
reflect(fetch, undefined, ["/undefined-receiver"]);
reflect(fetch, window, unresolvedArray);
const omitted = (r) => Reflect.apply(fetch, r, ["/omitted-receiver"]);
omitted();
const badReceiver = (r, url) => fetch.call(r, url);
badReceiver({}, "/invalid-receiver");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        assert_eq!(rows[0].url.as_deref(), Some("/bound"));
        assert_eq!(rows[0].method.as_deref(), Some("GET"));
        assert_eq!(rows[1].url.as_deref(), Some("/undefined-receiver"));
        assert!(rows[2].url.is_none());
        assert_eq!(rows[3].url.as_deref(), Some("/omitted-receiver"));
        assert!(rows.iter().all(|row| row.invocation_form == "wrapper"));
        Ok(())
    }

    #[test]
    fn forwarded_dispatch_does_not_promote_escaped_objects_or_invalidated_callable_values(
    ) -> Result<()> {
        let source = r#"
const mutate = (fn, r, url, init) => fn.apply(r, [url, (modify(init), init)]);
mutate(fetch, window, "/unknown-method", {method: "POST"});
const invalid = (fn, r, url) => fn.call((fn.call = replacement, r), url);
invalid(fetch, window, "/not-proven");
const customIterator = (url, init) => fetch(url, init, ...init);
customIterator("/iterator", {method: "PATCH"});
"#;
        let rows = analyze_api_surface(source)?;
        let wrappers = rows
            .iter()
            .filter(|row| row.invocation_form == "wrapper")
            .collect::<Vec<_>>();
        assert_eq!(wrappers.len(), 2, "{rows:#?}");
        assert_eq!(wrappers[0].url.as_deref(), Some("/unknown-method"));
        assert_eq!(wrappers[0].method_status.as_deref(), Some("unknown"));
        assert_eq!(wrappers[1].url.as_deref(), Some("/iterator"));
        assert_eq!(wrappers[1].method_status.as_deref(), Some("unknown"));
        Ok(())
    }

    #[test]
    fn forwarded_dispatch_preserves_operation_specific_mutation_provenance() -> Result<()> {
        let source = r#"
const call = (fn, receiver, url) => fn.call(receiver, url);
const apply = (fn, receiver, args) => fn.apply(receiver, args);
const reflect = (R, fn, receiver, args) => R.apply(fn, receiver, args);
const request = fetch;
request.call = replacement;
Reflect.apply = replacement;
call(request, window, "/call");
apply(request, window, ["/apply"]);
reflect(Reflect, request, window, ["/reflect"]);
"#;
        let analysis = super::analyze_api_surface(
            source,
            &WorkBudget::unlimited("forwarded-native-mutations"),
        )?;
        let rows = &analysis.callsites;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert_eq!(
            rows.iter().map(|row| row.kind.as_str()).collect::<Vec<_>>(),
            ["fetch_candidate", "fetch", "fetch_candidate"]
        );
        for (row, family) in [(&rows[0], "fetch_call"), (&rows[2], "reflect_apply")] {
            assert_eq!(row.mutation_site_ordinals.len(), 1);
            assert_eq!(
                analysis.mutation_sites[row.mutation_site_ordinals[0]].affected_families,
                [family]
            );
        }
        assert_eq!(rows[1].mutation_site_ordinals, [] as [usize; 0]);
        Ok(())
    }

    #[test]
    fn nested_bind_objects_with_identical_start_offsets_keep_distinct_identity() -> Result<()> {
        let source = r#"
const chain = fetch.bind(window).bind(window, "/chain");
chain.bind = replacement;
chain();
const alias = chain.bind(null);
alias();
"#;
        let analysis =
            super::analyze_api_surface(source, &WorkBudget::unlimited("nested-bind-identity"))?;
        assert_eq!(analysis.callsites.len(), 2, "{analysis:#?}");
        let direct = &analysis.callsites[0];
        let rebound = &analysis.callsites[1];
        assert_eq!(direct.kind, "fetch");
        assert_eq!(direct.url.as_deref(), Some("/chain"));
        assert_eq!(direct.mutation_site_ordinals, [] as [usize; 0]);
        assert_eq!(rebound.kind, "fetch_candidate");
        let site = &analysis.mutation_sites[rebound.mutation_site_ordinals[0]];
        let [start, end] = site
            .bound_function_span
            .context("missing bound object origin")?;
        assert_eq!(
            &source[start as usize..end as usize],
            r#"fetch.bind(window).bind(window, "/chain")"#
        );
        Ok(())
    }

    #[test]
    fn wrapper_chains_specialize_reordered_arguments_without_losing_original_sink() -> Result<()> {
        let source = r#"
function send(url, init) { return fetch(url, init); }
const relay = (ignored, init, url) => send(url, init);
const alias = relay;
alias(17, {method: "PATCH"}, "https://example.test/one");
alias(18, {method: "POST"}, "/two");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        let original = rows
            .iter()
            .find(|row| row.callee == "fetch")
            .context("missing original sink")?;
        assert!(original.forwarded_sink_span.is_none());
        assert!(original.url.is_none());
        let specialized = rows
            .iter()
            .filter(|row| row.callee == "alias")
            .collect::<Vec<_>>();
        assert_eq!(specialized.len(), 2);
        assert_eq!(
            specialized[0].url.as_deref(),
            Some("https://example.test/one")
        );
        assert_eq!(specialized[0].method.as_deref(), Some("PATCH"));
        assert_eq!(specialized[1].method.as_deref(), Some("POST"));
        for row in specialized {
            assert_eq!(row.invocation_form, "wrapper");
            assert_eq!(row.binding_status, "standard");
            assert_eq!(
                row.forwarded_sink_span,
                Some([original.start, original.end])
            );
            assert_eq!(
                row.binding_witnesses
                    .iter()
                    .filter(|w| w.kind == "wrapper_definition")
                    .count(),
                2
            );
        }
        Ok(())
    }

    #[test]
    fn wrappers_forward_callable_values_and_rest_without_inventing_receivers() -> Result<()> {
        let source = r#"
const invoke = (fn, ...args) => fn(...args);
const send = navigator.sendBeacon.bind(navigator);
invoke(fetch, "/fetch", {method: "PUT"});
invoke(navigator.sendBeacon, "/detached", payload);
invoke(send, "/beacon", payload);
invoke(fetch.bind(window, "/bound"), {method: "DELETE"});
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert!(rows
            .iter()
            .all(|row| row.invocation_form == "wrapper" && row.binding_status == "standard"));
        assert_eq!(rows[0].url.as_deref(), Some("/fetch"));
        assert_eq!(rows[0].method.as_deref(), Some("PUT"));
        assert_eq!(rows[1].kind, "send_beacon");
        assert_eq!(rows[1].url.as_deref(), Some("/beacon"));
        assert_eq!(rows[2].url.as_deref(), Some("/bound"));
        assert_eq!(rows[2].method.as_deref(), Some("DELETE"));
        Ok(())
    }

    #[test]
    fn wrapper_constructor_and_inline_arrow_recovery_preserves_invocation_kind() -> Result<()> {
        let source = r#"
const Socket = WebSocket.bind(null);
function connect(url) { return new Socket(url); }
connect("wss://example.test/live");
((u) => fetch(u))("/inline");
const invalid = (u) => WebSocket(u);
invalid("wss://example.test/bad");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        let specialized = rows
            .iter()
            .filter(|row| row.invocation_form == "wrapper")
            .collect::<Vec<_>>();
        assert_eq!(specialized.len(), 2);
        assert_eq!(specialized[0].kind, "websocket");
        assert_eq!(
            specialized[0].url.as_deref(),
            Some("wss://example.test/live")
        );
        assert_eq!(specialized[1].url.as_deref(), Some("/inline"));
        Ok(())
    }

    #[test]
    fn wrapper_scope_and_mutation_proof_do_not_invent_exact_local_targets() -> Result<()> {
        let source = r#"
function stable(url) { return fetch(url); }
const root = window;
root.stable = replacement;
stable("/candidate");
function changed(url) { return fetch(url); }
changed = replacement;
changed("/not-local");
function outer(stable) { stable("/shadow"); }
const recursive = (url) => recursive(url);
recursive("/recursive");
const effects = (url, init) => fetch((modify(init), url), init);
effects("/not-proven", {method: "PATCH"});
const mapped = function(url) { return fetch((arguments[0] = "/changed", url)); };
mapped("/not-original");
function* generator(url) { return fetch(url); }
generator("/not-executed");
"#;
        let analysis =
            super::analyze_api_surface(source, &WorkBudget::unlimited("wrapper-mutation-proof"))?;
        let rows = &analysis.callsites;
        let specialized = rows
            .iter()
            .filter(|row| row.invocation_form == "wrapper")
            .collect::<Vec<_>>();
        assert_eq!(specialized.len(), 2, "{rows:#?}");
        assert_eq!(specialized[0].callee, "stable");
        assert_eq!(specialized[0].kind, "fetch_candidate");
        assert_eq!(specialized[0].method_status.as_deref(), Some("conditional"));
        let site = &analysis.mutation_sites[specialized[0].mutation_site_ordinals[0]];
        assert!(site
            .affected_families
            .iter()
            .any(|family| family.starts_with("wrapper_global:")));
        assert_eq!(specialized[1].callee, "effects");
        assert!(specialized[1].url.is_none());
        assert!(specialized[1].method.is_none());
        Ok(())
    }

    #[test]
    fn wrapper_rest_prefixes_preserve_later_formal_positions_and_unknown_spreads() -> Result<()> {
        let source = r#"
const leaf = (a, b, c, url, init) => fetch(url, init);
const duplicate = (...args) => leaf(...args, ...args);
duplicate(1, {method: "PUT"}, 3, "/known", {method: "PATCH"});
duplicate(1, 2, ...unknown, "/not-known");
const omitted = (url, init) => fetch(url, init);
omitted("/omitted-init");
Array.prototype[Symbol.iterator] = unsafeIterator;
"#;
        let analysis = super::analyze_api_surface(source, &WorkBudget::unlimited("wrapper-rest"))?;
        let rows = &analysis.callsites;
        let duplicate = rows
            .iter()
            .filter(|row| row.callee == "duplicate")
            .collect::<Vec<_>>();
        assert_eq!(duplicate.len(), 2, "{rows:#?}");
        assert_eq!(duplicate[0].url.as_deref(), Some("/known"));
        assert_eq!(duplicate[0].method.as_deref(), Some("PATCH"));
        assert_eq!(duplicate[0].kind, "fetch_candidate");
        assert_eq!(duplicate[1].url, None);
        assert_eq!(duplicate[1].method_status.as_deref(), Some("unknown"));
        assert!(duplicate
            .iter()
            .all(|row| row.mutation_site_ordinals == [0]));
        let omitted = rows
            .iter()
            .find(|row| row.callee == "omitted")
            .context("missing omitted initializer wrapper")?;
        assert_eq!(omitted.method.as_deref(), Some("GET"));
        assert_eq!(omitted.mutation_site_ordinals, [] as [usize; 0]);
        Ok(())
    }

    #[test]
    fn visible_direct_eval_precludes_wrapper_parameter_specialization() -> Result<()> {
        let source = r#"
const unsafe = (url) => fetch((eval("url='other'"), url));
unsafe("/not-proven");
const safe = (url) => fetch(url);
safe("/safe");
"#;
        let rows = analyze_api_surface(source)?;
        let wrappers = rows
            .iter()
            .filter(|row| row.invocation_form == "wrapper")
            .collect::<Vec<_>>();
        assert_eq!(wrappers.len(), 1, "{rows:#?}");
        assert_eq!(wrappers[0].url.as_deref(), Some("/safe"));
        Ok(())
    }

    #[test]
    fn global_namespace_rebinding_affects_only_dependent_lookups() -> Result<()> {
        let source = r#"
const root = window;
window = replacement;
root.fetch("/captured");
window.fetch("/window");
globalThis.fetch("/global");
fetch("/bare");
fetch.call(window, "/receiver");
"#;
        let result =
            super::analyze_api_surface(source, &WorkBudget::unlimited("namespace-rebinding"))?;
        let rows = &result.callsites;
        assert_eq!(rows.len(), 5, "{rows:#?}");
        assert_eq!(
            rows.iter()
                .map(|row| row.binding_status.as_str())
                .collect::<Vec<_>>(),
            [
                "candidate",
                "candidate",
                "standard",
                "standard",
                "candidate"
            ]
        );
        assert_eq!(result.mutation_sites.len(), 1);
        assert_eq!(
            result.mutation_sites[0].affected_families,
            ["namespace_window"]
        );
        assert_eq!(rows[2].mutation_site_ordinals, [] as [usize; 0]);
        assert_eq!(rows[4].mutation_site_ordinals, [0]);
        Ok(())
    }

    #[test]
    fn namespace_aliases_and_nested_destructuring_retain_native_identity() -> Result<()> {
        let source = r#"
const root = globalThis;
const nav = root.navigator;
const key = "fe" + "tch";
const {[key]: request, navigator: {sendBeacon: report}, WebSocket: Socket} = root;
root.fetch("/direct");
request("/destructured", {method: "PATCH"});
nav.sendBeacon("/member", payload);
report.call(nav, "/report", payload);
new Socket("wss://example.test/live");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 5, "{rows:#?}");
        assert_eq!(
            rows.iter().map(|row| row.kind.as_str()).collect::<Vec<_>>(),
            ["fetch", "fetch", "send_beacon", "send_beacon", "websocket"]
        );
        assert!(rows.iter().all(|row| row.binding_status == "standard"));
        assert_eq!(rows[0].invocation_form, "alias");
        assert_eq!(rows[1].method.as_deref(), Some("PATCH"));
        assert_eq!(
            rows[1].binding_witnesses.last().map(|w| w.kind.as_str()),
            Some("destructure")
        );
        assert_eq!(rows[2].url.as_deref(), Some("/member"));
        assert_eq!(rows[3].invocation_form, "call");
        assert_eq!(rows[3].url.as_deref(), Some("/report"));
        assert_eq!(rows[4].url.as_deref(), Some("wss://example.test/live"));
        Ok(())
    }

    #[test]
    fn namespace_aliases_respect_scope_and_do_not_invent_dotted_properties() -> Result<()> {
        let source = r#"
const root = window;
function nested(root) { root.fetch("/shadow"); }
root["navigator.sendBeacon"]("/not-nested");
const {fetch: fallback = other} = root;
fallback("/not-proven");
let mutable = root;
mutable.fetch("/mutable");
const {navigator: nav} = root;
const {sendBeacon: detached} = nav;
detached("/invalid-receiver");
nav.sendBeacon("/real", body);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 1, "{rows:#?}");
        assert_eq!(rows[0].url.as_deref(), Some("/real"));
        Ok(())
    }

    #[test]
    fn explicit_dispatch_reuses_bound_arguments_and_checks_receiver() -> Result<()> {
        let source = r#"
const nav = navigator;
const send = nav.sendBeacon;
send.call(window, "/invalid");
send.call(nav, "/call", payload);
send.apply(nav, ["/apply", payload]);
const xhr = new XMLHttpRequest();
const open = xhr.open;
Reflect.apply(open, xhr, ["PATCH", "/xhr"]);
const request = fetch.bind(window, "/bound");
request.apply(null, [{method: "PUT"}]);
const r = Reflect;
r["ap" + "ply"](fetch, window, ["/reflected", {method: "POST"}]);
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 5, "{rows:#?}");
        assert!(rows.iter().all(|row| row.binding_status == "standard"));
        assert_eq!(
            rows.iter()
                .map(|row| row.invocation_form.as_str())
                .collect::<Vec<_>>(),
            ["call", "apply", "reflect_apply", "apply", "reflect_apply"]
        );
        assert_eq!(rows[0].url.as_deref(), Some("/call"));
        assert_eq!(rows[1].url.as_deref(), Some("/apply"));
        assert_eq!(rows[2].kind, "xhr_open");
        assert_eq!(rows[2].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[3].url.as_deref(), Some("/bound"));
        assert_eq!(rows[3].method.as_deref(), Some("PUT"));
        assert_eq!(rows[4].method.as_deref(), Some("POST"));
        Ok(())
    }

    #[test]
    fn dispatch_argument_arrays_preserve_holes_and_unknown_spread_boundaries() -> Result<()> {
        let source = r#"
fetch.apply(window, ["/known", ...args, {method: "POST"}]);
fetch.apply(window, [...args, "/unknown"]);
fetch.apply(window, [, {method: "PATCH"}]);
fetch.apply(window, args);
fetch.call(window, ...args, "/unknown");
Reflect.apply(fetch, window, null);
const bound = fetch.bind(window, "/invalid-array-like");
bound.apply(null, 3);
Reflect.apply(bound, null, "invalid");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 5, "{rows:#?}");
        assert_eq!(rows[0].url.as_deref(), Some("/known"));
        assert_eq!(rows[0].method_status.as_deref(), Some("unknown"));
        assert!(rows[1..].iter().all(|row| row.url.is_none()));
        assert_eq!(rows[2].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[3].method_status.as_deref(), Some("unknown"));
        assert_eq!(rows[4].method_status.as_deref(), Some("unknown"));
        Ok(())
    }

    #[test]
    fn namespace_and_dispatch_writes_invalidate_only_relevant_operations() -> Result<()> {
        let source = r#"
const root = window;
const F = root.Function;
const request = root.fetch;
F.prototype.call = customCall;
const r = root.Reflect;
r.apply = customReflect;
request.apply = customApply;
request.call(root, "/call");
request.apply(root, ["/apply"]);
r.apply(request, root, ["/reflect"]);
request("/direct");
const nav = root.navigator;
const O = root.Object;
O.defineProperty(nav, "sendBeacon", {value: fake});
nav.sendBeacon("/beacon", payload);
"#;
        let result = super::analyze_api_surface(
            source,
            &WorkBudget::unlimited("namespace-dispatch-writes"),
        )?;
        let rows = &result.callsites;
        assert_eq!(rows.len(), 5, "{rows:#?}");
        assert!(rows[..3].iter().all(|row| row.kind == "fetch_candidate"));
        assert_eq!(rows[3].kind, "fetch");
        assert_eq!(rows[3].mutation_site_ordinals, [] as [usize; 0]);
        for (row, family) in rows[..3]
            .iter()
            .zip(["function_call", "fetch_apply", "reflect_apply"])
        {
            assert_eq!(row.mutation_site_ordinals.len(), 1, "{row:#?}");
            assert_eq!(
                result.mutation_sites[row.mutation_site_ordinals[0]].affected_families,
                [family]
            );
        }
        assert_eq!(rows[4].kind, "send_beacon_candidate");
        assert_eq!(
            result.mutation_sites[rows[4].mutation_site_ordinals[0]].operation,
            "Object.defineProperty"
        );
        Ok(())
    }

    #[test]
    fn dispatch_member_mutation_on_one_bound_object_does_not_affect_others() -> Result<()> {
        let source = r#"
const a = fetch.bind(window);
const b = fetch.bind(window);
a.call = other;
a.call(null, "/candidate");
b.call(null, "/standard");
a("/direct");
"#;
        let result =
            super::analyze_api_surface(source, &WorkBudget::unlimited("bound-dispatch-writes"))?;
        assert_eq!(result.callsites.len(), 3, "{result:#?}");
        assert_eq!(result.callsites[0].kind, "fetch_candidate");
        assert_eq!(result.callsites[1].kind, "fetch");
        assert_eq!(result.callsites[2].kind, "fetch");
        let site = &result.mutation_sites[0];
        assert!(site.bound_function_span.is_some());
        assert_eq!(site.target_pattern, [Some("call".into())]);
        Ok(())
    }

    #[test]
    fn immutable_function_aliases_recover_fetch_and_constructor_identity() -> Result<()> {
        let source = r#"
const api = globalThis["fe" + "tch"];
const again = api;
const Socket = WebSocket;
const Request = window.XMLHttpRequest;
again("https://example.test/api", {method: "PATCH"});
new Socket("wss://example.test/live");
const xhr = new Request();
xhr.open("POST", "https://example.test/xhr");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert_eq!(rows[0].kind, "fetch");
        assert_eq!(rows[0].callee, "again");
        assert_eq!(rows[0].api_origin, "fetch");
        assert_eq!(rows[0].invocation_form, "alias");
        assert_eq!(rows[0].binding_witnesses.len(), 2);
        assert_eq!(rows[0].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[1].api_origin, "WebSocket");
        assert_eq!(rows[1].invocation_form, "alias");
        assert_eq!(rows[1].url.as_deref(), Some("wss://example.test/live"));
        assert_eq!(rows[2].kind, "xhr_open");
        assert_eq!(rows[2].api_origin, "XMLHttpRequest.prototype.open");
        assert_eq!(rows[2].binding_witnesses.len(), 1);
        Ok(())
    }

    #[test]
    fn bound_functions_keep_receiver_and_captured_argument_positions() -> Result<()> {
        let source = r#"
const endpoint = "https://example.test";
const report = navigator.sendBeacon.bind(navigator, endpoint + "/beacon");
const read = fetch.bind(globalThis, endpoint + "/fetch");
const post = read.bind({}, {method: "POST"});
const Socket = WebSocket.bind(null, "wss://example.test/bound");
report(payload);
post();
new Socket();
window.fetch.bind(window, endpoint + "/inline")({method: "PUT"});
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        assert!(rows
            .iter()
            .all(|row| row.invocation_form == "bound" && row.binding_status == "standard"));
        assert_eq!(rows[0].kind, "send_beacon");
        assert_eq!(rows[0].url.as_deref(), Some("https://example.test/beacon"));
        assert_eq!(rows[1].method.as_deref(), Some("POST"));
        assert_eq!(rows[1].url.as_deref(), Some("https://example.test/fetch"));
        assert_eq!(
            rows[1]
                .binding_witnesses
                .iter()
                .filter(|w| w.kind == "bind")
                .count(),
            2
        );
        assert_eq!(rows[2].url.as_deref(), Some("wss://example.test/bound"));
        assert_eq!(rows[3].url.as_deref(), Some("https://example.test/inline"));
        assert_eq!(rows[3].method.as_deref(), Some("PUT"));
        Ok(())
    }

    #[test]
    fn receiver_dependent_aliases_require_a_matching_bound_receiver() -> Result<()> {
        let source = r#"
const beacon = navigator.sendBeacon;
beacon("https://invalid.test/detached", payload);
const wrong = beacon.bind(window);
wrong("https://invalid.test/wrong", payload);
const valid = beacon.bind(self.navigator);
valid("https://example.test/beacon", payload);
const xhr = new XMLHttpRequest();
const open = xhr.open;
open("GET", "https://invalid.test/detached-xhr");
const wrongOpen = open.bind(navigator);
wrongOpen("GET", "https://invalid.test/wrong-xhr");
const bound = open.bind(xhr, "PATCH");
bound("https://example.test/xhr");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 2, "{rows:#?}");
        assert_eq!(rows[0].kind, "send_beacon");
        assert_eq!(rows[0].invocation_form, "bound");
        assert_eq!(rows[1].kind, "xhr_open");
        assert_eq!(rows[1].method.as_deref(), Some("PATCH"));
        assert_eq!(rows[1].url.as_deref(), Some("https://example.test/xhr"));
        assert_eq!(rows[1].binding_witnesses.len(), 3);
        Ok(())
    }

    #[test]
    fn alias_recovery_respects_scope_declaration_availability_and_invocation_kind() -> Result<()> {
        let source = r#"
later("https://invalid.test/before");
const later = fetch;
function nested(later) {
    const fake = later;
    fake("https://invalid.test/shadow");
}
let mutable = fetch;
mutable("https://invalid.test/mutable");
const Socket = WebSocket;
Socket("wss://invalid.test/not-new");
new later("https://invalid.test/not-call");
later("https://example.test/real");
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 1, "{rows:#?}");
        assert_eq!(rows[0].url.as_deref(), Some("https://example.test/real"));
        Ok(())
    }

    #[test]
    fn exact_global_replacements_preserve_captured_invocations_as_candidates() -> Result<()> {
        let source = r#"
const saved = fetch;
const Socket = WebSocket;
const Request = XMLHttpRequest;
window.fetch = replacement;
WebSocket = otherSocket;
XMLHttpRequest = otherRequest;
fetch("https://invalid.test/direct");
saved("https://example.test/maybe");
new Socket("wss://example.test/maybe");
const xhr = new Request();
xhr.open("GET", "https://example.test/maybe-xhr");
"#;
        let analysis = super::analyze_api_surface(
            source,
            &WorkBudget::unlimited("captured-binding-mutations"),
        )?;
        let constructor_write = analysis
            .mutation_sites
            .iter()
            .find(|site| site.target_pattern == [Some("XMLHttpRequest".into())])
            .context("missing constructor replacement")?;
        assert_eq!(constructor_write.affected_families, ["xhr"]);
        let rows = analysis.callsites;
        assert_eq!(rows.len(), 3, "{rows:#?}");
        assert_eq!(
            rows.iter().map(|row| row.kind.as_str()).collect::<Vec<_>>(),
            [
                "fetch_candidate",
                "websocket_candidate",
                "xhr_open_candidate"
            ]
        );
        assert!(rows
            .iter()
            .all(|row| !row.mutation_site_ordinals.is_empty()));
        assert_eq!(rows[0].method_status.as_deref(), Some("conditional"));
        assert_eq!(rows[2].method_status.as_deref(), Some("conditional"));
        Ok(())
    }

    #[test]
    fn bind_mutation_tracks_function_objects_not_just_original_api_family() -> Result<()> {
        let source = r#"
const original = fetch;
const first = original.bind(window);
const unaffected = original.bind(window);
first.bind = replaceBind;
const second = first.bind(window);
first("https://example.test/first");
unaffected("https://example.test/unaffected");
second("https://example.test/second");
Object.defineProperty(original, "bind", {value: replaceNativeBind});
const later = original.bind(window);
later("https://example.test/later");
original("https://example.test/direct");
"#;
        let analysis =
            super::analyze_api_surface(source, &WorkBudget::unlimited("bind-object-mutations"))?;
        let rows = &analysis.callsites;
        // Flow-insensitive mutation evidence includes the visible write to the
        // original native function for all its bind operations. The write to
        // first.bind affects only rebinding that distinct bound object.
        assert_eq!(rows.len(), 5, "{rows:#?}");
        assert!(rows[..4].iter().all(|row| row.kind == "fetch_candidate"));
        assert_eq!(rows[4].kind, "fetch");
        assert_eq!(rows[4].mutation_site_ordinals, [] as [usize; 0]);
        let own = analysis
            .mutation_sites
            .iter()
            .position(|site| {
                site.affected_families
                    .iter()
                    .any(|family| family.starts_with("bound_bind:"))
            })
            .context("missing bound-object mutation")?;
        assert!(!rows[0].mutation_site_ordinals.contains(&own));
        assert!(!rows[1].mutation_site_ordinals.contains(&own));
        assert!(rows[2].mutation_site_ordinals.contains(&own));
        assert!(!rows[3].mutation_site_ordinals.contains(&own));
        Ok(())
    }

    #[test]
    fn native_bind_prototype_mutation_does_not_invalidate_direct_api_calls() -> Result<()> {
        let source = r#"
Function.prototype["bi" + "nd"] = fakeBind;
const report = navigator.sendBeacon.bind(navigator);
report("https://example.test/candidate", payload);
navigator.sendBeacon("https://example.test/direct", payload);
"#;
        let analysis =
            super::analyze_api_surface(source, &WorkBudget::unlimited("native-bind-mutation"))?;
        assert_eq!(analysis.callsites.len(), 2);
        assert_eq!(analysis.callsites[0].kind, "send_beacon_candidate");
        assert_eq!(analysis.callsites[0].mutation_site_ordinals, [0]);
        assert_eq!(analysis.callsites[1].kind, "send_beacon");
        assert_eq!(
            analysis.callsites[1].mutation_site_ordinals,
            [] as [usize; 0]
        );
        assert_eq!(
            analysis.mutation_sites[0].affected_families,
            ["function_bind"]
        );
        Ok(())
    }

    #[test]
    fn unknown_spreads_cannot_shift_later_bound_or_direct_arguments_into_exact_slots() -> Result<()>
    {
        let source = r#"
const uncertain = fetch.bind(window, ...args);
uncertain("https://invalid.test/position", {method: "POST"});
const knownUrl = fetch.bind(window, "https://example.test/known", ...args);
knownUrl({method: "DELETE"});
const xhr = new XMLHttpRequest();
xhr.open(...args, "https://invalid.test/position");
fetch(...args, {method: "PUT"});
"#;
        let rows = analyze_api_surface(source)?;
        assert_eq!(rows.len(), 4, "{rows:#?}");
        assert_eq!(rows[0].url, None);
        assert_eq!(rows[0].method_status.as_deref(), Some("unknown"));
        assert_eq!(rows[1].url.as_deref(), Some("https://example.test/known"));
        assert_eq!(rows[1].method_status.as_deref(), Some("unknown"));
        assert_eq!(rows[2].url, None);
        assert_eq!(rows[3].url, None);
        assert_eq!(rows[3].method_status.as_deref(), Some("unknown"));
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
        assert_eq!(result.callsites[1].mutation_site_ordinals, [] as [usize; 0]);
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
    fn computed_object_keys_use_primitive_identity_not_regex_spelling() -> Result<()> {
        let source = r#"
const k = "fe" + "tch";
const {[k]: alias} = window;
alias("/before");
Object.assign(window, {[/x/]:replacement});
fetch("/after");
"#;
        let result =
            super::analyze_api_surface(source, &WorkBudget::unlimited("computed-key-coercion"))?;
        assert_eq!(result.callsites.len(), 2, "{result:#?}");
        assert_eq!(result.mutation_sites.len(), 1, "{result:#?}");
        assert_eq!(
            result.mutation_sites[0].target_pattern,
            [Some("window".into()), None]
        );
        assert_eq!(result.callsites[1].kind, "fetch_candidate");
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
        assert_eq!(result.callsites[1].mutation_site_ordinals, [] as [usize; 0]);
        assert_eq!(result.callsites[0].mutation_site_ordinals.len(), 1);
        assert_eq!(result.callsites[2].method.as_deref(), Some("GET"));
        assert_eq!(result.callsites[2].mutation_site_ordinals, [] as [usize; 0]);
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
                && site.affected_families.iter().any(|i: &String| i == "fetch")
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
