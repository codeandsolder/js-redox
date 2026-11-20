//! Lexical function identity, receiver semantics and positional argument recovery.
//!
//! A callable fact describes a value, not execution. Immutable aliases preserve
//! object identity; binding creates a new function object. Prefix arguments are
//! captured at the bind expression, and unknown spreads never shift a later
//! argument into a falsely proven position.
use super::*;
use oxc_ast::ast::{Argument, VariableDeclaration, VariableDeclarationKind};
use std::{collections::BTreeMap, rc::Rc};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ApiKind {
    Fetch,
    Beacon,
    WebSocket,
    XhrConstructor,
    XhrOpen,
}

impl ApiKind {
    fn from_global(path: &str) -> Option<Self> {
        if allowed_fetch_path(path) {
            Some(Self::Fetch)
        } else if allowed_send_beacon_path(path) {
            Some(Self::Beacon)
        } else if allowed_websocket_path(path) {
            Some(Self::WebSocket)
        } else if allowed_xhr_path(path) {
            Some(Self::XhrConstructor)
        } else {
            None
        }
    }

    pub(super) fn family(self) -> &'static str {
        match self {
            Self::Fetch => "fetch",
            Self::Beacon => "send_beacon",
            Self::WebSocket => "websocket",
            Self::XhrConstructor => "xhr",
            Self::XhrOpen => "xhr_open_method",
        }
    }

    pub(super) fn canonical_path(self) -> &'static str {
        match self {
            Self::Fetch => "fetch",
            Self::Beacon => "navigator.sendBeacon",
            Self::WebSocket => "WebSocket",
            Self::XhrConstructor => "XMLHttpRequest",
            Self::XhrOpen => "XMLHttpRequest.prototype.open",
        }
    }

    fn is_constructor(self) -> bool {
        matches!(self, Self::WebSocket | Self::XhrConstructor)
    }

    fn needs_receiver(self) -> bool {
        matches!(self, Self::Beacon | Self::XhrOpen)
    }

    pub(super) fn callsite_kind(self, candidate: bool) -> &'static str {
        match (self, candidate) {
            (Self::Fetch, false) => "fetch",
            (Self::Fetch, true) => "fetch_candidate",
            (Self::Beacon, false) => "send_beacon",
            (Self::Beacon, true) => "send_beacon_candidate",
            (Self::WebSocket, false) => "websocket",
            (Self::WebSocket, true) => "websocket_candidate",
            (Self::XhrOpen, false) => "xhr_open",
            (Self::XhrOpen, true) => "xhr_open_candidate",
            (Self::XhrConstructor, _) => "xhr_constructor",
        }
    }
}

#[derive(Clone, Debug)]
struct ArgumentEvidence {
    string: Option<String>,
    expression: Option<String>,
    init: FetchInitMethod,
}

/// Only the first two positional arguments can affect the supported APIs.
/// An unknown-length spread terminates the exact positional prefix.
#[derive(Clone, Debug, Default)]
pub(super) struct ApiArguments {
    prefix: Vec<Rc<ArgumentEvidence>>,
    unknown_tail: Option<Rc<str>>,
}

impl ApiArguments {
    pub(super) fn append(
        &mut self,
        args: &[Argument<'_>],
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) {
        for arg in args {
            if self.prefix.len() >= 2 || self.unknown_tail.is_some() {
                break;
            }
            if arg.as_expression().is_none() {
                self.unknown_tail = Some(Rc::from(source_fragment(source, arg.span())));
                break;
            }
            let (string, expression) = exact_argument(source, Some(arg), scoping, constants);
            self.prefix.push(Rc::new(ArgumentEvidence {
                string,
                expression,
                init: fetch_init_method(source, Some(arg), scoping, constants),
            }));
        }
    }

    pub(super) fn exact(&self, index: usize) -> (Option<String>, Option<String>) {
        self.prefix.get(index).map_or_else(
            || {
                (
                    None,
                    (index == self.prefix.len())
                        .then(|| self.unknown_tail.as_deref().map(str::to_owned))
                        .flatten(),
                )
            },
            |arg| (arg.string.clone(), arg.expression.clone()),
        )
    }

    pub(super) fn fetch_method(
        &self,
        input_is_static_string: bool,
        prototype_mutated: bool,
    ) -> (Option<String>, Option<String>, Option<String>) {
        if self.prefix.is_empty() && self.unknown_tail.is_some() {
            return (None, None, Some("unknown".into()));
        }
        let init = self.prefix.get(1).map_or_else(
            || {
                if self.unknown_tail.is_some() {
                    FetchInitMethod::Unknown
                } else {
                    FetchInitMethod::Missing
                }
            },
            |arg| arg.init.clone(),
        );
        method_from_init(init, input_is_static_string, prototype_mutated)
    }
}

#[derive(Debug, Clone)]
struct WitnessLink {
    previous: Option<Rc<Self>>,
    witness: ApiBindingWitness,
    bind_dependency: Option<String>,
}

#[derive(Debug, Clone)]
pub(super) struct Callable {
    pub(super) kind: ApiKind,
    pub(super) receiver: Option<SymbolId>,
    pub(super) captured: bool,
    pub(super) constructor_captured: bool,
    pub(super) bound: bool,
    detached: bool,
    pub(super) prefix: ApiArguments,
    witness: Option<Rc<WitnessLink>>,
    bound_object: Option<u32>,
}

impl Callable {
    fn native(kind: ApiKind) -> Self {
        Self {
            kind,
            receiver: None,
            captured: false,
            constructor_captured: false,
            bound: false,
            detached: false,
            prefix: ApiArguments::default(),
            witness: None,
            bound_object: None,
        }
    }

    fn add_witness(&mut self, kind: &str, span: Span, bind_dependency: Option<String>) {
        self.witness = Some(Rc::new(WitnessLink {
            previous: self.witness.take(),
            witness: ApiBindingWitness {
                kind: kind.to_owned(),
                start: span.start,
                end: span.end,
            },
            bind_dependency,
        }));
    }

    pub(super) fn witnesses(&self) -> Vec<ApiBindingWitness> {
        let mut result = Vec::new();
        let mut cursor = self.witness.as_deref();
        while let Some(link) = cursor {
            result.push(link.witness.clone());
            cursor = link.previous.as_deref();
        }
        result.reverse();
        result
    }

    pub(super) fn bind_dependencies(&self) -> BTreeSet<String> {
        let mut result = BTreeSet::new();
        let mut cursor = self.witness.as_deref();
        while let Some(link) = cursor {
            if let Some(key) = &link.bind_dependency {
                result.insert(key.clone());
                result.insert("function_bind".into());
            }
            cursor = link.previous.as_deref();
        }
        result
    }

    fn bind_member_family(&self) -> String {
        self.bound_object.map_or_else(
            || format!("{}_bind", self.kind.family()),
            |start| format!("bound_bind:{start}"),
        )
    }

    /// A bound function is a distinct object, not an alias of its target.
    pub(super) fn mutation_object_path(&self) -> MutationPath {
        if let Some(function_start) = self.bound_object {
            return MutationPath::Bound {
                function_start,
                members: Vec::new(),
            };
        }
        MutationPath::Global(
            self.kind
                .canonical_path()
                .split('.')
                .map(|segment| Some(segment.to_owned()))
                .collect(),
        )
    }

    pub(super) fn invocation_form(&self) -> &'static str {
        if self.bound {
            "bound"
        } else if self.captured {
            "alias"
        } else {
            "direct"
        }
    }

    pub(super) fn callable_as(&self, constructor: bool) -> bool {
        self.kind.is_constructor() == constructor && !self.detached
    }
}

#[derive(Debug, Clone)]
struct Available<T> {
    after: u32,
    value: T,
}

impl<T> Available<T> {
    fn at(&self, offset: u32) -> Option<&T> {
        (offset >= self.after).then_some(&self.value)
    }
}

#[derive(Default)]
pub(super) struct CallableIndex {
    aliases: BTreeMap<SymbolId, Available<Callable>>,
    xhr: BTreeMap<SymbolId, Available<Callable>>,
}

fn member_parts<'a, 'e>(
    expr: &'e Expression<'a>,
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
) -> Option<(&'e Expression<'a>, String)> {
    match unparenthesized(expr) {
        Expression::StaticMemberExpression(member) if !member.optional => {
            Some((&member.object, member.property.name.to_string()))
        }
        Expression::ComputedMemberExpression(member) if !member.optional => Some((
            &member.object,
            static_string(&member.expression, scoping, constants)?,
        )),
        _ => None,
    }
}

fn is_global_receiver(path: &str) -> bool {
    matches!(path, "window" | "globalThis" | "self")
}

fn is_navigator_receiver(path: &str) -> bool {
    matches!(
        path,
        "navigator" | "window.navigator" | "globalThis.navigator" | "self.navigator"
    )
}

impl CallableIndex {
    pub(super) fn collect(
        program: &Program<'_>,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Self {
        let mut collector = BindingCollector {
            source,
            scoping,
            constants,
            index: Self::default(),
        };
        collector.visit_program(program);
        collector.index
    }

    pub(super) fn resolve(
        &self,
        expr: &Expression<'_>,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<Callable> {
        let expr = unparenthesized(expr);
        if let Some(kind) = global_path(scoping, constants, expr)
            .as_deref()
            .and_then(ApiKind::from_global)
        {
            return Some(Callable::native(kind));
        }
        if let Some(symbol) = expression_symbol(scoping, expr) {
            return self.aliases.get(&symbol)?.at(expr.span().start).cloned();
        }
        if let Some((object, key)) = member_parts(expr, scoping, constants) {
            if key == "open" {
                let symbol = expression_symbol(scoping, object)?;
                let constructor = self.xhr.get(&symbol)?.at(object.span().start)?;
                let mut callable = Callable::native(ApiKind::XhrOpen);
                callable.receiver = Some(symbol);
                callable.constructor_captured = constructor.captured;
                callable.witness = constructor.witness.clone();
                return Some(callable);
            }
        }
        if let Expression::CallExpression(call) = expr {
            return self.resolve_bind(call, source, scoping, constants);
        }
        None
    }

    pub(super) fn resolve_bind(
        &self,
        call: &CallExpression<'_>,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<Callable> {
        if call.optional {
            return None;
        }
        let (object, key) = member_parts(&call.callee, scoping, constants)?;
        if key != "bind" {
            return None;
        }
        let mut callable = self.resolve(object, source, scoping, constants)?;
        let receiver = match call.arguments.first() {
            Some(arg) => Some(arg.as_expression()?),
            None => None,
        };
        let receiver_path = receiver.and_then(|expr| global_path(scoping, constants, expr));
        let valid_receiver = callable.bound
            || callable.kind.is_constructor()
            || match callable.kind {
                ApiKind::Fetch => {
                    receiver.is_none()
                        || receiver.is_some_and(|expr| {
                            matches!(unparenthesized(expr), Expression::NullLiteral(_))
                        })
                        || receiver_path
                            .as_deref()
                            .is_some_and(|path| is_global_receiver(path) || path == "undefined")
                }
                ApiKind::Beacon => receiver_path.as_deref().is_some_and(is_navigator_receiver),
                ApiKind::XhrOpen => receiver
                    .is_some_and(|expr| expression_symbol(scoping, expr) == callable.receiver),
                ApiKind::WebSocket | ApiKind::XhrConstructor => true,
            };
        if !valid_receiver {
            return None;
        }
        let dependency = callable.bind_member_family();
        callable.add_witness("bind", call.span, Some(dependency));
        callable.prefix.append(
            call.arguments.get(1..).unwrap_or_default(),
            source,
            scoping,
            constants,
        );
        callable.bound = true;
        callable.captured = true;
        callable.detached = false;
        callable.bound_object = Some(call.span.start);
        Some(callable)
    }
}

struct BindingCollector<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    constants: &'c ProvenConstantEnvironment,
    index: CallableIndex,
}

impl BindingCollector<'_, '_> {
    fn resolve(&self, expr: &Expression<'_>) -> Option<Callable> {
        self.index
            .resolve(expr, self.source, self.scoping, self.constants)
    }

    fn record(&mut self, declaration: &VariableDeclarator<'_>, immutable: bool) {
        let BindingPattern::BindingIdentifier(identifier) = &declaration.id else {
            return;
        };
        let (Some(symbol), Some(init)) = (identifier.symbol_id.get(), declaration.init.as_ref())
        else {
            return;
        };
        if !xhr_binding_is_not_reassigned(self.scoping, symbol) {
            return;
        }
        if immutable {
            if let Some(mut callable) = self.resolve(init) {
                callable.captured = true;
                callable.detached = !callable.bound && callable.kind.needs_receiver();
                callable.add_witness("const_alias", declaration.span, None);
                self.index.aliases.insert(
                    symbol,
                    Available {
                        after: declaration.span.end,
                        value: callable,
                    },
                );
                return;
            }
        }
        if let Expression::NewExpression(new) = unparenthesized(init) {
            if let Some(constructor) = self.resolve(&new.callee) {
                if constructor.kind == ApiKind::XhrConstructor {
                    self.index.xhr.insert(
                        symbol,
                        Available {
                            after: declaration.span.end,
                            value: constructor,
                        },
                    );
                }
            }
        }
    }
}

impl<'a> Visit<'a> for BindingCollector<'_, '_> {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        for declarator in &declaration.declarations {
            self.record(
                declarator,
                declaration.kind == VariableDeclarationKind::Const,
            );
            walk::walk_variable_declarator(self, declarator);
        }
    }
}
