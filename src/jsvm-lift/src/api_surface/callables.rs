//! Lexical function identity, receiver semantics and positional argument recovery.
//!
//! A callable fact describes a value, not execution. Immutable aliases preserve
//! object identity; binding creates a new function object. Prefix arguments are
//! captured at the bind expression, and unknown spreads never shift a later
//! argument into a falsely proven position.
use super::*;
use oxc_ast::ast::{
    Argument, ArrayExpression, ArrayExpressionElement, VariableDeclaration, VariableDeclarationKind,
};
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

/// A captured argument can include a privately constructed array whose
/// elements originate in different forwarding frames. Preserve that value
/// rather than substituting source text or evaluating JavaScript.
#[derive(Clone, Debug)]
pub(super) enum ForwardedValue<'e, 'a> {
    Expression(&'e Expression<'a>),
    /// Computed primitive captured in its actual invocation environment.
    Primitive {
        value: Rc<StaticPrimitiveValue>,
        span: Span,
    },
    Array {
        span: Span,
        positions: Rc<PositionalArguments<'e, 'a>>,
    },
    Object {
        span: Span,
        fields: Rc<BTreeMap<String, ForwardedValue<'e, 'a>>>,
    },
    Unknown(Option<Span>),
    Missing,
}

impl<'e, 'a> ForwardedValue<'e, 'a> {
    pub(super) fn expression(&self) -> Option<&'e Expression<'a>> {
        match self {
            Self::Expression(expression) => Some(expression),
            _ => None,
        }
    }
    /// Primitive facts are captured once in their originating frame.
    /// An unresolved expression must never be re-evaluated with another
    /// invocation's lexical bindings.
    pub(super) fn primitive(&self) -> Option<&StaticPrimitiveValue> {
        match self {
            Self::Primitive { value, .. } => Some(value.as_ref()),
            Self::Missing => Some(&StaticPrimitiveValue::Undefined),
            _ => None,
        }
    }

    fn init_method(
        &self,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> FetchInitMethod {
        match self {
            Self::Primitive { value, span } => match value.as_ref() {
                StaticPrimitiveValue::String(literal) => {
                    literal_method_evidence(source, literal, *span)
                }
                _ => FetchInitMethod::Unknown,
            },
            Self::Expression(expr) => method_value_evidence(source, expr, scoping, constants),
            _ => FetchInitMethod::Unknown,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct PositionalArguments<'e, 'a> {
    pub(super) values: Vec<ForwardedValue<'e, 'a>>,
    pub(super) unknown_tail: Option<Span>,
}

impl<'e, 'a> PositionalArguments<'e, 'a> {
    pub(super) fn value(&self, index: usize) -> ForwardedValue<'e, 'a> {
        self.values.get(index).cloned().unwrap_or_else(|| {
            self.unknown_tail.map_or(ForwardedValue::Missing, |span| {
                ForwardedValue::Unknown(Some(span))
            })
        })
    }
}

enum ArraySource<'e, 'a> {
    Empty,
    Literal(&'e ArrayExpression<'a>),
    Forwarded(Rc<PositionalArguments<'e, 'a>>),
    Unknown(Span),
}

/// Classify CreateListFromArrayLike inputs for both ordinary and forwarded
/// dispatch. Only Function.prototype.apply treats null/undefined as empty.
fn apply_array_source<'e, 'a>(
    value: ForwardedValue<'e, 'a>,
    mode: DispatchMode,
    scoping: &Scoping,
    constants: &ProvenConstantEnvironment,
    fallback: Span,
) -> Option<ArraySource<'e, 'a>> {
    match value {
        ForwardedValue::Missing => (!mode.reflect()).then_some(ArraySource::Empty),
        ForwardedValue::Primitive { value, .. } => (!mode.reflect()
            && matches!(
                value.as_ref(),
                StaticPrimitiveValue::Null | StaticPrimitiveValue::Undefined
            ))
        .then_some(ArraySource::Empty),
        ForwardedValue::Array { positions, .. } => Some(ArraySource::Forwarded(positions)),
        ForwardedValue::Object { span, .. } => Some(ArraySource::Unknown(span)),
        ForwardedValue::Unknown(span) => Some(ArraySource::Unknown(span.unwrap_or(fallback))),
        ForwardedValue::Expression(expr) => {
            let expr = unparenthesized(expr);
            if matches!(expr, Expression::NullLiteral(_))
                || global_path(scoping, constants, expr).as_deref() == Some("undefined")
            {
                return (!mode.reflect()).then_some(ArraySource::Empty);
            }
            if matches!(
                expr,
                Expression::StringLiteral(_)
                    | Expression::NumericLiteral(_)
                    | Expression::BooleanLiteral(_)
                    | Expression::BigIntLiteral(_)
            ) || static_string(expr, scoping, constants).is_some()
            {
                return None;
            }
            match expr {
                Expression::ArrayExpression(array) => Some(ArraySource::Literal(array)),
                _ => Some(ArraySource::Unknown(expr.span())),
            }
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
        let args = &args[..args.len().min(2usize.saturating_sub(self.prefix.len()))];
        let first_spread = args
            .iter()
            .position(|arg| matches!(arg, Argument::SpreadElement(_)));
        let values = args
            .iter()
            .take(first_spread.unwrap_or(args.len()))
            .filter_map(Argument::as_expression)
            .map(ForwardedValue::Expression);
        self.append_forwarded(
            values,
            first_spread.map(|index| args[index].span()),
            source,
            scoping,
            constants,
        );
    }

    pub(super) fn append_forwarded<'e, 'a: 'e>(
        &mut self,
        values: impl IntoIterator<Item = ForwardedValue<'e, 'a>>,
        unknown_tail: Option<Span>,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) {
        for value in values {
            if self.complete() {
                return;
            }
            match value {
                ForwardedValue::Expression(expr) => {
                    self.push_expression(expr, source, scoping, constants)
                }
                ForwardedValue::Primitive { value, span } => {
                    self.prefix.push(Rc::new(ArgumentEvidence {
                        string: match value.as_ref() {
                            StaticPrimitiveValue::String(text) => Some(text.clone()),
                            _ => None,
                        },
                        expression: Some(source_fragment(source, span)),
                        init: FetchInitMethod::Unknown,
                    }))
                }
                ForwardedValue::Array { span, .. } => self.prefix.push(Rc::new(ArgumentEvidence {
                    string: None,
                    expression: Some(source_fragment(source, span)),
                    init: FetchInitMethod::Unknown,
                })),
                ForwardedValue::Object { span, fields } => {
                    self.prefix.push(Rc::new(ArgumentEvidence {
                        string: None,
                        expression: Some(source_fragment(source, span)),
                        init: fields
                            .get("method")
                            .map_or(FetchInitMethod::NoOwnMethod, |value| {
                                value.init_method(source, scoping, constants)
                            }),
                    }))
                }
                ForwardedValue::Unknown(span) => self.prefix.push(Rc::new(ArgumentEvidence {
                    string: None,
                    expression: span.map(|span| source_fragment(source, span)),
                    init: FetchInitMethod::Unknown,
                })),
                ForwardedValue::Missing => self.prefix.push(Rc::new(ArgumentEvidence {
                    string: None,
                    expression: None,
                    init: FetchInitMethod::Missing,
                })),
            }
        }
        if !self.complete() {
            self.unknown_tail = unknown_tail.map(|span| Rc::from(source_fragment(source, span)));
        }
    }

    fn complete(&self) -> bool {
        self.prefix.len() >= 2 || self.unknown_tail.is_some()
    }

    fn push_expression(
        &mut self,
        expr: &Expression<'_>,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) {
        self.prefix.push(Rc::new(ArgumentEvidence {
            string: static_string(expr, scoping, constants),
            expression: Some(source_fragment(source, expr.span())),
            init: fetch_init_method(source, expr, scoping, constants),
        }));
    }

    fn append_array_source(
        &mut self,
        array: ArraySource<'_, '_>,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) {
        match array {
            ArraySource::Empty => {}
            ArraySource::Literal(array) => {
                for element in &array.elements {
                    if self.complete() {
                        break;
                    }
                    match element {
                        ArrayExpressionElement::Elision(_) => {
                            self.prefix.push(Rc::new(ArgumentEvidence {
                                string: None,
                                expression: None,
                                init: FetchInitMethod::Unknown,
                            }))
                        }
                        ArrayExpressionElement::SpreadElement(_) => {
                            self.unknown_tail =
                                Some(Rc::from(source_fragment(source, element.span())));
                        }
                        _ => {
                            if let Some(expr) = element.as_expression() {
                                self.push_expression(expr, source, scoping, constants);
                            }
                        }
                    }
                }
            }
            ArraySource::Forwarded(positions) => self.append_forwarded(
                positions.values.iter().cloned(),
                positions.unknown_tail,
                source,
                scoping,
                constants,
            ),
            ArraySource::Unknown(span) => {
                if !self.complete() {
                    self.unknown_tail = Some(Rc::from(source_fragment(source, span)));
                }
            }
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
    dependency: Option<String>,
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
    bound_object: Option<Span>,
    dispatch: Option<&'static str>,
    pub(super) forwarded_sink_span: Option<[u32; 2]>,
    namespace_dependencies: BTreeSet<&'static str>,
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
            dispatch: None,
            forwarded_sink_span: None,
            namespace_dependencies: BTreeSet::new(),
        }
    }

    fn add_witness(&mut self, kind: &str, span: Span, dependency: Option<String>) {
        self.witness = Some(Rc::new(WitnessLink {
            previous: self.witness.take(),
            witness: ApiBindingWitness {
                kind: kind.to_owned(),
                start: span.start,
                end: span.end,
            },
            dependency,
        }));
    }

    pub(super) fn mark_forwarding(&mut self, witnesses: &[ApiBindingWitness], sink: Span) {
        self.dispatch = Some("wrapper");
        self.forwarded_sink_span = Some([sink.start, sink.end]);
        for witness in witnesses {
            self.add_witness(&witness.kind, Span::new(witness.start, witness.end), None);
        }
    }

    pub(super) fn capture_as_argument(&mut self) {
        self.captured = true;
        self.detached = !self.bound && self.kind.needs_receiver();
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

    pub(super) fn dispatch_dependencies(&self) -> BTreeSet<String> {
        let mut result = self
            .namespace_dependencies
            .iter()
            .map(|key| (*key).to_owned())
            .collect::<BTreeSet<_>>();
        let mut cursor = self.witness.as_deref();
        while let Some(link) = cursor {
            if let Some(key) = &link.dependency {
                result.insert(key.clone());
                if matches!(link.witness.kind.as_str(), "bind" | "call" | "apply") {
                    result.insert(format!("function_{}", link.witness.kind));
                }
            }
            cursor = link.previous.as_deref();
        }
        result
    }

    fn dispatch_member_family(&self, operation: &str) -> String {
        self.bound_object.map_or_else(
            || format!("{}_{operation}", self.kind.family()),
            |span| format!("bound_{operation}:{}:{}", span.start, span.end),
        )
    }

    /// A bound function is a distinct object, not an alias of its target.
    pub(super) fn mutation_object_path(&self) -> MutationPath {
        if let Some(function_span) = self.bound_object {
            return MutationPath::Bound {
                function_span,
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
        if let Some(dispatch) = self.dispatch {
            dispatch
        } else if self.bound {
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

#[derive(Clone, Debug)]
struct Namespace {
    path: String,
    witness: Option<Rc<WitnessLink>>,
    dependencies: BTreeSet<&'static str>,
}

fn global_root_dependency(path: &str) -> Option<&'static str> {
    match path.split('.').next()? {
        "window" => Some("namespace_window"),
        "self" => Some("namespace_self"),
        "globalThis" => Some("namespace_globalThis"),
        _ => None,
    }
}

impl Namespace {
    fn from_path(path: String, witness: Option<Rc<WitnessLink>>) -> Option<Self> {
        let relative = path
            .strip_prefix("window.")
            .or_else(|| path.strip_prefix("globalThis."))
            .or_else(|| path.strip_prefix("self."))
            .unwrap_or(&path);
        let canonical = match relative {
            "window" | "globalThis" | "self" => "globalThis",
            "navigator" | "Object" | "Reflect" | "Function" | "Object.prototype"
            | "Function.prototype" | "Array" | "Array.prototype" => relative,
            _ => return None,
        };
        Some(Self {
            path: canonical.to_owned(),
            witness,
            dependencies: global_root_dependency(&path).into_iter().collect(),
        })
    }

    fn property(&self, name: &str) -> Option<String> {
        (!name.contains('.')).then(|| format!("{}.{}", self.path, name))
    }

    fn child(&self, key: &str) -> Option<Self> {
        let mut child = Self::from_path(self.property(key)?, self.witness.clone())?;
        child.dependencies = self.dependencies.clone();
        Some(child)
    }

    fn callable(&self, key: &str) -> Option<Callable> {
        let kind = ApiKind::from_global(&self.property(key)?)?;
        let mut callable = Callable::native(kind);
        callable.captured = self.witness.is_some();
        callable.witness = self.witness.clone();
        callable
            .namespace_dependencies
            .clone_from(&self.dependencies);
        Some(callable)
    }
}

#[derive(Clone, Debug)]
enum NamespaceValue {
    Namespace(Namespace),
    Callable(Callable),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DispatchMode {
    Call,
    Apply,
    ReflectApply,
}

impl DispatchMode {
    fn reflect(self) -> bool {
        self == Self::ReflectApply
    }

    fn receiver_index(self) -> usize {
        usize::from(self.reflect())
    }

    fn name(self) -> &'static str {
        match self {
            Self::Call => "call",
            Self::Apply => "apply",
            Self::ReflectApply => "reflect_apply",
        }
    }
}

pub(super) struct DispatchOperands<'s, 'e, 'a> {
    pub(super) original_object: &'e Expression<'a>,
    pub(super) object: &'e Expression<'a>,
    pub(super) key: &'s str,
    pub(super) original_args: &'e [Argument<'a>],
    pub(super) args: &'s PositionalArguments<'e, 'a>,
    pub(super) span: Span,
}

struct DispatchHead {
    mode: DispatchMode,
    reflective_namespace: Option<Namespace>,
}

pub(super) struct DispatchInvocation {
    pub(super) callable: Callable,
    pub(super) receiver_ref: Option<ReferenceId>,
}

#[derive(Default)]
pub(super) struct CallableIndex {
    aliases: BTreeMap<SymbolId, Available<Callable>>,
    namespaces: BTreeMap<SymbolId, Available<Namespace>>,
    xhr: BTreeMap<SymbolId, Available<Callable>>,
}

pub(super) fn member_parts<'a, 'e>(
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

    fn namespace(
        &self,
        expr: &Expression<'_>,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<Namespace> {
        if let Some(path) = global_path(scoping, constants, expr) {
            return Namespace::from_path(path, None);
        }
        if let Some(symbol) = expression_symbol(scoping, expr) {
            return self.namespaces.get(&symbol)?.at(expr.span().start).cloned();
        }
        let (object, key) = member_parts(expr, scoping, constants)?;
        let parent = self.namespace(object, scoping, constants)?;
        parent.child(&key)
    }

    pub(super) fn namespace_path(
        &self,
        expr: &Expression<'_>,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<Vec<Option<String>>> {
        let namespace = self.namespace(expr, scoping, constants)?;
        Some(
            namespace
                .path
                .split('.')
                .map(|part| Some(part.to_owned()))
                .collect(),
        )
    }

    pub(super) fn intrinsic_path(
        &self,
        expr: &Expression<'_>,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<String> {
        let (object, key) = member_parts(expr, scoping, constants)?;
        self.namespace(object, scoping, constants)?.property(&key)
    }

    pub(super) fn resolve(
        &self,
        expr: &Expression<'_>,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<Callable> {
        let expr = unparenthesized(expr);
        if let Some(path) = global_path(scoping, constants, expr) {
            if let Some(kind) = ApiKind::from_global(&path) {
                let mut callable = Callable::native(kind);
                callable
                    .namespace_dependencies
                    .extend(global_root_dependency(&path));
                return Some(callable);
            }
        }
        if let Some(symbol) = expression_symbol(scoping, expr) {
            return self.aliases.get(&symbol)?.at(expr.span().start).cloned();
        }
        if let Some((object, key)) = member_parts(expr, scoping, constants) {
            if let Some(namespace) = self.namespace(object, scoping, constants) {
                if let Some(callable) = namespace.callable(&key) {
                    return Some(callable);
                }
            }
            if key == "open" {
                let symbol = expression_symbol(scoping, object)?;
                let constructor = self.xhr.get(&symbol)?.at(object.span().start)?;
                let mut callable = Callable::native(ApiKind::XhrOpen);
                callable.receiver = Some(symbol);
                callable.constructor_captured = constructor.captured;
                callable.witness = constructor.witness.clone();
                callable
                    .namespace_dependencies
                    .clone_from(&constructor.namespace_dependencies);
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
        if !self.valid_receiver(&callable, receiver, scoping, constants) {
            return None;
        }
        self.add_receiver_dependencies(&mut callable, receiver, scoping, constants);
        let dependency = callable.dispatch_member_family("bind");
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
        callable.bound_object = Some(call.span);
        Some(callable)
    }
    fn valid_receiver(
        &self,
        callable: &Callable,
        receiver: Option<&Expression<'_>>,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> bool {
        let namespace = receiver.and_then(|expr| self.namespace(expr, scoping, constants));
        let path = namespace.as_ref().map(|ns| ns.path.as_str());
        callable.bound
            || callable.kind.is_constructor()
            || match callable.kind {
                ApiKind::Fetch => {
                    receiver.is_none()
                        || receiver.is_some_and(|expr| {
                            matches!(unparenthesized(expr), Expression::NullLiteral(_))
                                || global_path(scoping, constants, expr).as_deref()
                                    == Some("undefined")
                        })
                        || path.is_some_and(is_global_receiver)
                }
                ApiKind::Beacon => path.is_some_and(is_navigator_receiver),
                ApiKind::XhrOpen => receiver
                    .is_some_and(|expr| expression_symbol(scoping, expr) == callable.receiver),
                ApiKind::WebSocket | ApiKind::XhrConstructor => true,
            }
    }

    fn add_receiver_dependencies(
        &self,
        callable: &mut Callable,
        receiver: Option<&Expression<'_>>,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) {
        // Rebinding an already bound function ignores the supplied receiver.
        if callable.bound || callable.kind.is_constructor() {
            return;
        }
        if let Some(namespace) = receiver.and_then(|expr| self.namespace(expr, scoping, constants))
        {
            callable
                .namespace_dependencies
                .extend(namespace.dependencies);
        }
    }

    fn dispatch_head(
        &self,
        object: &Expression<'_>,
        key: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<DispatchHead> {
        let reflective_namespace = self
            .namespace(object, scoping, constants)
            .filter(|namespace| key == "apply" && namespace.path == "Reflect");
        let mode = if reflective_namespace.is_some() {
            DispatchMode::ReflectApply
        } else {
            match key {
                "call" => DispatchMode::Call,
                "apply" => DispatchMode::Apply,
                _ => return None,
            }
        };
        Some(DispatchHead {
            mode,
            reflective_namespace,
        })
    }

    fn prepare_dispatch(
        &self,
        head: DispatchHead,
        mut callable: Callable,
        receiver: Option<&Expression<'_>>,
        span: Span,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<DispatchInvocation> {
        if callable.kind.is_constructor()
            || !self.valid_receiver(&callable, receiver, scoping, constants)
        {
            return None;
        }
        self.add_receiver_dependencies(&mut callable, receiver, scoping, constants);
        if let Some(namespace) = head.reflective_namespace {
            callable
                .namespace_dependencies
                .extend(namespace.dependencies);
        }
        let receiver_ref = receiver
            .filter(|expr| {
                callable.receiver.is_some() && expression_symbol(scoping, expr) == callable.receiver
            })
            .and_then(direct_reference_id);
        let operation = head.mode.name();
        let dependency = if head.mode.reflect() {
            operation.to_owned()
        } else {
            callable.dispatch_member_family(operation)
        };
        callable.detached = false;
        callable.dispatch = Some(operation);
        callable.add_witness(operation, span, Some(dependency));
        Some(DispatchInvocation {
            callable,
            receiver_ref,
        })
    }

    /// Resolve a native dispatch from positional value origins. Both the
    /// syntax-only path and wrapper specialization use this exact routing:
    /// receiver, target (Reflect), bound prefixes and array-like arguments.
    pub(super) fn resolve_dispatch_values(
        &self,
        operands: DispatchOperands<'_, '_, '_>,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<DispatchInvocation> {
        let head = self.dispatch_head(operands.object, operands.key, scoping, constants)?;
        let mode = head.mode;
        let (target, captured) = if mode.reflect() {
            let target = operands.args.value(0).expression()?;
            let original = operands
                .original_args
                .first()
                .and_then(Argument::as_expression);
            (
                target,
                !original.is_some_and(|expr| std::ptr::eq(expr, target)),
            )
        } else {
            (
                operands.object,
                !std::ptr::eq(operands.original_object, operands.object),
            )
        };
        let mut callable = self.resolve(target, source, scoping, constants)?;
        if captured {
            callable.capture_as_argument();
        }
        let offset = mode.receiver_index();
        let receiver = match operands.args.value(offset) {
            ForwardedValue::Expression(expr) => Some(expr),
            ForwardedValue::Missing => None,
            ForwardedValue::Primitive { value, .. }
                if matches!(
                    value.as_ref(),
                    StaticPrimitiveValue::Null | StaticPrimitiveValue::Undefined
                ) =>
            {
                None
            }
            // A bound function ignores its new receiver altogether.
            ForwardedValue::Primitive { .. } if callable.bound => None,
            ForwardedValue::Array { .. }
            | ForwardedValue::Object { .. }
            | ForwardedValue::Unknown(_)
                if callable.bound =>
            {
                None
            }
            _ => return None,
        };
        let mut dispatch =
            self.prepare_dispatch(head, callable, receiver, operands.span, scoping, constants)?;
        if mode == DispatchMode::Call {
            dispatch.callable.prefix.append_forwarded(
                operands.args.values.iter().skip(offset + 1).cloned(),
                operands.args.unknown_tail,
                source,
                scoping,
                constants,
            );
        } else {
            let array = apply_array_source(
                operands.args.value(offset + 1),
                mode,
                scoping,
                constants,
                operands.span,
            )?;
            dispatch
                .callable
                .prefix
                .append_array_source(array, source, scoping, constants);
        }
        Some(dispatch)
    }

    pub(super) fn resolve_dispatch(
        &self,
        call: &CallExpression<'_>,
        source: &str,
        scoping: &Scoping,
        constants: &ProvenConstantEnvironment,
    ) -> Option<DispatchInvocation> {
        if call.optional {
            return None;
        }
        let (object, key) = member_parts(&call.callee, scoping, constants)?;
        let mut args = PositionalArguments::default();
        // The Reflect target, receiver and two sink positions are sufficient.
        // Unknown-length spreads stop the prefix, never becoming fixed slots.
        for arg in call.arguments.iter().take(4) {
            if let Some(expr) = arg.as_expression() {
                args.values.push(ForwardedValue::Expression(expr));
            } else {
                args.unknown_tail = Some(arg.span());
                break;
            }
        }
        self.resolve_dispatch_values(
            DispatchOperands {
                original_object: object,
                object,
                key: &key,
                original_args: &call.arguments,
                args: &args,
                span: call.span,
            },
            source,
            scoping,
            constants,
        )
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

    fn bind_value(
        &mut self,
        pattern: &BindingPattern<'_>,
        value: NamespaceValue,
        span: Span,
        after: u32,
        kind: &str,
    ) {
        match pattern {
            BindingPattern::BindingIdentifier(identifier) => {
                let Some(symbol) = identifier.symbol_id.get() else {
                    return;
                };
                if !xhr_binding_is_not_reassigned(self.scoping, symbol) {
                    return;
                }
                match value {
                    NamespaceValue::Callable(mut callable) => {
                        callable.captured = true;
                        callable.detached = !callable.bound && callable.kind.needs_receiver();
                        callable.add_witness(kind, span, None);
                        self.index.aliases.insert(
                            symbol,
                            Available {
                                after,
                                value: callable,
                            },
                        );
                    }
                    NamespaceValue::Namespace(mut namespace) => {
                        namespace.witness = Some(Rc::new(WitnessLink {
                            previous: namespace.witness.take(),
                            witness: ApiBindingWitness {
                                kind: kind.to_owned(),
                                start: span.start,
                                end: span.end,
                            },
                            dependency: None,
                        }));
                        self.index.namespaces.insert(
                            symbol,
                            Available {
                                after,
                                value: namespace,
                            },
                        );
                    }
                }
            }
            BindingPattern::ObjectPattern(object) => {
                let NamespaceValue::Namespace(namespace) = value else {
                    return;
                };
                for property in &object.properties {
                    let key = property
                        .key
                        .static_name()
                        .and_then(|name| name.into_cow_str().map(|key| key.into_owned()))
                        .or_else(|| {
                            property
                                .key
                                .as_expression()
                                .and_then(|expr| static_string(expr, self.scoping, self.constants))
                        });
                    let Some(key) = key else {
                        continue;
                    };
                    let property_value = namespace
                        .callable(&key)
                        .map(NamespaceValue::Callable)
                        .or_else(|| namespace.child(&key).map(NamespaceValue::Namespace));
                    if let Some(value) = property_value {
                        self.bind_value(
                            &property.value,
                            value,
                            property.span,
                            after,
                            "destructure",
                        );
                    }
                }
            }
            _ => {}
        }
    }

    fn record(&mut self, declaration: &VariableDeclarator<'_>, immutable: bool) {
        let Some(init) = declaration.init.as_ref() else {
            return;
        };
        if immutable {
            let value = self
                .resolve(init)
                .map(NamespaceValue::Callable)
                .or_else(|| {
                    self.index
                        .namespace(init, self.scoping, self.constants)
                        .map(NamespaceValue::Namespace)
                });
            if let Some(value) = value {
                self.bind_value(
                    &declaration.id,
                    value,
                    declaration.span,
                    declaration.span.end,
                    "const_alias",
                );
                return;
            }
        }
        let BindingPattern::BindingIdentifier(identifier) = &declaration.id else {
            return;
        };
        let Some(symbol) = identifier.symbol_id.get() else {
            return;
        };
        if !xhr_binding_is_not_reassigned(self.scoping, symbol) {
            return;
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
