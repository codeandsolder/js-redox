//! Specialize straight-line local forwarding chains using existing lexical
//! parameter proof and native callable evidence. Separate original body sink
//! sites from their call-specific specializations. No AST rewriting/evaluation.
use super::{
    callables::{member_parts, DispatchOperands, ForwardedValue, PositionalArguments},
    *,
};
use oxc_ast::{
    ast::{
        Argument, ArrayExpression, ArrayExpressionElement, FormalParameters, Function,
        FunctionBody, Statement, VariableDeclarationKind,
    },
    AstKind,
};
use oxc_semantic::Semantic;
use oxc_syntax::scope::ScopeId;
use std::{collections::BTreeMap, rc::Rc};

type ArgumentList<'a> = PositionalArguments<'a, 'a>;
type ValueFrame<'a> = BTreeMap<SymbolId, ForwardedValue<'a, 'a>>;

/// Carry value origins rather than copying syntax into a different scope.
/// Materialized arrays share their positional contents; spreading a known
/// array or rest value consumes those positions, while apply uses indexed
/// contents without depending on Array.prototype[Symbol.iterator].
struct ValueBuilder<'s, 'a> {
    frame: Option<ValueFrame<'a>>,
    scoping: &'s Scoping,
    constants: &'s ProvenConstantEnvironment,
    limit: usize,
    budget: &'s WorkBudget,
    used_iterator: bool,
}

impl<'s, 'a> ValueBuilder<'s, 'a> {
    fn new(
        frame: Option<ValueFrame<'a>>,
        scoping: &'s Scoping,
        constants: &'s ProvenConstantEnvironment,
        limit: usize,
        budget: &'s WorkBudget,
    ) -> Self {
        Self {
            frame,
            scoping,
            constants,
            limit,
            budget,
            used_iterator: false,
        }
    }

    fn expression(&mut self, expr: &'a Expression<'a>) -> Result<ForwardedValue<'a, 'a>> {
        self.budget.consume(1)?;
        if let Some(frame) = &self.frame {
            if let Some(value) =
                expression_symbol(self.scoping, expr).and_then(|symbol| frame.get(&symbol))
            {
                return Ok(value.clone());
            }
            if let Expression::ArrayExpression(array) = unparenthesized(expr) {
                let positions = self.array(array)?;
                return Ok(ForwardedValue::Array {
                    span: expr.span(),
                    positions: Rc::new(positions),
                });
            }
            if let Expression::ObjectExpression(object) = unparenthesized(expr) {
                let mut fields = BTreeMap::new();
                for item in &object.properties {
                    let ObjectPropertyKind::ObjectProperty(property) = item else {
                        return Ok(ForwardedValue::Expression(expr));
                    };
                    let Some(key) = literal_data_key(property, self.scoping, self.constants) else {
                        return Ok(ForwardedValue::Expression(expr));
                    };
                    fields.insert(key, self.expression(&property.value)?);
                }
                return Ok(ForwardedValue::Object {
                    span: expr.span(),
                    fields: Rc::new(fields),
                });
            }
        }
        Ok(ForwardedValue::Expression(expr))
    }

    fn extend(
        &self,
        result: &mut ArgumentList<'a>,
        origin: &ArgumentList<'a>,
        start: usize,
        span: Span,
    ) -> Result<()> {
        let available = origin.values.len().saturating_sub(start);
        let count = self
            .limit
            .saturating_sub(result.values.len())
            .min(available);
        self.budget.consume(count as u64)?;
        result
            .values
            .extend(origin.values.iter().skip(start).take(count).cloned());
        result.unknown_tail = if count < available {
            Some(span)
        } else {
            origin.unknown_tail
        };
        Ok(())
    }

    fn spread(
        &mut self,
        result: &mut ArgumentList<'a>,
        expression: &'a Expression<'a>,
        span: Span,
    ) -> Result<()> {
        let value = self.expression(expression)?;
        match value {
            ForwardedValue::Array { positions, .. } => {
                self.used_iterator = true;
                self.extend(result, &positions, 0, span)?;
            }
            ForwardedValue::Expression(expr) => {
                if let Expression::ArrayExpression(array) = unparenthesized(expr) {
                    // An expression captured in a preceding caller is not
                    // evaluated in the current wrapper's lexical frame.
                    let mut captured =
                        Self::new(None, self.scoping, self.constants, self.limit, self.budget);
                    let positions = captured.array(array)?;
                    self.used_iterator = true;
                    self.extend(result, &positions, 0, span)?;
                } else {
                    result.unknown_tail = Some(span);
                }
            }
            _ => result.unknown_tail = Some(span),
        }
        Ok(())
    }

    fn full(&self, result: &mut ArgumentList<'a>, span: Span) -> bool {
        if result.values.len() >= self.limit {
            result.unknown_tail = Some(span);
        }
        result.unknown_tail.is_some()
    }

    fn call(&mut self, args: &'a [Argument<'a>]) -> Result<ArgumentList<'a>> {
        let mut result = ArgumentList::default();
        self.budget.consume(args.len() as u64)?;
        for arg in args {
            if self.full(&mut result, arg.span()) {
                break;
            }
            if let Argument::SpreadElement(spread) = arg {
                self.spread(&mut result, &spread.argument, arg.span())?;
            } else if let Some(expr) = arg.as_expression() {
                result.values.push(self.expression(expr)?);
            }
            if result.unknown_tail.is_some() {
                break;
            }
        }
        Ok(result)
    }

    fn array(&mut self, array: &'a ArrayExpression<'a>) -> Result<ArgumentList<'a>> {
        let mut result = ArgumentList::default();
        self.budget.consume(array.elements.len() as u64)?;
        for element in &array.elements {
            if self.full(&mut result, element.span()) {
                break;
            }
            match element {
                ArrayExpressionElement::Elision(_) => {
                    result.values.push(ForwardedValue::Unknown(None))
                }
                ArrayExpressionElement::SpreadElement(spread) => {
                    self.spread(&mut result, &spread.argument, spread.span)?;
                }
                _ => {
                    if let Some(expr) = element.as_expression() {
                        result.values.push(self.expression(expr)?);
                    }
                }
            }
            if result.unknown_tail.is_some() {
                break;
            }
        }
        Ok(result)
    }
}

struct Parameters {
    fixed: Vec<SymbolId>,
    rest: Option<SymbolId>,
}

impl Parameters {
    fn from_formals(params: &FormalParameters<'_>, scoping: &Scoping) -> Option<Self> {
        let fixed = params
            .items
            .iter()
            .map(|param| {
                if param.initializer.is_some() {
                    return None;
                }
                param.pattern.get_binding_identifier()?.symbol_id.get()
            })
            .collect::<Option<Vec<_>>>()?;
        let rest = if let Some(rest) = &params.rest {
            let symbol = rest
                .rest
                .argument
                .get_binding_identifier()?
                .symbol_id
                .get()?;
            if !xhr_binding_is_not_reassigned(scoping, symbol) {
                return None;
            }
            // A rest array can be mutated via a member/escape even if its
            // binding is never reassigned. Only direct spread uses are trusted.
            Some(symbol)
        } else {
            None
        };
        let all = fixed.iter().copied().chain(rest);
        let mut unique = BTreeSet::new();
        if !all.into_iter().all(|symbol| unique.insert(symbol)) {
            return None;
        }
        Some(Self { fixed, rest })
    }
}

#[derive(Clone, Copy)]
struct LocalInitializer<'a> {
    symbol: SymbolId,
    span: Span,
    expression: &'a Expression<'a>,
}

struct Wrapper<'a> {
    span: Span,
    params: Parameters,
    locals: Vec<LocalInitializer<'a>>,
    body: &'a Expression<'a>,
    returns_value: bool,
}

/// Admit an ordered sequence of immutable identifier initializers and a
/// final invocation/value expression. Initializer purity and reference
/// confinement are checked against the specializing frame, not guessed
/// from the declaration keyword.
fn straight_line_body<'a>(
    body: &'a FunctionBody<'a>,
) -> Option<(Vec<LocalInitializer<'a>>, &'a Expression<'a>, bool)> {
    let (last, initializers) = body.statements.split_last()?;
    let (expression, returns_value) = match last {
        Statement::ReturnStatement(statement) => (statement.argument.as_ref()?, true),
        Statement::ExpressionStatement(statement) => (&statement.expression, false),
        _ => return None,
    };
    let mut locals = Vec::new();
    for statement in initializers {
        let Statement::VariableDeclaration(declaration) = statement else {
            return None;
        };
        if declaration.kind != VariableDeclarationKind::Const {
            return None;
        }
        for declarator in &declaration.declarations {
            locals.push(LocalInitializer {
                symbol: declarator.id.get_binding_identifier()?.symbol_id.get()?,
                span: declarator.span,
                expression: declarator.init.as_ref()?,
            });
        }
    }
    Some((locals, expression, returns_value))
}

#[derive(Default)]
struct ArgumentsObjectProbe(bool);

impl<'a> Visit<'a> for ArgumentsObjectProbe {
    fn visit_identifier_reference(&mut self, id: &oxc_ast::ast::IdentifierReference<'a>) {
        self.0 |= id.name == "arguments";
    }
}

fn uses_arguments_object(expression: &Expression<'_>) -> bool {
    let mut probe = ArgumentsObjectProbe::default();
    probe.visit_expression(expression);
    probe.0
}

impl<'a> Wrapper<'a> {
    fn function(fun: &'a Function<'a>, scoping: &Scoping) -> Option<Self> {
        if fun.generator {
            return None;
        }
        let (locals, body, returns_value) = straight_line_body(fun.body.as_ref()?)?;
        Some(Self {
            span: fun.span,
            params: Parameters::from_formals(&fun.params, scoping)?,
            locals,
            body,
            returns_value: returns_value && !fun.r#async,
        })
    }

    fn expression(expr: &'a Expression<'a>, scoping: &Scoping) -> Option<Self> {
        match unparenthesized(expr) {
            Expression::FunctionExpression(fun) => Self::function(fun, scoping),
            Expression::ArrowFunctionExpression(fun) => {
                let (locals, body, returns_value) = match &fun.body {
                    oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) => {
                        straight_line_body(body)?
                    }
                    body => (Vec::new(), body.as_expression()?, true),
                };
                Some(Self {
                    span: fun.span,
                    params: Parameters::from_formals(&fun.params, scoping)?,
                    locals,
                    body,
                    returns_value: returns_value && !fun.r#async,
                })
            }
            _ => None,
        }
    }

    fn invocation(&self) -> Option<(&'a Expression<'a>, &'a [Argument<'a>], Span, bool)> {
        let expr = unparenthesized(self.body);
        let expr = if let Expression::AwaitExpression(awaited) = expr {
            unparenthesized(&awaited.argument)
        } else {
            expr
        };
        match expr {
            Expression::CallExpression(call) if !call.optional => {
                Some((&call.callee, &call.arguments, call.span, false))
            }
            Expression::NewExpression(new) => Some((&new.callee, &new.arguments, new.span, true)),
            _ => None,
        }
    }
}

enum LocalBinding<'a> {
    Function(&'a Function<'a>),
    Initializer {
        value: &'a Expression<'a>,
        after: u32,
    },
}

enum BindingOrigin<'a> {
    Declaration(SymbolId, &'a Function<'a>),
    Expression(&'a Expression<'a>),
}

/// Reuse the already validated semantic AST, rather than reparsing the source
/// or textually resolving names. Mutable lexical definitions and direct eval
/// in a visible scope preclude an exact local target.
pub(super) struct WrapperIndex<'a> {
    bindings: BTreeMap<SymbolId, LocalBinding<'a>>,
    script_root_functions: BTreeMap<SymbolId, String>,
    eval_scopes: BTreeSet<ScopeId>,
    positional_limit: usize,
}

impl<'a> WrapperIndex<'a> {
    pub(super) fn collect(semantic: &Semantic<'a>, budget: &WorkBudget) -> Result<Self> {
        let scoping = semantic.scoping();
        let mut bindings = BTreeMap::new();
        let mut script_root_functions = BTreeMap::new();
        let mut eval_scopes = BTreeSet::new();
        // An acyclic wrapper chain can consume at most the sum of all
        // fixed formal counts before its final two API positions plus dispatch receiver and target. Keep a
        // bounded prefix large enough for every such chain; any truncation
        // carries an unknown-tail witness rather than inventing missing args.
        let mut positional_limit = 4usize;
        for node in semantic.nodes().iter() {
            budget.consume(1)?;
            let params = match node.kind() {
                AstKind::Function(fun) => fun.params.items.len(),
                AstKind::ArrowFunctionExpression(fun) => fun.params.items.len(),
                _ => 0,
            };
            positional_limit = positional_limit.saturating_add(params);
            if let AstKind::CallExpression(call) = node.kind() {
                if matches!(unparenthesized(&call.callee), Expression::Identifier(id) if id.name == "eval")
                {
                    eval_scopes.insert(node.scope_id());
                }
            }
        }
        for node in semantic.nodes().iter() {
            budget.consume(1)?;
            let (symbol, binding) = match node.kind() {
                AstKind::Function(fun) if fun.is_declaration() => {
                    if !Wrapper::function(fun, scoping).is_some_and(|wrapper| {
                        wrapper.invocation().is_some()
                            || (wrapper.returns_value
                                && matches!(
                                    unparenthesized(wrapper.body),
                                    Expression::Identifier(_)
                                        | Expression::StaticMemberExpression(_)
                                        | Expression::ComputedMemberExpression(_)
                                ))
                    }) {
                        continue;
                    }
                    let Some(symbol) = fun.id.as_ref().and_then(|id| id.symbol_id.get()) else {
                        continue;
                    };
                    (symbol, LocalBinding::Function(fun))
                }
                AstKind::VariableDeclarator(decl) => {
                    let Some(symbol) = decl
                        .id
                        .get_binding_identifier()
                        .and_then(|id| id.symbol_id.get())
                    else {
                        continue;
                    };
                    if !scoping.symbol_flags(symbol).is_const_variable() {
                        continue;
                    }
                    let Some(value) = decl.init.as_ref() else {
                        continue;
                    };
                    if !matches!(
                        unparenthesized(value),
                        Expression::Identifier(_)
                            | Expression::FunctionExpression(_)
                            | Expression::ArrowFunctionExpression(_)
                            | Expression::CallExpression(_)
                    ) {
                        continue;
                    }
                    (
                        symbol,
                        LocalBinding::Initializer {
                            value,
                            after: decl.span.end,
                        },
                    )
                }
                _ => continue,
            };
            if !scoping.symbol_redeclarations(symbol).is_empty()
                || !xhr_binding_is_not_reassigned(scoping, symbol)
            {
                continue;
            }
            if matches!(binding, LocalBinding::Function(_)) {
                let name = scoping.symbol_name(symbol);
                let mut dynamic = false;
                for scope in &eval_scopes {
                    budget.consume(1)?;
                    if scoping.find_binding(*scope, name.into()) == Some(symbol) {
                        dynamic = true;
                        break;
                    }
                }
                if dynamic {
                    continue;
                }
                if !semantic.source_type().is_module()
                    && scoping.symbol_scope_id(symbol) == scoping.root_scope_id()
                {
                    script_root_functions.insert(symbol, name.to_owned());
                }
            }
            bindings.insert(symbol, binding);
        }
        Ok(Self {
            bindings,
            script_root_functions,
            eval_scopes,
            positional_limit,
        })
    }

    pub(super) fn root_mutation_targets(&self) -> impl Iterator<Item = (&str, String)> {
        self.script_root_functions
            .iter()
            .map(|(symbol, name)| (name.as_str(), format!("wrapper_global:{symbol:?}")))
    }

    fn frame_has_dynamic_scope(
        &self,
        wrapper: &Wrapper<'_>,
        scoping: &Scoping,
        budget: &WorkBudget,
    ) -> Result<bool> {
        for symbol in wrapper
            .params
            .fixed
            .iter()
            .copied()
            .chain(wrapper.params.rest)
            .chain(wrapper.locals.iter().map(|local| local.symbol))
        {
            for scope in &self.eval_scopes {
                budget.consume(1)?;
                if scoping.find_binding(*scope, scoping.symbol_name(symbol).into()) == Some(symbol)
                {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    fn may_resolve(&self, expr: &Expression<'_>, scoping: &Scoping) -> bool {
        expression_symbol(scoping, expr).is_some_and(|symbol| self.bindings.contains_key(&symbol))
            || matches!(
                unparenthesized(expr),
                Expression::FunctionExpression(_)
                    | Expression::ArrowFunctionExpression(_)
                    | Expression::CallExpression(_)
            )
    }

    fn binding_origin(
        &self,
        mut expr: &'a Expression<'a>,
        scoping: &Scoping,
        budget: &WorkBudget,
        witnesses: &mut Vec<ApiBindingWitness>,
        alias_kind: &str,
    ) -> Result<Option<BindingOrigin<'a>>> {
        let mut visited = BTreeSet::new();
        loop {
            budget.consume(1)?;
            let Some(symbol) = expression_symbol(scoping, expr) else {
                return Ok(Some(BindingOrigin::Expression(expr)));
            };
            let Some(binding) = self.bindings.get(&symbol) else {
                return Ok(Some(BindingOrigin::Expression(expr)));
            };
            if !visited.insert(symbol) {
                return Ok(None);
            }
            match binding {
                LocalBinding::Function(fun) => {
                    return Ok(Some(BindingOrigin::Declaration(symbol, fun)))
                }
                LocalBinding::Initializer { value, after } => {
                    if expr.span().start < *after {
                        return Ok(None);
                    }
                    witnesses.push(ApiBindingWitness {
                        kind: alias_kind.into(),
                        start: value.span().start,
                        end: value.span().end,
                    });
                    expr = value;
                }
            }
        }
    }

    fn factory_call(
        &self,
        expr: &'a Expression<'a>,
        scoping: &Scoping,
        budget: &WorkBudget,
        witnesses: &mut Vec<ApiBindingWitness>,
    ) -> Result<Option<&'a CallExpression<'a>>> {
        let Some(BindingOrigin::Expression(expr)) =
            self.binding_origin(expr, scoping, budget, witnesses, "wrapper_return_alias")?
        else {
            return Ok(None);
        };
        Ok(match unparenthesized(expr) {
            Expression::CallExpression(call) if !call.optional => Some(call),
            _ => None,
        })
    }

    fn resolve(
        &self,
        expr: &'a Expression<'a>,
        scoping: &Scoping,
        budget: &WorkBudget,
        dependencies: &mut BTreeSet<String>,
        witnesses: &mut Vec<ApiBindingWitness>,
    ) -> Result<Option<Wrapper<'a>>> {
        Ok(
            match self.binding_origin(expr, scoping, budget, witnesses, "wrapper_alias")? {
                Some(BindingOrigin::Declaration(symbol, fun)) => {
                    if self.script_root_functions.contains_key(&symbol) {
                        dependencies.insert(format!("wrapper_global:{symbol:?}"));
                    }
                    Wrapper::function(fun, scoping)
                }
                Some(BindingOrigin::Expression(value)) => Wrapper::expression(value, scoping),
                None => None,
            },
        )
    }
}

/// A caller's object literal must not become exact property evidence after
/// the wrapper exposes or changes it. Only direct callee/argument uses in the
/// one forwarding invocation are accepted, including parenthesized references.
fn parameter_is_direct(
    symbol: SymbolId,
    sink: Span,
    locals: &[LocalInitializer<'_>],
    semantic: &Semantic<'_>,
    constants: &ProvenConstantEnvironment,
    spread_safe: bool,
    budget: &WorkBudget,
) -> Result<bool> {
    let scoping = semantic.scoping();
    for reference_id in scoping.get_resolved_reference_ids(symbol) {
        budget.consume(1)?;
        let reference = scoping.get_reference(*reference_id);
        if reference.is_write() || reference.flags().is_member_write_target() {
            return Ok(false);
        }
        let mut current = semantic.nodes().get_node(reference.node_id()).span();
        let used_in_final_value = current == sink;
        if used_in_final_value {
            continue;
        }
        let mut dispatch_member = false;
        let mut inside_array = false;
        let mut accepted = false;
        for id in semantic.nodes().ancestor_ids(reference.node_id()) {
            budget.consume(1)?;
            let kind = semantic.nodes().kind(id);
            match kind {
                AstKind::ParenthesizedExpression(_) => {}
                AstKind::ArrayExpression(_) if !dispatch_member => {
                    inside_array = true;
                }
                AstKind::ObjectProperty(property)
                    if !dispatch_member
                        && property.value.span() == current
                        && literal_data_key(property, scoping, constants).is_some() => {}
                AstKind::ObjectExpression(_) if !dispatch_member => {}

                AstKind::SpreadElement(_) if !dispatch_member && (inside_array || spread_safe) => {}
                AstKind::StaticMemberExpression(member)
                    if !dispatch_member
                        && !member.optional
                        && member.object.span() == current
                        && matches!(member.property.name.as_str(), "call" | "apply") =>
                {
                    dispatch_member = true;
                }
                AstKind::ComputedMemberExpression(member)
                    if !dispatch_member
                        && !member.optional
                        && member.object.span() == current
                        && static_string(&member.expression, scoping, constants)
                            .as_deref()
                            .is_some_and(|name| matches!(name, "call" | "apply")) =>
                {
                    dispatch_member = true;
                }
                AstKind::CallExpression(call) => {
                    accepted =
                        call.span == sink && (!dispatch_member || call.callee.span() == current);
                    break;
                }
                AstKind::NewExpression(new) => {
                    accepted = !dispatch_member && new.span == sink;
                    break;
                }
                AstKind::VariableDeclarator(declaration) => {
                    accepted = !dispatch_member
                        && locals.iter().any(|local| {
                            declaration.span == local.span && local.expression.span() == current
                        });
                    break;
                }
                _ => break,
            }
            current = kind.span();
            if current == sink && !dispatch_member {
                accepted = true;
                break;
            }
        }
        if !accepted {
            return Ok(false);
        }
    }
    Ok(true)
}

fn known_array(value: &ForwardedValue<'_, '_>) -> bool {
    match value {
        ForwardedValue::Array { .. } => true,
        ForwardedValue::Expression(expr) => {
            matches!(unparenthesized(expr), Expression::ArrayExpression(_))
        }
        _ => false,
    }
}

/// The local frame only evaluates transparent reads, pure constants and
/// private literal construction. A native property read uses the existing
/// browser identity assumptions; arbitrary property reads/calls may execute
/// user code, so must not be silently moved across initializer boundaries.
fn pure_initializer<'a>(
    expression: &'a Expression<'a>,
    builder: &mut ValueBuilder<'_, 'a>,
    all_locals: &BTreeSet<SymbolId>,
    collector: &Collector<'_, '_>,
) -> Result<bool> {
    builder.budget.consume(1)?;
    let expr = unparenthesized(expression);
    let scoping = collector.scoping;
    let constants = collector.constants;
    if let Some(symbol) = expression_symbol(scoping, expr) {
        if all_locals.contains(&symbol) {
            return Ok(builder
                .frame
                .as_ref()
                .is_some_and(|frame| frame.contains_key(&symbol)));
        }
        // Reads of other lexical bindings are non-effectful, but a
        // value origin needs its own static proof at the use site.
        return Ok(true);
    }
    match expr {
        Expression::StringLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::BigIntLiteral(_) => Ok(true),
        Expression::ArrayExpression(array) => {
            for element in &array.elements {
                match element {
                    ArrayExpressionElement::Elision(_) => {}
                    ArrayExpressionElement::SpreadElement(spread) => {
                        if !pure_initializer(&spread.argument, builder, all_locals, collector)?
                            || !known_array(&builder.expression(&spread.argument)?)
                        {
                            return Ok(false);
                        }
                    }
                    _ => {
                        let Some(expr) = element.as_expression() else {
                            return Ok(false);
                        };
                        if !pure_initializer(expr, builder, all_locals, collector)? {
                            return Ok(false);
                        }
                    }
                }
            }
            Ok(true)
        }
        Expression::ObjectExpression(object) => {
            for item in &object.properties {
                let ObjectPropertyKind::ObjectProperty(property) = item else {
                    return Ok(false);
                };
                if literal_data_key(property, scoping, constants).is_none()
                    || !pure_initializer(&property.value, builder, all_locals, collector)?
                {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // Only side-effect-free statically proven primitive expressions
        // and recognized native/namespace reads beyond the literal cases.
        _ => Ok(static_string(expr, scoping, constants).is_some()
            || global_path(scoping, constants, expr).as_deref() == Some("undefined")
            || (!matches!(expr, Expression::CallExpression(_))
                && (collector
                    .callables
                    .resolve(expr, collector.source, scoping, constants)
                    .is_some()
                    || collector
                        .callables
                        .namespace_path(expr, scoping, constants)
                        .is_some()))),
    }
}

fn uses_confined_value(
    symbol: SymbolId,
    value: &ForwardedValue<'_, '_>,
    wrapper: &Wrapper<'_>,
    sink: Span,
    semantic: &Semantic<'_>,
    constants: &ProvenConstantEnvironment,
    budget: &WorkBudget,
) -> Result<bool> {
    parameter_is_direct(
        symbol,
        sink,
        &wrapper.locals,
        semantic,
        constants,
        known_array(value),
        budget,
    )
}

/// Construct one invocation frame in source order. Every forwarded alias
/// must have confined references, and no initializer may call arbitrary
/// code. A failed frame is discarded as a unit (aliases can share objects).
fn instantiate<'a, 's>(
    wrapper: &Wrapper<'a>,
    args: &ArgumentList<'a>,
    sink: Span,
    semantic: &Semantic<'a>,
    collector: &Collector<'_, 's>,
    limit: usize,
    budget: &'s WorkBudget,
) -> Result<Option<ValueBuilder<'s, 'a>>> {
    let mut builder = ValueBuilder::new(
        Some(ValueFrame::new()),
        collector.scoping,
        collector.constants,
        limit,
        budget,
    );
    let all_locals = wrapper
        .params
        .fixed
        .iter()
        .copied()
        .chain(wrapper.params.rest)
        .chain(wrapper.locals.iter().map(|local| local.symbol))
        .collect::<BTreeSet<_>>();
    for (index, symbol) in wrapper
        .params
        .fixed
        .iter()
        .copied()
        .chain(wrapper.params.rest)
        .enumerate()
    {
        let value = if wrapper.params.rest == Some(symbol) {
            let mut positions = ArgumentList::default();
            builder.extend(&mut positions, args, index, wrapper.span)?;
            ForwardedValue::Array {
                span: wrapper.span,
                positions: Rc::new(positions),
            }
        } else {
            args.value(index)
        };
        if uses_confined_value(
            symbol,
            &value,
            wrapper,
            sink,
            semantic,
            collector.constants,
            budget,
        )? {
            if let Some(frame) = &mut builder.frame {
                frame.insert(symbol, value);
            }
        } else if wrapper.params.rest == Some(symbol) || !wrapper.locals.is_empty() {
            return Ok(None);
        }
    }
    // A parameter omitted from the frame above is not a transparent
    // origin. It must not be accidentally recovered via an alias.
    for local in &wrapper.locals {
        if uses_arguments_object(local.expression)
            || !pure_initializer(local.expression, &mut builder, &all_locals, collector)?
        {
            return Ok(None);
        }
        let value = builder.expression(local.expression)?;
        if !uses_confined_value(
            local.symbol,
            &value,
            wrapper,
            sink,
            semantic,
            collector.constants,
            budget,
        )? {
            return Ok(None);
        }
        if let Some(frame) = &mut builder.frame {
            frame.insert(local.symbol, value);
        }
    }
    Ok(Some(builder))
}

fn append_local_witnesses(wrapper: &Wrapper<'_>, witnesses: &mut Vec<ApiBindingWitness>) {
    witnesses.extend(wrapper.locals.iter().map(|local| ApiBindingWitness {
        kind: "wrapper_local_binding".into(),
        start: local.span.start,
        end: local.span.end,
    }));
}

struct ReturnedCallable {
    callable: Callable,
    witnesses: Vec<ApiBindingWitness>,
    dependencies: BTreeSet<String>,
}

/// Recover functions returning an existing native callable through a
/// confined straight-line value frame. Iterate over nested factory values
/// and immutable aliases, rather than running arbitrary factory bodies.
/// Async returns, closure creation and calls requiring a new environment
/// are not interpreted as existing native callable values.
fn resolve_returned_callable<'a>(
    mut expr: &'a Expression<'a>,
    semantic: &Semantic<'a>,
    wrappers: &WrapperIndex<'a>,
    collector: &Collector<'_, '_>,
    budget: &WorkBudget,
) -> Result<Option<ReturnedCallable>> {
    let mut witnesses = Vec::new();
    let mut dependencies = BTreeSet::new();
    let mut visited = BTreeSet::new();
    loop {
        budget.consume(1)?;
        if !visited.is_empty() {
            if let Some(mut callable) = collector.callables.resolve(
                expr,
                collector.source,
                collector.scoping,
                collector.constants,
            ) {
                callable.capture_as_argument();
                return Ok(Some(ReturnedCallable {
                    callable,
                    witnesses,
                    dependencies,
                }));
            }
        }
        let Some(factory) =
            wrappers.factory_call(expr, collector.scoping, budget, &mut witnesses)?
        else {
            return Ok(None);
        };
        if !visited.insert((factory.span.start, factory.span.end)) {
            return Ok(None);
        }
        let Some(wrapper) = wrappers.resolve(
            &factory.callee,
            collector.scoping,
            budget,
            &mut dependencies,
            &mut witnesses,
        )?
        else {
            return Ok(None);
        };
        if !wrapper.returns_value
            || wrapper.invocation().is_some()
            || wrappers.frame_has_dynamic_scope(&wrapper, collector.scoping, budget)?
            || uses_arguments_object(wrapper.body)
        {
            return Ok(None);
        }
        let mut arguments = ValueBuilder::new(
            None,
            collector.scoping,
            collector.constants,
            wrappers.positional_limit,
            budget,
        );
        let args = arguments.call(&factory.arguments)?;
        if arguments.used_iterator {
            dependencies.insert("rest_iterator".into());
        }
        let Some(mut builder) = instantiate(
            &wrapper,
            &args,
            wrapper.body.span(),
            semantic,
            collector,
            wrappers.positional_limit,
            budget,
        )?
        else {
            return Ok(None);
        };
        let locals = wrapper
            .params
            .fixed
            .iter()
            .copied()
            .chain(wrapper.params.rest)
            .chain(wrapper.locals.iter().map(|local| local.symbol))
            .collect::<BTreeSet<_>>();
        if !pure_initializer(wrapper.body, &mut builder, &locals, collector)? {
            return Ok(None);
        }
        let Some(origin) = builder.expression(wrapper.body)?.expression() else {
            return Ok(None);
        };
        if builder.used_iterator {
            dependencies.insert("rest_iterator".into());
        }
        witnesses.push(ApiBindingWitness {
            kind: "wrapper_definition".into(),
            start: wrapper.span.start,
            end: wrapper.span.end,
        });
        append_local_witnesses(&wrapper, &mut witnesses);
        witnesses.push(ApiBindingWitness {
            kind: "wrapper_return".into(),
            start: wrapper.body.span().start,
            end: wrapper.body.span().end,
        });
        witnesses.push(ApiBindingWitness {
            kind: "returned_callable".into(),
            start: factory.span.start,
            end: factory.span.end,
        });
        expr = origin;
    }
}

/// Resolve the same native dispatch head used by direct calls, but from the
/// argument values in the specializing caller frame. A captured function
/// value does not inherit its former member receiver.
fn forwarded_dispatch<'a>(
    callee: &'a Expression<'a>,
    original_args: &'a [Argument<'a>],
    args: &ArgumentList<'a>,
    span: Span,
    builder: &mut ValueBuilder<'_, 'a>,
    collector: &Collector<'_, '_>,
) -> Result<Option<Callable>> {
    let scoping = collector.scoping;
    let constants = collector.constants;
    let Some((original_object, key)) = member_parts(callee, scoping, constants) else {
        return Ok(None);
    };
    let Some(object) = builder.expression(original_object)?.expression() else {
        return Ok(None);
    };
    Ok(collector
        .callables
        .resolve_dispatch_values(
            DispatchOperands {
                original_object,
                object,
                key: &key,
                original_args,
                args,
                span,
            },
            collector.source,
            scoping,
            constants,
        )
        .map(|dispatch| dispatch.callable))
}

/// Follow a chain with concrete source argument origins. Each step has a
/// unique function span and charges the analysis budget; cycles cannot grow
/// the trace. Original syntactic API sites are emitted by the normal walker.
pub(super) struct InvocationSite<'a> {
    pub(super) callee: &'a Expression<'a>,
    pub(super) arguments: &'a [Argument<'a>],
    pub(super) span: Span,
    pub(super) constructor: bool,
}

pub(super) fn specialize<'a>(
    site: InvocationSite<'a>,
    semantic: &Semantic<'a>,
    wrappers: &WrapperIndex<'a>,
    collector: &mut Collector<'_, '_>,
    budget: &WorkBudget,
) -> Result<()> {
    let scoping = collector.scoping;
    if !wrappers.may_resolve(site.callee, scoping) {
        return Ok(());
    }
    let mut callee = site.callee;
    let mut builder = ValueBuilder::new(
        None,
        scoping,
        collector.constants,
        wrappers.positional_limit,
        budget,
    );
    let mut args = builder.call(site.arguments)?;
    let mut witnesses = Vec::new();
    let mut dependencies = BTreeSet::new();
    if builder.used_iterator {
        dependencies.insert("rest_iterator".into());
    }
    let mut visited = BTreeSet::new();
    let mut constructor = site.constructor;
    let mut captured_target = false;
    let mut sink = site.span;
    loop {
        budget.consume(1)?;
        let callable = if let Some(returned) =
            resolve_returned_callable(callee, semantic, wrappers, collector, budget)?
        {
            witnesses.extend(returned.witnesses);
            dependencies.extend(returned.dependencies);
            Some(returned.callable)
        } else if !visited.is_empty() {
            collector
                .callables
                .resolve(callee, collector.source, scoping, collector.constants)
                .map(|mut callable| {
                    if captured_target {
                        callable.capture_as_argument();
                    }
                    callable
                })
        } else {
            None
        };
        if let Some(mut callable) = callable {
            if callable.callable_as(constructor) {
                callable.prefix.append_forwarded(
                    args.values,
                    args.unknown_tail,
                    collector.source,
                    scoping,
                    collector.constants,
                );
                callable.mark_forwarding(&witnesses, sink);
                collector.emit_forwarded(site.callee, callable, site.span, &dependencies);
            }
            return Ok(());
        }
        if constructor {
            return Ok(());
        }
        let Some(wrapper) =
            wrappers.resolve(callee, scoping, budget, &mut dependencies, &mut witnesses)?
        else {
            return Ok(());
        };
        if !visited.insert((wrapper.span.start, wrapper.span.end))
            || wrappers.frame_has_dynamic_scope(&wrapper, scoping, budget)?
            || uses_arguments_object(wrapper.body)
        {
            return Ok(());
        }
        let Some((target, forwarded, sink_span, is_new)) = wrapper.invocation() else {
            return Ok(());
        };
        witnesses.push(ApiBindingWitness {
            kind: "wrapper_definition".into(),
            start: wrapper.span.start,
            end: wrapper.span.end,
        });
        witnesses.push(ApiBindingWitness {
            kind: "forwarded_invocation".into(),
            start: sink_span.start,
            end: sink_span.end,
        });
        sink = sink_span;
        let Some(mut builder) = instantiate(
            &wrapper,
            &args,
            sink,
            semantic,
            collector,
            wrappers.positional_limit,
            budget,
        )?
        else {
            return Ok(());
        };
        append_local_witnesses(&wrapper, &mut witnesses);
        let next_args = builder.call(forwarded)?;
        if !is_new {
            if let Some(mut callable) =
                forwarded_dispatch(target, forwarded, &next_args, sink, &mut builder, collector)?
            {
                if builder.used_iterator {
                    dependencies.insert("rest_iterator".into());
                }
                callable.mark_forwarding(&witnesses, sink);
                collector.emit_forwarded(site.callee, callable, site.span, &dependencies);
                return Ok(());
            }
        }
        let Some(target_expr) = builder.expression(target)?.expression() else {
            return Ok(());
        };
        if builder.used_iterator {
            dependencies.insert("rest_iterator".into());
        }
        captured_target = !std::ptr::eq(target, target_expr);
        args = next_args;
        callee = target_expr;
        constructor = is_new;
    }
}
