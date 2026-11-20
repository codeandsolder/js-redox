//! Ordered lexical frame plans, initializer purity, and reference confinement.
use super::super::{callables::ForwardedValue, *};
use super::values::{known_array, ArgumentList, ValueBuilder, ValueFrame};
use oxc_ast::{
    ast::{
        Argument, ArrayExpressionElement, FormalParameters, Function, FunctionBody, Statement,
        VariableDeclarationKind,
    },
    AstKind,
};
use oxc_semantic::Semantic;
use std::rc::Rc;

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

pub(super) struct Wrapper<'a> {
    pub(super) span: Span,
    params: Parameters,
    locals: Vec<LocalInitializer<'a>>,
    pub(super) body: &'a Expression<'a>,
    pub(super) returns_value: bool,
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

pub(super) fn uses_arguments_object(expression: &Expression<'_>) -> bool {
    let mut probe = ArgumentsObjectProbe::default();
    probe.visit_expression(expression);
    probe.0
}

impl<'a> Wrapper<'a> {
    pub(super) fn symbols(&self) -> impl Iterator<Item = SymbolId> + '_ {
        self.params
            .fixed
            .iter()
            .copied()
            .chain(self.params.rest)
            .chain(self.locals.iter().map(|local| local.symbol))
    }

    pub(super) fn returned_origin(
        &self,
        builder: &mut ValueBuilder<'_, 'a>,
        collector: &Collector<'_, '_>,
    ) -> Result<Option<&'a Expression<'a>>> {
        let locals = self.symbols().collect::<BTreeSet<_>>();
        if !pure_initializer(self.body, builder, &locals, collector)? {
            return Ok(None);
        }
        Ok(builder.expression(self.body)?.expression())
    }

    pub(super) fn function(fun: &'a Function<'a>, scoping: &Scoping) -> Option<Self> {
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

    pub(super) fn expression(expr: &'a Expression<'a>, scoping: &Scoping) -> Option<Self> {
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

    pub(super) fn invocation(
        &self,
    ) -> Option<(&'a Expression<'a>, &'a [Argument<'a>], Span, bool)> {
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
        let mut key_owner = None;
        for id in semantic.nodes().ancestor_ids(reference.node_id()) {
            budget.consume(1)?;
            match semantic.nodes().kind(id) {
                AstKind::ObjectProperty(property) => {
                    let span = property.key.span();
                    if property.computed
                        && span.start <= current.start
                        && current.end <= span.end
                        && literal_data_key(property, scoping, constants).is_some()
                    {
                        key_owner = Some(id);
                    }
                    break;
                }
                AstKind::CallExpression(_)
                | AstKind::NewExpression(_)
                | AstKind::VariableDeclarator(_)
                | AstKind::Function(_)
                | AstKind::ArrowFunctionExpression(_) => break,
                _ => {}
            }
        }
        let mut dispatch_member = false;
        let mut inside_array = false;
        let mut accepted = false;
        for id in semantic.nodes().ancestor_ids(reference.node_id()) {
            budget.consume(1)?;
            let kind = semantic.nodes().kind(id);
            if let Some(owner) = key_owner {
                if owner == id {
                    current = kind.span();
                    key_owner = None;
                }
                continue;
            }
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
pub(super) fn instantiate<'a, 's>(
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
    let all_locals = wrapper.symbols().collect::<BTreeSet<_>>();
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

pub(super) fn append_local_witnesses(
    wrapper: &Wrapper<'_>,
    witnesses: &mut Vec<ApiBindingWitness>,
) {
    witnesses.extend(wrapper.locals.iter().map(|local| ApiBindingWitness {
        kind: "wrapper_local_binding".into(),
        start: local.span.start,
        end: local.span.end,
    }));
}
