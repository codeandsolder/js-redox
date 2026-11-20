//! Materialized value origins and bounded positional argument construction.
use super::super::{
    callables::{ForwardedValue, PositionalArguments},
    *,
};
use jsvm_safe_core::eval_static_primitive_with_resolver;
use oxc_ast::ast::{Argument, ArrayExpression, ArrayExpressionElement};
use std::{collections::BTreeMap, rc::Rc};

pub(super) type ArgumentList<'a> = PositionalArguments<'a, 'a>;
pub(super) type ValueFrame<'a> = BTreeMap<SymbolId, ForwardedValue<'a, 'a>>;

/// Carry value origins rather than copying syntax into a different scope.
/// Materialized arrays share their positional contents; spreading a known
/// array or rest value consumes those positions, while apply uses indexed
/// contents without depending on Array.prototype[Symbol.iterator].
pub(super) struct ValueBuilder<'s, 'a> {
    pub(super) frame: Option<ValueFrame<'a>>,
    scoping: &'s Scoping,
    constants: &'s ProvenConstantEnvironment,
    limit: usize,
    pub(super) budget: &'s WorkBudget,
    pub(super) used_iterator: bool,
}

impl<'s, 'a> ValueBuilder<'s, 'a> {
    pub(super) fn new(
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

    /// Resolve primitive facts against the original invocation environment.
    /// Captured expressions retain the source context of their own origin.
    pub(super) fn primitive(&self, expr: &Expression<'_>) -> Option<StaticPrimitiveValue> {
        eval_static_primitive_with_resolver(expr, &|id| {
            let reference = self.scoping.get_reference(id.reference_id.get()?);
            if !reference.is_read()
                || reference.is_write()
                || reference.flags().is_member_write_target()
            {
                return None;
            }
            if let Some(value) = reference
                .symbol_id()
                .and_then(|symbol| self.frame.as_ref()?.get(&symbol))
            {
                return value.primitive(self.scoping, self.constants);
            }
            self.constants
                .resolve_identifier(id, self.scoping)
                .or_else(|| {
                    (reference.symbol_id().is_none() && id.name == "undefined")
                        .then_some(StaticPrimitiveValue::Undefined)
                })
        })
    }

    pub(super) fn data_key(&self, property: &oxc_ast::ast::ObjectProperty<'_>) -> Option<String> {
        literal_data_key(property, |expr| self.primitive(expr))
    }

    pub(super) fn expression(
        &mut self,
        expr: &'a Expression<'a>,
    ) -> Result<ForwardedValue<'a, 'a>> {
        self.budget.consume(1)?;
        if let Some(frame) = &self.frame {
            if let Some(value) =
                expression_symbol(self.scoping, expr).and_then(|symbol| frame.get(&symbol))
            {
                return Ok(value.clone());
            }
        }
        if let Some(value) = self.primitive(expr) {
            if let StaticPrimitiveValue::String(text) = &value {
                self.budget.consume(text.len() as u64)?;
            }
            return Ok(ForwardedValue::Primitive {
                value: Rc::new(value),
                span: expr.span(),
            });
        }
        if self.frame.is_some() {
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
                    let Some(key) = self.data_key(property) else {
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

    pub(super) fn extend(
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

    pub(super) fn call(&mut self, args: &'a [Argument<'a>]) -> Result<ArgumentList<'a>> {
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

pub(super) fn known_array(value: &ForwardedValue<'_, '_>) -> bool {
    match value {
        ForwardedValue::Array { .. } => true,
        ForwardedValue::Expression(expr) => {
            matches!(unparenthesized(expr), Expression::ArrayExpression(_))
        }
        _ => false,
    }
}
