//! Proof-domain constant evaluation for the safe deobfuscator.
//!
//! ECMAScript coercion primitives are delegated to `oxc_ecmascript`; the AST
//! subset remains deliberately narrower than Oxc's full constant evaluator.
//! Knowing an expression's result is not sufficient proof that replacing the
//! expression preserves its effects (for example `void sideEffect()`).  Callers
//! may resolve identifiers only after independently proving their bindings safe.

use oxc_ast::ast::{
    ArrayExpressionElement, Expression, IdentifierReference, LogicalExpression, StringLiteral,
    TemplateElement, UnaryExpression,
};
use oxc_ecmascript::{StringToNumber, ToInt32, ToUint32};
use oxc_syntax::number::ToJsString;

/// Convert an Oxc JavaScript string literal into Rust UTF-8.
///
/// Oxc preserves lone UTF-16 surrogates in `JSStr`; js-redox's proof domain
/// uses Rust `String`, so those values are deliberately not approximated.
#[must_use]
pub fn string_literal_value(literal: &StringLiteral<'_>) -> Option<String> {
    literal.value.as_str().map(str::to_owned)
}

/// Recover a template quasi using the same semantics as the pre-`JSStr` AST:
/// prefer cooked text, and fall back to raw source spelling when cooked is absent.
/// A cooked value containing a lone surrogate is not representable in the Rust
/// string proof domain and therefore fails closed.
#[must_use]
pub fn template_element_value(quasi: &TemplateElement<'_>) -> Option<String> {
    match quasi.value.cooked.as_ref() {
        Some(cooked) => (*cooked).as_str().map(str::to_owned),
        None => Some(quasi.value.raw.as_str().to_owned()),
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    String(String),
    Number(f64),
    Bool(bool),
    Null,
    Undefined,
}

impl Value {
    pub fn truthy(&self) -> bool {
        match self {
            Self::String(s) => !s.is_empty(),
            Self::Number(n) => *n != 0.0 && !n.is_nan(),
            Self::Bool(v) => *v,
            Self::Null | Self::Undefined => false,
        }
    }

    pub fn number(&self) -> Option<f64> {
        match self {
            Self::Number(n) => Some(*n),
            Self::Bool(v) => Some(if *v { 1.0 } else { 0.0 }),
            Self::Null => Some(0.0),
            Self::Undefined => Some(f64::NAN),
            Self::String(s) => Some(s.as_str().string_to_number()),
        }
    }

    pub fn js_string(&self) -> Option<String> {
        Some(match self {
            Self::String(s) => s.clone(),
            Self::Number(n) => n.to_js_string(),
            Self::Bool(v) => (if *v { "true" } else { "false" }).to_string(),
            Self::Null => "null".into(),
            Self::Undefined => "undefined".into(),
        })
    }

    pub fn render(&self) -> Option<String> {
        match self {
            Self::String(s) => serde_json::to_string(s).ok(),
            Self::Number(n) if n.is_finite() => Some(render_number(*n)),
            Self::Bool(v) => Some(v.to_string()),
            Self::Null => Some("null".into()),
            Self::Undefined => Some("void 0".into()),
            Self::Number(_) => None,
        }
    }
}

fn render_number(n: f64) -> String {
    // Number#toString canonicalizes -0 to "0", while source replacement must
    // retain the observable signed-zero value.
    if n == 0.0 && n.is_sign_negative() {
        "-0".into()
    } else {
        n.to_js_string()
    }
}

pub fn same_value(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::String(a), Value::String(b)) => a == b,
        // JavaScript Strict Equality: NaN is never equal to itself, while
        // +0 and -0 compare equal.
        (Value::Number(a), Value::Number(b)) => a == b,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Null, Value::Null) | (Value::Undefined, Value::Undefined) => true,
        _ => false,
    }
}

pub fn same_values(a: &[Value], b: &[Value]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(left, right)| same_value(left, right))
}

pub fn render_value_array(values: &[Value]) -> Option<String> {
    let rendered = values
        .iter()
        .map(Value::render)
        .collect::<Option<Vec<_>>>()?;
    Some(format!("[{}]", rendered.join(", ")))
}

pub fn eval(expr: &Expression<'_>) -> Option<Value> {
    eval_with_resolver(expr, &|_| None)
}

pub fn known_bool(expr: &Expression<'_>) -> Option<bool> {
    known_bool_with_resolver(expr, &|_| None)
}

pub fn eval_with_resolver<'a, F>(expr: &Expression<'a>, resolve: &F) -> Option<Value>
where
    F: Fn(&IdentifierReference<'a>) -> Option<Value>,
{
    match expr {
        Expression::Identifier(id) => resolve(id),
        Expression::StringLiteral(v) => string_literal_value(v).map(Value::String),
        Expression::NumericLiteral(v) => Some(Value::Number(v.value)),
        Expression::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        Expression::NullLiteral(_) => Some(Value::Null),
        Expression::TemplateLiteral(v) if v.expressions.is_empty() => v
            .quasis
            .first()
            .and_then(template_element_value)
            .map(Value::String),
        Expression::ParenthesizedExpression(v) => eval_with_resolver(&v.expression, resolve),
        Expression::UnaryExpression(v) => eval_unary_with_resolver(v, resolve),
        Expression::BinaryExpression(v) => eval_binary(
            v.operator.as_str(),
            eval_with_resolver(&v.left, resolve)?,
            eval_with_resolver(&v.right, resolve)?,
        ),
        Expression::LogicalExpression(v) => eval_logical_with_resolver(v, resolve),
        Expression::ConditionalExpression(v) => {
            let test = known_bool_with_resolver(&v.test, resolve)?;
            eval_with_resolver(if test { &v.consequent } else { &v.alternate }, resolve)
        }
        _ => None,
    }
}

/// A literal expression whose complete evaluation cannot access bindings,
/// invoke user code, or throw. Fresh array/RegExp/object allocations have
/// no externally visible effect until their values escape.
fn inert_literal_value(expr: &Expression<'_>) -> bool {
    match expr {
        Expression::StringLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::BigIntLiteral(_)
        | Expression::RegExpLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::BooleanLiteral(_) => true,
        Expression::TemplateLiteral(template) => template.expressions.is_empty(),
        Expression::ArrayExpression(array) => array.elements.iter().all(inert_array_element),
        Expression::ObjectExpression(object) => object.properties.is_empty(),
        Expression::ParenthesizedExpression(paren) => inert_literal_value(&paren.expression),
        Expression::UnaryExpression(unary)
            if matches!(unary.operator.as_str(), "!" | "void" | "typeof") =>
        {
            inert_literal_value(&unary.argument)
        }
        Expression::UnaryExpression(unary)
            if matches!(unary.operator.as_str(), "+" | "-" | "~") =>
        {
            inert_literal_value(&unary.argument) && eval(&unary.argument).is_some()
        }
        Expression::BinaryExpression(binary) => {
            inert_literal_value(&binary.left)
                && inert_literal_value(&binary.right)
                && eval(expr).is_some()
        }
        Expression::LogicalExpression(logical) => {
            inert_literal_value(&logical.left) && inert_literal_value(&logical.right)
        }
        Expression::ConditionalExpression(conditional) => {
            inert_literal_value(&conditional.test)
                && inert_literal_value(&conditional.consequent)
                && inert_literal_value(&conditional.alternate)
        }
        Expression::SequenceExpression(sequence) => {
            sequence.expressions.iter().all(inert_literal_value)
        }
        _ => false,
    }
}

fn inert_array_element(element: &ArrayExpressionElement<'_>) -> bool {
    match element {
        ArrayExpressionElement::Elision(_) => true,
        ArrayExpressionElement::SpreadElement(_) => false,
        _ => element.as_expression().is_some_and(inert_literal_value),
    }
}

pub fn known_bool_with_resolver<'a, F>(expr: &Expression<'a>, resolve: &F) -> Option<bool>
where
    F: Fn(&IdentifierReference<'a>) -> Option<Value>,
{
    if let Some(v) = eval_with_resolver(expr, resolve) {
        return Some(v.truthy());
    }
    match expr {
        Expression::ArrayExpression(v) if v.elements.iter().all(inert_array_element) => Some(true),
        Expression::ObjectExpression(v) if v.properties.is_empty() => Some(true),
        Expression::ParenthesizedExpression(v) => known_bool_with_resolver(&v.expression, resolve),
        _ => None,
    }
}

pub fn eval_unary(v: &UnaryExpression<'_>) -> Option<Value> {
    eval_unary_with_resolver(v, &|_| None)
}

pub(crate) fn eval_unary_value(op: &str, value: Value) -> Option<Value> {
    match op {
        "!" => Some(Value::Bool(!value.truthy())),
        "+" => value.number().map(Value::Number),
        "-" => value.number().map(|x| Value::Number(-x)),
        "~" => value
            .number()
            .map(|x| Value::Number(f64::from(!js_to_int32(x)))),
        "void" => Some(Value::Undefined),
        "typeof" => Some(Value::String(
            match value {
                Value::String(_) => "string",
                Value::Number(_) => "number",
                Value::Bool(_) => "boolean",
                Value::Null => "object",
                Value::Undefined => "undefined",
            }
            .into(),
        )),
        _ => None,
    }
}

fn eval_unary_with_resolver<'a, F>(v: &UnaryExpression<'a>, resolve: &F) -> Option<Value>
where
    F: Fn(&IdentifierReference<'a>) -> Option<Value>,
{
    let op = v.operator.as_str();
    if op == "!" {
        return known_bool_with_resolver(&v.argument, resolve).map(|x| Value::Bool(!x));
    }
    let value = eval_with_resolver(&v.argument, resolve)?;
    eval_unary_value(op, value)
}

#[inline]
pub fn js_to_uint32(n: f64) -> u32 {
    n.to_uint_32()
}

#[inline]
pub fn js_to_int32(n: f64) -> i32 {
    n.to_int_32()
}

/// ECMAScript Abstract Equality for the complete primitive domain modeled by
/// this evaluator. Object, Symbol and BigInt equality is deliberately handled
/// outside this domain, never guessed from source text.
fn abstract_primitive_equal(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::Null | Value::Undefined, Value::Null | Value::Undefined) => true,
        (Value::Bool(value), other) => {
            abstract_primitive_equal(&Value::Number(if *value { 1.0 } else { 0.0 }), other)
        }
        (other, Value::Bool(value)) => {
            abstract_primitive_equal(other, &Value::Number(if *value { 1.0 } else { 0.0 }))
        }
        (Value::String(text), Value::Number(number))
        | (Value::Number(number), Value::String(text)) => {
            text.as_str().string_to_number() == *number
        }
        (Value::Null | Value::Undefined, _) | (_, Value::Null | Value::Undefined) => false,
        _ => same_value(left, right),
    }
}

pub fn eval_binary(op: &str, left: Value, right: Value) -> Option<Value> {
    match op {
        "+" => {
            if matches!(left, Value::String(_)) || matches!(right, Value::String(_)) {
                Some(Value::String(format!(
                    "{}{}",
                    left.js_string()?,
                    right.js_string()?
                )))
            } else {
                Some(Value::Number(left.number()? + right.number()?))
            }
        }
        "-" => Some(Value::Number(left.number()? - right.number()?)),
        "*" => Some(Value::Number(left.number()? * right.number()?)),
        "/" => Some(Value::Number(left.number()? / right.number()?)),
        "%" => Some(Value::Number(left.number()? % right.number()?)),
        "**" => Some(Value::Number(left.number()?.powf(right.number()?))),
        "<<" => {
            let shift = js_to_uint32(right.number()?) & 31;
            Some(Value::Number(f64::from(
                js_to_int32(left.number()?).wrapping_shl(shift),
            )))
        }
        ">>" => {
            let shift = js_to_uint32(right.number()?) & 31;
            Some(Value::Number(f64::from(
                js_to_int32(left.number()?) >> shift,
            )))
        }
        ">>>" => {
            let shift = js_to_uint32(right.number()?) & 31;
            Some(Value::Number(f64::from(
                js_to_uint32(left.number()?) >> shift,
            )))
        }
        "|" => Some(Value::Number(f64::from(
            js_to_int32(left.number()?) | js_to_int32(right.number()?),
        ))),
        "^" => Some(Value::Number(f64::from(
            js_to_int32(left.number()?) ^ js_to_int32(right.number()?),
        ))),
        "&" => Some(Value::Number(f64::from(
            js_to_int32(left.number()?) & js_to_int32(right.number()?),
        ))),
        "===" => Some(Value::Bool(same_value(&left, &right))),
        "!==" => Some(Value::Bool(!same_value(&left, &right))),
        "==" | "!=" => {
            let equal = abstract_primitive_equal(&left, &right);
            Some(Value::Bool(if op == "==" { equal } else { !equal }))
        }
        "<" | "<=" | ">" | ">=" => {
            let result = if let (Value::String(a), Value::String(b)) = (&left, &right) {
                match op {
                    "<" => a < b,
                    "<=" => a <= b,
                    ">" => a > b,
                    ">=" => a >= b,
                    _ => unreachable!(),
                }
            } else {
                let a = left.number()?;
                let b = right.number()?;
                match op {
                    "<" => a < b,
                    "<=" => a <= b,
                    ">" => a > b,
                    ">=" => a >= b,
                    _ => unreachable!(),
                }
            };
            Some(Value::Bool(result))
        }
        _ => None,
    }
}

pub fn eval_logical(v: &LogicalExpression<'_>) -> Option<Value> {
    eval_logical_with_resolver(v, &|_| None)
}

pub(crate) enum LogicalStep {
    Value(Value),
    EvaluateRight,
}

pub(crate) fn eval_logical_left(op: &str, left: Value) -> Option<LogicalStep> {
    match op {
        "&&" if left.truthy() => Some(LogicalStep::EvaluateRight),
        "&&" => Some(LogicalStep::Value(left)),
        "||" if left.truthy() => Some(LogicalStep::Value(left)),
        "||" => Some(LogicalStep::EvaluateRight),
        "??" if matches!(left, Value::Null | Value::Undefined) => Some(LogicalStep::EvaluateRight),
        "??" => Some(LogicalStep::Value(left)),
        _ => None,
    }
}

fn eval_logical_with_resolver<'a, F>(v: &LogicalExpression<'a>, resolve: &F) -> Option<Value>
where
    F: Fn(&IdentifierReference<'a>) -> Option<Value>,
{
    let left = eval_with_resolver(&v.left, resolve)?;
    match eval_logical_left(v.operator.as_str(), left)? {
        LogicalStep::Value(value) => Some(value),
        LogicalStep::EvaluateRight => eval_with_resolver(&v.right, resolve),
    }
}
