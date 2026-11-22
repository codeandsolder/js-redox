//! Proof-domain constant evaluation for the safe deobfuscator.
//!
//! ECMAScript coercion primitives are delegated to `oxc_ecmascript`; the AST
//! subset remains deliberately narrower than Oxc's full constant evaluator.
//! Knowing an expression's result is not sufficient proof that replacing the
//! expression preserves its effects (for example `void sideEffect()`).  Callers
//! may resolve identifier and member reads only with independent proofs of
//! binding identity, initialization and side-effect-free property access.

use oxc_ast::ast::{
    ArrayExpressionElement, Expression, LogicalExpression, PropertyKey, StringLiteral,
    TemplateElement, UnaryExpression,
};
use oxc_ecmascript::{StringToNumber, ToInt32, ToUint32};
use oxc_syntax::number::ToJsString;

/// A JavaScript array index is a canonical decimal property key in
/// [0, 2^32 - 2]. Computed members use `ToPropertyKey`, *not* `ToNumber`:
/// `arr[true]` reads `"true"`, not index 1, and `arr["01"]` is not `arr[1]`.
/// Signed numeric zero becomes "0"; the string "-0" remains distinct.
#[must_use = "Use the returned index only when the property key is canonical"]
pub fn canonical_array_index(value: &Value) -> Option<u32> {
    canonical_array_index_key(&value.js_string())
}

pub fn canonical_array_index_key(key: &str) -> Option<u32> {
    let index = key.parse::<u32>().ok()?;
    (index != u32::MAX && index.to_string() == key).then_some(index)
}

/// Convert an Oxc JavaScript string literal into Rust UTF-8.
///
/// Oxc preserves lone UTF-16 surrogates in `JSStr`; js-redox's proof domain
/// uses Rust `String`, so those values are deliberately not approximated.
#[must_use = "Use the returned string only when it can be represented losslessly"]
pub fn string_literal_value(literal: &StringLiteral<'_>) -> Option<String> {
    literal.value.as_str().map(str::to_owned)
}

/// Exact `ToPropertyKey` for noncomputed object-literal keys. Oxc's
/// `StaticPropertyName` uses Rust float display for numeric literals, which
/// disagrees with JavaScript at exponential magnitudes and signed zero.
pub fn literal_property_key(key: &PropertyKey<'_>) -> Option<String> {
    match key {
        PropertyKey::StaticIdentifier(identifier) => Some(identifier.name.to_string()),
        PropertyKey::StringLiteral(literal) => string_literal_value(literal),
        PropertyKey::NumericLiteral(literal) => Some(literal.value.to_js_string()),
        PropertyKey::BigIntLiteral(literal) => Some(literal.value.to_string()),
        _ => None,
    }
}

/// Evaluate a computed property key only when its complete primitive
/// evaluation is proven. `BigInt` literals are exact even though `BigInt`
/// arithmetic is not in the shared primitive evaluator's domain.
#[must_use = "Use the property key only when its value is proven"]
pub fn exact_computed_property_key(
    expression: &Expression<'_>,
    primitive: impl FnOnce(&Expression<'_>) -> Option<Value>,
) -> Option<String> {
    let expression = expression.without_parentheses();
    if let Expression::BigIntLiteral(literal) = expression {
        return Some(literal.value.to_string());
    }
    Some(primitive(expression)?.js_string())
}

/// Canonical ECMAScript property identity, with an explicit computed-key
/// evaluator.
///
/// In particular, never treat a computed `RegExp` or object literal
/// as a statically known name: `ToPrimitive` can invoke user code.
#[must_use = "Use the property key only when its value is proven"]
pub fn exact_property_key(
    key: &PropertyKey<'_>,
    computed: bool,
    primitive: impl FnOnce(&Expression<'_>) -> Option<Value>,
) -> Option<String> {
    if computed {
        exact_computed_property_key(key.as_expression()?, primitive)
    } else {
        literal_property_key(key)
    }
}

/// The special object initializer colon-form is a prototype setter, not an
/// own property. Computed, shorthand, method and accessor forms are ordinary
/// definitions, even if the key has the same text.
#[must_use = "Check whether the property has special prototype setter semantics"]
pub fn is_prototype_setter(property: &oxc_ast::ast::ObjectProperty<'_>, name: &str) -> bool {
    name == "__proto__"
        && property.kind == oxc_ast::ast::PropertyKind::Init
        && !property.computed
        && !property.method
        && !property.shorthand
}

/// Recover the cooked value of a template quasi.
///
/// A tagged template with an invalid escape has an undefined cooked slot,
/// not its raw spelling. A cooked lone surrogate cannot be represented in
/// the UTF-8 string proof domain either.
#[must_use = "Use the returned template value only when decoding succeeds"]
pub fn template_element_value(quasi: &TemplateElement<'_>) -> Option<String> {
    quasi.value.cooked.as_ref()?.as_str().map(str::to_owned)
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
    #[must_use = "Use the returned ECMAScript truthiness result"]
    pub fn truthy(&self) -> bool {
        match self {
            Self::String(s) => !s.is_empty(),
            Self::Number(n) => *n != 0.0 && !n.is_nan(),
            Self::Bool(v) => *v,
            Self::Null | Self::Undefined => false,
        }
    }

    #[must_use = "Use the converted ECMAScript number, including NaN"]
    pub fn number(&self) -> f64 {
        match self {
            Self::Number(n) => *n,
            Self::Bool(v) => f64::from(u8::from(*v)),
            Self::Null => 0.0,
            Self::Undefined => f64::NAN,
            Self::String(s) => s.as_str().string_to_number(),
        }
    }

    #[must_use = "Use the converted ECMAScript string"]
    pub fn js_string(&self) -> String {
        match self {
            Self::String(s) => s.clone(),
            Self::Number(n) => n.to_js_string(),
            Self::Bool(v) => (if *v { "true" } else { "false" }).to_string(),
            Self::Null => "null".into(),
            Self::Undefined => "undefined".into(),
        }
    }

    #[must_use = "Use the returned rendering only when the value is representable"]
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

    /// Render a primitive for substitution into an arbitrary expression.
    /// A negative number and undefined are unary expressions, not atoms:
    /// substituting them without grouping can change a surrounding member,
    /// call, optional chain or exponentiation.
    #[must_use = "Use the returned rendering only when the value is representable as an expression"]
    pub fn render_expression(&self) -> Option<String> {
        let text = self.render()?;
        if matches!(self, Self::Undefined)
            || matches!(self, Self::Number(value) if value.is_sign_negative())
        {
            Some(format!("({text})"))
        } else {
            Some(text)
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

/// JavaScript Strict Equality (the `===` operator), not proof-fact identity.
#[must_use = "Use the JavaScript strict equality result"]
pub fn strict_primitive_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::String(a), Value::String(b)) => a == b,
        // JavaScript Strict Equality: NaN is never equal to itself, while
        // +0 and -0 compare equal.
        (Value::Number(a), Value::Number(b)) => crate::numeric::js_number_equal(*a, *b),
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Null, Value::Null) | (Value::Undefined, Value::Undefined) => true,
        _ => false,
    }
}

/// Compare two proof facts without conflating opposite signed zeros or
/// distinct floating-point encodings. This is intentionally stricter than
/// ECMAScript `SameValue`, which treats all NaNs as equal.
#[must_use = "Only merge primitive facts when their represented values are identical"]
pub fn identical_primitive_value(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::Number(left), Value::Number(right)) => left.to_bits() == right.to_bits(),
        _ => strict_primitive_equal(left, right),
    }
}

#[must_use = "Only merge primitive sequences when their represented values are identical"]
pub fn identical_primitive_values(a: &[Value], b: &[Value]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b)
            .all(|(left, right)| identical_primitive_value(left, right))
}

pub fn render_value_array(values: &[Value]) -> Option<String> {
    let rendered = values
        .iter()
        .map(Value::render)
        .collect::<Option<Vec<_>>>()?;
    Some(format!("[{}]", rendered.join(", ")))
}

#[must_use = "Use the returned value only for supported constant expressions"]
pub fn eval(expr: &Expression<'_>) -> Option<Value> {
    eval_with_resolver(expr, &|_| None)
}

pub fn known_bool(expr: &Expression<'_>) -> Option<bool> {
    known_bool_with_resolver(expr, &|_| None)
}

pub fn eval_with_resolver<'a, F>(expr: &Expression<'a>, resolve: &F) -> Option<Value>
where
    F: Fn(&Expression<'a>) -> Option<Value>,
{
    match expr {
        Expression::Identifier(_)
        | Expression::StaticMemberExpression(_)
        | Expression::ComputedMemberExpression(_) => resolve(expr),
        Expression::StringLiteral(v) => string_literal_value(v).map(Value::String),
        Expression::NumericLiteral(v) => Some(Value::Number(v.value)),
        Expression::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        Expression::NullLiteral(_) => Some(Value::Null),
        Expression::TemplateLiteral(v) => {
            let mut quasis = v.quasis.iter();
            let mut text = template_element_value(quasis.next()?)?;
            for expression in &v.expressions {
                text.push_str(&eval_with_resolver(expression, resolve)?.js_string());
                text.push_str(&template_element_value(quasis.next()?)?);
            }
            Some(Value::String(text))
        }
        Expression::ParenthesizedExpression(v) => eval_with_resolver(&v.expression, resolve),
        Expression::UnaryExpression(v) => eval_unary_with_resolver(v, resolve),
        Expression::BinaryExpression(v) => eval_binary(
            v.operator.as_str(),
            &eval_with_resolver(&v.left, resolve)?,
            &eval_with_resolver(&v.right, resolve)?,
        ),
        Expression::LogicalExpression(v) => eval_logical_with_resolver(v, resolve),
        Expression::ConditionalExpression(v) => {
            let test = known_bool_with_resolver(&v.test, resolve)?;
            eval_with_resolver(if test { &v.consequent } else { &v.alternate }, resolve)
        }
        Expression::SequenceExpression(sequence) => {
            let (last, prefixes) = sequence.expressions.split_last()?;
            // The comma operator discards each prefix's value, but every
            // prefix must still complete normally without observable effects.
            // A resolver may only supply independently proven inert reads.
            if prefixes.iter().all(|prefix| {
                inert_literal_value(prefix) || eval_with_resolver(prefix, resolve).is_some()
            }) {
                eval_with_resolver(last, resolve)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Prove a literal expression neither accesses bindings nor invokes user code or throws.
///
/// Proving effects does not require proving the exact returned value, for
/// example for implementation-approximated powers.
#[must_use = "Only discard a literal evaluation when its effects are proven inert"]
pub fn inert_literal_value(expr: &Expression<'_>) -> bool {
    inert_literal_kind(expr).is_some()
}

/// Possible result types of an already proven nonthrowing literal expression.
///
/// A union retains type uncertainty without requiring a constant value.
/// No member of the set implies an effectful coercion is safe.
#[derive(Clone, Copy, PartialEq, Eq)]
struct LiteralTypes(u8);

impl LiteralTypes {
    const NUMBER: Self = Self(1 << 0);
    const STRING: Self = Self(1 << 1);
    const BOOLEAN: Self = Self(1 << 2);
    const NULL: Self = Self(1 << 3);
    const UNDEFINED: Self = Self(1 << 4);
    const BIGINT: Self = Self(1 << 5);
    const OBJECT: Self = Self(1 << 6);
    const FUNCTION: Self = Self(1 << 7);
    const ORDINARY_PRIMITIVE: Self =
        Self(Self::NUMBER.0 | Self::STRING.0 | Self::BOOLEAN.0 | Self::NULL.0 | Self::UNDEFINED.0);
    const OBJECT_TYPEOF: Self = Self(Self::NULL.0 | Self::OBJECT.0);

    const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    const fn subset_of(self, other: Self) -> bool {
        self.0 & !other.0 == 0
    }

    const fn includes(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    const fn typeof_name(self) -> Option<&'static str> {
        if self.subset_of(Self::OBJECT_TYPEOF) {
            return Some("object");
        }
        match self {
            Self::NUMBER => Some("number"),
            Self::STRING => Some("string"),
            Self::BOOLEAN => Some("boolean"),
            Self::UNDEFINED => Some("undefined"),
            Self::BIGINT => Some("bigint"),
            Self::FUNCTION => Some("function"),
            _ => None,
        }
    }

    const fn truthiness(self) -> Option<bool> {
        if self.subset_of(Self::OBJECT.union(Self::FUNCTION)) {
            Some(true)
        } else if self.subset_of(Self::NULL.union(Self::UNDEFINED)) {
            Some(false)
        } else {
            None
        }
    }

    /// Addition of ordinary primitives may concatenate or add numbers.
    fn addition(self, other: Self) -> Self {
        if self == Self::STRING || other == Self::STRING {
            Self::STRING
        } else if self.includes(Self::STRING) || other.includes(Self::STRING) {
            Self::STRING.union(Self::NUMBER)
        } else {
            Self::NUMBER
        }
    }
}

fn inert_literal_kind(expr: &Expression<'_>) -> Option<LiteralTypes> {
    match expr {
        Expression::StringLiteral(_) => Some(LiteralTypes::STRING),
        Expression::NumericLiteral(_) => Some(LiteralTypes::NUMBER),
        Expression::NullLiteral(_) => Some(LiteralTypes::NULL),
        Expression::BooleanLiteral(_) => Some(LiteralTypes::BOOLEAN),
        Expression::BigIntLiteral(_) => Some(LiteralTypes::BIGINT),
        Expression::RegExpLiteral(_) => Some(LiteralTypes::OBJECT),
        // Creating a function does not execute its parameters or body.
        Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_) => {
            Some(LiteralTypes::FUNCTION)
        }
        Expression::TemplateLiteral(template) => template
            .expressions
            .iter()
            .all(|expression| {
                inert_literal_kind(expression).is_some_and(|kind| {
                    kind.subset_of(LiteralTypes::ORDINARY_PRIMITIVE.union(LiteralTypes::BIGINT))
                })
            })
            .then_some(LiteralTypes::STRING),
        Expression::ArrayExpression(array) => array
            .elements
            .iter()
            .all(inert_array_element)
            .then_some(LiteralTypes::OBJECT),
        Expression::ObjectExpression(object) => {
            object.properties.is_empty().then_some(LiteralTypes::OBJECT)
        }
        Expression::ParenthesizedExpression(paren) => inert_literal_kind(&paren.expression),
        Expression::UnaryExpression(unary) => {
            let kind = inert_literal_kind(&unary.argument)?;
            match unary.operator.as_str() {
                "!" => Some(LiteralTypes::BOOLEAN),
                "void" => Some(LiteralTypes::UNDEFINED),
                "typeof" => Some(LiteralTypes::STRING),
                "+" | "-" | "~" if kind.subset_of(LiteralTypes::ORDINARY_PRIMITIVE) => {
                    Some(LiteralTypes::NUMBER)
                }
                _ => None,
            }
        }
        Expression::BinaryExpression(binary) => {
            let left = inert_literal_kind(&binary.left)?;
            let right = inert_literal_kind(&binary.right)?;
            let ordinary = left
                .union(right)
                .subset_of(LiteralTypes::ORDINARY_PRIMITIVE);
            match binary.operator.as_str() {
                "===" | "!==" => Some(LiteralTypes::BOOLEAN),
                // Ordinary primitive coercion cannot invoke user callbacks
                // or cause language-level arithmetic errors.
                "+" if ordinary => Some(left.addition(right)),
                "-" | "*" | "/" | "%" | "**" | "<<" | ">>" | ">>>" | "&" | "|" | "^"
                    if ordinary =>
                {
                    Some(LiteralTypes::NUMBER)
                }
                "==" | "!=" | "<" | "<=" | ">" | ">=" if ordinary => Some(LiteralTypes::BOOLEAN),
                _ => None,
            }
        }
        Expression::LogicalExpression(logical) => {
            let left = inert_literal_kind(&logical.left)?;
            let right = inert_literal_kind(&logical.right)?;
            Some(left.union(right))
        }
        Expression::ConditionalExpression(conditional) => {
            inert_literal_kind(&conditional.test)?;
            let yes = inert_literal_kind(&conditional.consequent)?;
            let no = inert_literal_kind(&conditional.alternate)?;
            Some(yes.union(no))
        }
        Expression::SequenceExpression(sequence) => {
            let mut expressions = sequence.expressions.iter();
            let first = inert_literal_kind(expressions.next()?)?;
            expressions.try_fold(first, |_, expression| inert_literal_kind(expression))
        }
        _ => None,
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
    F: Fn(&Expression<'a>) -> Option<Value>,
{
    if let Some(v) = eval_with_resolver(expr, resolve) {
        return Some(v.truthy());
    }
    inert_literal_kind(expr)?.truthiness()
}

pub fn eval_unary(v: &UnaryExpression<'_>) -> Option<Value> {
    eval_unary_with_resolver(v, &|_| None)
}

pub fn eval_unary_value(op: &str, value: &Value) -> Option<Value> {
    match op {
        "!" => Some(Value::Bool(!value.truthy())),
        "+" => Some(Value::Number(value.number())),
        "-" => Some(Value::Number(-value.number())),
        "~" => Some(Value::Number(f64::from(!js_to_int32(value.number())))),
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
    F: Fn(&Expression<'a>) -> Option<Value>,
{
    let op = v.operator.as_str();
    if op == "!" {
        return known_bool_with_resolver(&v.argument, resolve).map(|x| Value::Bool(!x));
    }
    if matches!(op, "void" | "typeof") {
        if let Some(kind) = inert_literal_kind(&v.argument) {
            if op == "void" {
                return Some(Value::Undefined);
            }
            if let Some(name) = kind.typeof_name() {
                return Some(Value::String(name.into()));
            }
        }
    }
    let value = eval_with_resolver(&v.argument, resolve)?;
    eval_unary_value(op, &value)
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
/// this evaluator. Object, Symbol and `BigInt` equality is deliberately handled
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
            crate::numeric::js_number_equal(text.as_str().string_to_number(), *number)
        }
        (Value::Null | Value::Undefined, _) | (_, Value::Null | Value::Undefined) => false,
        _ => strict_primitive_equal(left, right),
    }
}

pub fn eval_binary(op: &str, left: &Value, right: &Value) -> Option<Value> {
    match op {
        "+" => {
            if matches!(left, Value::String(_)) || matches!(right, Value::String(_)) {
                Some(Value::String(format!(
                    "{}{}",
                    left.js_string(),
                    right.js_string()
                )))
            } else {
                Some(Value::Number(left.number() + right.number()))
            }
        }
        "-" => Some(Value::Number(left.number() - right.number())),
        "*" => Some(Value::Number(left.number() * right.number())),
        "/" => Some(Value::Number(left.number() / right.number())),
        "%" => Some(Value::Number(left.number() % right.number())),
        "**" => {
            crate::numeric::js_number_exponentiate(left.number(), right.number()).map(Value::Number)
        }
        "<<" => {
            let shift = js_to_uint32(right.number()) & 31;
            Some(Value::Number(f64::from(
                js_to_int32(left.number()).wrapping_shl(shift),
            )))
        }
        ">>" => {
            let shift = js_to_uint32(right.number()) & 31;
            Some(Value::Number(f64::from(
                js_to_int32(left.number()) >> shift,
            )))
        }
        ">>>" => {
            let shift = js_to_uint32(right.number()) & 31;
            Some(Value::Number(f64::from(
                js_to_uint32(left.number()) >> shift,
            )))
        }
        "|" => Some(Value::Number(f64::from(
            js_to_int32(left.number()) | js_to_int32(right.number()),
        ))),
        "^" => Some(Value::Number(f64::from(
            js_to_int32(left.number()) ^ js_to_int32(right.number()),
        ))),
        "&" => Some(Value::Number(f64::from(
            js_to_int32(left.number()) & js_to_int32(right.number()),
        ))),
        "===" => Some(Value::Bool(strict_primitive_equal(left, right))),
        "!==" => Some(Value::Bool(!strict_primitive_equal(left, right))),
        "==" | "!=" => {
            let equal = abstract_primitive_equal(left, right);
            Some(Value::Bool(if op == "==" { equal } else { !equal }))
        }
        "<" | "<=" | ">" | ">=" => {
            let result = if let (Value::String(a), Value::String(b)) = (left, right) {
                // ECMAScript compares UTF-16 code units, not Unicode
                // scalar values or UTF-8 bytes. No temporary allocation is
                // needed; supplementary characters expand to two units.
                let order = a.encode_utf16().cmp(b.encode_utf16());
                match op {
                    "<" => order.is_lt(),
                    "<=" => order.is_le(),
                    ">" => order.is_gt(),
                    ">=" => order.is_ge(),
                    _ => unreachable!(),
                }
            } else {
                let a = left.number();
                let b = right.number();
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

pub enum LogicalStep {
    Value(Value),
    EvaluateRight,
}

pub fn eval_logical_left(op: &str, left: Value) -> Option<LogicalStep> {
    match op {
        "&&" | "||" | "??" => {
            let evaluate_right = match op {
                "&&" => left.truthy(),
                "||" => !left.truthy(),
                "??" => matches!(left, Value::Null | Value::Undefined),
                _ => unreachable!(),
            };
            Some(if evaluate_right {
                LogicalStep::EvaluateRight
            } else {
                LogicalStep::Value(left)
            })
        }
        _ => None,
    }
}

fn eval_logical_with_resolver<'a, F>(v: &LogicalExpression<'a>, resolve: &F) -> Option<Value>
where
    F: Fn(&Expression<'a>) -> Option<Value>,
{
    let left = eval_with_resolver(&v.left, resolve)?;
    match eval_logical_left(v.operator.as_str(), left)? {
        LogicalStep::Value(value) => Some(value),
        LogicalStep::EvaluateRight => eval_with_resolver(&v.right, resolve),
    }
}

#[cfg(test)]
mod tests {
    use super::{eval_binary, Value};

    #[test]
    fn exact_property_keys_do_not_confuse_literal_names_and_computed_coercion() {
        use oxc_allocator::Allocator;
        use oxc_ast::ast::{Expression, ObjectPropertyKind, Statement};
        use oxc_span::SourceType;
        let source = r#"({
            1e21:1, 1e-7:2, 0x10n:3, [(-0)]:4, [(0x10n)]:5,
            ["a"+"b"]:6, [true]:7, [null]:8, [void 0]:9,
            [/x/]:10, [{}]:11, ["\uD800"]:12, __proto__:13,
            ["__proto__"]:14, __proto__(){}, get __proto__(){}
        });"#;
        let allocator = Allocator::default();
        let program = crate::parse_as(&allocator, source, SourceType::cjs())
            .unwrap_or_else(|| unreachable!("literal property fixture"));
        let [Statement::ExpressionStatement(statement)] = program.body.as_slice() else {
            unreachable!("one expression");
        };
        let Expression::ObjectExpression(object) = statement.expression.without_parentheses()
        else {
            unreachable!("object literal");
        };
        let names = object
            .properties
            .iter()
            .map(|item| {
                let ObjectPropertyKind::ObjectProperty(property) = item else {
                    unreachable!("ordinary property");
                };
                let name = super::exact_property_key(&property.key, property.computed, super::eval);
                let prototype = name
                    .as_deref()
                    .is_some_and(|name| super::is_prototype_setter(property, name));
                (name, prototype)
            })
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            [
                (Some("1e+21".into()), false),
                (Some("1e-7".into()), false),
                (Some("16".into()), false),
                (Some("0".into()), false),
                (Some("16".into()), false),
                (Some("ab".into()), false),
                (Some("true".into()), false),
                (Some("null".into()), false),
                (Some("undefined".into()), false),
                (None, false),
                (None, false),
                (None, false),
                (Some("__proto__".into()), true),
                (Some("__proto__".into()), false),
                (Some("__proto__".into()), false),
                (Some("__proto__".into()), false),
            ]
        );
    }

    #[test]
    fn literal_effect_proof_is_independent_of_exact_value() {
        use oxc_allocator::Allocator;
        use oxc_ast::ast::Statement;
        use oxc_span::SourceType;

        for (expression, inert) in [
            ("2 ** 1.5", true),
            ("(2 ** 1.5) + (3 ** 2.5)", true),
            ("+(2 ** 1.5)", true),
            ("(2 ** 1.5) < 7", true),
            ("(true ? 2 ** 1.5 : 1) * 2", true),
            ("(false || 2 ** 1.5) * 2", true),
            ("([], 2 ** 1.5) | 1", true),
            ("[2 ** 1.5]", true),
            ("void (2 ** 1.5)", true),
            (r"+'\ud800'", true),
            ("[] === {}", true),
            ("1n !== 0", true),
            ("!1n", true),
            ("`value=${2 ** 1.5}`", true),
            ("1n / 0n", false),
            ("2n ** (-1n)", false),
            ("1n + 1", false),
            ("+1n", false),
            ("[] + 1", false),
            ("({}) == 0", false),
            ("1 instanceof 2", false),
            ("'x' in 0", false),
            ("[...[]]", false),
            ("void effect()", false),
            ("`value=${{}}`", false),
            ("(false ? 1 : 2n) * 2", false),
        ] {
            let allocator = Allocator::default();
            let source = format!("({expression});");
            let program = crate::parse_as(&allocator, &source, SourceType::cjs())
                .unwrap_or_else(|| unreachable!("{source}"));
            let [Statement::ExpressionStatement(statement)] = program.body.as_slice() else {
                unreachable!("one expression");
            };
            assert_eq!(
                super::inert_literal_value(&statement.expression),
                inert,
                "{expression}"
            );
            if expression == "2 ** 1.5" {
                assert!(super::eval(&statement.expression).is_none());
            }
        }
    }

    #[test]
    fn literal_type_and_discard_proofs_do_not_need_exact_values() {
        use oxc_allocator::Allocator;
        use oxc_ast::ast::Statement;
        use oxc_span::SourceType;

        for (expression, expected) in [
            ("typeof (2 ** 1.5)", Some(r#""number""#)),
            ("typeof (2 ** 1.5 + 3)", Some(r#""number""#)),
            ("typeof (2 ** 1.5 + 'x')", Some(r#""string""#)),
            ("typeof (2 ** 1.5 < 3)", Some(r#""boolean""#)),
            ("typeof (2 ** 1.5 ? null : {})", Some(r#""object""#)),
            ("typeof (2 ** 1.5 ? 0 : 'x')", None),
            ("typeof ((2 ** 1.5 ? 0 : 'x') + 'y')", Some(r#""string""#)),
            ("typeof (void (2 ** 1.5))", Some(r#""undefined""#)),
            ("typeof (1n)", Some(r#""bigint""#)),
            (r"typeof '\ud800'", Some(r#""string""#)),
            ("typeof /x/", Some(r#""object""#)),
            (
                "typeof (function f(x=effect()){effect()})",
                Some(r#""function""#),
            ),
            ("typeof (()=>effect())", Some(r#""function""#)),
            ("typeof [2 ** 1.5]", Some(r#""object""#)),
            ("typeof ([], 2 ** 1.5)", Some(r#""number""#)),
            ("void (2 ** 1.5)", Some("void 0")),
            ("void (1n)", Some("void 0")),
            ("void `value=${1n}`", Some("void 0")),
            ("void [2 ** 1.5]", Some("void 0")),
            ("!(/x/)", Some("false")),
            ("!(2 ** 1.5 ? [] : function(){})", Some("false")),
            ("!(2 ** 1.5 ? null : void 0)", Some("true")),
            ("void (1n / 0n)", None),
            ("typeof (1n + 1)", None),
            ("void ({} + 1)", None),
            ("typeof [effect()]", None),
            ("void effect()", None),
            ("typeof (class extends effect() {})", None),
            ("typeof (unknown)", None),
            ("void (1, effect())", None),
        ] {
            let allocator = Allocator::default();
            let source = format!("({expression});");
            let program = crate::parse_as(&allocator, &source, SourceType::cjs())
                .unwrap_or_else(|| unreachable!("{source}"));
            let [Statement::ExpressionStatement(statement)] = program.body.as_slice() else {
                unreachable!("one expression");
            };
            let actual = super::eval(&statement.expression).and_then(|value| value.render());
            assert_eq!(actual.as_deref(), expected, "{expression}");
        }
    }

    #[test]
    fn primitive_sequence_requires_normal_inert_prefix_evaluation() {
        use oxc_allocator::Allocator;
        use oxc_ast::ast::Statement;
        use oxc_span::SourceType;

        for (expression, expected) in [
            ("(2 ** 1.5, 3)", Some("3")),
            ("(([], {}), 'result')", Some(r#""result""#)),
            ("(false && effect(), 7)", Some("7")),
            ("((2 ** 1.5, 4) + 1)", Some("5")),
            ("((1n, 2), 4)", Some("4")),
            ("(effect(), 7)", None),
            ("(1n/0n, 7)", None),
            ("(obj.property, 7)", None),
            ("(missing, 7)", None),
            ("([1, ...unknown], 7)", None),
            ("(2 ** 1.5, unknown)", None),
        ] {
            let allocator = Allocator::default();
            let source = format!("({expression});");
            let program = crate::parse_as(&allocator, &source, SourceType::cjs())
                .unwrap_or_else(|| unreachable!("{source}"));
            let [Statement::ExpressionStatement(statement)] = program.body.as_slice() else {
                unreachable!("one expression");
            };
            let actual = super::eval(&statement.expression).and_then(|value| value.render());
            assert_eq!(actual.as_deref(), expected, "{expression}");
        }
    }

    #[test]
    fn invalid_tagged_escape_is_not_the_raw_template_value() {
        use oxc_allocator::Allocator;
        use oxc_ast::ast::{Expression, Statement};
        use oxc_span::SourceType;

        let allocator = Allocator::default();
        let program = crate::parse_as(
            &allocator,
            r"tag`\xZ`; tag`\n`; tag`\ud800`;",
            SourceType::cjs(),
        )
        .unwrap_or_else(|| unreachable!("valid tagged templates"));
        let values = program
            .body
            .iter()
            .map(|statement| {
                let Statement::ExpressionStatement(statement) = statement else {
                    unreachable!("expression statement");
                };
                let Expression::TaggedTemplateExpression(tagged) = &statement.expression else {
                    unreachable!("tagged template");
                };
                let quasi = tagged
                    .quasi
                    .quasis
                    .first()
                    .unwrap_or_else(|| unreachable!("quasi"));
                super::template_element_value(quasi)
            })
            .collect::<Vec<_>>();
        assert_eq!(values, [None, Some("\n".into()), None]);
    }

    #[test]
    fn relational_string_comparison_uses_utf16_code_units() {
        for (left, right, lt, eq) in [
            ("a", "ab", true, false),
            ("a", "a", false, true),
            ("😀", "\u{e000}", true, false),
            ("\u{10000}", "\u{ffff}", true, false),
            ("\u{10ffff}", "\u{10000}", false, false),
            ("\u{e000}", "😀", false, false),
        ] {
            let left = Value::String(left.into());
            let right = Value::String(right.into());
            for (operator, expected) in
                [("<", lt), ("<=", lt || eq), (">", !lt && !eq), (">=", !lt)]
            {
                assert!(
                    matches!(eval_binary(operator, &left, &right), Some(Value::Bool(actual)) if actual == expected),
                    "{left:?} {operator} {right:?}"
                );
            }
        }
    }
}

#[cfg(test)]
mod primitive_equality_tests {
    use super::{
        identical_primitive_value, identical_primitive_values, strict_primitive_equal, Value,
    };

    #[test]
    fn strict_equality_and_fact_identity_differ_for_signed_zero_and_nan() {
        let positive_zero = Value::Number(0.0);
        let negative_zero = Value::Number(-0.0);
        let nan = Value::Number(f64::from_bits(0x7ff8_0000_0000_0001));
        let other_nan = Value::Number(f64::from_bits(0x7ff8_0000_0000_0002));

        assert!(strict_primitive_equal(&positive_zero, &negative_zero));
        assert!(!identical_primitive_value(&positive_zero, &negative_zero));
        assert!(!strict_primitive_equal(&nan, &nan));
        assert!(identical_primitive_value(&nan, &nan));
        assert!(!identical_primitive_value(&nan, &other_nan));
        assert!(!identical_primitive_values(
            &[positive_zero],
            &[negative_zero]
        ));
        assert!(identical_primitive_values(
            std::slice::from_ref(&nan),
            std::slice::from_ref(&nan)
        ));
        assert!(!identical_primitive_values(&[other_nan], &[]));
        assert!(identical_primitive_value(
            &Value::String("a".into()),
            &Value::String("a".into())
        ));
        assert!(!identical_primitive_value(&Value::Null, &Value::Undefined));
    }
}
