use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, BindingPattern, CallExpression, ComputedMemberExpression,
    Expression, ExpressionStatement, IfStatement, LogicalExpression, PropertyKind, Statement,
    StaticMemberExpression, UnaryExpression, VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_semantic::{ReferenceId, Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Debug, Clone)]
enum Value {
    String(String),
    Number(f64),
    Bool(bool),
    Null,
    Undefined,
}

impl Value {
    fn truthy(&self) -> bool {
        match self {
            Self::String(s) => !s.is_empty(),
            Self::Number(n) => *n != 0.0 && !n.is_nan(),
            Self::Bool(v) => *v,
            Self::Null | Self::Undefined => false,
        }
    }

    fn number(&self) -> Option<f64> {
        match self {
            Self::Number(n) => Some(*n),
            Self::Bool(v) => Some(if *v { 1.0 } else { 0.0 }),
            Self::Null => Some(0.0),
            Self::Undefined => Some(f64::NAN),
            Self::String(s) => {
                let s = s.trim();
                if s.is_empty() {
                    Some(0.0)
                } else {
                    s.parse().ok()
                }
            }
        }
    }

    fn js_string(&self) -> Option<String> {
        match self {
            Self::String(s) => Some(s.clone()),
            Self::Number(n) if n.is_finite() => Some(render_number(*n)),
            Self::Bool(v) => Some(if *v { "true" } else { "false" }.to_string()),
            Self::Null => Some("null".into()),
            Self::Undefined => Some("undefined".into()),
            Self::Number(_) => None,
        }
    }

    fn render(&self) -> Option<String> {
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
    if n == 0.0 && n.is_sign_negative() {
        return "-0".into();
    }
    if n.fract() == 0.0 && n.abs() <= 9_007_199_254_740_991.0 {
        format!("{n:.0}")
    } else {
        n.to_string()
    }
}

fn same_value(a: &Value, b: &Value) -> bool {
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

fn same_values(a: &[Value], b: &[Value]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(left, right)| same_value(left, right))
}

fn render_value_array(values: &[Value]) -> Option<String> {
    let rendered = values
        .iter()
        .map(Value::render)
        .collect::<Option<Vec<_>>>()?;
    Some(format!("[{}]", rendered.join(", ")))
}

fn eval(expr: &Expression<'_>) -> Option<Value> {
    match expr {
        Expression::StringLiteral(v) => Some(Value::String(v.value.to_string())),
        Expression::NumericLiteral(v) => Some(Value::Number(v.value)),
        Expression::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        Expression::NullLiteral(_) => Some(Value::Null),
        Expression::TemplateLiteral(v) if v.expressions.is_empty() => v
            .quasis
            .first()
            .map(|q| Value::String(q.value.cooked.as_ref().unwrap_or(&q.value.raw).to_string())),
        Expression::ParenthesizedExpression(v) => eval(&v.expression),
        Expression::UnaryExpression(v) => eval_unary(v),
        Expression::BinaryExpression(v) => {
            eval_binary(v.operator.as_str(), eval(&v.left)?, eval(&v.right)?)
        }
        Expression::LogicalExpression(v) => eval_logical(v),
        Expression::ConditionalExpression(v) => {
            let test = known_bool(&v.test)?;
            eval(if test { &v.consequent } else { &v.alternate })
        }
        _ => None,
    }
}

fn known_bool(expr: &Expression<'_>) -> Option<bool> {
    if let Some(v) = eval(expr) {
        return Some(v.truthy());
    }
    match expr {
        Expression::ArrayExpression(v) if v.elements.is_empty() => Some(true),
        Expression::ObjectExpression(v) if v.properties.is_empty() => Some(true),
        Expression::ParenthesizedExpression(v) => known_bool(&v.expression),
        _ => None,
    }
}

fn eval_unary(v: &UnaryExpression<'_>) -> Option<Value> {
    let op = v.operator.as_str();
    if op == "!" {
        return known_bool(&v.argument).map(|x| Value::Bool(!x));
    }
    if op == "void" {
        eval(&v.argument)?;
        return Some(Value::Undefined);
    }
    let value = eval(&v.argument)?;
    match op {
        "+" => value.number().map(Value::Number),
        "-" => value.number().map(|x| Value::Number(-x)),
        "~" => value
            .number()
            .map(|x| Value::Number((!js_to_int32(x)) as f64)),
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

fn js_to_uint32(n: f64) -> u32 {
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    n.trunc().rem_euclid(4_294_967_296.0) as u32
}

fn js_to_int32(n: f64) -> i32 {
    js_to_uint32(n) as i32
}

fn eval_binary(op: &str, left: Value, right: Value) -> Option<Value> {
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
            Some(Value::Number(
                js_to_int32(left.number()?).wrapping_shl(shift) as f64,
            ))
        }
        ">>" => {
            let shift = js_to_uint32(right.number()?) & 31;
            Some(Value::Number((js_to_int32(left.number()?) >> shift) as f64))
        }
        ">>>" => {
            let shift = js_to_uint32(right.number()?) & 31;
            Some(Value::Number(
                (js_to_uint32(left.number()?) >> shift) as f64,
            ))
        }
        "|" => Some(Value::Number(
            (js_to_int32(left.number()?) | js_to_int32(right.number()?)) as f64,
        )),
        "^" => Some(Value::Number(
            (js_to_int32(left.number()?) ^ js_to_int32(right.number()?)) as f64,
        )),
        "&" => Some(Value::Number(
            (js_to_int32(left.number()?) & js_to_int32(right.number()?)) as f64,
        )),
        "===" => Some(Value::Bool(same_value(&left, &right))),
        "!==" => Some(Value::Bool(!same_value(&left, &right))),
        "==" | "!=" => {
            let equal = same_value(&left, &right)
                || matches!(
                    (&left, &right),
                    (Value::Null, Value::Undefined) | (Value::Undefined, Value::Null)
                );
            if !equal {
                return None;
            }
            Some(Value::Bool(op == "=="))
        }
        "<" | "<=" | ">" | ">=" => {
            let result = match (&left, &right) {
                (Value::String(a), Value::String(b)) => match op {
                    "<" => a < b,
                    "<=" => a <= b,
                    ">" => a > b,
                    ">=" => a >= b,
                    _ => unreachable!(),
                },
                _ => {
                    let a = left.number()?;
                    let b = right.number()?;
                    match op {
                        "<" => a < b,
                        "<=" => a <= b,
                        ">" => a > b,
                        ">=" => a >= b,
                        _ => unreachable!(),
                    }
                }
            };
            Some(Value::Bool(result))
        }
        _ => None,
    }
}

fn eval_logical(v: &LogicalExpression<'_>) -> Option<Value> {
    let left = eval(&v.left)?;
    match v.operator.as_str() {
        "&&" => {
            if left.truthy() {
                eval(&v.right)
            } else {
                Some(left)
            }
        }
        "||" => {
            if left.truthy() {
                Some(left)
            } else {
                eval(&v.right)
            }
        }
        "??" => {
            if matches!(left, Value::Null | Value::Undefined) {
                eval(&v.right)
            } else {
                Some(left)
            }
        }
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub struct ArithmeticStateProof {
    pub iteration: usize,
    pub input_start: usize,
    pub input_end: usize,
    pub state_var: String,
    pub state_path: Vec<String>,
    pub termination: String,
}

#[derive(Debug, Clone)]
struct Replacement {
    start: usize,
    end: usize,
    text: String,
    kind: &'static str,
    arithmetic_state_proof: Option<ArithmeticStateProof>,
}

#[derive(Debug, Clone)]
enum DecoderTransform {
    Plain,
    LowerAlphabetBase64Uri,
    StandardBase64,
    FixedBase64Alphabet(String),
}

#[derive(Debug, Clone)]
struct Decoder {
    values: Vec<Value>,
    offset: i64,
    provider: String,
    provider_array_span: Span,
    transform: DecoderTransform,
}

impl Decoder {
    fn value_for_raw_rotated(&self, raw: i64, rotation: usize) -> Option<Value> {
        let index = raw - self.offset;
        if index < 0 || self.values.is_empty() {
            return None;
        }
        let index = index as usize;
        // Array indexing never wraps. Rotation only maps an already-valid
        // logical table index onto the physically rotated backing array.
        // Applying modulo before this bounds check would incorrectly turn an
        // out-of-range runtime lookup (undefined) into an unrelated entry.
        if index >= self.values.len() {
            return None;
        }
        let index = index.checked_add(rotation)? % self.values.len();
        let value = self.values.get(index)?.clone();
        match (&self.transform, value) {
            (DecoderTransform::Plain, value) => Some(value),
            (DecoderTransform::LowerAlphabetBase64Uri, Value::String(encoded)) => {
                decode_lower_alphabet_base64_uri(&encoded).map(Value::String)
            }
            (DecoderTransform::LowerAlphabetBase64Uri, _) => None,
            (DecoderTransform::StandardBase64, Value::String(encoded)) => {
                decode_standard_base64_latin1(&encoded).map(Value::String)
            }
            (DecoderTransform::StandardBase64, _) => None,
            (DecoderTransform::FixedBase64Alphabet(alphabet), Value::String(encoded)) => {
                decode_fixed_base64_latin1(&encoded, alphabet).map(Value::String)
            }
            // DataDome-style tables intentionally mix encoded strings with
            // literal numbers, booleans, and null. The runtime decoder only
            // transforms strings and returns every other table value as-is.
            (DecoderTransform::FixedBase64Alphabet(_), value) => Some(value),
        }
    }

    fn value_for_raw(&self, raw: i64) -> Option<Value> {
        self.value_for_raw_rotated(raw, 0)
    }
}

fn decode_standard_base64_latin1(input: &str) -> Option<String> {
    let compact = input
        .chars()
        .filter(|ch| !matches!(ch, ' ' | '\t' | '\n' | '\r' | '\x0c'))
        .collect::<String>();
    if compact.len() % 4 == 1 {
        return None;
    }

    let padding = compact.chars().rev().take_while(|ch| *ch == '=').count();
    if padding > 2 {
        return None;
    }
    if padding > 0 {
        if compact.len() % 4 != 0 {
            return None;
        }
        if compact[..compact.len() - padding].contains('=') {
            return None;
        }
    } else if compact.contains('=') {
        return None;
    }

    decode_base64_latin1(
        &compact,
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=",
    )
}

fn decode_fixed_base64_latin1(input: &str, alphabet: &str) -> Option<String> {
    let alphabet = alphabet.chars().collect::<Vec<_>>();
    if alphabet.len() != 65 {
        return None;
    }
    let unique = alphabet.iter().copied().collect::<HashSet<_>>();
    if unique.len() != 65 {
        return None;
    }

    // Match the observed decoder rather than treating the alphabet as a
    // generic RFC 4648 alphabet: it first strips everything outside this
    // character class, then decodes in groups of four. Missing charAt()
    // positions become "", and alphabet.indexOf("") is 0 in JavaScript.
    let filtered = input
        .chars()
        .filter(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '+' | '/' | '='))
        .collect::<Vec<_>>();

    let mut out = String::with_capacity(filtered.len().div_ceil(4) * 3);
    let mut index = 0usize;
    while index < filtered.len() {
        let symbol = |offset: usize| -> Option<usize> {
            match filtered.get(index + offset) {
                Some(ch) => alphabet.iter().position(|candidate| candidate == ch),
                None => Some(0),
            }
        };
        let a = symbol(0)?;
        let b = symbol(1)?;
        let c = symbol(2)?;
        let d = symbol(3)?;

        let mut push_code_unit = |value: usize| -> Option<()> {
            // String.fromCharCode applies ToUint16. These decoder expressions
            // are small, but mask explicitly so the modeled primitive is exact.
            out.push(char::from_u32((value & 0xffff) as u32)?);
            Some(())
        };
        push_code_unit((a << 2) | (b >> 4))?;
        if c != 64 {
            push_code_unit(((b & 15) << 4) | (c >> 2))?;
        }
        if d != 64 {
            push_code_unit(((c & 3) << 6) | d)?;
        }
        index += 4;
    }

    Some(out)
}

fn decode_base64_latin1(input: &str, alphabet: &str) -> Option<String> {
    let alphabet = alphabet.chars().collect::<Vec<_>>();
    if alphabet.len() != 65 {
        return None;
    }
    let unique = alphabet.iter().copied().collect::<HashSet<_>>();
    if unique.len() != 65 {
        return None;
    }

    let mut bits = 0u32;
    let mut bit_count = 0u32;
    let mut out = Vec::with_capacity(input.len() * 3 / 4);
    for ch in input.chars() {
        let index = alphabet.iter().position(|candidate| *candidate == ch)?;
        if index == 64 {
            break;
        }
        bits = (bits << 6) | index as u32;
        bit_count += 6;
        while bit_count >= 8 {
            bit_count -= 8;
            out.push(((bits >> bit_count) & 0xff) as u8);
            bits &= if bit_count == 0 {
                0
            } else {
                (1u32 << bit_count) - 1
            };
        }
    }

    Some(out.into_iter().map(char::from).collect())
}

fn decode_lower_alphabet_base64_uri(input: &str) -> Option<String> {
    const ALPHABET: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/=";
    let mut bits = 0u32;
    let mut bit_count = 0u32;
    let mut out = Vec::with_capacity(input.len() * 3 / 4);

    for ch in input.chars() {
        let index = ALPHABET.find(ch)?;
        if index >= 64 {
            break;
        }
        bits = (bits << 6) | index as u32;
        bit_count += 6;
        while bit_count >= 8 {
            bit_count -= 8;
            out.push(((bits >> bit_count) & 0xff) as u8);
            bits &= if bit_count == 0 {
                0
            } else {
                (1u32 << bit_count) - 1
            };
        }
    }

    String::from_utf8(out).ok()
}

#[derive(Default)]
struct Counts(BTreeMap<String, usize>);

impl Counts {
    fn bump(&mut self, kind: &str) {
        *self.0.entry(kind.to_string()).or_default() += 1;
    }
}

fn fragment(source: &str, span: Span) -> &str {
    source
        .get(span.start as usize..(span.end as usize).min(source.len()))
        .unwrap_or_default()
}

fn valid_property(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first == '$' || first.is_ascii_alphabetic())
        && chars.all(|c| c == '_' || c == '$' || c.is_ascii_alphanumeric())
}

fn symbol_of(scoping: &Scoping, expr: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(id) = expr else {
        return None;
    };
    scoping.get_reference(id.reference_id.get()?).symbol_id()
}

#[derive(Debug, Clone)]
struct ConstBinding {
    value: Value,
    available_after: u32,
}

fn eval_with_constants(
    expr: &Expression<'_>,
    scoping: &Scoping,
    constants: &HashMap<SymbolId, ConstBinding>,
) -> Option<Value> {
    match expr {
        Expression::Identifier(id) => {
            let reference_id = id.reference_id.get()?;
            let reference = scoping.get_reference(reference_id);
            if !reference.is_read()
                || reference.is_write()
                || reference.flags().is_member_write_target()
            {
                return None;
            }
            let symbol = reference.symbol_id()?;
            let binding = constants.get(&symbol)?;
            if id.span.start < binding.available_after {
                return None;
            }
            Some(binding.value.clone())
        }
        Expression::StringLiteral(v) => Some(Value::String(v.value.to_string())),
        Expression::NumericLiteral(v) => Some(Value::Number(v.value)),
        Expression::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        Expression::NullLiteral(_) => Some(Value::Null),
        Expression::TemplateLiteral(v) if v.expressions.is_empty() => v
            .quasis
            .first()
            .map(|q| Value::String(q.value.cooked.as_ref().unwrap_or(&q.value.raw).to_string())),
        Expression::ParenthesizedExpression(v) => {
            eval_with_constants(&v.expression, scoping, constants)
        }
        Expression::UnaryExpression(v) => {
            let op = v.operator.as_str();
            if op == "!" {
                return known_bool_with_constants(&v.argument, scoping, constants)
                    .map(|x| Value::Bool(!x));
            }
            if op == "void" {
                eval_with_constants(&v.argument, scoping, constants)?;
                return Some(Value::Undefined);
            }
            let value = eval_with_constants(&v.argument, scoping, constants)?;
            match op {
                "+" => value.number().map(Value::Number),
                "-" => value.number().map(|x| Value::Number(-x)),
                "~" => value.number().map(|x| Value::Number((!(x as i32)) as f64)),
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
        Expression::BinaryExpression(v) => eval_binary(
            v.operator.as_str(),
            eval_with_constants(&v.left, scoping, constants)?,
            eval_with_constants(&v.right, scoping, constants)?,
        ),
        Expression::LogicalExpression(v) => {
            let left = eval_with_constants(&v.left, scoping, constants)?;
            match v.operator.as_str() {
                "&&" => {
                    if left.truthy() {
                        eval_with_constants(&v.right, scoping, constants)
                    } else {
                        Some(left)
                    }
                }
                "||" => {
                    if left.truthy() {
                        Some(left)
                    } else {
                        eval_with_constants(&v.right, scoping, constants)
                    }
                }
                "??" => {
                    if matches!(left, Value::Null | Value::Undefined) {
                        eval_with_constants(&v.right, scoping, constants)
                    } else {
                        Some(left)
                    }
                }
                _ => None,
            }
        }
        Expression::ConditionalExpression(v) => {
            let test = known_bool_with_constants(&v.test, scoping, constants)?;
            eval_with_constants(
                if test { &v.consequent } else { &v.alternate },
                scoping,
                constants,
            )
        }
        _ => None,
    }
}

fn known_bool_with_constants(
    expr: &Expression<'_>,
    scoping: &Scoping,
    constants: &HashMap<SymbolId, ConstBinding>,
) -> Option<bool> {
    if let Some(v) = eval_with_constants(expr, scoping, constants) {
        return Some(v.truthy());
    }
    match expr {
        Expression::ArrayExpression(v) if v.elements.is_empty() => Some(true),
        Expression::ObjectExpression(v) if v.properties.is_empty() => Some(true),
        Expression::ParenthesizedExpression(v) => {
            known_bool_with_constants(&v.expression, scoping, constants)
        }
        _ => None,
    }
}

struct ConstValueCollector<'s, 'c> {
    scoping: &'c Scoping,
    constants: &'s mut HashMap<SymbolId, ConstBinding>,
    changed: bool,
}

impl<'a> Visit<'a> for ConstValueCollector<'_, '_> {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        if it.kind == VariableDeclarationKind::Const {
            for d in &it.declarations {
                let BindingPattern::BindingIdentifier(id) = &d.id else {
                    continue;
                };
                let Some(symbol) = id.symbol_id.get() else {
                    continue;
                };
                if self.constants.contains_key(&symbol) {
                    continue;
                }
                let Some(init) = &d.init else {
                    continue;
                };
                let Some(value) = eval_with_constants(init, self.scoping, self.constants) else {
                    continue;
                };
                self.constants.insert(
                    symbol,
                    ConstBinding {
                        value,
                        available_after: d.span.end,
                    },
                );
                self.changed = true;
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn collect_const_values(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, ConstBinding> {
    let mut constants = HashMap::new();
    loop {
        let changed = {
            let mut collector = ConstValueCollector {
                scoping,
                constants: &mut constants,
                changed: false,
            };
            collector.visit_program(program);
            collector.changed
        };
        if !changed {
            break;
        }
    }
    constants
}

fn array_element(el: &ArrayExpressionElement<'_>) -> Option<Value> {
    match el {
        ArrayExpressionElement::StringLiteral(v) => Some(Value::String(v.value.to_string())),
        ArrayExpressionElement::NumericLiteral(v) => Some(Value::Number(v.value)),
        ArrayExpressionElement::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        ArrayExpressionElement::NullLiteral(_) => Some(Value::Null),
        ArrayExpressionElement::UnaryExpression(v) => eval_unary(v),
        _ => None,
    }
}

#[derive(Debug, Clone)]
struct StaticArrayInfo {
    symbol: SymbolId,
    name: String,
    values: Vec<Value>,
    span: Span,
}

#[derive(Default)]
struct StaticArrayCollector {
    candidates: Vec<StaticArrayInfo>,
}

impl<'a> Visit<'a> for StaticArrayCollector {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        for d in &it.declarations {
            let BindingPattern::BindingIdentifier(id) = &d.id else {
                continue;
            };
            let Some(symbol) = id.symbol_id.get() else {
                continue;
            };
            let Some(Expression::ArrayExpression(arr)) = &d.init else {
                continue;
            };
            let Some(values) = arr
                .elements
                .iter()
                .map(array_element)
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            if !values.is_empty() {
                self.candidates.push(StaticArrayInfo {
                    symbol,
                    name: id.name.to_string(),
                    values,
                    span: arr.span,
                });
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn top_level_arrays(program: &oxc_ast::ast::Program<'_>) -> HashMap<SymbolId, Vec<Value>> {
    let mut out = HashMap::new();
    for stmt in &program.body {
        let Statement::VariableDeclaration(decl) = stmt else {
            continue;
        };
        if decl.kind != VariableDeclarationKind::Const {
            continue;
        }
        for d in &decl.declarations {
            let BindingPattern::BindingIdentifier(id) = &d.id else {
                continue;
            };
            let Some(symbol) = id.symbol_id.get() else {
                continue;
            };
            let Some(Expression::ArrayExpression(arr)) = &d.init else {
                continue;
            };
            let Some(values) = arr
                .elements
                .iter()
                .map(array_element)
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            if !values.is_empty() {
                out.insert(symbol, values);
            }
        }
    }
    out
}

fn decoder_static_arrays(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> Vec<StaticArrayInfo> {
    let mut collector = StaticArrayCollector::default();
    collector.visit_program(program);
    collector.candidates.retain(|candidate| {
        scoping
            .get_resolved_reference_ids(candidate.symbol)
            .iter()
            .all(|reference_id| {
                let reference = scoping.get_reference(*reference_id);
                !reference.is_write() && !reference.flags().is_member_write_target()
            })
    });
    collector.candidates
}

#[derive(Default)]
struct DirectCallCounter {
    count: usize,
}

impl<'a> Visit<'a> for DirectCallCounter {
    fn visit_call_expression(&mut self, it: &CallExpression<'a>) {
        self.count += 1;
        walk::walk_call_expression(self, it);
    }

    fn visit_function(&mut self, _f: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {
        // Nested functions do not execute as part of the candidate decoder
        // invocation itself, so do not count calls inside them.
    }
}

fn direct_body_call_count(body: &oxc_ast::ast::FunctionBody<'_>) -> usize {
    let mut counter = DirectCallCounter::default();
    for statement in &body.statements {
        counter.visit_statement(statement);
    }
    counter.count
}

fn fixed_decoder_control_shape(body: &oxc_ast::ast::FunctionBody<'_>) -> bool {
    if body.statements.len() != 3 {
        return false;
    }
    let first = matches!(
        &body.statements[0],
        Statement::IfStatement(statement)
            if statement.alternate.is_none()
                && matches!(&statement.consequent, Statement::ReturnStatement(_))
    );
    let second = match &body.statements[1] {
        Statement::ForStatement(statement) => match &statement.body {
            Statement::ExpressionStatement(_) => true,
            // The generic sequence splitter may already have turned the
            // decoder's six comma-separated loop operations into six
            // expression statements by the time the literal table becomes
            // fully static on a later fixed-point iteration.
            Statement::BlockStatement(block) => {
                block.body.len() == 6
                    && block
                        .body
                        .iter()
                        .all(|statement| matches!(statement, Statement::ExpressionStatement(_)))
            }
            _ => false,
        },
        _ => false,
    };
    let third = matches!(&body.statements[2], Statement::ReturnStatement(_));
    first && second && third
}

#[derive(Debug, Clone)]
struct LocalStaticArrayInfo {
    values: Vec<Value>,
    span: Span,
}

#[derive(Debug)]
struct FnInfo {
    name: String,
    symbol: SymbolId,
    scope: ScopeId,
    params: Vec<String>,
    span: Span,
    static_arrays: HashMap<String, LocalStaticArrayInfo>,
}

fn function_info(f: &oxc_ast::ast::Function<'_>, scoping: &Scoping) -> Option<FnInfo> {
    if f.r#type != oxc_ast::ast::FunctionType::FunctionDeclaration {
        return None;
    }
    let id = f.id.as_ref()?;
    let symbol = id.symbol_id.get()?;
    let params = f
        .params
        .items
        .iter()
        .filter_map(|p| match &p.pattern {
            BindingPattern::BindingIdentifier(id) => Some(id.name.to_string()),
            _ => None,
        })
        .collect();

    let mut static_arrays = HashMap::new();
    if let Some(body) = &f.body {
        for stmt in &body.statements {
            let Statement::VariableDeclaration(decl) = stmt else {
                continue;
            };
            for d in &decl.declarations {
                let BindingPattern::BindingIdentifier(array_id) = &d.id else {
                    continue;
                };
                let Some(Expression::ArrayExpression(array)) = &d.init else {
                    continue;
                };
                let Some(values) = array
                    .elements
                    .iter()
                    .map(array_element)
                    .collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                if !values.is_empty() {
                    static_arrays.insert(
                        array_id.name.to_string(),
                        LocalStaticArrayInfo {
                            values,
                            span: array.span,
                        },
                    );
                }
            }
        }
    }

    Some(FnInfo {
        name: id.name.to_string(),
        symbol,
        scope: scoping.symbol_scope_id(symbol),
        params,
        span: f.span,
        static_arrays,
    })
}

struct FunctionDeclarationCollector<'s> {
    scoping: &'s Scoping,
    out: Vec<FnInfo>,
}

impl<'a> Visit<'a> for FunctionDeclarationCollector<'_> {
    fn visit_function(
        &mut self,
        it: &oxc_ast::ast::Function<'a>,
        flags: oxc_syntax::scope::ScopeFlags,
    ) {
        if let Some(info) = function_info(it, self.scoping) {
            self.out.push(info);
        }
        walk::walk_function(self, it, flags);
    }
}

fn all_function_declarations(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> Vec<FnInfo> {
    let mut collector = FunctionDeclarationCollector {
        scoping,
        out: Vec::new(),
    };
    collector.visit_program(program);
    collector.out
}

#[derive(Debug)]
struct DirectFnInfo {
    symbol: SymbolId,
    params: Vec<String>,
    span: Span,
    body_statement_count: usize,
    direct_call_count: usize,
    fixed_decoder_control_shape: bool,
}

#[derive(Default)]
struct DirectFnInfoCollector {
    out: Vec<DirectFnInfo>,
}

impl<'a> Visit<'a> for DirectFnInfoCollector {
    fn visit_function(&mut self, f: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if let Some(id) = &f.id {
            if let Some(symbol) = id.symbol_id.get() {
                let params = f
                    .params
                    .items
                    .iter()
                    .filter_map(|p| match &p.pattern {
                        BindingPattern::BindingIdentifier(id) => Some(id.name.to_string()),
                        _ => None,
                    })
                    .collect();

                self.out.push(DirectFnInfo {
                    symbol,
                    params,
                    span: f.span,
                    body_statement_count: f.body.as_ref().map_or(0, |body| body.statements.len()),
                    direct_call_count: f
                        .body
                        .as_ref()
                        .map_or(0, |body| direct_body_call_count(body)),
                    fixed_decoder_control_shape: f
                        .body
                        .as_ref()
                        .is_some_and(|body| fixed_decoder_control_shape(body)),
                });
            }
        }
        walk::walk_function(self, f, flags);
    }
}

fn all_functions(program: &oxc_ast::ast::Program<'_>) -> Vec<DirectFnInfo> {
    let mut collector = DirectFnInfoCollector::default();
    collector.visit_program(program);
    collector.out
}

#[derive(Debug, Clone)]
enum PureExpr {
    Value(Value),
    Param(usize),
    Unary {
        operator: String,
        argument: Box<PureExpr>,
    },
    Binary {
        operator: String,
        left: Box<PureExpr>,
        right: Box<PureExpr>,
    },
    Logical {
        operator: String,
        left: Box<PureExpr>,
        right: Box<PureExpr>,
    },
    Conditional {
        test: Box<PureExpr>,
        consequent: Box<PureExpr>,
        alternate: Box<PureExpr>,
    },
}

impl PureExpr {
    fn eval(&self, args: &[Value]) -> Option<Value> {
        match self {
            Self::Value(value) => Some(value.clone()),
            Self::Param(index) => args.get(*index).cloned(),
            Self::Unary { operator, argument } => {
                let value = argument.eval(args)?;
                match operator.as_str() {
                    "!" => Some(Value::Bool(!value.truthy())),
                    "+" => value.number().map(Value::Number),
                    "-" => value.number().map(|n| Value::Number(-n)),
                    "~" => value
                        .number()
                        .map(|n| Value::Number((!js_to_int32(n)) as f64)),
                    "void" => Some(Value::Undefined),
                    "typeof" => Some(Value::String(
                        match value {
                            Value::String(_) => "string",
                            Value::Number(_) => "number",
                            Value::Bool(_) => "boolean",
                            Value::Null => "object",
                            Value::Undefined => "undefined",
                        }
                        .to_string(),
                    )),
                    _ => None,
                }
            }
            Self::Binary {
                operator,
                left,
                right,
            } => eval_binary(operator, left.eval(args)?, right.eval(args)?),
            Self::Logical {
                operator,
                left,
                right,
            } => {
                let left = left.eval(args)?;
                match operator.as_str() {
                    "&&" => {
                        if left.truthy() {
                            right.eval(args)
                        } else {
                            Some(left)
                        }
                    }
                    "||" => {
                        if left.truthy() {
                            Some(left)
                        } else {
                            right.eval(args)
                        }
                    }
                    "??" => {
                        if matches!(left, Value::Null | Value::Undefined) {
                            right.eval(args)
                        } else {
                            Some(left)
                        }
                    }
                    _ => None,
                }
            }
            Self::Conditional {
                test,
                consequent,
                alternate,
            } => {
                if test.eval(args)?.truthy() {
                    consequent.eval(args)
                } else {
                    alternate.eval(args)
                }
            }
        }
    }
}

fn compile_pure_expr(expr: &Expression<'_>, params: &HashMap<String, usize>) -> Option<PureExpr> {
    match expr {
        Expression::Identifier(id) => params.get(id.name.as_str()).copied().map(PureExpr::Param),
        Expression::StringLiteral(v) => Some(PureExpr::Value(Value::String(v.value.to_string()))),
        Expression::NumericLiteral(v) => Some(PureExpr::Value(Value::Number(v.value))),
        Expression::BooleanLiteral(v) => Some(PureExpr::Value(Value::Bool(v.value))),
        Expression::NullLiteral(_) => Some(PureExpr::Value(Value::Null)),
        Expression::TemplateLiteral(v) if v.expressions.is_empty() => v.quasis.first().map(|q| {
            PureExpr::Value(Value::String(
                q.value.cooked.as_ref().unwrap_or(&q.value.raw).to_string(),
            ))
        }),
        Expression::ParenthesizedExpression(v) => compile_pure_expr(&v.expression, params),
        Expression::UnaryExpression(v)
            if matches!(
                v.operator.as_str(),
                "!" | "+" | "-" | "~" | "void" | "typeof"
            ) =>
        {
            Some(PureExpr::Unary {
                operator: v.operator.as_str().to_string(),
                argument: Box::new(compile_pure_expr(&v.argument, params)?),
            })
        }
        Expression::BinaryExpression(v)
            if matches!(
                v.operator.as_str(),
                "+" | "-"
                    | "*"
                    | "/"
                    | "%"
                    | "**"
                    | "<<"
                    | ">>"
                    | ">>>"
                    | "|"
                    | "^"
                    | "&"
                    | "==="
                    | "!=="
                    | "=="
                    | "!="
                    | "<"
                    | "<="
                    | ">"
                    | ">="
            ) =>
        {
            Some(PureExpr::Binary {
                operator: v.operator.as_str().to_string(),
                left: Box::new(compile_pure_expr(&v.left, params)?),
                right: Box::new(compile_pure_expr(&v.right, params)?),
            })
        }
        Expression::LogicalExpression(v) => Some(PureExpr::Logical {
            operator: v.operator.as_str().to_string(),
            left: Box::new(compile_pure_expr(&v.left, params)?),
            right: Box::new(compile_pure_expr(&v.right, params)?),
        }),
        Expression::ConditionalExpression(v) => Some(PureExpr::Conditional {
            test: Box::new(compile_pure_expr(&v.test, params)?),
            consequent: Box::new(compile_pure_expr(&v.consequent, params)?),
            alternate: Box::new(compile_pure_expr(&v.alternate, params)?),
        }),
        _ => None,
    }
}

#[derive(Debug, Clone)]
struct PureFunction {
    arity: usize,
    expression: PureExpr,
}

struct PureFunctionCollector<'c> {
    scoping: &'c Scoping,
    functions: HashMap<SymbolId, PureFunction>,
}

impl<'a> Visit<'a> for PureFunctionCollector<'_> {
    fn visit_function(&mut self, f: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if !f.r#async && !f.generator && f.params.rest.is_none() {
            if let (Some(id), Some(body)) = (&f.id, &f.body) {
                if let Some(symbol) = id.symbol_id.get() {
                    let immutable =
                        self.scoping.get_resolved_reference_ids(symbol).iter().all(
                            |reference_id| !self.scoping.get_reference(*reference_id).is_write(),
                        );
                    if immutable && body.statements.len() == 1 {
                        let mut params = HashMap::new();
                        let mut valid_params = true;
                        for (index, parameter) in f.params.items.iter().enumerate() {
                            let BindingPattern::BindingIdentifier(parameter_id) =
                                &parameter.pattern
                            else {
                                valid_params = false;
                                break;
                            };
                            if parameter.initializer.is_some()
                                || params
                                    .insert(parameter_id.name.to_string(), index)
                                    .is_some()
                            {
                                valid_params = false;
                                break;
                            }
                        }
                        if valid_params {
                            if let Statement::ReturnStatement(ret) = &body.statements[0] {
                                if let Some(argument) = &ret.argument {
                                    if let Some(expression) = compile_pure_expr(argument, &params) {
                                        self.functions.insert(
                                            symbol,
                                            PureFunction {
                                                arity: f.params.items.len(),
                                                expression,
                                            },
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_function(self, f, flags);
    }
}

fn collect_pure_functions(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, PureFunction> {
    let mut collector = PureFunctionCollector {
        scoping,
        functions: HashMap::new(),
    };
    collector.visit_program(program);
    collector.functions
}

fn fixed_base64_alphabet(body: &str) -> Option<String> {
    if !body.contains("String.fromCharCode")
        || !body.contains(".indexOf")
        || !body.contains(".charAt")
    {
        return None;
    }
    let re = regex::Regex::new(r#"["']([A-Za-z0-9+/=]{65})["']"#).unwrap();
    let standard = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="
        .chars()
        .collect::<HashSet<_>>();
    let mut candidates = re
        .captures_iter(body)
        .filter_map(|caps| caps.get(1).map(|capture| capture.as_str().to_string()))
        .filter(|candidate| candidate.chars().collect::<HashSet<_>>() == standard)
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.dedup();
    (candidates.len() == 1).then(|| candidates.remove(0))
}

fn function_inner_source(body: &str) -> Option<&str> {
    let start = body.find('{')?.checked_add(1)?;
    let end = body.rfind('}')?;
    (start <= end).then(|| &body[start..end])
}

fn standard_base64_decoder_matches(body: &str, array: &str, param: &str) -> bool {
    let Some(inner) = function_inner_source(body) else {
        return false;
    };

    // Match the complete function body, not merely a decoder-looking
    // expression somewhere inside it. Replacing a call removes the entire
    // function execution, so accepting extra statements could silently drop
    // observable side effects.
    let direct = regex::Regex::new(&format!(
        r#"(?s)^\s*return\s+atob\s*\(\s*{}\s*\[\s*{}\s*\]\s*\)\s*;?\s*$"#,
        regex::escape(array),
        regex::escape(param)
    ))
    .unwrap();
    if direct.is_match(inner) {
        return true;
    }

    let sequence = regex::Regex::new(&format!(
        r#"(?s)^\s*return\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*{}\s*\[\s*{}\s*\]\s*,\s*atob\s*\(\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\)\s*;?\s*$"#,
        regex::escape(array),
        regex::escape(param)
    ))
    .unwrap();
    if sequence
        .captures(inner)
        .is_some_and(|caps| caps.get(1).map(|m| m.as_str()) == caps.get(2).map(|m| m.as_str()))
    {
        return true;
    }

    let assignment = regex::Regex::new(&format!(
        r#"(?s)^\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*{}\s*\[\s*{}\s*\]\s*;\s*return\s+atob\s*\(\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\)\s*;?\s*$"#,
        regex::escape(array),
        regex::escape(param)
    ))
    .unwrap();
    assignment
        .captures(inner)
        .is_some_and(|caps| caps.get(1).map(|m| m.as_str()) == caps.get(2).map(|m| m.as_str()))
}

fn fixed_base64_decoder_matches(body: &str, array: &str, param: &str) -> Option<String> {
    let alphabet = fixed_base64_alphabet(body)?;
    let guarded_load = regex::Regex::new(&format!(
        r#"typeof\s*\(?\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*{}\s*\[\s*{}\s*\]\s*\)?"#,
        regex::escape(array),
        regex::escape(param)
    ))
    .unwrap();

    let alias = guarded_load
        .captures_iter(body)
        .find_map(|caps| caps.get(1).map(|m| m.as_str()))?;
    let return_alias =
        regex::Regex::new(&format!(r#"\breturn\s+{}\s*;"#, regex::escape(alias))).unwrap();
    if !return_alias.is_match(body) {
        return None;
    }

    // Fail closed on a recognizable Base64 decoder shape rather than merely
    // seeing an alphabet and String.fromCharCode somewhere in the function.
    if !body.contains(".replace(/[^A-Za-z0-9\\+\\/\\=]/g")
        || body.matches(".indexOf(").count() != 4
        || body.matches(".charAt(").count() != 4
        || body.matches("String.fromCharCode").count() != 3
        || body.matches("<<").count() != 3
        || body.matches(">>").count() != 2
    {
        return None;
    }
    let sentinel_checks = regex::Regex::new(r#"(?:64\s*!=|!=\s*64)"#).unwrap();
    if sentinel_checks.find_iter(body).count() != 2 {
        return None;
    }

    Some(alphabet)
}

fn function_has_external_write(
    span: Span,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> bool {
    for symbol in scoping.symbol_ids() {
        let declaration = scoping.symbol_span(symbol);
        if span.start <= declaration.start && declaration.end <= span.end {
            continue;
        }
        for reference_id in scoping.get_resolved_reference_ids(symbol) {
            let Some(reference_span) = reference_spans.get(reference_id) else {
                continue;
            };
            if span.start <= reference_span.start && reference_span.end <= span.end {
                let reference = scoping.get_reference(*reference_id);
                if reference.is_write() || reference.flags().is_member_write_target() {
                    return true;
                }
            }
        }
    }

    for reference_ids in scoping.root_unresolved_references_ids() {
        for reference_id in reference_ids {
            let Some(reference_span) = reference_spans.get(&reference_id) else {
                continue;
            };
            if span.start <= reference_span.start && reference_span.end <= span.end {
                let reference = scoping.get_reference(reference_id);
                if reference.is_write() || reference.flags().is_member_write_target() {
                    return true;
                }
            }
        }
    }
    false
}

fn detect_direct_table_decoders(
    source: &str,
    functions: &[DirectFnInfo],
    arrays: &[StaticArrayInfo],
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<SymbolId, Decoder> {
    let mut arrays_by_name: HashMap<&str, Vec<&StaticArrayInfo>> = HashMap::new();
    for array in arrays {
        arrays_by_name
            .entry(array.name.as_str())
            .or_default()
            .push(array);
    }

    let mut out = HashMap::new();
    for function in functions {
        if scoping
            .get_resolved_reference_ids(function.symbol)
            .iter()
            .any(|reference_id| scoping.get_reference(*reference_id).is_write())
        {
            continue;
        }
        let Some(param) = function.params.first() else {
            continue;
        };
        let body = fragment(source, function.span);
        let access = regex::Regex::new(&format!(
            r#"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*\[\s*{}\s*\]"#,
            regex::escape(param)
        ))
        .unwrap();
        let mut matched = access
            .captures_iter(body)
            .filter_map(|caps| caps.get(1).map(|capture| capture.as_str()))
            .filter_map(|name| arrays_by_name.get(name))
            .filter(|candidates| candidates.len() == 1)
            .map(|candidates| candidates[0])
            .collect::<Vec<_>>();
        matched.sort_by_key(|array| array.symbol);
        matched.dedup_by_key(|array| array.symbol);
        if matched.len() != 1 {
            continue;
        }
        let array = matched[0];

        // A direct literal-table decoder should have exactly one resolved
        // use of the table binding: the indexed load proved above. Requiring a
        // single confined read fails closed on aliases/escapes both outside
        // and *inside* the decoder (an internal alias can otherwise mutate the
        // array before the returned lookup without writing the original
        // binding itself).
        let table_references = scoping.get_resolved_reference_ids(array.symbol);
        if table_references.len() != 1 {
            continue;
        }
        let reference_id = table_references[0];
        let reference = scoping.get_reference(reference_id);
        if reference.is_write() || reference.flags().is_member_write_target() {
            continue;
        }
        let Some(span) = reference_spans.get(&reference_id) else {
            continue;
        };
        if function.span.start > span.start || span.end > function.span.end {
            continue;
        }

        let mutator = regex::Regex::new(&format!(
            r#"\b{}\s*\.\s*(?:copyWithin|fill|pop|push|reverse|shift|sort|splice|unshift)\s*\("#,
            regex::escape(&array.name)
        ))
        .unwrap();
        if mutator.is_match(source) {
            continue;
        }

        let transform = if standard_base64_decoder_matches(body, &array.name, param) {
            DecoderTransform::StandardBase64
        } else if function.body_statement_count == 3
            && function.fixed_decoder_control_shape
            && function.direct_call_count == 12
            && !function_has_external_write(function.span, scoping, reference_spans)
        {
            let Some(alphabet) = fixed_base64_decoder_matches(body, &array.name, param) else {
                continue;
            };
            DecoderTransform::FixedBase64Alphabet(alphabet)
        } else {
            continue;
        };

        out.insert(
            function.symbol,
            Decoder {
                values: array.values.clone(),
                offset: 0,
                provider: array.name.clone(),
                provider_array_span: array.span,
                transform,
            },
        );
    }
    out
}

#[derive(Default)]
struct StableVarNumberCollector {
    candidates: HashMap<SymbolId, i64>,
}

impl<'a> Visit<'a> for StableVarNumberCollector {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        if it.kind == VariableDeclarationKind::Var {
            for declaration in &it.declarations {
                let BindingPattern::BindingIdentifier(id) = &declaration.id else {
                    continue;
                };
                let Some(symbol) = id.symbol_id.get() else {
                    continue;
                };
                let Some(init) = &declaration.init else {
                    continue;
                };
                let Some(Value::Number(number)) = eval(init) else {
                    continue;
                };
                if !number.is_finite()
                    || number.fract() != 0.0
                    || number < i64::MIN as f64
                    || number > i64::MAX as f64
                {
                    continue;
                }
                self.candidates.insert(symbol, number as i64);
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn collect_stable_var_numbers(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, i64> {
    let mut collector = StableVarNumberCollector::default();
    collector.visit_program(program);
    collector.candidates.retain(|symbol, _| {
        scoping
            .get_resolved_reference_ids(*symbol)
            .iter()
            .all(|reference_id| {
                let reference = scoping.get_reference(*reference_id);
                !reference.is_write() && !reference.flags().is_member_write_target()
            })
    });
    collector.candidates
}

fn expression_integer(expr: &Expression<'_>) -> Option<i64> {
    let Value::Number(number) = eval(expr)? else {
        return None;
    };
    if !number.is_finite()
        || number.fract() != 0.0
        || number < i64::MIN as f64
        || number > i64::MAX as f64
    {
        return None;
    }
    Some(number as i64)
}

fn selector_identifier_symbol(expr: &Expression<'_>, scoping: &Scoping) -> Option<SymbolId> {
    match expr {
        Expression::Identifier(_) => symbol_of(scoping, expr),
        Expression::ParenthesizedExpression(parenthesized) => {
            selector_identifier_symbol(&parenthesized.expression, scoping)
        }
        _ => None,
    }
}

fn selector_test_value(
    expr: &Expression<'_>,
    selector_symbol: SymbolId,
    selector_value: i64,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> Option<bool> {
    match expr {
        Expression::ParenthesizedExpression(parenthesized) => selector_test_value(
            &parenthesized.expression,
            selector_symbol,
            selector_value,
            scoping,
            stable_var_numbers,
        ),
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "!" => {
            selector_test_value(
                &unary.argument,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )
            .map(|value| !value)
        }
        Expression::LogicalExpression(logical) => {
            let left = selector_test_value(
                &logical.left,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            );
            let right = selector_test_value(
                &logical.right,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            );
            match logical.operator.as_str() {
                "&&" => match (left, right) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                },
                "||" => match (left, right) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                },
                _ => None,
            }
        }
        Expression::BinaryExpression(binary)
            if matches!(binary.operator.as_str(), "==" | "===" | "!=" | "!==") =>
        {
            let left_symbol = selector_identifier_symbol(&binary.left, scoping);
            let right_symbol = selector_identifier_symbol(&binary.right, scoping);

            let other = if left_symbol == Some(selector_symbol) {
                Some(&binary.right)
            } else if right_symbol == Some(selector_symbol) {
                Some(&binary.left)
            } else {
                None
            }?;

            let equal = if let Some(number) = expression_integer(other) {
                selector_value == number
            } else {
                let symbol = selector_identifier_symbol(other, scoping)?;
                let initialized_value = *stable_var_numbers.get(&symbol)?;
                if selector_value == initialized_value {
                    // A var binding is undefined before its initializer executes
                    // and has the proven number afterward. Equality to that exact
                    // number therefore depends on runtime ordering.
                    return None;
                }
                false
            };

            Some(if matches!(binary.operator.as_str(), "==" | "===") {
                equal
            } else {
                !equal
            })
        }
        _ => known_bool(expr),
    }
}

#[derive(Debug, Clone, Copy)]
enum SelectorFlow {
    Continue,
    Return(Span),
}

fn selector_return_expression(
    expr: &Expression<'_>,
    selector_symbol: SymbolId,
    selector_value: i64,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> Option<Span> {
    match expr {
        Expression::ConditionalExpression(conditional) => {
            let test = selector_test_value(
                &conditional.test,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )?;
            selector_return_expression(
                if test {
                    &conditional.consequent
                } else {
                    &conditional.alternate
                },
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )
        }
        _ => Some(expr.span()),
    }
}

fn selector_statement_flow(
    statement: &Statement<'_>,
    selector_symbol: SymbolId,
    selector_value: i64,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> Option<SelectorFlow> {
    match statement {
        Statement::BlockStatement(block) => selector_statements_flow(
            &block.body,
            selector_symbol,
            selector_value,
            scoping,
            stable_var_numbers,
        ),
        Statement::IfStatement(branch) => {
            let test = selector_test_value(
                &branch.test,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )?;
            if test {
                selector_statement_flow(
                    &branch.consequent,
                    selector_symbol,
                    selector_value,
                    scoping,
                    stable_var_numbers,
                )
            } else if let Some(alternate) = &branch.alternate {
                selector_statement_flow(
                    alternate,
                    selector_symbol,
                    selector_value,
                    scoping,
                    stable_var_numbers,
                )
            } else {
                Some(SelectorFlow::Continue)
            }
        }
        Statement::ReturnStatement(ret) => {
            let expression = ret.argument.as_ref()?;
            let span = selector_return_expression(
                expression,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )?;
            Some(SelectorFlow::Return(span))
        }
        Statement::EmptyStatement(_) => Some(SelectorFlow::Continue),
        _ => None,
    }
}

fn selector_statements_flow(
    statements: &[Statement<'_>],
    selector_symbol: SymbolId,
    selector_value: i64,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> Option<SelectorFlow> {
    for statement in statements {
        match selector_statement_flow(
            statement,
            selector_symbol,
            selector_value,
            scoping,
            stable_var_numbers,
        )? {
            SelectorFlow::Continue => {}
            returned @ SelectorFlow::Return(_) => return Some(returned),
        }
    }
    Some(SelectorFlow::Continue)
}

#[derive(Default)]
struct SelectorLiteralCollector<'c> {
    scoping: Option<&'c Scoping>,
    selector_symbol: Option<SymbolId>,
    values: HashSet<i64>,
}

impl<'a> Visit<'a> for SelectorLiteralCollector<'_> {
    fn visit_function(&mut self, _function: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {
        // Do not collect selector tests from nested functions.
    }

    fn visit_binary_expression(&mut self, binary: &oxc_ast::ast::BinaryExpression<'a>) {
        if matches!(binary.operator.as_str(), "==" | "===" | "!=" | "!==") {
            let Some(scoping) = self.scoping else {
                return;
            };
            let Some(selector_symbol) = self.selector_symbol else {
                return;
            };
            let left_symbol = selector_identifier_symbol(&binary.left, scoping);
            let right_symbol = selector_identifier_symbol(&binary.right, scoping);
            let literal = if left_symbol == Some(selector_symbol) {
                expression_integer(&binary.right)
            } else if right_symbol == Some(selector_symbol) {
                expression_integer(&binary.left)
            } else {
                None
            };
            if let Some(literal) = literal {
                self.values.insert(literal);
            }
        }
        walk::walk_binary_expression(self, binary);
    }
}

#[derive(Debug, Clone)]
struct SelectorDispatcher {
    params: Vec<String>,
    param_symbols: Vec<SymbolId>,
    returns: HashMap<i64, Span>,
}

struct SelectorDispatcherCollector<'c> {
    scoping: &'c Scoping,
    stable_var_numbers: &'c HashMap<SymbolId, i64>,
    dispatchers: HashMap<SymbolId, SelectorDispatcher>,
}

impl<'a> Visit<'a> for SelectorDispatcherCollector<'_> {
    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if !function.r#async && !function.generator && function.params.rest.is_none() {
            if let (Some(id), Some(body)) = (&function.id, &function.body) {
                if let Some(function_symbol) = id.symbol_id.get() {
                    let binding_is_stable = self
                        .scoping
                        .get_resolved_reference_ids(function_symbol)
                        .iter()
                        .all(|reference_id| {
                            let reference = self.scoping.get_reference(*reference_id);
                            !reference.is_write() && !reference.flags().is_member_write_target()
                        });

                    let params = function
                        .params
                        .items
                        .iter()
                        .map(|param| {
                            if param.initializer.is_some() {
                                return None;
                            }
                            match &param.pattern {
                                BindingPattern::BindingIdentifier(id) => {
                                    Some((id.name.to_string(), id.symbol_id.get()?))
                                }
                                _ => None,
                            }
                        })
                        .collect::<Option<Vec<_>>>();

                    if binding_is_stable && body.directives.is_empty() {
                        if let Some(params) = params {
                            if let Some((_, selector_symbol)) = params.first() {
                                let mut literals = SelectorLiteralCollector {
                                    scoping: Some(self.scoping),
                                    selector_symbol: Some(*selector_symbol),
                                    values: HashSet::new(),
                                };
                                for statement in &body.statements {
                                    literals.visit_statement(statement);
                                }

                                let mut returns = HashMap::new();
                                for value in literals.values {
                                    if let Some(SelectorFlow::Return(span)) =
                                        selector_statements_flow(
                                            &body.statements,
                                            *selector_symbol,
                                            value,
                                            self.scoping,
                                            self.stable_var_numbers,
                                        )
                                    {
                                        returns.insert(value, span);
                                    }
                                }

                                if !returns.is_empty() {
                                    self.dispatchers.insert(
                                        function_symbol,
                                        SelectorDispatcher {
                                            params: params
                                                .iter()
                                                .map(|(name, _)| name.clone())
                                                .collect(),
                                            param_symbols: params
                                                .into_iter()
                                                .map(|(_, symbol)| symbol)
                                                .collect(),
                                            returns,
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_function(self, function, flags);
    }
}

fn collect_selector_dispatchers(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> HashMap<SymbolId, SelectorDispatcher> {
    let mut collector = SelectorDispatcherCollector {
        scoping,
        stable_var_numbers,
        dispatchers: HashMap::new(),
    };
    collector.visit_program(program);
    collector.dispatchers
}

fn parse_i64_literal(text: &str) -> Option<i64> {
    let text = text.trim();
    let (negative, text) = if let Some(rest) = text.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = text.strip_prefix('+') {
        (false, rest)
    } else {
        (false, text)
    };
    let value = if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        i64::from_str_radix(hex, 16).ok()?
    } else {
        text.parse::<i64>().ok()?
    };
    Some(if negative { -value } else { value })
}

fn js_parse_int(text: &str, radix: u32) -> Option<f64> {
    if !(2..=36).contains(&radix) {
        return None;
    }
    let text = text.trim_start();
    let (negative, text) = if let Some(rest) = text.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = text.strip_prefix('+') {
        (false, rest)
    } else {
        (false, text)
    };
    let mut value = 0u64;
    let mut digits = 0usize;
    for ch in text.chars() {
        let Some(digit) = ch.to_digit(radix) else {
            break;
        };
        value = value.checked_mul(radix as u64)?.checked_add(digit as u64)?;
        digits += 1;
    }
    if digits == 0 {
        return None;
    }
    let value = value as f64;
    Some(if negative { -value } else { value })
}

struct RotationExprParser<'a, 'd> {
    source: &'a str,
    pos: usize,
    alias: &'a str,
    decoder: &'d Decoder,
    rotation: usize,
}

impl RotationExprParser<'_, '_> {
    fn rest(&self) -> &str {
        &self.source[self.pos..]
    }

    fn skip_ws(&mut self) {
        while let Some(ch) = self.rest().chars().next() {
            if !ch.is_whitespace() {
                break;
            }
            self.pos += ch.len_utf8();
        }
    }

    fn eat(&mut self, text: &str) -> bool {
        self.skip_ws();
        if self.rest().starts_with(text) {
            self.pos += text.len();
            true
        } else {
            false
        }
    }

    fn ident(&mut self) -> Option<String> {
        self.skip_ws();
        let rest = self.rest();
        let mut len = 0usize;
        for (i, ch) in rest.char_indices() {
            let valid = if i == 0 {
                ch == '_' || ch == '$' || ch.is_ascii_alphabetic()
            } else {
                ch == '_' || ch == '$' || ch.is_ascii_alphanumeric()
            };
            if !valid {
                break;
            }
            len = i + ch.len_utf8();
        }
        if len == 0 {
            return None;
        }
        let value = rest[..len].to_string();
        self.pos += len;
        Some(value)
    }

    fn number(&mut self) -> Option<f64> {
        self.skip_ws();
        let rest = self.rest();
        if rest.starts_with("0x") || rest.starts_with("0X") {
            let digits = rest[2..]
                .bytes()
                .take_while(|byte| byte.is_ascii_hexdigit())
                .count();
            if digits == 0 {
                return None;
            }
            let len = 2 + digits;
            let value = i64::from_str_radix(&rest[2..len], 16).ok()? as f64;
            self.pos += len;
            return Some(value);
        }

        let bytes = rest.as_bytes();
        let mut len = 0usize;
        while len < bytes.len() && bytes[len].is_ascii_digit() {
            len += 1;
        }
        if len < bytes.len() && bytes[len] == b'.' {
            len += 1;
            while len < bytes.len() && bytes[len].is_ascii_digit() {
                len += 1;
            }
        }
        if len < bytes.len() && matches!(bytes[len], b'e' | b'E') {
            let exp_start = len;
            len += 1;
            if len < bytes.len() && matches!(bytes[len], b'+' | b'-') {
                len += 1;
            }
            let digits_start = len;
            while len < bytes.len() && bytes[len].is_ascii_digit() {
                len += 1;
            }
            if digits_start == len {
                len = exp_start;
            }
        }
        if len == 0 {
            return None;
        }
        let value = rest[..len].parse().ok()?;
        self.pos += len;
        Some(value)
    }

    fn signed_integer(&mut self) -> Option<i64> {
        self.skip_ws();
        let start = self.pos;
        if self.eat("-") || self.eat("+") {
            self.skip_ws();
        }
        let rest = self.rest();
        let len = if rest.starts_with("0x") || rest.starts_with("0X") {
            let digits = rest[2..]
                .bytes()
                .take_while(|byte| byte.is_ascii_hexdigit())
                .count();
            if digits == 0 {
                self.pos = start;
                return None;
            }
            2 + digits
        } else {
            let digits = rest
                .bytes()
                .take_while(|byte| byte.is_ascii_digit())
                .count();
            if digits == 0 {
                self.pos = start;
                return None;
            }
            digits
        };
        self.pos += len;
        parse_i64_literal(&self.source[start..self.pos].replace(char::is_whitespace, ""))
    }

    fn decoder_call(&mut self) -> Option<String> {
        let name = self.ident()?;
        if name != self.alias || !self.eat("(") {
            return None;
        }
        let raw = self.signed_integer()?;
        if !self.eat(")") {
            return None;
        }
        let value = self.decoder.value_for_raw_rotated(raw, self.rotation)?;
        match value {
            Value::String(value) => Some(value),
            value => value.js_string(),
        }
    }

    fn factor(&mut self) -> Option<f64> {
        self.skip_ws();
        if self.eat("(") {
            let value = self.expr()?;
            if !self.eat(")") {
                return None;
            }
            return Some(value);
        }
        if self.eat("+") {
            return self.factor();
        }
        if self.eat("-") {
            return self.factor().map(|value| -value);
        }

        let before = self.pos;
        if let Some(name) = self.ident() {
            if name == "parseInt" && self.eat("(") {
                let decoded = self.decoder_call()?;
                let radix = if self.eat(",") {
                    let radix = self.signed_integer()?;
                    u32::try_from(radix).ok()?
                } else {
                    10
                };
                if !self.eat(")") {
                    return None;
                }
                return js_parse_int(&decoded, radix);
            }
            self.pos = before;
        }
        self.number()
    }

    fn term(&mut self) -> Option<f64> {
        let mut value = self.factor()?;
        loop {
            if self.eat("*") {
                value *= self.factor()?;
            } else if self.eat("/") {
                value /= self.factor()?;
            } else if self.eat("%") {
                value %= self.factor()?;
            } else {
                break;
            }
        }
        Some(value)
    }

    fn expr(&mut self) -> Option<f64> {
        let mut value = self.term()?;
        loop {
            if self.eat("+") {
                value += self.term()?;
            } else if self.eat("-") {
                value -= self.term()?;
            } else {
                break;
            }
        }
        Some(value)
    }
}

fn eval_rotation_checksum(
    expression: &str,
    alias: &str,
    decoder: &Decoder,
    rotation: usize,
) -> Option<f64> {
    let mut parser = RotationExprParser {
        source: expression,
        pos: 0,
        alias,
        decoder,
        rotation,
    };
    let value = parser.expr()?;
    parser.skip_ws();
    (parser.pos == expression.len()).then_some(value)
}

#[derive(Debug, Clone)]
struct RotationIife {
    provider: String,
    target: i64,
    body_span: Span,
    statement_span: Span,
}

fn rotation_iife_function<'a>(expr: &'a Expression<'a>) -> Option<&'a oxc_ast::ast::Function<'a>> {
    match expr {
        Expression::FunctionExpression(function) => Some(function),
        Expression::ParenthesizedExpression(parenthesized) => {
            rotation_iife_function(&parenthesized.expression)
        }
        _ => None,
    }
}

fn rotation_iife_call<'a>(expr: &'a Expression<'a>) -> Option<&'a CallExpression<'a>> {
    match expr {
        Expression::CallExpression(call) => Some(call),
        Expression::ParenthesizedExpression(parenthesized) => {
            rotation_iife_call(&parenthesized.expression)
        }
        _ => None,
    }
}

#[derive(Default)]
struct RotationIifeCollector {
    out: Vec<RotationIife>,
}

impl<'a> Visit<'a> for RotationIifeCollector {
    fn visit_expression_statement(&mut self, it: &ExpressionStatement<'a>) {
        let Some(call) = rotation_iife_call(&it.expression) else {
            walk::walk_expression_statement(self, it);
            return;
        };
        if !call.optional && call.arguments.len() == 2 {
            let provider = match &call.arguments[0] {
                Argument::Identifier(identifier) => Some(identifier.name.to_string()),
                _ => None,
            };
            let target = argument_integer(&call.arguments[1]);
            let function = rotation_iife_function(&call.callee);
            if let (Some(provider), Some(target), Some(function)) = (provider, target, function) {
                if !function.r#async && !function.generator && function.params.items.len() == 2 {
                    if let Some(body) = &function.body {
                        self.out.push(RotationIife {
                            provider,
                            target,
                            body_span: body.span,
                            statement_span: it.span,
                        });
                    }
                }
            }
        }
        walk::walk_expression_statement(self, it);
    }
}

fn collect_rotation_iifes(program: &oxc_ast::ast::Program<'_>) -> Vec<RotationIife> {
    let mut collector = RotationIifeCollector::default();
    collector.visit_program(program);
    collector.out
}

fn apply_proven_decoder_rotations(
    source: &str,
    decoders: &mut HashMap<String, Decoder>,
    rotation_iifes: &[RotationIife],
) -> (Vec<(usize, usize)>, Vec<Replacement>) {
    let checksum_re = regex::Regex::new(
        r#"(?s)\btry\s*\{\s*(?:var|let|const)\s+[A-Za-z_$][A-Za-z0-9_$]*\s*=\s*(?P<expr>[^;]+);"#,
    )
    .unwrap();
    let mut protected_spans = Vec::new();
    let mut proven_iifes: Vec<(String, usize, usize)> = Vec::new();

    for iife in rotation_iifes {
        let body = fragment(source, iife.body_span);
        if !body.contains("push") || !body.contains("shift") {
            continue;
        }
        let Some(checksum) = checksum_re.captures(body) else {
            continue;
        };
        let expression = &checksum["expr"];
        let mut proven_here = false;

        for (decoder_name, decoder) in decoders.iter_mut() {
            if decoder.provider != iife.provider || decoder.values.is_empty() {
                continue;
            }
            let alias_re = regex::Regex::new(&format!(
                r#"\b(?:var|let|const)\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*{}\b"#,
                regex::escape(decoder_name)
            ))
            .unwrap();
            let alias = if let Some(alias_caps) = alias_re.captures(body) {
                alias_caps[1].to_string()
            } else if body.contains(&format!("{decoder_name}(")) {
                decoder_name.clone()
            } else {
                continue;
            };

            let mut matches = Vec::new();
            for rotation in 0..decoder.values.len() {
                let Some(value) = eval_rotation_checksum(expression, &alias, decoder, rotation)
                else {
                    continue;
                };
                if value.is_finite() && (value - iife.target as f64).abs() < 1e-9 {
                    matches.push(rotation);
                    if matches.len() > 1 {
                        break;
                    }
                }
            }
            if matches.len() == 1 {
                proven_here = true;
                if matches[0] != 0 {
                    decoder.values.rotate_left(matches[0]);
                }
            }
        }

        if proven_here {
            let start = iife.statement_span.start as usize;
            let end = iife.statement_span.end as usize;
            protected_spans.push((start, end));
            proven_iifes.push((iife.provider.clone(), start, end));
        }
    }

    // Materialization is stricter than decoding. Every detected decoder sharing
    // a provider must agree on the same final rotated table and the same literal
    // array span. If that cannot be proved, keep the runtime IIFE intact.
    let proven_providers = proven_iifes
        .iter()
        .map(|(provider, _, _)| provider.clone())
        .collect::<HashSet<_>>();
    let mut materialized: HashMap<String, (Span, Vec<Value>)> = HashMap::new();
    let mut inconsistent = HashSet::new();
    for decoder in decoders.values() {
        if !proven_providers.contains(&decoder.provider) {
            continue;
        }
        match materialized.get(&decoder.provider) {
            None => {
                materialized.insert(
                    decoder.provider.clone(),
                    (decoder.provider_array_span, decoder.values.clone()),
                );
            }
            Some((span, values))
                if *span == decoder.provider_array_span && same_values(values, &decoder.values) => {
            }
            Some(_) => {
                inconsistent.insert(decoder.provider.clone());
            }
        }
    }
    for provider in &inconsistent {
        materialized.remove(provider);
    }

    let mut replacements = Vec::new();
    for (provider, (array_span, values)) in materialized {
        let Some(array_text) = render_value_array(&values) else {
            continue;
        };
        replacements.push(Replacement {
            start: array_span.start as usize,
            end: array_span.end as usize,
            text: array_text,
            kind: "materialize_decoder_rotation",
            arithmetic_state_proof: None,
        });
        for (_, start, end) in proven_iifes
            .iter()
            .filter(|(iife_provider, _, _)| iife_provider.as_str() == provider.as_str())
        {
            replacements.push(Replacement {
                start: *start,
                end: *end,
                text: String::new(),
                kind: "remove_decoder_rotation_iife",
                arithmetic_state_proof: None,
            });
        }
    }

    (protected_spans, replacements)
}

type DecoderDetection = (
    HashMap<SymbolId, Decoder>,
    Vec<(usize, usize)>,
    Vec<Replacement>,
);

fn detect_decoders(
    source: &str,
    functions: &[FnInfo],
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> DecoderDetection {
    let local_re = regex::Regex::new(
        r"\b(?:const|let|var)\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*([A-Za-z_$][A-Za-z0-9_$]*)\(\)\s*;",
    )
    .unwrap();
    let offset_re = regex::Regex::new(
        r"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*-\s*(0[xX][0-9A-Fa-f]+|[0-9]+)\s*;",
    )
    .unwrap();
    let index_re = regex::Regex::new(
        r"\b(?:let|const|var)\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*([A-Za-z_$][A-Za-z0-9_$]*)\[([A-Za-z_$][A-Za-z0-9_$]*)\]\s*;",
    )
    .unwrap();

    let mut name_counts: HashMap<String, usize> = HashMap::new();
    for f in functions {
        *name_counts.entry(f.name.clone()).or_default() += 1;
    }

    let mut providers = HashMap::new();
    for f in functions {
        if !f.params.is_empty() {
            continue;
        }
        let body = fragment(source, f.span);
        if (!body.contains(&format!("{} = function", f.name))
            && !body.contains(&format!("{}=function", f.name)))
            || !body.contains(&format!("return {}();", f.name))
        {
            continue;
        }
        for (array_name, values) in &f.static_arrays {
            if body.contains(&format!("return {array_name};")) {
                providers.insert((f.scope, f.name.clone()), values.clone());
                break;
            }
        }
    }

    let mut by_name = HashMap::new();
    for f in functions {
        if f.params.is_empty() {
            continue;
        }
        let body = fragment(source, f.span);
        let Some(local) = local_re.captures(body) else {
            continue;
        };
        let local_array = local[1].to_string();
        let provider = local[2].to_string();
        // Rotation proof below is textual. Fail closed if either function name
        // occurs in more than one lexical scope, so a sibling IIFE cannot
        // accidentally supply another decoder's rotation.
        if name_counts.get(&f.name).copied() != Some(1)
            || name_counts.get(&provider).copied() != Some(1)
        {
            continue;
        }
        let Some(provider_info) = providers.get(&(f.scope, provider.clone())) else {
            continue;
        };
        let Some(off) = offset_re.captures(body) else {
            continue;
        };
        if off[1] != off[2] {
            continue;
        }
        let param = off[1].to_string();
        let Some(public_param) = f.params.first() else {
            continue;
        };
        let Some(offset) = parse_i64_literal(&off[3]) else {
            continue;
        };
        let Some(index) = index_re.captures(body) else {
            continue;
        };
        if index[2] != local_array || index[3] != param {
            continue;
        }
        let value_var = index[1].to_string();
        let bare_value_return = body.contains(&format!("return {value_var};"));
        let sequence_value_return =
            body.contains(&format!(", {value_var};")) || body.contains(&format!(",{value_var};"));

        let installs_replacement_re = regex::Regex::new(&format!(
            r#"\b{}\s*=\s*function\s*\(\s*{}\b"#,
            regex::escape(&f.name),
            regex::escape(&param),
        ))
        .unwrap();
        let tail_calls_public_re = regex::Regex::new(&format!(
            r#"(?:\breturn\b|,)\s*{}\s*\(\s*{}\b"#,
            regex::escape(&f.name),
            regex::escape(public_param),
        ))
        .unwrap();
        let self_rewriting =
            installs_replacement_re.is_match(body) && tail_calls_public_re.is_match(body);

        // Some javascript-obfuscator-style outputs use the simpler, equally
        // static shape directly instead of installing a memoizing replacement:
        //
        //   function d(i, unused) {
        //     i = i - 123;
        //     const table = provider();
        //     let value = table[i];
        //     return value;
        //   }
        //
        // Match the complete function body rather than merely looking for the
        // three ingredients, so arbitrary application array accessors are not
        // promoted to decoders.
        let direct_re = regex::Regex::new(&format!(
            r#"(?s)^\s*function\s+{}\s*\([^)]*\)\s*\{{\s*{}\s*=\s*{}\s*-\s*(?:0[xX][0-9A-Fa-f]+|[0-9]+)\s*;\s*(?:const|let|var)\s+{}\s*=\s*{}\s*\(\s*\)\s*;\s*(?:const|let|var)\s+{}\s*=\s*{}\s*\[\s*{}\s*\]\s*;\s*return\s+{}\s*;\s*\}}\s*$"#,
            regex::escape(&f.name),
            regex::escape(&param),
            regex::escape(&param),
            regex::escape(&local_array),
            regex::escape(&provider),
            regex::escape(&value_var),
            regex::escape(&local_array),
            regex::escape(&param),
            regex::escape(&value_var),
        ))
        .unwrap();
        let direct_index = direct_re.is_match(body);

        if !direct_index && !(self_rewriting && (bare_value_return || sequence_value_return)) {
            continue;
        }

        let transform = if body
            .contains("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/=")
            && body.contains("decodeURIComponent")
        {
            // Recognize the pure javascript-obfuscator Base64 -> percent-URI
            // decoder by its actual dataflow ingredients, not by whether the
            // source happens to be minified. Some variants add a source-text
            // self-defence gate whose result depends on Function#toString /
            // line layout. Those introduce an additional charCodeAt probe.
            //
            // Requiring exactly the one charCodeAt used by the final
            // percent-encoding loop accepts clean formatted decoders such as
            // current aclib/suv5 while failing closed on the guarded variant.
            let char_code_at_count = body.matches(".charCodeAt(").count();
            let base64_uri_shape = body.contains(".charAt(")
                && body.contains(".indexOf(")
                && body.contains("String.fromCharCode")
                && body.contains(".toString(16)");
            if !base64_uri_shape || char_code_at_count == 0 {
                continue;
            }

            // A single charCodeAt is the ordinary percent-encoding loop and is
            // source-layout independent. Extra charCodeAt probes are treated as
            // source-sensitive self-defence: retain the historical proof that
            // they are safe only when the exact decoder representation is one
            // physical line.
            if char_code_at_count > 1 && (body.contains('\n') || body.contains('\r')) {
                continue;
            }
            DecoderTransform::LowerAlphabetBase64Uri
        } else {
            DecoderTransform::Plain
        };

        by_name.insert(
            f.name.clone(),
            Decoder {
                values: provider_info.values.clone(),
                offset,
                provider,
                provider_array_span: provider_info.span,
                transform,
            },
        );
    }

    let rotation_iifes = collect_rotation_iifes(program);
    let (protected_spans, rotation_replacements) =
        apply_proven_decoder_rotations(source, &mut by_name, &rotation_iifes);

    let mut out = HashMap::new();
    for f in functions {
        if let Some(decoder) = by_name.get(&f.name) {
            out.insert(f.symbol, decoder.clone());
        }
    }

    let aliases = collect_symbol_aliases(program, scoping);
    loop {
        let mut changed = false;
        for (alias_symbol, target_symbol) in &aliases {
            if out.contains_key(alias_symbol) {
                continue;
            }
            if let Some(decoder) = out.get(target_symbol).cloned() {
                out.insert(*alias_symbol, decoder);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    (out, protected_spans, rotation_replacements)
}

struct SymbolAliasCollector<'s> {
    scoping: &'s Scoping,
    aliases: Vec<(SymbolId, SymbolId)>,
}

impl<'a> Visit<'a> for SymbolAliasCollector<'_> {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        // Decoder aliases are only propagated when JavaScript itself proves
        // the binding cannot later be rebound. This keeps the transform
        // fail-closed without needing a second write-analysis pass.
        if it.kind != VariableDeclarationKind::Const {
            walk::walk_variable_declaration(self, it);
            return;
        }
        for d in &it.declarations {
            let BindingPattern::BindingIdentifier(alias) = &d.id else {
                continue;
            };
            let Some(alias_symbol) = alias.symbol_id.get() else {
                continue;
            };
            let Some(Expression::Identifier(target)) = &d.init else {
                continue;
            };
            let Some(reference_id) = target.reference_id.get() else {
                continue;
            };
            let Some(target_symbol) = self.scoping.get_reference(reference_id).symbol_id() else {
                continue;
            };
            self.aliases.push((alias_symbol, target_symbol));
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn collect_symbol_aliases(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> Vec<(SymbolId, SymbolId)> {
    let mut collector = SymbolAliasCollector {
        scoping,
        aliases: Vec::new(),
    };
    collector.visit_program(program);
    collector.aliases
}

fn static_dispatch_order(expr: &Expression<'_>) -> Option<Vec<String>> {
    match expr {
        Expression::ArrayExpression(array) => {
            let values = array
                .elements
                .iter()
                .map(array_element)
                .collect::<Option<Vec<_>>>()?;
            let order = values
                .iter()
                .map(Value::js_string)
                .collect::<Option<Vec<_>>>()?;
            (order.len() >= 2).then_some(order)
        }
        Expression::CallExpression(call)
            if !call.optional && call.arguments.len() == 1 && !call.arguments[0].is_spread() =>
        {
            let Expression::StaticMemberExpression(member) = &call.callee else {
                return None;
            };
            if member.optional || member.property.name.as_str() != "split" {
                return None;
            }
            let Expression::StringLiteral(source) = &member.object else {
                return None;
            };
            let argument = call.arguments[0].as_expression()?;
            let Expression::StringLiteral(separator) = argument else {
                return None;
            };
            let separator = separator.value.as_str();
            if separator.len() != 1 || !separator.is_ascii() {
                return None;
            }
            let order = source
                .value
                .as_str()
                .split(separator)
                .map(str::to_string)
                .collect::<Vec<_>>();
            (order.len() >= 2).then_some(order)
        }
        _ => None,
    }
}

#[derive(Default)]
struct DispatchBindingCollector {
    orders: HashMap<SymbolId, Vec<String>>,
    zero_counters: HashSet<SymbolId>,
}

impl<'a> Visit<'a> for DispatchBindingCollector {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        for declarator in &it.declarations {
            let BindingPattern::BindingIdentifier(id) = &declarator.id else {
                continue;
            };
            let Some(symbol) = id.symbol_id.get() else {
                continue;
            };
            let Some(init) = &declarator.init else {
                continue;
            };

            if let Some(order) = static_dispatch_order(init) {
                self.orders.insert(symbol, order);
            }
            if matches!(eval(init), Some(Value::Number(n)) if n == 0.0) {
                self.zero_counters.insert(symbol);
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn collect_dispatch_bindings(
    program: &oxc_ast::ast::Program<'_>,
) -> (HashMap<SymbolId, Vec<String>>, HashSet<SymbolId>) {
    let mut collector = DispatchBindingCollector::default();
    collector.visit_program(program);
    (collector.orders, collector.zero_counters)
}

#[derive(Debug, Clone)]
enum ProxyProperty {
    Literal(Value),
    Unary { operator: String },
    Binary { operator: String },
    StaticMember { property: String },
    ComputedMember,
    Call { arity: usize },
}

fn proxy_literal_kind(value: &Value) -> &'static str {
    if matches!(value, Value::String(_)) {
        "proxy_string"
    } else {
        "proxy_literal"
    }
}

#[derive(Debug, Clone)]
struct ProxyObject {
    properties: HashMap<String, ProxyProperty>,
}

#[derive(Default)]
struct MemberReferenceCollector {
    refs: HashMap<ReferenceId, u32>,
}

impl MemberReferenceCollector {
    fn record_object(&mut self, object: &Expression<'_>) {
        let Expression::Identifier(id) = object else {
            return;
        };
        if let Some(reference_id) = id.reference_id.get() {
            self.refs.insert(reference_id, id.span.start);
        }
    }
}

impl<'a> Visit<'a> for MemberReferenceCollector {
    fn visit_static_member_expression(&mut self, it: &StaticMemberExpression<'a>) {
        self.record_object(&it.object);
        walk::walk_static_member_expression(self, it);
    }

    fn visit_computed_member_expression(&mut self, it: &ComputedMemberExpression<'a>) {
        self.record_object(&it.object);
        walk::walk_computed_member_expression(self, it);
    }
}

fn direct_identifier_name<'a>(expr: &'a Expression<'a>) -> Option<&'a str> {
    match expr {
        Expression::Identifier(id) => Some(id.name.as_str()),
        _ => None,
    }
}

fn analyze_proxy_return(
    params: &oxc_ast::ast::FormalParameters<'_>,
    returned: &Expression<'_>,
) -> Option<ProxyProperty> {
    if params.items.is_empty() || params.rest.is_some() {
        return None;
    }
    let params = params
        .items
        .iter()
        .map(|param| match &param.pattern {
            BindingPattern::BindingIdentifier(id) => Some(id.name.as_str()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;

    if params.len() == 1 {
        if let Expression::UnaryExpression(unary) = returned {
            let operator = unary.operator.as_str();
            if matches!(operator, "!" | "+" | "-" | "~" | "void")
                && direct_identifier_name(&unary.argument)? == params[0]
            {
                return Some(ProxyProperty::Unary {
                    operator: operator.to_string(),
                });
            }
        }
    }

    if params.len() == 1 {
        if let Expression::StaticMemberExpression(member) = returned {
            if !member.optional && direct_identifier_name(&member.object)? == params[0] {
                return Some(ProxyProperty::StaticMember {
                    property: member.property.name.to_string(),
                });
            }
        }
    }

    if params.len() == 2 {
        if let Expression::ComputedMemberExpression(member) = returned {
            if !member.optional
                && direct_identifier_name(&member.object)? == params[0]
                && direct_identifier_name(&member.expression)? == params[1]
            {
                return Some(ProxyProperty::ComputedMember);
            }
        }

        if let Expression::BinaryExpression(binary) = returned {
            if direct_identifier_name(&binary.left)? == params[0]
                && direct_identifier_name(&binary.right)? == params[1]
            {
                return Some(ProxyProperty::Binary {
                    operator: binary.operator.as_str().to_string(),
                });
            }
        }
    }

    let Expression::CallExpression(call) = returned else {
        return None;
    };
    if call.optional || call.arguments.len() + 1 != params.len() {
        return None;
    }
    if direct_identifier_name(&call.callee)? != params[0] {
        return None;
    }
    for (argument, expected) in call.arguments.iter().zip(params.iter().skip(1)) {
        if argument.is_spread() {
            return None;
        }
        let expression = argument.as_expression()?;
        if direct_identifier_name(expression)? != *expected {
            return None;
        }
    }

    Some(ProxyProperty::Call {
        arity: call.arguments.len(),
    })
}

fn analyze_proxy_function(function: &oxc_ast::ast::Function<'_>) -> Option<ProxyProperty> {
    if function.generator || function.r#async {
        return None;
    }
    let body = function.body.as_ref()?;
    if !body.directives.is_empty() || body.statements.len() != 1 {
        return None;
    }
    let Statement::ReturnStatement(ret) = &body.statements[0] else {
        return None;
    };
    analyze_proxy_return(&function.params, ret.argument.as_ref()?)
}

fn analyze_proxy_arrow(
    function: &oxc_ast::ast::ArrowFunctionExpression<'_>,
) -> Option<ProxyProperty> {
    if function.r#async || !function.body.directives.is_empty() {
        return None;
    }

    if let Some(returned) = function.get_expression() {
        return analyze_proxy_return(&function.params, returned);
    }

    if function.body.statements.len() != 1 {
        return None;
    }
    let Statement::ReturnStatement(ret) = &function.body.statements[0] else {
        return None;
    };
    analyze_proxy_return(&function.params, ret.argument.as_ref()?)
}

fn analyze_proxy_object(
    object: &oxc_ast::ast::ObjectExpression<'_>,
) -> HashMap<String, ProxyProperty> {
    let mut properties = HashMap::new();
    for item in &object.properties {
        let oxc_ast::ast::ObjectPropertyKind::ObjectProperty(prop) = item else {
            continue;
        };
        if prop.kind != PropertyKind::Init || prop.computed || prop.method || prop.shorthand {
            continue;
        }
        let Some(key) = prop.key.static_name().map(|name| name.into_owned()) else {
            continue;
        };
        if let Some(value) = eval(&prop.value) {
            properties.insert(key, ProxyProperty::Literal(value));
            continue;
        }
        let proxy = match &prop.value {
            Expression::FunctionExpression(function) => analyze_proxy_function(function),
            Expression::ArrowFunctionExpression(function) => analyze_proxy_arrow(function),
            _ => None,
        };
        if let Some(proxy) = proxy {
            properties.insert(key, proxy);
        }
    }
    properties
}

struct ProxyObjectCollector<'s, 'c> {
    scoping: &'c Scoping,
    member_refs: &'s HashMap<ReferenceId, u32>,
    objects: HashMap<SymbolId, ProxyObject>,
}

impl<'a> Visit<'a> for ProxyObjectCollector<'_, '_> {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        for d in &it.declarations {
            let BindingPattern::BindingIdentifier(id) = &d.id else {
                continue;
            };
            let Some(symbol) = id.symbol_id.get() else {
                continue;
            };
            let Some(Expression::ObjectExpression(object)) = &d.init else {
                continue;
            };

            let refs = self.scoping.get_resolved_reference_ids(symbol);
            if refs.is_empty() {
                continue;
            }
            let safe = refs.iter().all(|reference_id| {
                let reference = self.scoping.get_reference(*reference_id);
                !reference.is_write()
                    && !reference.flags().is_member_write_target()
                    && self
                        .member_refs
                        .get(reference_id)
                        .is_some_and(|start| *start >= d.span.end)
            });
            if !safe {
                continue;
            }

            let properties = analyze_proxy_object(object);
            if !properties.is_empty() {
                self.objects.insert(symbol, ProxyObject { properties });
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn collect_proxy_objects(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, ProxyObject> {
    let mut member_collector = MemberReferenceCollector::default();
    member_collector.visit_program(program);

    let mut collector = ProxyObjectCollector {
        scoping,
        member_refs: &member_collector.refs,
        objects: HashMap::new(),
    };
    collector.visit_program(program);
    collector.objects
}

fn static_proxy_member<'a>(
    expr: &'a Expression<'a>,
    scoping: &Scoping,
) -> Option<(SymbolId, String)> {
    match expr {
        Expression::StaticMemberExpression(member) if !member.optional => Some((
            symbol_of(scoping, &member.object)?,
            member.property.name.to_string(),
        )),
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Value::String(key) = eval(&member.expression)? else {
                return None;
            };
            Some((symbol_of(scoping, &member.object)?, key))
        }
        _ => None,
    }
}

#[derive(Default)]
struct ReferenceSpanCollector {
    spans: HashMap<ReferenceId, Span>,
}

impl<'a> Visit<'a> for ReferenceSpanCollector {
    fn visit_identifier_reference(&mut self, it: &oxc_ast::ast::IdentifierReference<'a>) {
        if let Some(reference_id) = it.reference_id.get() {
            self.spans.insert(reference_id, it.span);
        }
    }
}

fn collect_reference_spans(program: &oxc_ast::ast::Program<'_>) -> HashMap<ReferenceId, Span> {
    let mut collector = ReferenceSpanCollector::default();
    collector.visit_program(program);
    collector.spans
}

#[derive(Default)]
struct ShorthandCollector {
    spans: HashSet<(u32, u32)>,
}

impl<'a> Visit<'a> for ShorthandCollector {
    fn visit_object_property(&mut self, it: &oxc_ast::ast::ObjectProperty<'a>) {
        if it.shorthand {
            let span = it.value.span();
            self.spans.insert((span.start, span.end));
        }
        walk::walk_object_property(self, it);
    }
}

fn collect_shorthand_spans(program: &oxc_ast::ast::Program<'_>) -> HashSet<(u32, u32)> {
    let mut collector = ShorthandCollector::default();
    collector.visit_program(program);
    collector.spans
}

#[derive(Debug, Clone)]
struct ReferenceIdentityTable {
    rows: u32,
    columns: u32,
    root_row: u32,
    column_multiplier: u32,
    row_multiplier: u32,
    salt_left: u32,
    salt_right: u32,
    construction_start: usize,
    construction_end: usize,
}

impl ReferenceIdentityTable {
    fn row_for(&self, row: u32, column: u32) -> Option<u32> {
        if row >= self.rows || column >= self.columns || !self.rows.is_power_of_two() {
            return None;
        }
        let column_term = js_to_uint32(self.column_multiplier as f64 * column as f64);
        let row_term = js_to_uint32(self.row_multiplier as f64 * row as f64);
        let salt_term = js_to_uint32(self.salt_left as f64 * self.salt_right as f64);
        Some((column_term ^ row_term ^ salt_term) & (self.rows - 1))
    }

    fn identity_for(&self, first: u32, second: u32) -> Option<u32> {
        let row = self.row_for(self.root_row, first)?;
        self.row_for(row, second)
    }
}

fn unique_symbol_named_near(
    scoping: &Scoping,
    name: &str,
    start: u32,
    end: u32,
) -> Option<SymbolId> {
    let mut matches = scoping.symbol_ids().filter(|symbol| {
        scoping.symbol_name(*symbol) == name && {
            let span = scoping.symbol_span(*symbol);
            start <= span.start && span.end <= end
        }
    });
    let symbol = matches.next()?;
    matches.next().is_none().then_some(symbol)
}

fn detect_reference_identity_tables(
    source: &str,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<SymbolId, ReferenceIdentityTable> {
    let identifier = r"[A-Za-z_$][A-Za-z0-9_$]*";
    let ws = r"\s*";
    let row_re = regex::Regex::new(&format!(
        r"(?P<table>{identifier}){ws}={ws}\[\]{ws},{ws}(?P<idx>{identifier}){ws}={ws}0{ws};{ws}(?P<test>{identifier}){ws}<{ws}(?P<rows>\d+){ws};{ws}(?P<update>{identifier}){ws}\+\+{ws}\){ws}(?P<table2>{identifier}){ws}\[{ws}(?P<idx2>{identifier}){ws}\]{ws}={ws}new{ws}Array{ws}\({ws}(?P<columns>\d+){ws}\)"
    ))
    .unwrap();
    let timer_re = regex::Regex::new(&format!(
        r"(?P<timer>{identifier}){ws}={ws}function{ws}\({ws}(?P<arg>{identifier}){ws}\){ws}\{{{ws}setTimeout{ws}\({ws}(?P<arg2>{identifier}){ws},{ws}0{ws}\){ws};?{ws}\}}"
    ))
    .unwrap();
    let outer_re = regex::Regex::new(&format!(
        r"for{ws}\({ws}var\s+(?P<loop>{identifier}){ws}={ws}0{ws};{ws}(?P<test>{identifier}){ws}<{ws}(?P<chunks>\d+){ws};{ws}(?P<update>{identifier}){ws}\+\+{ws}\){ws}\({ws}\(?{ws}(?P<callback>{identifier}){ws}\)?{ws}=>{ws}\{{{ws}(?P<timer>{identifier}){ws}\({ws}function{ws}\({ws}\){ws}\{{"
    ))
    .unwrap();
    let fill_re = regex::Regex::new(&format!(
        r"for{ws}\({ws}var\s+(?P<t>{identifier}){ws}={ws}(?P<chunk>\d+){ws}\*{ws}(?P<callback>{identifier}){ws},{ws}(?P<n>{identifier}){ws}={ws}Math{ws}\.{ws}min{ws}\({ws}(?P<t2>{identifier}){ws}\+{ws}(?P<chunk2>\d+){ws},{ws}(?P<columns>\d+){ws}\){ws},{ws}(?P<column>{identifier}){ws}={ws}(?P<t3>{identifier}){ws};{ws}(?P<column2>{identifier}){ws}<{ws}(?P<n2>{identifier}){ws};{ws}(?P<column3>{identifier}){ws}\+\+{ws}\){ws}for{ws}\({ws}(?P<row>{identifier}){ws}={ws}0{ws};{ws}(?P<row2>{identifier}){ws}<{ws}(?P<rows>\d+){ws};{ws}(?P<row3>{identifier}){ws}\+\+{ws}\){ws}(?P<table>{identifier}){ws}\[{ws}(?P<row4>{identifier}){ws}\]{ws}\[{ws}(?P<column4>{identifier}){ws}\]{ws}={ws}(?P<table2>{identifier}){ws}\[{ws}\({ws}(?P<a>\d+){ws}\*{ws}(?P<column5>{identifier}){ws}\^{ws}(?P<b>\d+){ws}\*{ws}(?P<row5>{identifier}){ws}\^{ws}(?P<c>\d+){ws}\*{ws}(?P<k>\d+){ws}\){ws}>>>{ws}0{ws}&{ws}(?P<mask>\d+){ws}-{ws}1{ws}\]"
    ))
    .unwrap();
    let root_re = regex::Regex::new(&format!(
        r"(?P<timer>{identifier}){ws}\({ws}function{ws}\({ws}\){ws}\{{{ws}(?P<target>{identifier}){ws}={ws}(?P<table>{identifier}){ws}\[{ws}(?P<root>\d+){ws}\]{ws};?{ws}\}}{ws}\)"
    ))
    .unwrap();

    let mut out = HashMap::new();
    for row_caps in row_re.captures_iter(source) {
        let row_match = row_caps.get(0).unwrap();
        let table_name = row_caps.name("table").unwrap().as_str();
        let row_index = row_caps.name("idx").unwrap().as_str();
        if row_caps.name("test").unwrap().as_str() != row_index
            || row_caps.name("update").unwrap().as_str() != row_index
            || row_caps.name("idx2").unwrap().as_str() != row_index
            || row_caps.name("table2").unwrap().as_str() != table_name
        {
            continue;
        }
        let Ok(rows) = row_caps.name("rows").unwrap().as_str().parse::<u32>() else {
            continue;
        };
        let Ok(columns) = row_caps.name("columns").unwrap().as_str().parse::<u32>() else {
            continue;
        };
        if rows < 2 || columns < 2 || !rows.is_power_of_two() {
            continue;
        }

        let window_start = row_match.start().saturating_sub(256);
        let window_end = (row_match.end() + 1800).min(source.len());
        let window = &source[window_start..window_end];

        let Some(timer_caps) = timer_re.captures(window) else {
            continue;
        };
        if timer_caps.name("arg").unwrap().as_str() != timer_caps.name("arg2").unwrap().as_str() {
            continue;
        }
        let timer_name = timer_caps.name("timer").unwrap().as_str();

        let Some(outer_caps) = outer_re.captures(window) else {
            continue;
        };
        let outer_loop = outer_caps.name("loop").unwrap().as_str();
        if outer_caps.name("test").unwrap().as_str() != outer_loop
            || outer_caps.name("update").unwrap().as_str() != outer_loop
            || outer_caps.name("timer").unwrap().as_str() != timer_name
        {
            continue;
        }
        let callback_name = outer_caps.name("callback").unwrap().as_str();
        let Ok(chunks) = outer_caps.name("chunks").unwrap().as_str().parse::<u32>() else {
            continue;
        };

        let Some(fill_caps) = fill_re.captures(window) else {
            continue;
        };
        if fill_caps.name("callback").unwrap().as_str() != callback_name
            || fill_caps.name("table").unwrap().as_str() != table_name
            || fill_caps.name("table2").unwrap().as_str() != table_name
        {
            continue;
        }
        let t_name = fill_caps.name("t").unwrap().as_str();
        let n_name = fill_caps.name("n").unwrap().as_str();
        let column_name = fill_caps.name("column").unwrap().as_str();
        let row_name = fill_caps.name("row").unwrap().as_str();
        if fill_caps.name("t2").unwrap().as_str() != t_name
            || fill_caps.name("t3").unwrap().as_str() != t_name
            || fill_caps.name("n2").unwrap().as_str() != n_name
            || fill_caps.name("column2").unwrap().as_str() != column_name
            || fill_caps.name("column3").unwrap().as_str() != column_name
            || fill_caps.name("column4").unwrap().as_str() != column_name
            || fill_caps.name("column5").unwrap().as_str() != column_name
            || fill_caps.name("row2").unwrap().as_str() != row_name
            || fill_caps.name("row3").unwrap().as_str() != row_name
            || fill_caps.name("row4").unwrap().as_str() != row_name
            || fill_caps.name("row5").unwrap().as_str() != row_name
        {
            continue;
        }

        let Ok(chunk) = fill_caps.name("chunk").unwrap().as_str().parse::<u32>() else {
            continue;
        };
        let Ok(chunk2) = fill_caps.name("chunk2").unwrap().as_str().parse::<u32>() else {
            continue;
        };
        let Ok(fill_columns) = fill_caps.name("columns").unwrap().as_str().parse::<u32>() else {
            continue;
        };
        let Ok(fill_rows) = fill_caps.name("rows").unwrap().as_str().parse::<u32>() else {
            continue;
        };
        let Ok(mask) = fill_caps.name("mask").unwrap().as_str().parse::<u32>() else {
            continue;
        };
        if chunk == 0
            || chunk != chunk2
            || fill_columns != columns
            || fill_rows != rows
            || mask != rows
            || chunks.checked_mul(chunk) != Some(columns)
        {
            continue;
        }

        let Some(root_caps) = root_re.captures(window) else {
            continue;
        };
        if root_caps.name("timer").unwrap().as_str() != timer_name
            || root_caps.name("table").unwrap().as_str() != table_name
        {
            continue;
        }
        let target_name = root_caps.name("target").unwrap().as_str();
        let Ok(root_row) = root_caps.name("root").unwrap().as_str().parse::<u32>() else {
            continue;
        };
        if root_row >= rows {
            continue;
        }

        let absolute_start = window_start as u32;
        let absolute_end = window_end as u32;
        let Some(target_symbol) =
            unique_symbol_named_near(scoping, target_name, absolute_start, absolute_end)
        else {
            continue;
        };
        let Some(table_symbol) =
            unique_symbol_named_near(scoping, table_name, absolute_start, absolute_end)
        else {
            continue;
        };

        let construction_end = (window_start + root_caps.get(0).unwrap().end()) as u32;
        if scoping
            .get_resolved_reference_ids(table_symbol)
            .iter()
            .any(|reference_id| {
                reference_spans
                    .get(reference_id)
                    .is_none_or(|span| span.start < absolute_start || span.end > construction_end)
            })
        {
            continue;
        }
        let target_writes = scoping
            .get_resolved_reference_ids(target_symbol)
            .iter()
            .filter(|reference_id| scoping.get_reference(**reference_id).is_write())
            .count();
        if target_writes != 1 {
            continue;
        }

        let parse_capture = |name: &str| {
            fill_caps
                .name(name)
                .and_then(|capture| capture.as_str().parse::<u32>().ok())
        };
        let (Some(column_multiplier), Some(row_multiplier), Some(salt_left), Some(salt_right)) = (
            parse_capture("a"),
            parse_capture("b"),
            parse_capture("c"),
            parse_capture("k"),
        ) else {
            continue;
        };

        let construction_start = window_start
            + timer_caps
                .get(0)
                .unwrap()
                .start()
                .min(row_match.start() - window_start);
        let descriptor = ReferenceIdentityTable {
            rows,
            columns,
            root_row,
            column_multiplier,
            row_multiplier,
            salt_left,
            salt_right,
            construction_start,
            construction_end: construction_end as usize,
        };
        let valid = (0..rows)
            .all(|row| (0..columns).all(|column| descriptor.row_for(row, column).is_some()));
        if valid {
            out.insert(target_symbol, descriptor);
        }
    }
    out
}

fn reference_identity(
    expr: &Expression<'_>,
    scoping: &Scoping,
    tables: &HashMap<SymbolId, ReferenceIdentityTable>,
) -> Option<(SymbolId, u32)> {
    let Expression::ComputedMemberExpression(outer) = expr else {
        return None;
    };
    if outer.optional {
        return None;
    }
    let Expression::ComputedMemberExpression(inner) = &outer.object else {
        return None;
    };
    if inner.optional {
        return None;
    }
    let symbol = symbol_of(scoping, &inner.object)?;
    let table = tables.get(&symbol)?;
    let Value::Number(first) = eval(&inner.expression)? else {
        return None;
    };
    let Value::Number(second) = eval(&outer.expression)? else {
        return None;
    };
    if !first.is_finite()
        || !second.is_finite()
        || first.fract() != 0.0
        || second.fract() != 0.0
        || first < 0.0
        || second < 0.0
        || first > u32::MAX as f64
        || second > u32::MAX as f64
    {
        return None;
    }
    Some((symbol, table.identity_for(first as u32, second as u32)?))
}

struct Collector<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    arrays: &'c HashMap<SymbolId, Vec<Value>>,
    decoders: &'c HashMap<SymbolId, Decoder>,
    constants: &'c HashMap<SymbolId, ConstBinding>,
    shorthand_spans: &'c HashSet<(u32, u32)>,
    proxies: &'c HashMap<SymbolId, ProxyObject>,
    pure_functions: &'c HashMap<SymbolId, PureFunction>,
    reference_identity_tables: &'c HashMap<SymbolId, ReferenceIdentityTable>,
    selector_dispatchers: &'c HashMap<SymbolId, SelectorDispatcher>,
    dispatch_orders: &'c HashMap<SymbolId, Vec<String>>,
    zero_counters: &'c HashSet<SymbolId>,
    reference_spans: &'c HashMap<ReferenceId, Span>,
    protected_spans: &'c [(usize, usize)],
    replacements: Vec<Replacement>,
}

impl Collector<'_, '_> {
    fn is_protected(&self, start: usize, end: usize) -> bool {
        self.protected_spans
            .iter()
            .any(|(protected_start, protected_end)| {
                start < *protected_end && *protected_start < end
            })
    }

    fn push(&mut self, span: Span, text: String, kind: &'static str) {
        let start = span.start as usize;
        let end = span.end as usize;
        if start >= end || end > self.source.len() || self.is_protected(start, end) {
            return;
        }
        if self.source.get(start..end) == Some(text.as_str()) {
            return;
        }
        self.replacements.push(Replacement {
            start,
            end,
            text,
            kind,
            arithmetic_state_proof: None,
        });
    }

    fn push_arithmetic(&mut self, span: Span, text: String, mut proof: ArithmeticStateProof) {
        let start = span.start as usize;
        let end = span.end as usize;
        if start >= end || end > self.source.len() || self.is_protected(start, end) {
            return;
        }
        if self.source.get(start..end) == Some(text.as_str()) {
            return;
        }
        proof.input_start = start;
        proof.input_end = end;
        self.replacements.push(Replacement {
            start,
            end,
            text,
            kind: "arithmetic_state_unflatten",
            arithmetic_state_proof: Some(proof),
        });
    }
}

fn single_resolved_reference(scoping: &Scoping, symbol: SymbolId, expected: ReferenceId) -> bool {
    let refs = scoping.get_resolved_reference_ids(symbol);
    refs.len() == 1 && refs[0] == expected
}

impl Collector<'_, '_> {
    fn ordered_switch_replacement(&self, it: &oxc_ast::ast::WhileStatement<'_>) -> Option<String> {
        if known_bool(&it.test) != Some(true) {
            return None;
        }
        let Statement::BlockStatement(body) = &it.body else {
            return None;
        };
        if body.body.len() != 2 {
            return None;
        }
        let Statement::SwitchStatement(switch) = &body.body[0] else {
            return None;
        };
        let Statement::BreakStatement(tail_break) = &body.body[1] else {
            return None;
        };
        if tail_break.label.is_some() {
            return None;
        }

        let Expression::ComputedMemberExpression(selector) = &switch.discriminant else {
            return None;
        };
        if selector.optional {
            return None;
        }
        let Expression::Identifier(order_id) = &selector.object else {
            return None;
        };
        let order_ref = order_id.reference_id.get()?;
        let order_symbol = self.scoping.get_reference(order_ref).symbol_id()?;
        let order = self.dispatch_orders.get(&order_symbol)?;
        if !single_resolved_reference(self.scoping, order_symbol, order_ref) {
            return None;
        }

        let Expression::UpdateExpression(update) = &selector.expression else {
            return None;
        };
        if update.prefix || update.operator.as_str() != "++" {
            return None;
        }
        let oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(counter_id) =
            &update.argument
        else {
            return None;
        };
        let counter_ref = counter_id.reference_id.get()?;
        let counter_symbol = self.scoping.get_reference(counter_ref).symbol_id()?;
        if !self.zero_counters.contains(&counter_symbol)
            || !single_resolved_reference(self.scoping, counter_symbol, counter_ref)
        {
            return None;
        }

        if switch.cases.len() != order.len() {
            return None;
        }

        let mut cases: HashMap<String, &oxc_ast::ast::SwitchCase<'_>> = HashMap::new();
        for case in &switch.cases {
            let key = eval(case.test.as_ref()?)?.js_string()?;
            if cases.insert(key, case).is_some() {
                return None;
            }
        }
        let unique_order = order.iter().collect::<HashSet<_>>();
        if unique_order.len() != order.len() || unique_order.len() != cases.len() {
            return None;
        }

        let mut chunks = Vec::with_capacity(order.len());
        for key in order {
            let case = cases.get(key)?;
            let (last, prefix) = case.consequent.split_last()?;
            let Statement::ContinueStatement(continue_stmt) = last else {
                return None;
            };
            if continue_stmt.label.is_some() {
                return None;
            }
            let chunk = prefix
                .iter()
                .map(|stmt| fragment(self.source, stmt.span()))
                .collect::<Vec<_>>()
                .join("\n");
            chunks.push(chunk);
        }

        Some(format!("{{\n{}\n}}", chunks.join("\n")))
    }
}

fn eval_with_env(expr: &Expression<'_>, env: &HashMap<String, Value>) -> Option<Value> {
    match expr {
        Expression::Identifier(id) => {
            if id.name.as_str() == "undefined" {
                Some(Value::Undefined)
            } else {
                env.get(id.name.as_str()).cloned()
            }
        }
        Expression::StringLiteral(v) => Some(Value::String(v.value.to_string())),
        Expression::NumericLiteral(v) => Some(Value::Number(v.value)),
        Expression::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        Expression::NullLiteral(_) => Some(Value::Null),
        Expression::TemplateLiteral(v) if v.expressions.is_empty() => v
            .quasis
            .first()
            .map(|q| Value::String(q.value.cooked.as_ref().unwrap_or(&q.value.raw).to_string())),
        Expression::ParenthesizedExpression(v) => eval_with_env(&v.expression, env),
        Expression::UnaryExpression(v) => {
            if v.operator.as_str() == "void" {
                eval_with_env(&v.argument, env)?;
                return Some(Value::Undefined);
            }
            let value = eval_with_env(&v.argument, env)?;
            match v.operator.as_str() {
                "!" => Some(Value::Bool(!value.truthy())),
                "+" => value.number().map(Value::Number),
                "-" => value.number().map(|n| Value::Number(-n)),
                "~" => value
                    .number()
                    .map(|n| Value::Number((!js_to_int32(n)) as f64)),
                "typeof" => Some(Value::String(
                    match value {
                        Value::String(_) => "string",
                        Value::Number(_) => "number",
                        Value::Bool(_) => "boolean",
                        Value::Null => "object",
                        Value::Undefined => "undefined",
                    }
                    .to_string(),
                )),
                _ => None,
            }
        }
        Expression::BinaryExpression(v) => eval_binary(
            v.operator.as_str(),
            eval_with_env(&v.left, env)?,
            eval_with_env(&v.right, env)?,
        ),
        Expression::LogicalExpression(v) => {
            let left = eval_with_env(&v.left, env)?;
            match v.operator.as_str() {
                "&&" => {
                    if left.truthy() {
                        eval_with_env(&v.right, env)
                    } else {
                        Some(left)
                    }
                }
                "||" => {
                    if left.truthy() {
                        Some(left)
                    } else {
                        eval_with_env(&v.right, env)
                    }
                }
                "??" => {
                    if matches!(left, Value::Null | Value::Undefined) {
                        eval_with_env(&v.right, env)
                    } else {
                        Some(left)
                    }
                }
                _ => None,
            }
        }
        Expression::ConditionalExpression(v) => {
            let test = eval_with_env(&v.test, env)?.truthy();
            eval_with_env(if test { &v.consequent } else { &v.alternate }, env)
        }
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StateFlow {
    Normal,
    Break,
    Continue,
    Return,
    Throw,
}

#[derive(Default)]
struct NameUseCollector {
    names: HashSet<String>,
}

impl<'a> Visit<'a> for NameUseCollector {
    fn visit_identifier_reference(&mut self, it: &oxc_ast::ast::IdentifierReference<'a>) {
        self.names.insert(it.name.to_string());
    }
}

fn expression_mentions(expr: &Expression<'_>, name: &str) -> bool {
    let mut collector = NameUseCollector::default();
    collector.visit_expression(expr);
    collector.names.contains(name)
}

fn statement_mentions(stmt: &Statement<'_>, name: &str) -> bool {
    let mut collector = NameUseCollector::default();
    collector.visit_statement(stmt);
    collector.names.contains(name)
}

#[derive(Default)]
struct LoopControlDetector {
    found: bool,
}

impl<'a> Visit<'a> for LoopControlDetector {
    fn visit_break_statement(&mut self, _it: &oxc_ast::ast::BreakStatement<'a>) {
        self.found = true;
    }

    fn visit_continue_statement(&mut self, _it: &oxc_ast::ast::ContinueStatement<'a>) {
        self.found = true;
    }

    fn visit_function(&mut self, _it: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {
        // A nested function's control flow cannot target the surrounding
        // dispatcher loop, so do not descend into it.
    }
}

fn statement_has_loop_control(stmt: &Statement<'_>) -> bool {
    let mut detector = LoopControlDetector::default();
    detector.visit_statement(stmt);
    detector.found
}

fn direct_assignment_name<'a>(target: &'a oxc_ast::ast::AssignmentTarget<'a>) -> Option<&'a str> {
    match target {
        oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.as_str()),
        _ => None,
    }
}

fn direct_update_name<'a>(target: &'a oxc_ast::ast::SimpleAssignmentTarget<'a>) -> Option<&'a str> {
    match target {
        oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(id) => {
            Some(id.name.as_str())
        }
        _ => None,
    }
}

fn invalidate_non_state(env: &mut HashMap<String, Value>, state_var: &str) {
    let state = env.get(state_var).cloned();
    env.clear();
    if let Some(state) = state {
        env.insert(state_var.to_string(), state);
    }
}

fn apply_known_assignment(
    operator: &str,
    name: &str,
    right: &Expression<'_>,
    env: &mut HashMap<String, Value>,
) -> Option<()> {
    let value = if operator == "=" {
        eval_with_env(right, env)
    } else if let Some(binary_op) = operator.strip_suffix('=') {
        let left = env.get(name)?.clone();
        let right = eval_with_env(right, env)?;
        eval_binary(binary_op, left, right)
    } else {
        None
    };
    if let Some(value) = value {
        env.insert(name.to_string(), value);
        Some(())
    } else {
        env.remove(name);
        None
    }
}

#[derive(Default)]
struct VariableDeclarationDetector {
    found: bool,
}

impl<'a> Visit<'a> for VariableDeclarationDetector {
    fn visit_variable_declaration(&mut self, _it: &oxc_ast::ast::VariableDeclaration<'a>) {
        self.found = true;
    }
}

fn body_has_variable_declaration(body: &oxc_ast::ast::FunctionBody<'_>) -> bool {
    let mut detector = VariableDeclarationDetector::default();
    detector.visit_function_body(body);
    detector.found
}

fn iife_body<'a>(expr: &'a Expression<'a>) -> Option<&'a oxc_ast::ast::FunctionBody<'a>> {
    match expr {
        Expression::ParenthesizedExpression(p) => iife_body(&p.expression),
        Expression::UnaryExpression(u)
            if matches!(u.operator.as_str(), "!" | "void" | "+" | "-" | "~") =>
        {
            iife_body(&u.argument)
        }
        Expression::CallExpression(call) if !call.optional && call.arguments.is_empty() => {
            match &call.callee {
                Expression::FunctionExpression(fun)
                    if !fun.r#async && !fun.generator && fun.params.items.is_empty() =>
                {
                    let body = fun.body.as_ref()?;
                    body.directives.is_empty().then_some(&**body)
                }
                Expression::ArrowFunctionExpression(fun)
                    if !fun.r#async
                        && fun.params.items.is_empty()
                        && fun.body.directives.is_empty() =>
                {
                    Some(&fun.body)
                }
                Expression::ParenthesizedExpression(p) => iife_body(&p.expression),
                _ => None,
            }
        }
        _ => None,
    }
}

fn simulate_expression(
    expr: &Expression<'_>,
    state_var: &str,
    env: &mut HashMap<String, Value>,
) -> Option<StateFlow> {
    match expr {
        Expression::ParenthesizedExpression(p) => {
            simulate_expression(&p.expression, state_var, env)
        }
        Expression::SequenceExpression(seq) => {
            for item in &seq.expressions {
                let flow = simulate_expression(item, state_var, env)?;
                if flow != StateFlow::Normal {
                    return Some(flow);
                }
            }
            Some(StateFlow::Normal)
        }
        Expression::AssignmentExpression(assign) => {
            if let Some(name) = direct_assignment_name(&assign.left) {
                let known =
                    apply_known_assignment(assign.operator.as_str(), name, &assign.right, env);
                if name == state_var && known.is_none() {
                    return None;
                }
                return Some(StateFlow::Normal);
            }
            if expression_mentions(expr, state_var) {
                return None;
            }
            invalidate_non_state(env, state_var);
            Some(StateFlow::Normal)
        }
        Expression::UpdateExpression(update) => {
            let Some(name) = direct_update_name(&update.argument) else {
                if expression_mentions(expr, state_var) {
                    return None;
                }
                invalidate_non_state(env, state_var);
                return Some(StateFlow::Normal);
            };
            let Some(Value::Number(current)) = env.get(name).cloned() else {
                if name == state_var {
                    return None;
                }
                env.remove(name);
                return Some(StateFlow::Normal);
            };
            let next = match update.operator.as_str() {
                "++" => current + 1.0,
                "--" => current - 1.0,
                _ => return None,
            };
            env.insert(name.to_string(), Value::Number(next));
            Some(StateFlow::Normal)
        }
        _ => {
            if let Some(body) = iife_body(expr) {
                // Name-only abstract environments cannot safely model function-local
                // var shadowing. Reject such IIFEs rather than risk propagating a
                // local binding into the outer dispatcher state.
                if body_has_variable_declaration(body) {
                    return None;
                }

                let outer_names = env.keys().cloned().collect::<Vec<_>>();
                let mut nested = env.clone();
                let flow = simulate_statements(&body.statements, state_var, &mut nested)?;

                // An immediately invoked function can mutate free variables used by
                // later state transitions. Propagate every already-known outer name,
                // including removals when a nested assignment became unknown.
                for name in outer_names {
                    if let Some(value) = nested.get(&name).cloned() {
                        env.insert(name, value);
                    } else {
                        env.remove(&name);
                    }
                }

                return match flow {
                    StateFlow::Throw => Some(StateFlow::Throw),
                    StateFlow::Return
                    | StateFlow::Normal
                    | StateFlow::Break
                    | StateFlow::Continue => Some(StateFlow::Normal),
                };
            }
            if expression_mentions(expr, state_var) {
                return None;
            }
            invalidate_non_state(env, state_var);
            Some(StateFlow::Normal)
        }
    }
}

fn select_switch_case(
    switch: &oxc_ast::ast::SwitchStatement<'_>,
    env: &HashMap<String, Value>,
) -> Option<usize> {
    let discriminant = eval_with_env(&switch.discriminant, env)?;
    let mut default = None;
    for (index, case) in switch.cases.iter().enumerate() {
        let Some(test) = &case.test else {
            default = Some(index);
            continue;
        };
        if same_value(&discriminant, &eval_with_env(test, env)?) {
            return Some(index);
        }
    }
    default
}

fn simulate_switch(
    switch: &oxc_ast::ast::SwitchStatement<'_>,
    state_var: &str,
    env: &mut HashMap<String, Value>,
) -> Option<StateFlow> {
    let start = select_switch_case(switch, env)?;
    for case in switch.cases.iter().skip(start) {
        for stmt in &case.consequent {
            match simulate_statement(stmt, state_var, env)? {
                StateFlow::Normal => {}
                StateFlow::Break => return Some(StateFlow::Normal),
                flow => return Some(flow),
            }
        }
    }
    Some(StateFlow::Normal)
}

fn simulate_statement(
    stmt: &Statement<'_>,
    state_var: &str,
    env: &mut HashMap<String, Value>,
) -> Option<StateFlow> {
    match stmt {
        Statement::BlockStatement(block) => simulate_statements(&block.body, state_var, env),
        Statement::VariableDeclaration(decl) => {
            if decl.kind != VariableDeclarationKind::Var {
                return None;
            }
            for d in &decl.declarations {
                let BindingPattern::BindingIdentifier(id) = &d.id else {
                    return None;
                };
                if let Some(init) = &d.init {
                    if let Some(value) = eval_with_env(init, env) {
                        env.insert(id.name.to_string(), value);
                    } else {
                        env.remove(id.name.as_str());
                    }
                } else {
                    env.insert(id.name.to_string(), Value::Undefined);
                }
            }
            Some(StateFlow::Normal)
        }
        Statement::ExpressionStatement(es) => simulate_expression(&es.expression, state_var, env),
        Statement::IfStatement(branch) => {
            let test = eval_with_env(&branch.test, env)?.truthy();
            if test {
                simulate_statement(&branch.consequent, state_var, env)
            } else if let Some(alt) = &branch.alternate {
                simulate_statement(alt, state_var, env)
            } else {
                Some(StateFlow::Normal)
            }
        }
        Statement::SwitchStatement(switch) => simulate_switch(switch, state_var, env),
        Statement::BreakStatement(brk) if brk.label.is_none() => Some(StateFlow::Break),
        Statement::ContinueStatement(cont) if cont.label.is_none() => Some(StateFlow::Continue),
        Statement::ReturnStatement(_) => Some(StateFlow::Return),
        Statement::ThrowStatement(_) => Some(StateFlow::Throw),
        Statement::EmptyStatement(_) | Statement::DebuggerStatement(_) => Some(StateFlow::Normal),
        _ => None,
    }
}

fn simulate_statements(
    statements: &[Statement<'_>],
    state_var: &str,
    env: &mut HashMap<String, Value>,
) -> Option<StateFlow> {
    for stmt in statements {
        let flow = simulate_statement(stmt, state_var, env)?;
        if flow != StateFlow::Normal {
            return Some(flow);
        }
    }
    Some(StateFlow::Normal)
}

fn state_undefined_test(expr: &Expression<'_>, state_var: &str) -> bool {
    let Expression::BinaryExpression(binary) = expr else {
        return false;
    };
    if !matches!(binary.operator.as_str(), "!=" | "!==") {
        return false;
    }
    let left_state = direct_identifier_name(&binary.left) == Some(state_var);
    let right_state = direct_identifier_name(&binary.right) == Some(state_var);
    let left_undefined = matches!(eval(&binary.left), Some(Value::Undefined));
    let right_undefined = matches!(eval(&binary.right), Some(Value::Undefined));
    (left_state && right_undefined) || (right_state && left_undefined)
}

fn resolved_refs_within(
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
    symbol: SymbolId,
    span: Span,
) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| {
            reference_spans
                .get(reference_id)
                .is_some_and(|reference_span| {
                    reference_span.start >= span.start && reference_span.end <= span.end
                })
        })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReferenceCaseFlow {
    Normal,
    Continue,
    Break,
    Return,
    Throw,
}

impl Collector<'_, '_> {
    fn reference_state_assignment(
        &self,
        expr: &Expression<'_>,
        state_var: &str,
        table_symbol: SymbolId,
    ) -> Option<u32> {
        let expr = match expr {
            Expression::ParenthesizedExpression(parenthesized) => &parenthesized.expression,
            _ => expr,
        };
        let Expression::AssignmentExpression(assign) = expr else {
            return None;
        };
        if assign.operator.as_str() != "="
            || direct_assignment_name(&assign.left) != Some(state_var)
        {
            return None;
        }
        let (symbol, identity) =
            reference_identity(&assign.right, self.scoping, self.reference_identity_tables)?;
        (symbol == table_symbol).then_some(identity)
    }

    fn clean_reference_state_statement(
        &self,
        stmt: &Statement<'_>,
        state_var: &str,
        table_symbol: SymbolId,
    ) -> Option<(String, Option<u32>, ReferenceCaseFlow)> {
        match stmt {
            Statement::BlockStatement(block) => {
                let mut chunks = Vec::new();
                let mut next_state = None;
                for child in &block.body {
                    let (text, next, flow) =
                        self.clean_reference_state_statement(child, state_var, table_symbol)?;
                    if !text.trim().is_empty() {
                        chunks.push(text);
                    }
                    if let Some(next) = next {
                        next_state = Some(next);
                    }
                    if flow != ReferenceCaseFlow::Normal {
                        return Some((
                            format!(
                                "{{
{}
}}",
                                chunks.join(
                                    "
"
                                )
                            ),
                            next_state,
                            flow,
                        ));
                    }
                }
                Some((
                    format!(
                        "{{
{}
}}",
                        chunks.join(
                            "
"
                        )
                    ),
                    next_state,
                    ReferenceCaseFlow::Normal,
                ))
            }
            Statement::ExpressionStatement(expression) => {
                if let Some(next) =
                    self.reference_state_assignment(&expression.expression, state_var, table_symbol)
                {
                    return Some((String::new(), Some(next), ReferenceCaseFlow::Normal));
                }
                if expression_mentions(&expression.expression, state_var) {
                    return None;
                }
                Some((
                    fragment(self.source, stmt.span()).to_string(),
                    None,
                    ReferenceCaseFlow::Normal,
                ))
            }
            Statement::ContinueStatement(continue_stmt) if continue_stmt.label.is_none() => {
                Some((String::new(), None, ReferenceCaseFlow::Continue))
            }
            Statement::BreakStatement(break_stmt) if break_stmt.label.is_none() => {
                Some((String::new(), None, ReferenceCaseFlow::Break))
            }
            Statement::ReturnStatement(_) => {
                if statement_mentions(stmt, state_var) {
                    return None;
                }
                Some((
                    fragment(self.source, stmt.span()).to_string(),
                    None,
                    ReferenceCaseFlow::Return,
                ))
            }
            Statement::ThrowStatement(_) => {
                if statement_mentions(stmt, state_var) {
                    return None;
                }
                Some((
                    fragment(self.source, stmt.span()).to_string(),
                    None,
                    ReferenceCaseFlow::Throw,
                ))
            }
            _ => {
                if statement_mentions(stmt, state_var) || statement_has_loop_control(stmt) {
                    return None;
                }
                Some((
                    fragment(self.source, stmt.span()).to_string(),
                    None,
                    ReferenceCaseFlow::Normal,
                ))
            }
        }
    }

    fn reference_state_replacement(&self, it: &oxc_ast::ast::ForStatement<'_>) -> Option<String> {
        if it.update.is_some() || !matches!(eval(it.test.as_ref()?), Some(Value::Bool(true))) {
            return None;
        }

        let init = it.init.as_ref()?;
        let oxc_ast::ast::ForStatementInit::VariableDeclaration(init_decl) = init else {
            return None;
        };
        if init_decl.kind != VariableDeclarationKind::Var || init_decl.declarations.is_empty() {
            return None;
        }

        let mut state_index = None;
        let mut state_symbol = None;
        let mut state_var = None;
        let mut table_symbol = None;
        let mut initial_identity = None;
        for (index, declaration) in init_decl.declarations.iter().enumerate() {
            let Some(init) = &declaration.init else {
                continue;
            };
            let Some((symbol, identity)) =
                reference_identity(init, self.scoping, self.reference_identity_tables)
            else {
                continue;
            };
            if state_index.is_some() {
                return None;
            }
            let BindingPattern::BindingIdentifier(id) = &declaration.id else {
                return None;
            };
            state_index = Some(index);
            state_symbol = id.symbol_id.get();
            state_var = Some(id.name.as_str());
            table_symbol = Some(symbol);
            initial_identity = Some(identity);
        }

        let state_index = state_index?;
        let state_symbol = state_symbol?;
        let state_var = state_var?;
        let table_symbol = table_symbol?;
        let mut current = initial_identity?;

        if !resolved_refs_within(self.scoping, self.reference_spans, state_symbol, it.span) {
            return None;
        }
        for declaration in &init_decl.declarations {
            if let Some(init) = &declaration.init {
                if expression_mentions(init, state_var)
                    && direct_identifier_name(init) != Some(state_var)
                {
                    return None;
                }
            }
        }

        let Statement::BlockStatement(body) = &it.body else {
            return None;
        };
        if body.body.len() != 2 {
            return None;
        }
        let Statement::SwitchStatement(switch) = &body.body[0] else {
            return None;
        };
        let Statement::BreakStatement(outer_break) = &body.body[1] else {
            return None;
        };
        if outer_break.label.is_some()
            || direct_identifier_name(&switch.discriminant) != Some(state_var)
        {
            return None;
        }

        let mut cases = HashMap::new();
        for (index, case) in switch.cases.iter().enumerate() {
            let test = case.test.as_ref()?;
            let (symbol, identity) =
                reference_identity(test, self.scoping, self.reference_identity_tables)?;
            if symbol != table_symbol || cases.insert(identity, index).is_some() {
                return None;
            }
        }

        let mut chunks = Vec::new();
        let other_declarations = init_decl
            .declarations
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != state_index)
            .map(|(_, declaration)| fragment(self.source, declaration.span))
            .collect::<Vec<_>>();
        if !other_declarations.is_empty() {
            chunks.push(format!("var {};", other_declarations.join(",")));
        }

        let mut seen = HashSet::new();
        for _ in 0..256 {
            if !seen.insert(current) {
                return None;
            }
            let Some(start) = cases.get(&current).copied() else {
                // No case matches, so the switch falls through and the
                // unconditional break after it terminates the dispatcher.
                return Some(format!(
                    "{{
{}
}}",
                    chunks.join(
                        "
"
                    )
                ));
            };

            let mut next_state = None;
            let mut flow = ReferenceCaseFlow::Normal;
            'cases: for case in switch.cases.iter().skip(start) {
                for stmt in &case.consequent {
                    let (text, next, stmt_flow) =
                        self.clean_reference_state_statement(stmt, state_var, table_symbol)?;
                    if !text.trim().is_empty() {
                        chunks.push(text);
                    }
                    if let Some(next) = next {
                        next_state = Some(next);
                    }
                    if stmt_flow != ReferenceCaseFlow::Normal {
                        flow = stmt_flow;
                        break 'cases;
                    }
                }
            }

            match flow {
                ReferenceCaseFlow::Continue => {
                    current = next_state?;
                }
                ReferenceCaseFlow::Break
                | ReferenceCaseFlow::Return
                | ReferenceCaseFlow::Throw
                | ReferenceCaseFlow::Normal => {
                    return Some(format!(
                        "{{
{}
}}",
                        chunks.join(
                            "
"
                        )
                    ));
                }
            }
        }
        None
    }

    fn arithmetic_state_replacement(
        &self,
        it: &oxc_ast::ast::ForStatement<'_>,
    ) -> Option<(String, ArithmeticStateProof)> {
        if it.update.is_some() {
            return None;
        }
        let init = it.init.as_ref()?;
        let oxc_ast::ast::ForStatementInit::VariableDeclaration(init_decl) = init else {
            return None;
        };
        if init_decl.kind != VariableDeclarationKind::Var || init_decl.declarations.len() != 1 {
            return None;
        }
        let state_decl = &init_decl.declarations[0];
        let BindingPattern::BindingIdentifier(state_id) = &state_decl.id else {
            return None;
        };
        let state_symbol = state_id.symbol_id.get()?;
        let state_var = state_id.name.as_str();
        let initial = eval(state_decl.init.as_ref()?)?;
        let Value::Number(initial_number) = initial else {
            return None;
        };
        if !initial_number.is_finite() || initial_number.fract() != 0.0 {
            return None;
        }
        if !state_undefined_test(it.test.as_ref()?, state_var)
            || !resolved_refs_within(self.scoping, self.reference_spans, state_symbol, it.span)
        {
            return None;
        }

        let Statement::BlockStatement(body) = &it.body else {
            return None;
        };
        if body.body.len() < 2 {
            return None;
        }
        let (switch_stmt, selector_stmts) = body.body.split_last()?;
        let Statement::SwitchStatement(switch) = switch_stmt else {
            return None;
        };
        if selector_stmts.is_empty()
            || !selector_stmts
                .iter()
                .all(|stmt| matches!(stmt, Statement::VariableDeclaration(decl) if decl.kind == VariableDeclarationKind::Var))
        {
            return None;
        }

        let mut env = HashMap::new();
        env.insert(state_var.to_string(), Value::Number(initial_number));
        let mut chunks = vec![format!("{};", fragment(self.source, init_decl.span))];
        let mut seen_states = HashSet::new();
        let mut state_path = Vec::new();

        for _ in 0..256 {
            let state_key = env.get(state_var)?.render()?;
            if !seen_states.insert(state_key.clone()) {
                return None;
            }
            state_path.push(state_key);

            for selector_stmt in selector_stmts {
                let Statement::VariableDeclaration(decl) = selector_stmt else {
                    unreachable!();
                };
                simulate_statement(selector_stmt, state_var, &mut env)?;
                chunks.push(fragment(self.source, decl.span).to_string());
            }

            let start = select_switch_case(switch, &env)?;
            let mut flow = StateFlow::Normal;
            'cases: for case in switch.cases.iter().skip(start) {
                for stmt in &case.consequent {
                    match stmt {
                        Statement::BreakStatement(brk) if brk.label.is_none() => {
                            flow = StateFlow::Normal;
                            break 'cases;
                        }
                        Statement::ContinueStatement(cont) if cont.label.is_none() => {
                            flow = StateFlow::Continue;
                            break 'cases;
                        }
                        _ => {
                            let stmt_flow = simulate_statement(stmt, state_var, &mut env)?;
                            chunks.push(fragment(self.source, stmt.span()).to_string());
                            match stmt_flow {
                                StateFlow::Normal => {}
                                StateFlow::Return | StateFlow::Throw => {
                                    flow = stmt_flow;
                                    break 'cases;
                                }
                                StateFlow::Break | StateFlow::Continue => return None,
                            }
                        }
                    }
                }
            }

            match flow {
                StateFlow::Return | StateFlow::Throw => {
                    let termination = if flow == StateFlow::Return {
                        "return"
                    } else {
                        "throw"
                    };
                    return Some((
                        format!("{{\n{}\n}}", chunks.join("\n")),
                        ArithmeticStateProof {
                            iteration: 0,
                            input_start: it.span.start as usize,
                            input_end: it.span.end as usize,
                            state_var: state_var.to_string(),
                            state_path,
                            termination: termination.to_string(),
                        },
                    ));
                }
                StateFlow::Normal | StateFlow::Continue => {}
                StateFlow::Break => return None,
            }

            match env.get(state_var) {
                Some(Value::Undefined) => {
                    return Some((
                        format!("{{\n{}\n}}", chunks.join("\n")),
                        ArithmeticStateProof {
                            iteration: 0,
                            input_start: it.span.start as usize,
                            input_end: it.span.end as usize,
                            state_var: state_var.to_string(),
                            state_path,
                            termination: "undefined".to_string(),
                        },
                    ));
                }
                Some(Value::Number(n)) if n.is_finite() && n.fract() == 0.0 => {}
                _ => return None,
            }
        }
        None
    }
}

impl<'a> Visit<'a> for Collector<'_, '_> {
    fn visit_expression(&mut self, it: &Expression<'a>) {
        if let Expression::Identifier(id) = it {
            if self.shorthand_spans.contains(&(id.span.start, id.span.end)) {
                walk::walk_expression(self, it);
                return;
            }
            if let Some(reference_id) = id.reference_id.get() {
                let reference = self.scoping.get_reference(reference_id);
                if reference.is_read()
                    && !reference.is_write()
                    && !reference.flags().is_member_write_target()
                {
                    if let Some(symbol) = reference.symbol_id() {
                        if let Some(binding) = self.constants.get(&symbol) {
                            if id.span.start >= binding.available_after {
                                if let Some(text) = binding.value.render() {
                                    self.push(id.span, text, "const_propagate");
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_expression(self, it);
    }

    fn visit_binary_expression(&mut self, it: &oxc_ast::ast::BinaryExpression<'a>) {
        if matches!(it.operator.as_str(), "==" | "===" | "!=" | "!==") {
            let left_reference =
                reference_identity(&it.left, self.scoping, self.reference_identity_tables);
            let right_reference =
                reference_identity(&it.right, self.scoping, self.reference_identity_tables);
            if let (Some((left_symbol, left_identity)), Some((right_symbol, right_identity))) =
                (left_reference, right_reference)
            {
                if left_symbol == right_symbol {
                    let equal = left_identity == right_identity;
                    let value = if matches!(it.operator.as_str(), "==" | "===") {
                        equal
                    } else {
                        !equal
                    };
                    self.push(
                        it.span,
                        if value { "true" } else { "false" }.to_string(),
                        "reference_identity_compare",
                    );
                    return;
                }
            }
        }
        if let (Some(left), Some(right)) = (eval(&it.left), eval(&it.right)) {
            if let Some(value) = eval_binary(it.operator.as_str(), left, right) {
                if let Some(text) = value.render() {
                    self.push(it.span, text, "constant_fold");
                }
            }
        }
        walk::walk_binary_expression(self, it);
    }

    fn visit_unary_expression(&mut self, it: &UnaryExpression<'a>) {
        if let Some(value) = eval_unary(it) {
            if let Some(text) = value.render() {
                self.push(it.span, text, "constant_fold");
            }
        }
        walk::walk_unary_expression(self, it);
    }

    fn visit_logical_expression(&mut self, it: &LogicalExpression<'a>) {
        if let Some(value) = eval_logical(it) {
            if let Some(text) = value.render() {
                self.push(it.span, text, "constant_fold");
            }
        }
        walk::walk_logical_expression(self, it);
    }

    fn visit_conditional_expression(&mut self, it: &oxc_ast::ast::ConditionalExpression<'a>) {
        if let Some(test) = known_bool(&it.test) {
            let selected = if test { &it.consequent } else { &it.alternate };
            self.push(
                it.span,
                fragment(self.source, selected.span()).to_string(),
                "constant_branch",
            );
        }
        walk::walk_conditional_expression(self, it);
    }

    fn visit_if_statement(&mut self, it: &IfStatement<'a>) {
        if let Some(test) = known_bool(&it.test) {
            let text = if test {
                fragment(self.source, it.consequent.span()).to_string()
            } else {
                it.alternate
                    .as_ref()
                    .map(|s| fragment(self.source, s.span()).to_string())
                    .unwrap_or_else(|| ";".into())
            };
            self.push(it.span, text, "dead_branch");
        }
        walk::walk_if_statement(self, it);
    }

    fn visit_for_statement(&mut self, it: &oxc_ast::ast::ForStatement<'a>) {
        if let Some(text) = self.reference_state_replacement(it) {
            self.push(it.span, text, "reference_state_unflatten");
            return;
        }
        if let Some((text, proof)) = self.arithmetic_state_replacement(it) {
            self.push_arithmetic(it.span, text, proof);
            return;
        }
        walk::walk_for_statement(self, it);
    }

    fn visit_while_statement(&mut self, it: &oxc_ast::ast::WhileStatement<'a>) {
        if let Some(text) = self.ordered_switch_replacement(it) {
            self.push(it.span, text, "ordered_switch_unflatten");
            return;
        }
        walk::walk_while_statement(self, it);
    }

    fn visit_expression_statement(&mut self, it: &ExpressionStatement<'a>) {
        if let Expression::SequenceExpression(seq) = &it.expression {
            let text = seq
                .expressions
                .iter()
                .map(|expr| format!("({});", fragment(self.source, expr.span())))
                .collect::<Vec<_>>()
                .join("\n");
            self.push(it.span, format!("{{\n{text}\n}}"), "split_sequence");
        }
        walk::walk_expression_statement(self, it);
    }

    fn visit_static_member_expression(&mut self, it: &StaticMemberExpression<'a>) {
        if !it.optional {
            if let Some(symbol) = symbol_of(self.scoping, &it.object) {
                if let Some(ProxyProperty::Literal(value)) = self
                    .proxies
                    .get(&symbol)
                    .and_then(|object| object.properties.get(it.property.name.as_str()))
                {
                    if let Some(text) = value.render() {
                        self.push(it.span, text, proxy_literal_kind(value));
                        return;
                    }
                }
            }
        }
        walk::walk_static_member_expression(self, it);
    }

    fn visit_computed_member_expression(&mut self, it: &ComputedMemberExpression<'a>) {
        if !it.optional {
            if let Some(Value::String(property)) = eval(&it.expression) {
                if let Some(symbol) = symbol_of(self.scoping, &it.object) {
                    if let Some(ProxyProperty::Literal(value)) = self
                        .proxies
                        .get(&symbol)
                        .and_then(|object| object.properties.get(&property))
                    {
                        if let Some(text) = value.render() {
                            self.push(it.span, text, proxy_literal_kind(value));
                            return;
                        }
                    }
                }
                if valid_property(&property) {
                    self.push(
                        it.span,
                        format!("{}.{}", fragment(self.source, it.object.span()), property),
                        "computed_property",
                    );
                    walk::walk_computed_member_expression(self, it);
                    return;
                }
            }
            if let Some(symbol) = symbol_of(self.scoping, &it.object) {
                if let Some(values) = self.arrays.get(&symbol) {
                    if let Some(index) = eval(&it.expression)
                        .and_then(|v| v.number())
                        .filter(|n| n.is_finite() && *n >= 0.0 && n.fract() == 0.0)
                        .map(|n| n as usize)
                    {
                        if let Some(text) = values.get(index).and_then(Value::render) {
                            self.push(it.span, text, "static_array_lookup");
                            walk::walk_computed_member_expression(self, it);
                            return;
                        }
                    }
                }
            }
        }
        walk::walk_computed_member_expression(self, it);
    }

    fn visit_call_expression(&mut self, it: &CallExpression<'a>) {
        if !it.optional && !it.arguments.iter().any(Argument::is_spread) {
            if let Some(symbol) = symbol_of(self.scoping, &it.callee) {
                if let Some(dispatcher) = self.selector_dispatchers.get(&symbol) {
                    if let Some(selector) = it.arguments.first().and_then(argument_integer) {
                        if let Some(return_span) = dispatcher.returns.get(&selector) {
                            let used_param_count = dispatcher
                                .param_symbols
                                .iter()
                                .enumerate()
                                .filter_map(|(index, symbol)| {
                                    self.scoping
                                        .get_resolved_reference_ids(*symbol)
                                        .iter()
                                        .filter_map(|reference_id| {
                                            self.reference_spans.get(reference_id)
                                        })
                                        .any(|span| {
                                            return_span.start <= span.start
                                                && span.end <= return_span.end
                                        })
                                        .then_some(index + 1)
                                })
                                .max()
                                .unwrap_or(0);
                            let params = dispatcher.params[..used_param_count].join(", ");
                            let args = it
                                .arguments
                                .iter()
                                .map(|argument| fragment(self.source, argument.span()))
                                .collect::<Vec<_>>()
                                .join(", ");
                            let returned = fragment(self.source, *return_span);
                            self.push(
                                it.span,
                                format!("(function({params}){{return ({returned});}})({args})"),
                                "selector_dispatch_specialize",
                            );
                            return;
                        }
                    }
                }
            }
        }

        if !it.optional && !it.arguments.iter().any(Argument::is_spread) {
            if let Some((symbol, key)) = static_proxy_member(&it.callee, self.scoping) {
                if let Some(ProxyProperty::Call { arity }) = self
                    .proxies
                    .get(&symbol)
                    .and_then(|object| object.properties.get(&key))
                {
                    if it.arguments.len() == arity + 1 {
                        let callee = fragment(self.source, it.arguments[0].span());
                        let args = it.arguments[1..]
                            .iter()
                            .map(|argument| fragment(self.source, argument.span()))
                            .collect::<Vec<_>>()
                            .join(", ");
                        self.push(it.span, format!("((0, ({callee})))({args})"), "proxy_call");
                        return;
                    }
                }
            }
        }

        if !it.optional && it.arguments.len() == 1 && !it.arguments.iter().any(Argument::is_spread)
        {
            if let Some((symbol, key)) = static_proxy_member(&it.callee, self.scoping) {
                if let Some(ProxyProperty::StaticMember { property }) = self
                    .proxies
                    .get(&symbol)
                    .and_then(|object| object.properties.get(&key))
                {
                    let object = fragment(self.source, it.arguments[0].span());
                    self.push(
                        it.span,
                        format!("(({object}).{property})"),
                        "proxy_static_member",
                    );
                    return;
                }
            }
        }

        if !it.optional && it.arguments.len() == 2 && !it.arguments.iter().any(Argument::is_spread)
        {
            if let Some((symbol, key)) = static_proxy_member(&it.callee, self.scoping) {
                if let Some(ProxyProperty::ComputedMember) = self
                    .proxies
                    .get(&symbol)
                    .and_then(|object| object.properties.get(&key))
                {
                    let object = fragment(self.source, it.arguments[0].span());
                    let property = fragment(self.source, it.arguments[1].span());
                    self.push(
                        it.span,
                        format!("(({object})[{property}])"),
                        "proxy_computed_member",
                    );
                    return;
                }
            }
        }

        if !it.optional && it.arguments.len() == 1 && !it.arguments.iter().any(Argument::is_spread)
        {
            if let Some((symbol, key)) = static_proxy_member(&it.callee, self.scoping) {
                if let Some(ProxyProperty::Unary { operator }) = self
                    .proxies
                    .get(&symbol)
                    .and_then(|object| object.properties.get(&key))
                {
                    let argument = fragment(self.source, it.arguments[0].span());
                    let text = if operator == "void" {
                        format!("(void ({argument}))")
                    } else {
                        format!("({operator}({argument}))")
                    };
                    self.push(it.span, text, "proxy_unary");
                    return;
                }
            }
        }

        if !it.optional && it.arguments.len() == 2 && !it.arguments.iter().any(Argument::is_spread)
        {
            if let Some((symbol, key)) = static_proxy_member(&it.callee, self.scoping) {
                if let Some(ProxyProperty::Binary { operator }) = self
                    .proxies
                    .get(&symbol)
                    .and_then(|object| object.properties.get(&key))
                {
                    let left = fragment(self.source, it.arguments[0].span());
                    let right = fragment(self.source, it.arguments[1].span());
                    self.push(
                        it.span,
                        format!("(({left}) {operator} ({right}))"),
                        "proxy_binary",
                    );
                    return;
                }
            }
        }
        if !it.optional && !it.arguments.iter().any(Argument::is_spread) {
            if let Some(symbol) = symbol_of(self.scoping, &it.callee) {
                if let Some(function) = self.pure_functions.get(&symbol) {
                    if it.arguments.len() == function.arity {
                        let values = it
                            .arguments
                            .iter()
                            .map(eval_static_argument)
                            .collect::<Option<Vec<_>>>();
                        if let Some(values) = values {
                            if let Some(text) = function
                                .expression
                                .eval(&values)
                                .and_then(|value| value.render())
                            {
                                self.push(it.span, text, "pure_function_eval");
                                walk::walk_call_expression(self, it);
                                return;
                            }
                        }
                    }
                }
            }
        }

        if let Some(symbol) = symbol_of(self.scoping, &it.callee) {
            if let Some(decoder) = self.decoders.get(&symbol) {
                if let Some(argument) = it.arguments.first() {
                    if let Some(raw) = argument_integer(argument) {
                        if let Some(text) =
                            decoder.value_for_raw(raw).and_then(|value| value.render())
                        {
                            self.push(it.span, text, "string_array_decode");
                            walk::walk_call_expression(self, it);
                            return;
                        }
                    } else if let Argument::ConditionalExpression(conditional) = argument {
                        let consequent = expression_integer(&conditional.consequent)
                            .and_then(|raw| decoder.value_for_raw(raw))
                            .and_then(|value| value.render());
                        let alternate = expression_integer(&conditional.alternate)
                            .and_then(|raw| decoder.value_for_raw(raw))
                            .and_then(|value| value.render());
                        if let (Some(consequent), Some(alternate)) = (consequent, alternate) {
                            let test = fragment(self.source, conditional.test.span());
                            self.push(
                                it.span,
                                format!("(({}) ? ({}) : ({}))", test, consequent, alternate),
                                "string_array_decode",
                            );
                            // The replacement spans the whole call. Revisit its
                            // copied test expression on the next fixed-point
                            // iteration instead of creating overlapping edits.
                            return;
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, it);
    }
}

fn eval_static_argument(arg: &Argument<'_>) -> Option<Value> {
    match arg {
        Argument::StringLiteral(v) => Some(Value::String(v.value.to_string())),
        Argument::NumericLiteral(v) => Some(Value::Number(v.value)),
        Argument::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        Argument::NullLiteral(_) => Some(Value::Null),
        Argument::TemplateLiteral(v) if v.expressions.is_empty() => v
            .quasis
            .first()
            .map(|q| Value::String(q.value.cooked.as_ref().unwrap_or(&q.value.raw).to_string())),
        Argument::ParenthesizedExpression(v) => eval(&v.expression),
        Argument::UnaryExpression(v) => eval_unary(v),
        Argument::BinaryExpression(v) => {
            eval_binary(v.operator.as_str(), eval(&v.left)?, eval(&v.right)?)
        }
        Argument::LogicalExpression(v) => eval_logical(v),
        Argument::ConditionalExpression(v) => {
            let test = known_bool(&v.test)?;
            eval(if test { &v.consequent } else { &v.alternate })
        }
        _ => None,
    }
}

fn argument_integer(arg: &Argument<'_>) -> Option<i64> {
    match arg {
        Argument::NumericLiteral(v)
            if v.value.is_finite()
                && v.value.fract() == 0.0
                && v.value >= i64::MIN as f64
                && v.value <= i64::MAX as f64 =>
        {
            Some(v.value as i64)
        }
        Argument::UnaryExpression(v) if v.operator.as_str() == "-" => match &v.argument {
            Expression::NumericLiteral(n)
                if n.value.is_finite() && n.value.fract() == 0.0 && n.value <= i64::MAX as f64 =>
            {
                Some(-(n.value as i64))
            }
            _ => None,
        },
        _ => None,
    }
}

#[derive(Default)]
struct DirectEvalProbe {
    found: bool,
}

impl<'a> Visit<'a> for DirectEvalProbe {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if matches!(
            &call.callee,
            Expression::Identifier(identifier) if identifier.name.as_str() == "eval"
        ) {
            self.found = true;
            return;
        }
        walk::walk_call_expression(self, call);
    }
}

fn has_direct_eval(program: &oxc_ast::ast::Program<'_>) -> bool {
    let mut probe = DirectEvalProbe::default();
    probe.visit_program(program);
    probe.found
}

fn remove_unused_proven_helpers(
    functions: &[FnInfo],
    scoping: &Scoping,
    decoders: &HashMap<SymbolId, Decoder>,
    pure_functions: &HashMap<SymbolId, PureFunction>,
    direct_eval_present: bool,
) -> Vec<Replacement> {
    if direct_eval_present {
        return Vec::new();
    }
    let root_scope = scoping.root_scope_id();
    let recognized = decoders
        .keys()
        .chain(pure_functions.keys())
        .copied()
        .collect::<HashSet<_>>();

    functions
        .iter()
        .filter(|function| {
            function.scope != root_scope
                && recognized.contains(&function.symbol)
                && scoping
                    .get_resolved_reference_ids(function.symbol)
                    .is_empty()
        })
        .map(|function| Replacement {
            start: function.span.start as usize,
            end: function.span.end as usize,
            text: String::new(),
            kind: "remove_unused_proven_helper",
            arithmetic_state_proof: None,
        })
        .collect()
}

fn js_word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$') || byte >= 0x80
}

fn needs_lexical_separator(left: u8, right: u8) -> bool {
    (js_word_byte(left) && js_word_byte(right))
        || (left == b'+' && right == b'+')
        || (left == b'-' && right == b'-')
        || (left == b'/' && matches!(right, b'/' | b'*'))
        || (left.is_ascii_digit() && right == b'.')
}

fn append_with_safe_boundary(out: &mut String, piece: &str) {
    if piece.is_empty() {
        return;
    }
    if let (Some(left), Some(right)) = (
        out.as_bytes().last().copied(),
        piece.as_bytes().first().copied(),
    ) {
        if needs_lexical_separator(left, right) {
            out.push(' ');
        }
    }
    out.push_str(piece);
}

fn apply(
    source: &str,
    mut replacements: Vec<Replacement>,
    counts: &mut Counts,
    arithmetic_state_proofs: &mut Vec<ArithmeticStateProof>,
    iteration: usize,
) -> String {
    replacements.sort_by(|a, b| {
        (b.end - b.start)
            .cmp(&(a.end - a.start))
            .then_with(|| a.start.cmp(&b.start))
    });

    let mut selected: Vec<Replacement> = Vec::new();
    'next: for candidate in replacements {
        for existing in &selected {
            if candidate.start < existing.end && existing.start < candidate.end {
                continue 'next;
            }
        }
        selected.push(candidate);
    }
    selected.sort_by_key(|replacement| replacement.start);

    let mut out = String::with_capacity(source.len());
    let mut cursor = 0usize;
    for mut replacement in selected {
        append_with_safe_boundary(&mut out, &source[cursor..replacement.start]);
        append_with_safe_boundary(&mut out, &replacement.text);
        cursor = replacement.end;
        counts.bump(replacement.kind);
        if let Some(mut proof) = replacement.arithmetic_state_proof.take() {
            proof.iteration = iteration;
            arithmetic_state_proofs.push(proof);
        }
    }
    append_with_safe_boundary(&mut out, &source[cursor..]);
    out
}

fn parse<'a>(allocator: &'a Allocator, source: &'a str) -> Option<oxc_ast::ast::Program<'a>> {
    for source_type in [SourceType::mjs(), SourceType::cjs()] {
        let parsed = Parser::new(allocator, source, source_type).parse();
        if !parsed.panicked && parsed.diagnostics.is_empty() {
            return Some(parsed.program);
        }
    }
    None
}

fn transform_once(
    source: &str,
    counts: &mut Counts,
    arithmetic_state_proofs: &mut Vec<ArithmeticStateProof>,
    iteration: usize,
) -> Option<String> {
    let allocator = Allocator::default();
    let program = parse(&allocator, source)?;
    let semantic_ret = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(&program);
    if !semantic_ret.diagnostics.is_empty() {
        return None;
    }
    let semantic = semantic_ret.semantic;
    let scoping = semantic.scoping();

    let arrays = top_level_arrays(&program);
    let array_infos = decoder_static_arrays(&program, scoping);
    let direct_functions = all_functions(&program);
    let functions = all_function_declarations(&program, scoping);
    let reference_spans = collect_reference_spans(&program);
    let (mut decoders, mut protected_spans, mut rotation_replacements) =
        detect_decoders(source, &functions, &program, scoping);
    for (symbol, decoder) in detect_direct_table_decoders(
        source,
        &direct_functions,
        &array_infos,
        scoping,
        &reference_spans,
    ) {
        decoders.entry(symbol).or_insert(decoder);
    }
    let constants = collect_const_values(&program, scoping);
    let shorthand_spans = collect_shorthand_spans(&program);
    let proxies = collect_proxy_objects(&program, scoping);
    let pure_functions = collect_pure_functions(&program, scoping);
    let reference_identity_tables =
        detect_reference_identity_tables(source, scoping, &reference_spans);
    protected_spans.extend(
        reference_identity_tables
            .values()
            .map(|table| (table.construction_start, table.construction_end)),
    );
    let stable_var_numbers = collect_stable_var_numbers(&program, scoping);
    let selector_dispatchers = collect_selector_dispatchers(&program, scoping, &stable_var_numbers);
    let (dispatch_orders, zero_counters) = collect_dispatch_bindings(&program);
    rotation_replacements.extend(remove_unused_proven_helpers(
        &functions,
        scoping,
        &decoders,
        &pure_functions,
        has_direct_eval(&program),
    ));

    let mut collector = Collector {
        source,
        scoping,
        arrays: &arrays,
        decoders: &decoders,
        constants: &constants,
        shorthand_spans: &shorthand_spans,
        proxies: &proxies,
        pure_functions: &pure_functions,
        reference_identity_tables: &reference_identity_tables,
        selector_dispatchers: &selector_dispatchers,
        dispatch_orders: &dispatch_orders,
        zero_counters: &zero_counters,
        reference_spans: &reference_spans,
        protected_spans: &protected_spans,
        replacements: rotation_replacements,
    };
    collector.visit_program(&program);
    if collector.replacements.is_empty() {
        Some(source.to_string())
    } else {
        Some(apply(
            source,
            collector.replacements,
            counts,
            arithmetic_state_proofs,
            iteration,
        ))
    }
}

#[derive(Debug, Clone)]
pub struct SafeTransformResult {
    pub source: String,
    pub iterations: usize,
    pub transforms: BTreeMap<String, usize>,
    pub arithmetic_state_proofs: Vec<ArithmeticStateProof>,
}

pub fn deobfuscate(source: &str, max_iterations: usize) -> Option<SafeTransformResult> {
    // Validate before the first rewrite. The caller may canonicalize for presentation,
    // but the engine intentionally has no codegen dependency so it stays dist-friendly.
    {
        let allocator = Allocator::default();
        parse(&allocator, source)?;
    }

    let mut current = source.to_string();
    let mut counts = Counts::default();
    let mut iterations = 0usize;
    let mut arithmetic_state_proofs = Vec::new();

    for iteration in 1..=max_iterations {
        let next = transform_once(
            &current,
            &mut counts,
            &mut arithmetic_state_proofs,
            iteration,
        )?;
        if next == current {
            break;
        }
        iterations += 1;
        current = next;
    }

    Some(SafeTransformResult {
        source: current,
        iterations,
        transforms: counts.0,
        arithmetic_state_proofs,
    })
}
