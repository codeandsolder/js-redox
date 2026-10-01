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
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
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
            let equal = if same_value(&left, &right) {
                true
            } else if matches!(
                (&left, &right),
                (Value::Null, Value::Undefined) | (Value::Undefined, Value::Null)
            ) {
                true
            } else {
                return None;
            };
            Some(Value::Bool(if op == "==" { equal } else { !equal }))
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

    let mut out = String::with_capacity(((filtered.len() + 3) / 4) * 3);
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

#[derive(Debug)]
struct FnInfo {
    name: String,
    symbol: SymbolId,
    params: Vec<String>,
    span: Span,
    body_statement_count: usize,
    direct_call_count: usize,
    fixed_decoder_control_shape: bool,
    static_arrays: HashMap<String, Vec<Value>>,
}

fn top_level_functions(program: &oxc_ast::ast::Program<'_>) -> Vec<FnInfo> {
    let mut out = Vec::new();
    for stmt in &program.body {
        let Statement::FunctionDeclaration(f) = stmt else {
            continue;
        };
        let Some(id) = &f.id else { continue };
        let Some(symbol) = id.symbol_id.get() else {
            continue;
        };
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
                        static_arrays.insert(array_id.name.to_string(), values);
                    }
                }
            }
        }

        out.push(FnInfo {
            name: id.name.to_string(),
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
            static_arrays,
        });
    }
    out
}

#[derive(Default)]
struct FnInfoCollector {
    out: Vec<FnInfo>,
}

impl<'a> Visit<'a> for FnInfoCollector {
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
                                static_arrays.insert(array_id.name.to_string(), values);
                            }
                        }
                    }
                }

                self.out.push(FnInfo {
                    name: id.name.to_string(),
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
                    static_arrays,
                });
            }
        }
        walk::walk_function(self, f, flags);
    }
}

fn all_functions(program: &oxc_ast::ast::Program<'_>) -> Vec<FnInfo> {
    let mut collector = FnInfoCollector::default();
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
    functions: &[FnInfo],
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
                transform,
            },
        );
    }
    out
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

fn apply_proven_decoder_rotations(
    source: &str,
    decoders: &mut HashMap<String, Decoder>,
) -> Vec<(usize, usize)> {
    let iife_re = regex::Regex::new(
        r#"(?s)\(\s*function\s*\([^)]*\)\s*\{(?P<body>.*?)\}\s*\)?\s*\(\s*(?P<provider>[A-Za-z_$][A-Za-z0-9_$]*)\s*,\s*(?P<target>-?(?:0[xX][0-9A-Fa-f]+|[0-9]+))\s*\)"#,
    )
    .unwrap();
    let checksum_re = regex::Regex::new(
        r#"(?s)\btry\s*\{\s*(?:var|let|const)\s+[A-Za-z_$][A-Za-z0-9_$]*\s*=\s*(?P<expr>[^;]+);"#,
    )
    .unwrap();
    let mut protected_spans = Vec::new();

    for caps in iife_re.captures_iter(source) {
        let body = &caps["body"];
        if !body.contains("push") || !body.contains("shift") {
            continue;
        }
        let provider = &caps["provider"];
        let Some(target) = parse_i64_literal(&caps["target"]) else {
            continue;
        };
        let Some(checksum) = checksum_re.captures(body) else {
            continue;
        };
        let expression = &checksum["expr"];
        let mut proven_here = false;

        for (decoder_name, decoder) in decoders.iter_mut() {
            if decoder.provider != provider || decoder.values.is_empty() {
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
                if value.is_finite() && (value - target as f64).abs() < 1e-9 {
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
            if let Some(full_match) = caps.get(0) {
                protected_spans.push((full_match.start(), full_match.end()));
            }
        }
    }

    protected_spans
}

fn detect_decoders(
    source: &str,
    functions: &[FnInfo],
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> (HashMap<SymbolId, Decoder>, Vec<(usize, usize)>) {
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
                providers.insert(f.name.clone(), values.clone());
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
        let Some(values) = providers.get(&provider) else {
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
        if (!body.contains(&format!("{} = function({param}", f.name))
            && !body.contains(&format!("{}=function({param}", f.name)))
            || (!body.contains(&format!("return {}({public_param}", f.name))
                && !body.contains(&format!(",{}({public_param}", f.name))
                && !body.contains(&format!(", {}({public_param}", f.name)))
        {
            continue;
        }
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
        if !body.contains(&format!("return {value_var};")) {
            continue;
        }

        let transform = if body
            .contains("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/=")
            && body.contains("decodeURIComponent")
        {
            // javascript-obfuscator's common base64 decoder includes a
            // self-defending guard based on Function#toString. A literal LF
            // at one of the probed positions substitutes the loop counter for
            // the decoded byte. For a one-line decoder the guard is provably
            // inert; after pretty-printing it may not be. Refuse to decode
            // unless the current representation proves no line terminators.
            if body.contains('\n') || body.contains('\r') {
                continue;
            }
            DecoderTransform::LowerAlphabetBase64Uri
        } else {
            DecoderTransform::Plain
        };

        by_name.insert(
            f.name.clone(),
            Decoder {
                values: values.clone(),
                offset,
                provider,
                transform,
            },
        );
    }

    let protected_spans = apply_proven_decoder_rotations(source, &mut by_name);

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

    (out, protected_spans)
}

struct SymbolAliasCollector<'s> {
    scoping: &'s Scoping,
    aliases: Vec<(SymbolId, SymbolId)>,
}

impl<'a> Visit<'a> for SymbolAliasCollector<'_> {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
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
    String(String),
    Binary { operator: String },
    Call { arity: usize },
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

    if params.len() == 2 {
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
        if let Some(Value::String(value)) = eval(&prop.value) {
            properties.insert(key, ProxyProperty::String(value));
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

struct Collector<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    arrays: &'c HashMap<SymbolId, Vec<Value>>,
    decoders: &'c HashMap<SymbolId, Decoder>,
    constants: &'c HashMap<SymbolId, ConstBinding>,
    shorthand_spans: &'c HashSet<(u32, u32)>,
    proxies: &'c HashMap<SymbolId, ProxyObject>,
    pure_functions: &'c HashMap<SymbolId, PureFunction>,
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

impl Collector<'_, '_> {
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
                if let Some(ProxyProperty::String(value)) = self
                    .proxies
                    .get(&symbol)
                    .and_then(|object| object.properties.get(it.property.name.as_str()))
                {
                    if let Ok(text) = serde_json::to_string(value) {
                        self.push(it.span, text, "proxy_string");
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
                    if let Some(ProxyProperty::String(value)) = self
                        .proxies
                        .get(&symbol)
                        .and_then(|object| object.properties.get(&property))
                    {
                        if let Ok(text) = serde_json::to_string(value) {
                            self.push(it.span, text, "proxy_string");
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

fn expression_integer(expr: &Expression<'_>) -> Option<i64> {
    let Value::Number(value) = eval(expr)? else {
        return None;
    };
    if value.is_finite()
        && value.fract() == 0.0
        && value >= i64::MIN as f64
        && value <= i64::MAX as f64
    {
        Some(value as i64)
    } else {
        None
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
    selected.sort_by(|a, b| b.start.cmp(&a.start));

    let mut out = source.to_string();
    for mut replacement in selected {
        out.replace_range(replacement.start..replacement.end, &replacement.text);
        counts.bump(replacement.kind);
        if let Some(mut proof) = replacement.arithmetic_state_proof.take() {
            proof.iteration = iteration;
            arithmetic_state_proofs.push(proof);
        }
    }
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
    let functions = all_functions(&program);
    let legacy_functions = top_level_functions(&program);
    let reference_spans = collect_reference_spans(&program);
    let (mut decoders, protected_spans) =
        detect_decoders(source, &legacy_functions, &program, scoping);
    for (symbol, decoder) in
        detect_direct_table_decoders(source, &functions, &array_infos, scoping, &reference_spans)
    {
        decoders.entry(symbol).or_insert(decoder);
    }
    let constants = collect_const_values(&program, scoping);
    let shorthand_spans = collect_shorthand_spans(&program);
    let proxies = collect_proxy_objects(&program, scoping);
    let pure_functions = collect_pure_functions(&program, scoping);
    let (dispatch_orders, zero_counters) = collect_dispatch_bindings(&program);

    let mut collector = Collector {
        source,
        scoping,
        arrays: &arrays,
        decoders: &decoders,
        constants: &constants,
        shorthand_spans: &shorthand_spans,
        proxies: &proxies,
        pure_functions: &pure_functions,
        dispatch_orders: &dispatch_orders,
        zero_counters: &zero_counters,
        reference_spans: &reference_spans,
        protected_spans: &protected_spans,
        replacements: Vec::new(),
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
