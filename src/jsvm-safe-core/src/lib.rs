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
use oxc_syntax::{scope::ScopeId, symbol::SymbolId};
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
        (Value::Number(a), Value::Number(b)) => {
            (a.is_nan() && b.is_nan()) || a.to_bits() == b.to_bits()
        }
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
        "<<" => Some(Value::Number(
            ((left.number()? as i32) << ((right.number()? as u32) & 31)) as f64,
        )),
        ">>" => Some(Value::Number(
            ((left.number()? as i32) >> ((right.number()? as u32) & 31)) as f64,
        )),
        ">>>" => Some(Value::Number(
            ((left.number()? as u32) >> ((right.number()? as u32) & 31)) as f64,
        )),
        "|" => Some(Value::Number(
            ((left.number()? as i32) | (right.number()? as i32)) as f64,
        )),
        "^" => Some(Value::Number(
            ((left.number()? as i32) ^ (right.number()? as i32)) as f64,
        )),
        "&" => Some(Value::Number(
            ((left.number()? as i32) & (right.number()? as i32)) as f64,
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

#[derive(Debug, Clone, Copy)]
enum DecoderTransform {
    Plain,
    LowerAlphabetBase64Uri,
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
        let index = (index as usize).checked_add(rotation)? % self.values.len();
        let value = self.values.get(index)?.clone();
        match (self.transform, value) {
            (DecoderTransform::Plain, value) => Some(value),
            (DecoderTransform::LowerAlphabetBase64Uri, Value::String(encoded)) => {
                decode_lower_alphabet_base64_uri(&encoded).map(Value::String)
            }
            (DecoderTransform::LowerAlphabetBase64Uri, _) => None,
        }
    }

    fn value_for_raw(&self, raw: i64) -> Option<Value> {
        self.value_for_raw_rotated(raw, 0)
    }
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

#[derive(Debug, Clone)]
struct StaticArrayInfo {
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
    static_arrays: HashMap<String, StaticArrayInfo>,
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
                        StaticArrayInfo {
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

fn detect_decoders(
    source: &str,
    functions: &[FnInfo],
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> (
    HashMap<SymbolId, Decoder>,
    Vec<(usize, usize)>,
    Vec<Replacement>,
) {
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

struct Collector<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    arrays: &'c HashMap<SymbolId, Vec<Value>>,
    decoders: &'c HashMap<SymbolId, Decoder>,
    constants: &'c HashMap<SymbolId, ConstBinding>,
    shorthand_spans: &'c HashSet<(u32, u32)>,
    proxies: &'c HashMap<SymbolId, ProxyObject>,
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
                "~" => value.number().map(|n| Value::Number((!(n as i32)) as f64)),
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
        if let Some(symbol) = symbol_of(self.scoping, &it.callee) {
            if let Some(decoder) = self.decoders.get(&symbol) {
                if let Some(raw) = it.arguments.first().and_then(argument_integer) {
                    if let Some(text) = decoder.value_for_raw(raw).and_then(|value| value.render())
                    {
                        self.push(it.span, text, "string_array_decode");
                        walk::walk_call_expression(self, it);
                        return;
                    }
                }
            }
        }
        walk::walk_call_expression(self, it);
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
    selected.sort_by(|a, b| a.start.cmp(&b.start));

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
    let functions = all_function_declarations(&program, scoping);
    let (decoders, protected_spans, rotation_replacements) =
        detect_decoders(source, &functions, &program, scoping);
    let constants = collect_const_values(&program, scoping);
    let shorthand_spans = collect_shorthand_spans(&program);
    let proxies = collect_proxy_objects(&program, scoping);
    let (dispatch_orders, zero_counters) = collect_dispatch_bindings(&program);
    let reference_spans = collect_reference_spans(&program);

    let mut collector = Collector {
        source,
        scoping,
        arrays: &arrays,
        decoders: &decoders,
        constants: &constants,
        shorthand_spans: &shorthand_spans,
        proxies: &proxies,
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
