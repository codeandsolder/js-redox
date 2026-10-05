use crate::decoder_encoding::{
    decode_fixed_base64_latin1, decode_lower_alphabet_base64_uri, decode_standard_base64_latin1,
};
use crate::rewrite::Replacement;
use crate::value_eval::{render_value_array, same_values, Value};
use crate::{argument_integer, array_element, fragment};
use oxc_ast::ast::{
    Argument, BindingPattern, CallExpression, Expression, ExpressionStatement, Statement,
    VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::Span;
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::collections::{HashMap, HashSet};

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
enum DecoderTransform {
    Plain,
    LowerAlphabetBase64Uri,
    StandardBase64,
    FixedBase64Alphabet(String),
}

#[derive(Debug, Clone)]
pub(super) struct Decoder {
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

    pub(super) fn value_for_raw(&self, raw: i64) -> Option<Value> {
        self.value_for_raw_rotated(raw, 0)
    }
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

pub(super) struct DecoderAnalysis {
    pub(super) decoders: HashMap<SymbolId, Decoder>,
    pub(super) protected_spans: Vec<(usize, usize)>,
    pub(super) replacements: Vec<Replacement>,
    pub(super) removable_helpers: HashMap<SymbolId, Span>,
}

pub(super) fn analyze_decoders(
    source: &str,
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> DecoderAnalysis {
    let arrays = decoder_static_arrays(program, scoping);
    let direct_functions = all_functions(program);
    let functions = all_function_declarations(program, scoping);

    let (mut decoders, protected_spans, replacements) =
        detect_decoders(source, &functions, program, scoping);
    for (symbol, decoder) in
        detect_direct_table_decoders(source, &direct_functions, &arrays, scoping, reference_spans)
    {
        decoders.entry(symbol).or_insert(decoder);
    }

    let removable_helpers = functions
        .iter()
        .filter(|function| decoders.contains_key(&function.symbol))
        .map(|function| (function.symbol, function.span))
        .collect();

    DecoderAnalysis {
        decoders,
        protected_spans,
        replacements,
        removable_helpers,
    }
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
