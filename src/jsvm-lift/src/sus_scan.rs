use crate::numeric::exact_u64;
use anyhow::{ensure, Result};
use base64::{engine::general_purpose, Engine as _};
use jsvm_safe_core::{string_literal_value, template_element_value};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrayExpression, ArrayExpressionElement, BinaryExpression, CallExpression,
    ComputedMemberExpression, Expression, Function, NewExpression, ObjectExpression,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::scope::ScopeFlags;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::{
    collections::{BTreeMap, HashMap},
    path::Path,
};

use crate::structural_signals::{self as structures, apiish_name};

#[derive(Debug, Clone)]
pub struct SusScanOptions {
    pub window_bytes: usize,
    pub min_score: u32,
    pub min_signals: usize,
    pub max_clusters: usize,
    pub blob_min_len: usize,
    pub include_signals: bool,
}

impl Default for SusScanOptions {
    fn default() -> Self {
        Self {
            window_bytes: 3072,
            min_score: 12,
            min_signals: 3,
            max_clusters: 20,
            blob_min_len: 96,
            include_signals: false,
        }
    }
}

impl SusScanOptions {
    pub fn validate(&self) -> Result<()> {
        ensure!(self.window_bytes >= 64, "window_bytes must be at least 64");
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct SusSignal {
    pub kind: String,
    pub weight: u32,
    pub start: u32,
    pub end: u32,
    pub line: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub subject: Option<String>,
    pub detail: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct RepeatedSubject {
    pub subject: String,
    pub count: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct SusCluster {
    pub score: u32,
    pub density_per_kib: f64,
    pub start: u32,
    pub end: u32,
    pub start_line: usize,
    pub end_line: usize,
    pub signal_count: usize,
    pub kinds: BTreeMap<String, usize>,
    pub repeated_subjects: Vec<RepeatedSubject>,
    pub signals: Vec<SusSignal>,
    pub snippet: String,
}

#[derive(Debug, Serialize)]
pub struct SusFileReport {
    pub input: String,
    pub bytes: usize,
    pub decode_encoding: String,
    pub decode_source: String,
    pub decode_had_errors: bool,
    pub decode_uncertain: bool,
    pub diagnostics: usize,
    pub fatal_error: bool,
    pub signal_count: usize,
    pub signal_kinds: BTreeMap<String, usize>,
    pub top_score: u32,
    pub clusters: Vec<SusCluster>,
    pub actionable_signal_count: usize,
    pub actionable_signal_kinds: BTreeMap<String, usize>,
    pub actionable_top_score: u32,
    pub actionable_clusters: Vec<SusCluster>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signals: Option<Vec<SusSignal>>,
}

#[derive(Debug, Serialize)]
pub struct SusScanReport {
    pub schema: &'static str,
    pub window_bytes: usize,
    pub min_score: u32,
    pub min_signals: usize,
    pub files_scanned: usize,
    pub files_with_clusters: usize,
    pub total_clusters: usize,
    pub files_with_actionable_clusters: usize,
    pub total_actionable_clusters: usize,
    pub total_actionable_signals: usize,
    pub files: Vec<SusFileReport>,
}

#[derive(Debug, Clone)]
struct RawSignal {
    kind: &'static str,
    weight: u32,
    start: u32,
    end: u32,
    subject: Option<String>,
    detail: String,
}

fn saturating_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

fn capped_u32(value: usize, cap: u32) -> u32 {
    saturating_u32(value).min(cap)
}

struct Collector<'s> {
    source: &'s str,
    blob_min_len: usize,
    signals: Vec<RawSignal>,
}

impl Collector<'_> {
    fn push(
        &mut self,
        kind: &'static str,
        weight: u32,
        span: Span,
        subject: Option<String>,
        detail: impl Into<String>,
    ) {
        self.signals.push(RawSignal {
            kind,
            weight,
            start: span.start,
            end: span.end,
            subject,
            detail: detail.into(),
        });
    }

    fn fragment(&self, span: Span) -> &str {
        self.source
            .get(span.start as usize..(span.end as usize).min(self.source.len()))
            .unwrap_or_default()
    }

    fn argument_string(arg: &Argument<'_>) -> Option<String> {
        match arg {
            Argument::StringLiteral(value) => string_literal_value(value),
            Argument::TemplateLiteral(value) if value.expressions.is_empty() => {
                value.quasis.first().and_then(template_element_value)
            }
            _ => None,
        }
    }

    fn identifier(expr: &Expression<'_>) -> Option<String> {
        match expr {
            Expression::Identifier(id) => Some(id.name.to_string()),
            _ => None,
        }
    }

    fn record_blob(&mut self, span: Span, value: &str) {
        let Some(probe) = base64_probe(value, self.blob_min_len) else {
            if value.len() >= self.blob_min_len * 2
                && looks_hex_blob(value)
                && !value.bytes().all(|b| b == b'0')
            {
                self.push(
                    "hex_blob",
                    5,
                    span,
                    None,
                    format!("{} hex chars", value.len()),
                );
            } else if value.len() >= self.blob_min_len * 4 && looks_opaque_blob(value) {
                self.push(
                    "opaque_blob",
                    3,
                    span,
                    None,
                    format!("{} compact high-variety chars", value.len()),
                );
            }
            return;
        };

        if probe.asset_like {
            return;
        }

        let size_bonus = if value.len() >= 4096 {
            6
        } else if value.len() >= 1024 {
            4
        } else if value.len() >= 256 {
            2
        } else {
            0
        };
        let weight = if probe.text_like { 6 } else { 4 } + size_bonus;
        self.push(
            "base64_blob",
            weight,
            span,
            None,
            format!(
                "{} chars; decoded prefix looks {}{}",
                value.len(),
                if probe.text_like {
                    "text-like"
                } else {
                    "binary"
                },
                probe
                    .magic
                    .as_deref()
                    .map(|kind| format!(" ({kind})"))
                    .unwrap_or_default()
            ),
        );
    }

    fn record_binary_plus(&mut self, it: &BinaryExpression<'_>) {
        if it.operator.as_str() != "+" {
            return;
        }
        let (parts, string_literals) = plus_binary_stats(it);
        if parts >= 4 && string_literals >= 1 {
            self.push(
                "string_plus_chain",
                2 + capped_u32(parts / 4, 4),
                it.span,
                None,
                format!("{parts} '+' operands; {string_literals} literal string(s)"),
            );
        }
    }

    fn record_array(&mut self, it: &ArrayExpression<'_>) {
        let mut strings = 0usize;
        let mut identifier_strings = 0usize;
        let mut api_hits = 0usize;
        let mut hot_api_hits = 0usize;
        let mut numeric = 0usize;
        let mut byte_numeric = 0usize;
        let mut printable_numeric = 0usize;
        let mut string_chars = 0usize;

        for element in &it.elements {
            match element {
                ArrayExpressionElement::StringLiteral(s) => {
                    strings += 1;
                    let Some(value) = s.value.as_str() else {
                        continue;
                    };
                    string_chars += value.len();
                    if is_identifierish(value) {
                        identifier_strings += 1;
                    }
                    if apiish_name(value) {
                        api_hits += 1;
                    }
                    if hot_api_name(value) {
                        hot_api_hits += 1;
                    }
                }
                ArrayExpressionElement::NumericLiteral(n)
                    if n.value.is_finite() && n.value.fract() == 0.0 =>
                {
                    numeric += 1;
                    if (0.0..=255.0).contains(&n.value) {
                        byte_numeric += 1;
                        if (32.0..=126.0).contains(&n.value) {
                            printable_numeric += 1;
                        }
                    }
                }
                _ => {}
            }
        }

        if strings >= 6 && api_hits >= 3 && api_hits * 4 >= strings {
            self.push(
                "api_string_table",
                4 + capped_u32(api_hits, 8) + capped_u32(hot_api_hits, 4),
                it.span,
                None,
                format!("{api_hits}/{strings} API/property names; {hot_api_hits} decoder/dynamic hot names"),
            );
        } else if strings >= 12
            && identifier_strings * 4 >= strings * 3
            && string_chars / strings.max(1) <= 24
        {
            self.push(
                "identifier_string_table",
                3 + capped_u32(strings / 16, 4),
                it.span,
                None,
                format!("{identifier_strings}/{strings} identifier-like short strings"),
            );
        }

        if numeric >= 16 && byte_numeric * 5 >= numeric * 4 {
            let printable_heavy = printable_numeric.saturating_mul(5) >= numeric.saturating_mul(3);
            let printable_percent = printable_numeric
                .saturating_mul(100)
                .saturating_add(numeric / 2)
                / numeric;
            self.push(
                if printable_heavy {
                    "charcode_array"
                } else {
                    "byte_array"
                },
                if printable_heavy { 5 } else { 3 } + capped_u32(numeric / 32, 4),
                it.span,
                None,
                format!(
                    "{byte_numeric}/{numeric} byte-range integers; {printable_percent}% printable ASCII"
                ),
            );
        }
    }

    fn record_computed_lookup(&mut self, it: &ComputedMemberExpression<'_>) {
        let Some(subject) = Self::identifier(&it.object) else {
            return;
        };
        if matches!(it.expression, Expression::StringLiteral(_)) {
            return;
        }
        let dynamic = !matches!(
            it.expression,
            Expression::NumericLiteral(_)
                | Expression::BooleanLiteral(_)
                | Expression::NullLiteral(_)
        );
        self.push(
            "indexed_lookup",
            if dynamic { 2 } else { 1 },
            it.span,
            Some(subject),
            if dynamic {
                "dynamic computed index"
            } else {
                "computed numeric/literal index"
            },
        );
    }

    fn record_structural_call(&mut self, it: &CallExpression<'_>) {
        for signal in structures::call_signals(it) {
            self.push(
                signal.kind,
                signal.weight,
                signal.span,
                signal.subject,
                signal.detail,
            );
        }
    }

    fn record_structural_object(&mut self, it: &ObjectExpression<'_>) {
        for signal in structures::object_signals(it) {
            self.push(
                signal.kind,
                signal.weight,
                signal.span,
                signal.subject,
                signal.detail,
            );
        }
    }

    fn record_structural_function(&mut self, it: &Function<'_>) {
        for signal in structures::function_signals(it) {
            self.push(
                signal.kind,
                signal.weight,
                signal.span,
                signal.subject,
                signal.detail,
            );
        }
    }

    fn record_decoder_calls(&mut self, it: &CallExpression<'_>, callee: &str, lower: &str) {
        if callee == "String.fromCharCode"
            || callee.ends_with(".fromCharCode")
            || callee.contains("fromCharCode.apply")
            || callee == "String.fromCodePoint"
            || callee.ends_with(".fromCodePoint")
            || callee.contains("fromCodePoint.apply")
        {
            let numeric_args = it
                .arguments
                .iter()
                .filter(|arg| matches!(arg, Argument::NumericLiteral(_)))
                .count();
            self.push(
                "charcode_decode_call",
                6 + capped_u32(it.arguments.len() / 4, 6),
                it.span,
                None,
                format!(
                    "{} args; {numeric_args} immediate numeric literal(s)",
                    it.arguments.len()
                ),
            );
        }

        if is_identifierish(callee)
            && !matches!(
                callee,
                "Number"
                    | "String"
                    | "Boolean"
                    | "parseInt"
                    | "parseFloat"
                    | "setTimeout"
                    | "setInterval"
                    | "require"
            )
            && it.arguments.len() <= 3
        {
            if let Some(first) = it.arguments.first() {
                if matches!(first, Argument::NumericLiteral(_)) {
                    let raw = self.fragment(first.span()).trim();
                    let hex = raw.starts_with("0x") || raw.starts_with("0X");
                    self.push(
                        "numeric_decoder_call_candidate",
                        if hex { 3 } else { 2 },
                        it.span,
                        Some(format!("call:{callee}")),
                        if hex {
                            "identifier call with hexadecimal numeric argument"
                        } else {
                            "identifier call with numeric argument"
                        },
                    );
                }
            }
        }

        if lower == "atob"
            || lower.ends_with(".atob")
            || (callee == "Buffer.from"
                && it
                    .arguments
                    .get(1)
                    .and_then(Self::argument_string)
                    .is_some_and(|value| value.eq_ignore_ascii_case("base64")))
        {
            self.push(
                "base64_decode_call",
                8,
                it.span,
                None,
                format!("decoder call via {callee}"),
            );
        }

        if matches!(callee, "eval" | "Function")
            || callee.ends_with(".eval")
            || lower.ends_with(".constructor")
        {
            self.push(
                "dynamic_code_call",
                9,
                it.span,
                None,
                format!("dynamic-code-like call via {callee}"),
            );
        }

        if matches!(callee, "setTimeout" | "setInterval")
            && it
                .arguments
                .first()
                .and_then(Self::argument_string)
                .is_some()
        {
            self.push(
                "string_timer_call",
                7,
                it.span,
                None,
                format!("{callee} called with literal string"),
            );
        }
    }

    fn record_string_assembly_calls(&mut self, it: &CallExpression<'_>, callee: &str) {
        if callee.ends_with(".join") {
            if let Expression::StaticMemberExpression(member) = &it.callee {
                let empty_or_tiny_separator = it
                    .arguments
                    .first()
                    .and_then(Self::argument_string)
                    .map_or(it.arguments.is_empty(), |sep| sep.len() <= 1);
                if empty_or_tiny_separator {
                    let literal_parts = match &member.object {
                        Expression::ArrayExpression(array) => array.elements.len(),
                        _ => 0,
                    };
                    self.push(
                        "string_join",
                        if literal_parts >= 4 { 5 } else { 2 },
                        it.span,
                        Self::identifier(&member.object),
                        if literal_parts >= 4 {
                            format!("join over {literal_parts} literal array elements")
                        } else {
                            "join with empty/tiny separator".to_string()
                        },
                    );
                }
            }
        }

        if callee.ends_with(".concat") && it.arguments.len() >= 2 {
            self.push(
                "concat_call",
                2 + capped_u32(it.arguments.len() / 3, 3),
                it.span,
                None,
                format!("{} concatenation argument(s)", it.arguments.len()),
            );
        }

        if (callee.ends_with(".toString") || callee == "Number.prototype.toString")
            && it.arguments.first().is_some_and(|arg| {
                matches!(arg, Argument::NumericLiteral(n) if exact_u64(n.value).is_some_and(|value| matches!(value, 16 | 32 | 36)))
            })
        {
            self.push(
                "radix_string_call",
                4,
                it.span,
                None,
                format!("radix conversion via {callee}"),
            );
        }
    }

    fn record_argument_decode_calls(&mut self, it: &CallExpression<'_>, callee: &str) {
        for arg in &it.arguments {
            let Some(value) = Self::argument_string(arg) else {
                continue;
            };
            if base64_probe(&value, self.blob_min_len).is_some_and(|probe| !probe.asset_like) {
                self.push(
                    "base64_call_arg",
                    7,
                    arg.span(),
                    None,
                    format!(
                        "{}-char base64-like literal passed to {callee}",
                        value.len()
                    ),
                );
            }
        }

        if let Expression::ComputedMemberExpression(member) = &it.callee {
            let subject = Self::identifier(&member.object);
            self.push(
                "computed_dispatch_call",
                4,
                it.span,
                subject,
                "call through computed member".to_string(),
            );
        }

        if matches!(
            callee,
            "decodeURIComponent" | "unescape" | "TextDecoder.prototype.decode"
        ) && it
            .arguments
            .first()
            .and_then(Self::argument_string)
            .is_some_and(|value| value.len() >= 32)
        {
            self.push(
                "text_decode_call",
                4,
                it.span,
                None,
                format!("literal decoding via {callee}"),
            );
        }
    }

    fn record_call(&mut self, it: &CallExpression<'_>) {
        self.record_structural_call(it);
        let callee = self.fragment(it.callee.span()).trim().to_string();
        let lower = callee.to_ascii_lowercase();
        self.record_decoder_calls(it, &callee, &lower);
        self.record_string_assembly_calls(it, &callee);
        self.record_argument_decode_calls(it, &callee);
    }

    fn record_new(&mut self, it: &NewExpression<'_>) {
        let callee = self.fragment(it.callee.span()).trim().to_string();
        if callee == "Function" || callee.ends_with(".Function") {
            self.push(
                "dynamic_code_constructor",
                10,
                it.span,
                None,
                format!("new {callee}(...)"),
            );
        }
    }
}

impl<'a> Visit<'a> for Collector<'_> {
    fn visit_function(&mut self, it: &Function<'a>, flags: ScopeFlags) {
        self.record_structural_function(it);
        walk::walk_function(self, it, flags);
    }

    fn visit_expression(&mut self, it: &Expression<'a>) {
        match it {
            Expression::StringLiteral(value) => {
                if let Some(text) = value.value.as_str() {
                    self.record_blob(value.span, text);
                }
            }
            Expression::TemplateLiteral(value) if value.expressions.len() >= 4 => self.push(
                "template_assembly",
                3 + capped_u32(value.expressions.len() / 4, 4),
                value.span,
                None,
                format!("{} interpolated expressions", value.expressions.len()),
            ),
            _ => {}
        }
        walk::walk_expression(self, it);
    }

    fn visit_binary_expression(&mut self, it: &BinaryExpression<'a>) {
        self.record_binary_plus(it);
        if matches!(it.operator.as_str(), "^" | "<<" | ">>" | ">>>") {
            self.push(
                "bitwise_mix",
                1,
                it.span,
                None,
                format!("{} expression", it.operator.as_str()),
            );
        }
        walk::walk_binary_expression(self, it);
    }

    fn visit_array_expression(&mut self, it: &ArrayExpression<'a>) {
        self.record_array(it);
        walk::walk_array_expression(self, it);
    }

    fn visit_object_expression(&mut self, it: &ObjectExpression<'a>) {
        self.record_structural_object(it);
        walk::walk_object_expression(self, it);
    }

    fn visit_computed_member_expression(&mut self, it: &ComputedMemberExpression<'a>) {
        self.record_computed_lookup(it);
        walk::walk_computed_member_expression(self, it);
    }

    fn visit_call_expression(&mut self, it: &CallExpression<'a>) {
        self.record_call(it);
        walk::walk_call_expression(self, it);
    }

    fn visit_new_expression(&mut self, it: &NewExpression<'a>) {
        self.record_new(it);
        walk::walk_new_expression(self, it);
    }
}

#[derive(Debug)]
struct Base64Probe {
    text_like: bool,
    asset_like: bool,
    magic: Option<String>,
}

fn base64_probe(value: &str, min_len: usize) -> Option<Base64Probe> {
    let trimmed = value.trim();
    if trimmed.len() < min_len {
        return None;
    }

    let lower = trimmed.get(..trimmed.len().min(64))?.to_ascii_lowercase();
    if lower.starts_with("data:image/")
        || lower.starts_with("data:font/")
        || lower.starts_with("data:audio/")
        || lower.starts_with("data:video/")
    {
        return Some(Base64Probe {
            text_like: false,
            asset_like: true,
            magic: Some("data-uri asset".into()),
        });
    }

    let payload = if lower.starts_with("data:") {
        let comma = trimmed.find(',')?;
        if !trimmed[..comma].to_ascii_lowercase().contains(";base64") {
            return None;
        }
        &trimmed[comma + 1..]
    } else {
        trimmed
    };

    if payload.len() < min_len {
        return None;
    }

    let mut valid = 0usize;
    let mut seen = 0usize;
    for b in payload
        .bytes()
        .filter(|b| !b.is_ascii_whitespace())
        .take(8192)
    {
        seen += 1;
        if b.is_ascii_alphanumeric() || matches!(b, b'+' | b'/' | b'_' | b'-' | b'=') {
            valid += 1;
        }
    }
    if seen < min_len.min(128) || valid * 100 < seen * 98 {
        return None;
    }

    let mut sample: String = payload
        .chars()
        .filter(|c| !c.is_ascii_whitespace())
        .take(4096)
        .collect();
    if sample.len() < min_len {
        return None;
    }
    let usable = sample.len() / 4 * 4;
    if usable < 16 {
        return None;
    }
    sample.truncate(usable);

    let decoded = general_purpose::STANDARD
        .decode(sample.as_bytes())
        .or_else(|_| general_purpose::URL_SAFE.decode(sample.as_bytes()))
        .or_else(|_| {
            general_purpose::STANDARD_NO_PAD.decode(sample.trim_end_matches('=').as_bytes())
        })
        .or_else(|_| {
            general_purpose::URL_SAFE_NO_PAD.decode(sample.trim_end_matches('=').as_bytes())
        })
        .ok()?;

    let magic = decoded_magic(&decoded);
    let asset_like = magic.is_some_and(|kind| {
        matches!(
            kind,
            "png" | "jpeg" | "gif" | "webp" | "svg" | "woff" | "woff2" | "ttf" | "otf" | "pdf"
        )
    });

    let printable = decoded
        .iter()
        .filter(|&&b| b == b'\n' || b == b'\r' || b == b'\t' || (0x20..=0x7e).contains(&b))
        .count();
    let text_like = !decoded.is_empty() && printable * 100 >= decoded.len() * 82;

    Some(Base64Probe {
        text_like,
        asset_like,
        magic: magic.map(str::to_string),
    })
}

fn decoded_magic(decoded: &[u8]) -> Option<&'static str> {
    if decoded.starts_with(b"\x89PNG\r\n\x1a\n") {
        Some("png")
    } else if decoded.starts_with(&[0xff, 0xd8, 0xff]) {
        Some("jpeg")
    } else if decoded.starts_with(b"GIF87a") || decoded.starts_with(b"GIF89a") {
        Some("gif")
    } else if decoded.len() >= 12 && decoded.starts_with(b"RIFF") && &decoded[8..12] == b"WEBP" {
        Some("webp")
    } else if decoded
        .iter()
        .copied()
        .skip_while(u8::is_ascii_whitespace)
        .take(4)
        .eq(b"<svg".iter().copied())
    {
        Some("svg")
    } else if decoded.starts_with(b"wOFF") {
        Some("woff")
    } else if decoded.starts_with(b"wOF2") {
        Some("woff2")
    } else if decoded.starts_with(&[0x00, 0x01, 0x00, 0x00]) {
        Some("ttf")
    } else if decoded.starts_with(b"OTTO") {
        Some("otf")
    } else if decoded.starts_with(b"%PDF-") {
        Some("pdf")
    } else if decoded.starts_with(b"PK\x03\x04") {
        Some("zip")
    } else if decoded.starts_with(&[0x1f, 0x8b]) {
        Some("gzip")
    } else if decoded.starts_with(b"\0asm") {
        Some("wasm")
    } else {
        None
    }
}

fn looks_hex_blob(value: &str) -> bool {
    let trimmed = value.trim();
    trimmed.len() >= 128
        && trimmed.len().is_multiple_of(2)
        && trimmed.bytes().all(|b| b.is_ascii_hexdigit())
}

fn looks_opaque_blob(value: &str) -> bool {
    let trimmed = value.trim();
    if trimmed.bytes().any(|b| b.is_ascii_whitespace()) {
        return false;
    }
    let mut seen = [false; 128];
    let mut unique = 0usize;
    for b in trimmed.bytes().take(8192) {
        if !b.is_ascii() || b.is_ascii_control() {
            return false;
        }
        if !seen[b as usize] {
            seen[b as usize] = true;
            unique += 1;
        }
    }
    unique >= 32
}

fn plus_binary_stats(expr: &BinaryExpression<'_>) -> (usize, usize) {
    fn walk_expr(expr: &Expression<'_>, parts: &mut usize, strings: &mut usize) {
        if let Expression::BinaryExpression(binary) = expr {
            if binary.operator.as_str() == "+" {
                walk_expr(&binary.left, parts, strings);
                walk_expr(&binary.right, parts, strings);
                return;
            }
        }
        *parts += 1;
        if matches!(
            expr,
            Expression::StringLiteral(_) | Expression::TemplateLiteral(_)
        ) {
            *strings += 1;
        }
    }

    let mut parts = 0usize;
    let mut strings = 0usize;
    walk_expr(&expr.left, &mut parts, &mut strings);
    walk_expr(&expr.right, &mut parts, &mut strings);
    (parts, strings)
}

fn is_identifierish(value: &str) -> bool {
    let mut chars = value.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first == '$' || first.is_ascii_alphabetic())
        && chars.all(|c| c == '_' || c == '$' || c.is_ascii_alphanumeric())
}

fn hot_api_name(value: &str) -> bool {
    matches!(
        value,
        "constructor"
            | "prototype"
            | "eval"
            | "Function"
            | "atob"
            | "btoa"
            | "fromCharCode"
            | "fromCodePoint"
            | "charCodeAt"
            | "decodeURIComponent"
            | "unescape"
    )
}

fn line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0usize];
    for (index, byte) in source.bytes().enumerate() {
        if byte == b'\n' {
            starts.push(index + 1);
        }
    }
    starts
}

fn line_for(starts: &[usize], offset: usize) -> usize {
    starts.partition_point(|&start| start <= offset).max(1)
}

fn compact_snippet(source: &str, start: usize, end: usize) -> String {
    let start = start.min(source.len());
    let end = end.min(source.len()).max(start);
    let fragment = source.get(start..end).unwrap_or_default();
    let mut out = String::new();
    let mut previous_space = false;
    for ch in fragment.chars().take(280) {
        if ch.is_whitespace() {
            if !previous_space {
                out.push(' ');
                previous_space = true;
            }
        } else {
            out.push(ch);
            previous_space = false;
        }
    }
    if fragment.chars().count() > 280 {
        out.push('…');
    }
    out
}

fn materialize_signal(raw: &RawSignal, lines: &[usize]) -> SusSignal {
    SusSignal {
        kind: raw.kind.to_string(),
        weight: raw.weight,
        start: raw.start,
        end: raw.end,
        line: line_for(lines, raw.start as usize),
        subject: raw.subject.clone(),
        detail: raw.detail.clone(),
    }
}

fn is_actionable_signal(kind: &str) -> bool {
    // Broad discovery signals below are common in ordinary minified/bundled code.
    // Keep them in raw evidence, but do not let them alone keep a body in residual debt.
    !matches!(
        kind,
        "indexed_lookup"
            | "numeric_decoder_call_candidate"
            | "computed_dispatch_call"
            | "string_plus_chain"
            | "string_join"
            | "concat_call"
            | "template_assembly"
            | "bitwise_mix"
            | "identifier_string_table"
            | "byte_array"
    )
}
fn normalize_signals(raw: Vec<RawSignal>) -> Vec<RawSignal> {
    // Left-associative string concatenation is represented as nested BinaryExpression
    // nodes. Without normalization, one ordinary long expression such as
    // `a + b + c + ...` produces O(n) overlapping string_plus_chain signals and can
    // dominate a cluster by itself. Keep only the outermost chain for each contained
    // region; its weight/detail already encode the operand count.
    let mut order = (0..raw.len()).collect::<Vec<_>>();
    order.sort_by_key(|&index| {
        let signal = &raw[index];
        (signal.start, std::cmp::Reverse(signal.end))
    });

    let mut keep = vec![true; raw.len()];
    let mut outer_string_chains: Vec<(u32, u32)> = Vec::new();
    for index in order {
        let signal = &raw[index];
        if signal.kind != "string_plus_chain" {
            continue;
        }
        if outer_string_chains
            .iter()
            .any(|&(start, end)| start <= signal.start && end >= signal.end)
        {
            keep[index] = false;
            continue;
        }
        outer_string_chains.push((signal.start, signal.end));
    }

    raw.into_iter()
        .enumerate()
        .filter_map(|(index, signal)| keep[index].then_some(signal))
        .collect()
}

#[derive(Debug, Clone)]
struct ClusterCandidate {
    score: u32,
    density_per_kib: f64,
    start: u32,
    end: u32,
    left: usize,
    right: usize,
}

fn score_cluster_candidates(
    signals: &[RawSignal],
    window_bytes: usize,
    min_score: u32,
    min_signals: usize,
) -> Vec<ClusterCandidate> {
    let mut candidates = Vec::with_capacity(signals.len().min(4096));
    let mut right = 0usize;
    let mut weight_sum = 0u32;
    let mut kind_counts: HashMap<&'static str, usize> = HashMap::new();
    let mut subject_counts: HashMap<String, usize> = HashMap::new();

    for left in 0..signals.len() {
        if right < left {
            right = left;
        }
        while right < signals.len()
            && signals[right].start.saturating_sub(signals[left].start) as usize <= window_bytes
        {
            let signal = &signals[right];
            weight_sum += signal.weight;
            *kind_counts.entry(signal.kind).or_default() += 1;
            if let Some(subject) = &signal.subject {
                *subject_counts.entry(subject.clone()).or_default() += 1;
            }
            right += 1;
        }

        let count = right.saturating_sub(left);
        if count >= min_signals || weight_sum >= min_score {
            let repeated_bonus = subject_counts
                .values()
                .filter(|&&count| count >= 3)
                .map(|&count| 3_u32.saturating_add(saturating_u32(count.saturating_sub(3))))
                .sum::<u32>();
            let mut score = weight_sum
                .saturating_add(
                    saturating_u32(kind_counts.len().saturating_sub(1)).saturating_mul(2),
                )
                .saturating_add(repeated_bonus);
            let start = signals[left].start;
            let end = signals[right - 1].end;
            let span = end.saturating_sub(start).max(1);
            if span as usize <= window_bytes / 4 {
                score += 3;
            } else if span as usize <= window_bytes / 2 {
                score += 1;
            }
            if score >= min_score {
                candidates.push(ClusterCandidate {
                    score,
                    density_per_kib: f64::from(score) * 1024.0 / f64::from(span),
                    start,
                    end,
                    left,
                    right,
                });
            }
        }

        if left < right {
            let signal = &signals[left];
            weight_sum = weight_sum.saturating_sub(signal.weight);
            if let Some(count) = kind_counts.get_mut(signal.kind) {
                *count -= 1;
                if *count == 0 {
                    kind_counts.remove(signal.kind);
                }
            }
            if let Some(subject) = &signal.subject {
                if let Some(count) = subject_counts.get_mut(subject) {
                    *count -= 1;
                    if *count == 0 {
                        subject_counts.remove(subject);
                    }
                }
            }
        }
    }
    candidates
}

fn suppress_overlapping_candidates(
    mut candidates: Vec<ClusterCandidate>,
    max_clusters: usize,
) -> Vec<ClusterCandidate> {
    candidates.sort_by(|a, b| {
        b.score
            .cmp(&a.score)
            .then_with(|| b.density_per_kib.total_cmp(&a.density_per_kib))
            .then_with(|| a.start.cmp(&b.start))
    });
    let mut selected: Vec<ClusterCandidate> = Vec::with_capacity(max_clusters);
    'candidate: for candidate in candidates {
        for existing in &selected {
            let overlap_start = candidate.start.max(existing.start);
            let overlap_end = candidate.end.min(existing.end);
            let overlap = overlap_end.saturating_sub(overlap_start);
            let shorter = candidate
                .end
                .saturating_sub(candidate.start)
                .min(existing.end.saturating_sub(existing.start))
                .max(1);
            if overlap * 100 >= shorter * 60 {
                continue 'candidate;
            }
        }
        selected.push(candidate);
        if selected.len() >= max_clusters {
            break;
        }
    }
    selected
}

fn materialize_clusters(
    source: &str,
    signals: &[RawSignal],
    candidates: Vec<ClusterCandidate>,
) -> Vec<SusCluster> {
    let lines = line_starts(source);
    let mut selected = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let window = &signals[candidate.left..candidate.right];
        let mut kinds = BTreeMap::new();
        let mut repeated_counts: HashMap<String, usize> = HashMap::new();
        for signal in window {
            *kinds.entry(signal.kind.to_string()).or_default() += 1;
            if let Some(subject) = &signal.subject {
                *repeated_counts.entry(subject.clone()).or_default() += 1;
            }
        }
        let mut repeated_subjects = repeated_counts
            .into_iter()
            .filter(|(_, count)| *count >= 3)
            .map(|(subject, count)| RepeatedSubject { subject, count })
            .collect::<Vec<_>>();
        repeated_subjects.sort_by_key(|item| std::cmp::Reverse(item.count));
        selected.push(SusCluster {
            score: candidate.score,
            density_per_kib: candidate.density_per_kib,
            start: candidate.start,
            end: candidate.end,
            start_line: line_for(&lines, candidate.start as usize),
            end_line: line_for(&lines, candidate.end.saturating_sub(1) as usize),
            signal_count: window.len(),
            kinds,
            repeated_subjects,
            signals: window
                .iter()
                .map(|signal| materialize_signal(signal, &lines))
                .collect(),
            snippet: compact_snippet(source, candidate.start as usize, candidate.end as usize),
        });
    }
    selected.sort_by_key(|cluster| std::cmp::Reverse(cluster.score));
    selected
}

fn cluster_signals(
    source: &str,
    raw: &[RawSignal],
    window_bytes: usize,
    min_score: u32,
    min_signals: usize,
    max_clusters: usize,
) -> Vec<SusCluster> {
    if raw.is_empty() || max_clusters == 0 {
        return Vec::new();
    }
    let mut signals = raw.to_vec();
    signals.sort_by_key(|signal| (signal.start, signal.end));
    let candidates = score_cluster_candidates(&signals, window_bytes, min_score, min_signals);
    let selected = suppress_overlapping_candidates(candidates, max_clusters);
    materialize_clusters(source, &signals, selected)
}

fn parse_source<'a>(
    allocator: &'a Allocator,
    source: &'a str,
    path: &Path,
) -> (oxc_ast::ast::Program<'a>, usize, bool) {
    let source_type = match path.extension().and_then(|ext| ext.to_str()) {
        Some("cjs") => SourceType::cjs(),
        _ => SourceType::mjs(),
    };
    let parsed = parse_program(allocator, source, source_type);
    let diagnostics = parsed.diagnostics;
    (parsed.program, diagnostics, parsed.fatal_error)
}

pub fn analyze_source(
    source: &str,
    input: &Path,
    options: &SusScanOptions,
) -> Result<SusFileReport> {
    options.validate()?;
    let allocator = Allocator::default();
    let (program, diagnostics, fatal_error) = parse_source(&allocator, source, input);

    let mut collector = Collector {
        source,
        blob_min_len: options.blob_min_len,
        signals: Vec::new(),
    };
    if !fatal_error {
        collector.visit_program(&program);
    }

    let signals = normalize_signals(collector.signals);
    let mut signal_kinds = BTreeMap::new();
    for signal in &signals {
        *signal_kinds.entry(signal.kind.to_string()).or_default() += 1;
    }
    let clusters = cluster_signals(
        source,
        &signals,
        options.window_bytes,
        options.min_score,
        options.min_signals,
        options.max_clusters,
    );
    let top_score = clusters.first().map_or(0, |cluster| cluster.score);
    let actionable_signals = signals
        .iter()
        .filter(|signal| is_actionable_signal(signal.kind))
        .cloned()
        .collect::<Vec<_>>();
    let mut actionable_signal_kinds = BTreeMap::new();
    for signal in &actionable_signals {
        *actionable_signal_kinds
            .entry(signal.kind.to_string())
            .or_default() += 1;
    }
    let actionable_clusters = cluster_signals(
        source,
        &actionable_signals,
        options.window_bytes,
        options.min_score,
        options.min_signals,
        options.max_clusters,
    );
    let actionable_top_score = actionable_clusters
        .first()
        .map_or(0, |cluster| cluster.score);
    let lines = line_starts(source);

    Ok(SusFileReport {
        input: input.display().to_string(),
        bytes: source.len(),
        decode_encoding: "UTF-8".to_string(),
        decode_source: "already-unicode".to_string(),
        decode_had_errors: false,
        decode_uncertain: false,
        diagnostics,
        fatal_error,
        signal_count: signals.len(),
        signal_kinds,
        top_score,
        clusters,
        actionable_signal_count: actionable_signals.len(),
        actionable_signal_kinds,
        actionable_top_score,
        actionable_clusters,
        signals: options.include_signals.then(|| {
            signals
                .iter()
                .map(|signal| materialize_signal(signal, &lines))
                .collect()
        }),
    })
}

pub fn build_report(
    mut files: Vec<SusFileReport>,
    options: &SusScanOptions,
) -> Result<SusScanReport> {
    options.validate()?;
    files.sort_by(|a, b| {
        b.actionable_top_score
            .cmp(&a.actionable_top_score)
            .then_with(|| b.top_score.cmp(&a.top_score))
            .then_with(|| a.input.cmp(&b.input))
    });
    let files_with_clusters = files
        .iter()
        .filter(|file| !file.clusters.is_empty())
        .count();
    let total_clusters = files.iter().map(|file| file.clusters.len()).sum();
    let files_with_actionable_clusters = files
        .iter()
        .filter(|file| !file.actionable_clusters.is_empty())
        .count();
    let total_actionable_clusters = files
        .iter()
        .map(|file| file.actionable_clusters.len())
        .sum();
    let total_actionable_signals = files.iter().map(|file| file.actionable_signal_count).sum();
    Ok(SusScanReport {
        schema: "js-sus-scan/v3",
        window_bytes: options.window_bytes,
        min_score: options.min_score,
        min_signals: options.min_signals,
        files_scanned: files.len(),
        files_with_clusters,
        total_clusters,
        files_with_actionable_clusters,
        total_actionable_clusters,
        total_actionable_signals,
        files,
    })
}
