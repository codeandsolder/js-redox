use crate::{
    browser_decode::{decode_script, ScriptDecodeContext},
    numeric::exact_u64,
};
use anyhow::{ensure, Context, Result};
use base64::{engine::general_purpose, Engine as _};
use jsvm_safe_core::{
    eval_static_primitive, recover_browser_legacy_call_assignments, string_literal_value,
    template_element_value,
};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrayExpression, ArrayExpressionElement, BinaryExpression, CallExpression,
    ComputedMemberExpression, Expression, Function, NewExpression, ObjectExpression,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::scope::ScopeFlags;
use serde::Serialize;
use std::{
    collections::{BTreeMap, HashMap},
    fs,
    path::{Path, PathBuf},
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

#[derive(Debug, Clone, Serialize)]
pub struct SusOpaqueParseSpan {
    pub start: u32,
    pub end: u32,
    pub kind: String,
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
    pub parser_fatal_error: bool,
    pub fatal_error: bool,
    pub analysis_complete: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub parse_recovery: Option<String>,
    pub opaque_parse_spans: Vec<SusOpaqueParseSpan>,
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
    pub files_with_parse_recovery: usize,
    pub files_with_incomplete_analysis: usize,
    pub files_with_fatal_error: usize,
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

    fn argument_static_string(arg: &Argument<'_>) -> Option<String> {
        eval_static_primitive(arg.as_expression()?)?.js_string()
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
            if numeric_args > 0 && numeric_args == it.arguments.len() {
                self.push(
                    "charcode_literal_decode",
                    7 + capped_u32(numeric_args / 4, 6),
                    it.span,
                    None,
                    format!("{numeric_args} immediate numeric code point(s)"),
                );
            }
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
            let static_source = if callee == "eval" || callee.ends_with(".eval") {
                it.arguments
                    .first()
                    .is_none_or(|arg| Self::argument_static_string(arg).is_some())
            } else {
                it.arguments
                    .iter()
                    .all(|arg| Self::argument_static_string(arg).is_some())
            };
            self.push(
                if static_source {
                    "static_dynamic_code_call"
                } else {
                    "dynamic_code_call"
                },
                if static_source { 3 } else { 9 },
                it.span,
                None,
                if static_source {
                    format!("dynamic-code-like call via {callee} with statically known source")
                } else {
                    format!("dynamic-code-like call via {callee}")
                },
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
            let static_source = it
                .arguments
                .iter()
                .all(|arg| Self::argument_static_string(arg).is_some());
            self.push(
                if static_source {
                    "static_dynamic_code_constructor"
                } else {
                    "dynamic_code_constructor"
                },
                if static_source { 3 } else { 10 },
                it.span,
                None,
                if static_source {
                    format!("new {callee}(...) with statically known source")
                } else {
                    format!("new {callee}(...)")
                },
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
            | "charcode_decode_call"
            | "base64_decode_call"
            | "radix_string_call"
            | "base64_blob"
            | "opaque_blob"
            | "static_dynamic_code_call"
            | "static_dynamic_code_constructor"
            | "string_timer_call"
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

fn primary_source_type(path: &Path) -> SourceType {
    match path.extension().and_then(|ext| ext.to_str()) {
        Some("cjs") => SourceType::cjs(),
        _ => SourceType::mjs(),
    }
}

fn overlaps_opaque_span(signal: &RawSignal, opaque_spans: &[SusOpaqueParseSpan]) -> bool {
    opaque_spans
        .iter()
        .any(|span| signal.start < span.end && span.start < signal.end)
}

struct ParseAnalysisState {
    diagnostics: usize,
    parser_fatal_error: bool,
    fatal_error: bool,
    analysis_complete: bool,
    parse_recovery: Option<String>,
    opaque_parse_spans: Vec<SusOpaqueParseSpan>,
}

fn analyze_program(
    source: &str,
    input: &Path,
    options: &SusScanOptions,
    program: &oxc_ast::ast::Program<'_>,
    state: ParseAnalysisState,
) -> Result<SusFileReport> {
    let ParseAnalysisState {
        diagnostics,
        parser_fatal_error,
        fatal_error,
        analysis_complete,
        parse_recovery,
        opaque_parse_spans,
    } = state;
    let mut collector = Collector {
        source,
        blob_min_len: options.blob_min_len,
        signals: Vec::new(),
    };
    if !fatal_error {
        collector.visit_program(program);
    }
    if !opaque_parse_spans.is_empty() {
        collector
            .signals
            .retain(|signal| !overlaps_opaque_span(signal, &opaque_parse_spans));
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
        parser_fatal_error,
        fatal_error,
        analysis_complete,
        parse_recovery,
        opaque_parse_spans,
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

pub fn analyze_source(
    source: &str,
    input: &Path,
    options: &SusScanOptions,
) -> Result<SusFileReport> {
    options.validate()?;
    let source_type = primary_source_type(input);
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, source_type).parse();
    if !parsed.fatal_error {
        return analyze_program(
            source,
            input,
            options,
            &parsed.program,
            ParseAnalysisState {
                diagnostics: parsed.diagnostics.len(),
                parser_fatal_error: false,
                fatal_error: false,
                analysis_complete: true,
                parse_recovery: None,
                opaque_parse_spans: Vec::new(),
            },
        );
    }

    let initial_diagnostics = parsed.diagnostics.len();
    let may_try_classic = path_allows_classic_fallback(input);
    if may_try_classic {
        let classic_allocator = Allocator::default();
        let classic = Parser::new(&classic_allocator, source, SourceType::cjs()).parse();
        if !classic.fatal_error {
            return analyze_program(
                source,
                input,
                options,
                &classic.program,
                ParseAnalysisState {
                    diagnostics: classic.diagnostics.len(),
                    parser_fatal_error: true,
                    fatal_error: false,
                    analysis_complete: true,
                    parse_recovery: Some("classic-script-fallback".to_string()),
                    opaque_parse_spans: Vec::new(),
                },
            );
        }
        if let Some(recovery) = recover_browser_legacy_call_assignments(source, SourceType::cjs()) {
            let recovery_allocator = Allocator::default();
            let recovered =
                Parser::new(&recovery_allocator, &recovery.source, SourceType::cjs()).parse();
            if !recovered.fatal_error {
                return analyze_program(
                    source,
                    input,
                    options,
                    &recovered.program,
                    ParseAnalysisState {
                        diagnostics: recovered.diagnostics.len(),
                        parser_fatal_error: true,
                        fatal_error: false,
                        analysis_complete: false,
                        parse_recovery: Some("browser-legacy-call-assignment".to_string()),
                        opaque_parse_spans: recovery
                            .opaque_spans
                            .into_iter()
                            .map(|span| SusOpaqueParseSpan {
                                start: span.start,
                                end: span.end,
                                kind: "browser_legacy_call_assignment_target".to_string(),
                            })
                            .collect(),
                    },
                );
            }
        }
    } else if let Some(recovery) = recover_browser_legacy_call_assignments(source, source_type) {
        let recovery_allocator = Allocator::default();
        let recovered = Parser::new(&recovery_allocator, &recovery.source, source_type).parse();
        if !recovered.fatal_error {
            return analyze_program(
                source,
                input,
                options,
                &recovered.program,
                ParseAnalysisState {
                    diagnostics: recovered.diagnostics.len(),
                    parser_fatal_error: true,
                    fatal_error: false,
                    analysis_complete: false,
                    parse_recovery: Some("browser-legacy-call-assignment".to_string()),
                    opaque_parse_spans: recovery
                        .opaque_spans
                        .into_iter()
                        .map(|span| SusOpaqueParseSpan {
                            start: span.start,
                            end: span.end,
                            kind: "browser_legacy_call_assignment_target".to_string(),
                        })
                        .collect(),
                },
            );
        }
    }

    analyze_program(
        source,
        input,
        options,
        &parsed.program,
        ParseAnalysisState {
            diagnostics: initial_diagnostics,
            parser_fatal_error: true,
            fatal_error: true,
            analysis_complete: false,
            parse_recovery: None,
            opaque_parse_spans: Vec::new(),
        },
    )
}

fn path_allows_classic_fallback(path: &Path) -> bool {
    !matches!(path.extension().and_then(|ext| ext.to_str()), Some("mjs"))
}

/// Analyze a JavaScript file from raw bytes using the same browser-oriented
/// decoding fallback as capture ingestion. Detached classic scripts cannot
/// recover their embedding document encoding, so replacement decoding remains
/// explicitly uncertain rather than failing the scan.
pub fn analyze_bytes(
    bytes: &[u8],
    input: &Path,
    options: &SusScanOptions,
) -> Result<SusFileReport> {
    if let Ok(source) = std::str::from_utf8(bytes) {
        return analyze_source(source, input, options);
    }

    let decoded = decode_script(bytes, ScriptDecodeContext::classic_unknown());
    let mut report = analyze_source(&decoded.source, input, options)?;
    report.bytes = bytes.len();
    report.decode_encoding = decoded.encoding;
    report.decode_source = decoded.decode_source.as_str().to_string();
    report.decode_had_errors = decoded.had_errors;
    report.decode_uncertain = decoded.uncertain;
    Ok(report)
}

/// Read and analyze one explicitly selected source file.
pub fn scan_file(path: &Path, options: &SusScanOptions) -> Result<SusFileReport> {
    let bytes = fs::read(path).with_context(|| format!("reading JavaScript {}", path.display()))?;
    analyze_bytes(&bytes, path, options)
}

fn is_js_file(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|ext| ext.to_str()),
        Some("js" | "mjs" | "cjs" | "jsx")
    )
}

fn collect_path(path: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    let metadata =
        fs::symlink_metadata(path).with_context(|| format!("stat {}", path.display()))?;
    if metadata.is_file() {
        // Explicit file arguments are authoritative: corpus bodies are often
        // content-addressed and extensionless. Directory walks remain filtered.
        out.push(path.to_path_buf());
        return Ok(());
    }
    if !metadata.is_dir() {
        return Ok(());
    }

    let mut entries = fs::read_dir(path)
        .with_context(|| format!("reading directory {}", path.display()))?
        .collect::<std::io::Result<Vec<_>>>()?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let child = entry.path();
        let metadata = fs::symlink_metadata(&child)?;
        if metadata.file_type().is_symlink() {
            continue;
        }
        if metadata.is_dir() {
            collect_path(&child, out)?;
        } else if metadata.is_file() && is_js_file(&child) {
            out.push(child);
        }
    }
    Ok(())
}

/// Expand explicit files and recursive directories into a deterministic source
/// list. Explicit files are accepted regardless of extension; recursive walks
/// select JavaScript-like extensions and never follow symlinks.
pub fn collect_input_paths(inputs: &[PathBuf]) -> Result<Vec<PathBuf>> {
    let mut paths = Vec::new();
    for input in inputs {
        collect_path(input, &mut paths)?;
    }
    paths.sort();
    paths.dedup();
    Ok(paths)
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
    let files_with_parse_recovery = files
        .iter()
        .filter(|file| file.parse_recovery.is_some())
        .count();
    let files_with_incomplete_analysis =
        files.iter().filter(|file| !file.analysis_complete).count();
    let files_with_fatal_error = files.iter().filter(|file| file.fatal_error).count();
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
        schema: "js-sus-scan/v8",
        window_bytes: options.window_bytes,
        min_score: options.min_score,
        min_signals: options.min_signals,
        files_scanned: files.len(),
        files_with_parse_recovery,
        files_with_incomplete_analysis,
        files_with_fatal_error,
        files_with_clusters,
        total_clusters,
        files_with_actionable_clusters,
        total_actionable_clusters,
        total_actionable_signals,
        files,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        analyze_bytes, analyze_source, collect_input_paths, scan_file, SusFileReport,
        SusScanOptions,
    };
    use anyhow::{Context, Result};
    use std::{fs, path::PathBuf};

    fn options() -> SusScanOptions {
        SusScanOptions {
            include_signals: true,
            ..SusScanOptions::default()
        }
    }

    fn kind_count(report: &SusFileReport, kind: &str) -> usize {
        report.signal_kinds.get(kind).copied().unwrap_or(0)
    }

    fn actionable_kind_count(report: &SusFileReport, kind: &str) -> usize {
        report
            .actionable_signal_kinds
            .get(kind)
            .copied()
            .unwrap_or(0)
    }

    fn fixture(name: &str) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/generated/sus-scanner")
            .join(name)
    }

    #[test]
    fn file_boundary_preserves_extensionless_inputs_and_decode_provenance() -> Result<()> {
        let workspace = tempfile::tempdir()?;
        let extensionless = workspace.path().join("0123456789abcdef");
        fs::write(&extensionless, "const value = 1;\n")?;
        let paths = collect_input_paths(std::slice::from_ref(&extensionless))?;
        assert_eq!(paths, vec![extensionless.clone()]);
        let report = scan_file(&extensionless, &options())?;
        assert_eq!(PathBuf::from(&report.input), extensionless);
        assert!(!report.fatal_error);

        let malformed = workspace.path().join("deadbeef");
        let malformed_bytes = b"// Copyright \xa9 2013\nconst ok = 1;\n";
        fs::write(&malformed, malformed_bytes)?;
        let report = analyze_bytes(malformed_bytes, &malformed, &options())?;
        assert!(!report.fatal_error);
        assert!(report.decode_had_errors);
        assert!(report.decode_uncertain);
        assert_eq!(report.decode_encoding, "UTF-8");
        assert_eq!(report.decode_source, "utf8-fallback");
        Ok(())
    }

    #[test]
    fn parse_recovery_is_explicit_and_fails_closed_outside_supported_web_syntax() -> Result<()> {
        let options = options();
        let legacy = analyze_source(
            "function target() { return 1; }\ntarget() = 2;\neval('visible');\n",
            PathBuf::from("legacy.js").as_path(),
            &options,
        )?;
        assert!(legacy.parser_fatal_error);
        assert!(!legacy.fatal_error);
        assert!(!legacy.analysis_complete);
        assert_eq!(
            legacy.parse_recovery.as_deref(),
            Some("browser-legacy-call-assignment")
        );
        assert_eq!(legacy.opaque_parse_spans.len(), 1);
        assert_eq!(
            legacy.opaque_parse_spans[0].kind,
            "browser_legacy_call_assignment_target"
        );
        assert!(kind_count(&legacy, "static_dynamic_code_call") >= 1);

        let html_comment = analyze_source(
            "<!--\n$(document).ready(function() { $('#slideshow0').nivoSlider(); });\n-->",
            PathBuf::from("legacy-html-comment.js").as_path(),
            &options,
        )?;
        assert!(html_comment.parser_fatal_error);
        assert!(!html_comment.fatal_error);
        assert!(html_comment.analysis_complete);
        assert_eq!(
            html_comment.parse_recovery.as_deref(),
            Some("classic-script-fallback")
        );
        assert!(html_comment.opaque_parse_spans.is_empty());

        let invalid = analyze_source(
            "(1 + 2) = 3;\n",
            PathBuf::from("invalid-assignment.js").as_path(),
            &options,
        )?;
        assert!(invalid.parser_fatal_error);
        assert!(invalid.fatal_error);
        assert!(!invalid.analysis_complete);
        assert!(invalid.parse_recovery.is_none());
        assert!(invalid.opaque_parse_spans.is_empty());
        Ok(())
    }

    #[test]
    fn actionability_separates_exposed_codecs_from_hidden_dynamic_code() -> Result<()> {
        let options = options();
        let literal = analyze_source(
            concat!(
                "eval('window.visible = 1');\n",
                "Function('x', 'return x + 1');\n",
                "new Function('x', 'return x * 2');\n",
                "Function();\n",
                "new Function();\n",
                "eval('window.stillVisible = 1', getIgnored());\n",
                "new Function('x', '' + 'return x - 1');\n",
                "setTimeout('tick()', 10);\n",
            ),
            PathBuf::from("literal.js").as_path(),
            &options,
        )?;
        assert_eq!(kind_count(&literal, "static_dynamic_code_call"), 4);
        assert_eq!(kind_count(&literal, "static_dynamic_code_constructor"), 3);
        assert_eq!(kind_count(&literal, "string_timer_call"), 1);
        assert_eq!(kind_count(&literal, "dynamic_code_call"), 0);
        assert_eq!(kind_count(&literal, "dynamic_code_constructor"), 0);
        assert_eq!(literal.actionable_signal_count, 0);
        assert_eq!(literal.actionable_top_score, 0);

        let hidden = analyze_source(
            concat!(
                "const source = getSource();\n",
                "eval(source);\n",
                "Function('x', source);\n",
                "new Function('x', source);\n",
            ),
            PathBuf::from("hidden.js").as_path(),
            &options,
        )?;
        assert_eq!(kind_count(&hidden, "dynamic_code_call"), 2);
        assert_eq!(kind_count(&hidden, "dynamic_code_constructor"), 1);
        assert_eq!(hidden.actionable_signal_count, 3);
        assert!(hidden.actionable_top_score > 0);

        let codec = analyze_source(
            concat!(
                "function utf8(cp) { return String.fromCharCode(cp); }\n",
                "function decode(x) { return atob(x); }\n",
                "function id(n) { return n.toString(36); }\n",
            ),
            PathBuf::from("codec-control.js").as_path(),
            &options,
        )?;
        assert_eq!(kind_count(&codec, "charcode_decode_call"), 1);
        assert_eq!(kind_count(&codec, "base64_decode_call"), 1);
        assert_eq!(kind_count(&codec, "radix_string_call"), 1);
        assert_eq!(codec.actionable_signal_count, 0);
        assert_eq!(codec.actionable_top_score, 0);

        let codepoints = analyze_source(
            "const hidden = String.fromCharCode(120, 116, 49);\nsink(hidden);\n",
            PathBuf::from("literal-codepoints.js").as_path(),
            &options,
        )?;
        assert_eq!(kind_count(&codepoints, "charcode_decode_call"), 1);
        assert_eq!(kind_count(&codepoints, "charcode_literal_decode"), 1);
        assert_eq!(
            actionable_kind_count(&codepoints, "charcode_literal_decode"),
            1
        );
        assert_eq!(
            actionable_kind_count(&codepoints, "charcode_decode_call"),
            0
        );

        let encoded = "QUJD".repeat(40);
        let opaque =
            "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ-_~!@#$%^&*()[]{}:;,.?|"
                .repeat(6);
        let blobs = analyze_source(
            &format!("const encoded = {encoded:?};\nconst opaque = {opaque:?};\nsink(encoded, opaque);\n"),
            PathBuf::from("data-blobs.js").as_path(),
            &options,
        )?;
        assert!(kind_count(&blobs, "base64_blob") >= 1);
        assert!(kind_count(&blobs, "opaque_blob") >= 1);
        assert_eq!(actionable_kind_count(&blobs, "base64_blob"), 0);
        assert_eq!(actionable_kind_count(&blobs, "opaque_blob"), 0);
        assert_eq!(blobs.actionable_signal_count, 0);

        let cookie = analyze_source(
            concat!(
                "function getCookieValue(name) {\n",
                "  const cookie = {};\n",
                "  document.cookie.split(';').forEach((item) => {\n",
                "    const [key, value] = item.split('=');\n",
                "    cookie[key.trim()] = value ? decodeURIComponent(value) : '';\n",
                "  });\n",
                "  return cookie[name];\n",
                "}\n",
            ),
            PathBuf::from("cookie-helper.js").as_path(),
            &options,
        )?;
        assert_eq!(actionable_kind_count(&cookie, "direct_table_decoder"), 0);

        let direct = analyze_source(
            "const table = ['QQ==', 'Qg=='];\nfunction decode(i) { return atob(table[i]); }\nsink(decode(0));\n",
            PathBuf::from("direct-table-decoder.js").as_path(),
            &options,
        )?;
        assert!(actionable_kind_count(&direct, "direct_table_decoder") >= 1);
        Ok(())
    }

    #[test]
    fn generated_corpus_keeps_detector_controls_discriminative() -> Result<()> {
        let options = options();
        let load = |name: &str| -> Result<SusFileReport> {
            let path = fixture(name);
            scan_file(&path, &options).with_context(|| format!("scanning {}", path.display()))
        };

        let dense = load("dense-obfuscation.js")?;
        assert!(!dense.clusters.is_empty());
        assert!(dense.top_score >= 30);
        assert!(!dense.actionable_clusters.is_empty());
        assert!(dense.actionable_top_score >= 12);
        assert!(kind_count(&dense, "api_string_table") >= 1);
        assert!(kind_count(&dense, "indexed_lookup") >= 10);
        assert!(kind_count(&dense, "charcode_decode_call") >= 1);
        assert!(kind_count(&dense, "base64_blob") >= 1);
        assert!(kind_count(&dense, "base64_decode_call") >= 1);
        assert!(kind_count(&dense, "numeric_decoder_call_candidate") >= 4);
        assert!(kind_count(&dense, "bitwise_mix") >= 1);
        assert!(dense.clusters.iter().any(|cluster| {
            cluster
                .repeated_subjects
                .iter()
                .any(|item| matches!(item.subject.as_str(), "pool" | "chars") && item.count >= 3)
        }));

        let clean = load("clean-control.js")?;
        assert!(clean.clusters.is_empty());
        assert_eq!(clean.top_score, 0);
        assert!(clean.actionable_clusters.is_empty());
        assert_eq!(clean.actionable_top_score, 0);

        let module_loader = load("module-loader-control.js")?;
        assert!(kind_count(&module_loader, "numeric_decoder_call_candidate") >= 4);
        assert!(module_loader.top_score > 0);
        assert_eq!(module_loader.actionable_top_score, 0);
        assert!(module_loader.actionable_clusters.is_empty());

        let asset = load("asset-control.js")?;
        assert!(asset.clusters.is_empty());
        assert_eq!(kind_count(&asset, "base64_blob"), 0);

        let long_string = load("long-string-control.js")?;
        assert!(long_string.clusters.is_empty());
        assert_eq!(long_string.top_score, 0);
        assert_eq!(kind_count(&long_string, "string_plus_chain"), 1);

        let rotation = load("array-rotation.js")?;
        assert!(!rotation.clusters.is_empty());
        assert_eq!(kind_count(&rotation, "array_rotation"), 2);
        assert!(rotation
            .signals
            .as_deref()
            .context("rotation signals omitted")?
            .iter()
            .filter(|signal| signal.kind == "array_rotation")
            .all(|signal| signal.subject.as_deref() == Some("table")));
        let rotation_control = load("array-rotation-control.js")?;
        assert!(rotation_control.clusters.is_empty());
        assert_eq!(kind_count(&rotation_control, "array_rotation"), 1);

        let bootstrap = load("rotation-bootstrap.js")?;
        assert_eq!(kind_count(&bootstrap, "array_rotation"), 2);
        assert_eq!(kind_count(&bootstrap, "rotation_checksum_iife"), 1);
        assert_eq!(
            kind_count(
                &load("rotation-bootstrap-control.js")?,
                "rotation_checksum_iife"
            ),
            0
        );

        for (positive, control, kind, expected) in [
            (
                "operator-proxy-table.js",
                "operator-proxy-table-control.js",
                "operator_proxy_table",
                1,
            ),
            (
                "one-shot-wrapper.js",
                "one-shot-wrapper-control.js",
                "one_shot_wrapper",
                1,
            ),
            (
                "direct-table-decoder.js",
                "direct-table-decoder-control.js",
                "direct_table_decoder",
                1,
            ),
            (
                "mba-helper-cluster.js",
                "mba-helper-control.js",
                "mba_helper",
                4,
            ),
            (
                "selector-dispatcher.js",
                "selector-dispatcher-control.js",
                "selector_dispatcher",
                1,
            ),
        ] {
            assert_eq!(kind_count(&load(positive)?, kind), expected, "{positive}");
            assert_eq!(kind_count(&load(control)?, kind), 0, "{control}");
        }
        Ok(())
    }
}
