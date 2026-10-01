use anyhow::{Context, Result};
use base64::{engine::general_purpose, Engine as _};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrayExpression, ArrayExpressionElement, BinaryExpression, CallExpression,
    ComputedMemberExpression, Expression, NewExpression, ObjectExpression,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_span::{GetSpan, SourceType, Span};
use serde::Serialize;
use std::{
    collections::{BTreeMap, HashMap},
    fs,
    path::{Path, PathBuf},
};

#[path = "sus-scan/structures.rs"]
mod structures;

#[derive(ClapParser, Debug)]
#[command(
    about = "Fast explainable triage for dense clusters of obfuscation/packing-like JavaScript structures"
)]
struct Args {
    /// JavaScript files or directories to scan recursively.
    #[arg(required = true)]
    inputs: Vec<PathBuf>,

    /// Emit one JSON report instead of human-readable text.
    #[arg(long)]
    json: bool,

    /// Maximum byte span considered one suspicious cluster.
    #[arg(long, default_value_t = 3072)]
    window_bytes: usize,

    /// Minimum cluster score to report.
    #[arg(long, default_value_t = 12)]
    min_score: u32,

    /// Minimum number of evidence points in a reported cluster.
    #[arg(long, default_value_t = 3)]
    min_signals: usize,

    /// Maximum clusters reported per file.
    #[arg(long, default_value_t = 20)]
    max_clusters: usize,

    /// Minimum string length for opaque/base64 blob heuristics.
    #[arg(long, default_value_t = 96)]
    blob_min_len: usize,

    /// Include every raw evidence point in JSON, not only clustered evidence.
    #[arg(long)]
    include_signals: bool,
}

#[derive(Debug, Clone, Serialize)]
struct Signal {
    kind: String,
    weight: u32,
    start: u32,
    end: u32,
    line: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    subject: Option<String>,
    detail: String,
}

#[derive(Debug, Clone, Serialize)]
struct RepeatedSubject {
    subject: String,
    count: usize,
}

#[derive(Debug, Clone, Serialize)]
struct Cluster {
    score: u32,
    density_per_kib: f64,
    start: u32,
    end: u32,
    start_line: usize,
    end_line: usize,
    signal_count: usize,
    kinds: BTreeMap<String, usize>,
    repeated_subjects: Vec<RepeatedSubject>,
    signals: Vec<Signal>,
    snippet: String,
}

#[derive(Debug, Serialize)]
struct FileReport {
    input: String,
    bytes: usize,
    diagnostics: usize,
    panicked: bool,
    signal_count: usize,
    signal_kinds: BTreeMap<String, usize>,
    top_score: u32,
    clusters: Vec<Cluster>,
    #[serde(skip_serializing_if = "Option::is_none")]
    signals: Option<Vec<Signal>>,
}

#[derive(Debug, Serialize)]
struct Report {
    schema: &'static str,
    window_bytes: usize,
    min_score: u32,
    min_signals: usize,
    files_scanned: usize,
    files_with_clusters: usize,
    total_clusters: usize,
    files: Vec<FileReport>,
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
            Argument::StringLiteral(value) => Some(value.value.to_string()),
            Argument::TemplateLiteral(value) if value.expressions.is_empty() => {
                value.quasis.first().map(|quasi| {
                    quasi
                        .value
                        .cooked
                        .as_ref()
                        .unwrap_or(&quasi.value.raw)
                        .to_string()
                })
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
                2 + (parts as u32 / 4).min(4),
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
                    let value = s.value.as_str();
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
                4 + (api_hits as u32).min(8) + (hot_api_hits as u32).min(4),
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
                3 + ((strings / 16) as u32).min(4),
                it.span,
                None,
                format!("{identifier_strings}/{strings} identifier-like short strings"),
            );
        }

        if numeric >= 16 && byte_numeric * 5 >= numeric * 4 {
            let printable_ratio = printable_numeric as f64 / numeric as f64;
            self.push(
                if printable_ratio >= 0.60 {
                    "charcode_array"
                } else {
                    "byte_array"
                },
                if printable_ratio >= 0.60 { 5 } else { 3 } + ((numeric / 32) as u32).min(4),
                it.span,
                None,
                format!(
                    "{byte_numeric}/{numeric} byte-range integers; {:.0}% printable ASCII",
                    printable_ratio * 100.0
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

    fn record_call(&mut self, it: &CallExpression<'_>) {
        self.record_structural_call(it);
        let callee = self.fragment(it.callee.span()).trim().to_string();
        let lower = callee.to_ascii_lowercase();

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
                6 + ((it.arguments.len() / 4) as u32).min(6),
                it.span,
                None,
                format!(
                    "{} args; {numeric_args} immediate numeric literal(s)",
                    it.arguments.len()
                ),
            );
        }

        if is_identifierish(&callee)
            && !matches!(
                callee.as_str(),
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

        if matches!(callee.as_str(), "eval" | "Function")
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

        if matches!(callee.as_str(), "setTimeout" | "setInterval")
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

        if callee.ends_with(".join") {
            if let Expression::StaticMemberExpression(member) = &it.callee {
                let empty_or_tiny_separator = it
                    .arguments
                    .first()
                    .and_then(Self::argument_string)
                    .map(|sep| sep.len() <= 1)
                    .unwrap_or(it.arguments.is_empty());
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
                2 + ((it.arguments.len() / 3) as u32).min(3),
                it.span,
                None,
                format!("{} concatenation argument(s)", it.arguments.len()),
            );
        }

        if (callee.ends_with(".toString") || callee == "Number.prototype.toString")
            && it
                .arguments
                .first()
                .is_some_and(|arg| matches!(arg, Argument::NumericLiteral(n) if matches!(n.value as i32, 16 | 32 | 36)))
        {
            self.push(
                "radix_string_call",
                4,
                it.span,
                None,
                format!("radix conversion via {callee}"),
            );
        }

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
            callee.as_str(),
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
    fn visit_expression(&mut self, it: &Expression<'a>) {
        match it {
            Expression::StringLiteral(value) => self.record_blob(value.span, value.value.as_str()),
            Expression::TemplateLiteral(value) if value.expressions.len() >= 4 => self.push(
                "template_assembly",
                3 + ((value.expressions.len() / 4) as u32).min(4),
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
        .skip_while(|b| b.is_ascii_whitespace())
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

fn apiish_name(value: &str) -> bool {
    matches!(
        value,
        "apply"
            | "call"
            | "bind"
            | "constructor"
            | "prototype"
            | "length"
            | "push"
            | "pop"
            | "shift"
            | "unshift"
            | "slice"
            | "splice"
            | "split"
            | "join"
            | "concat"
            | "replace"
            | "charAt"
            | "charCodeAt"
            | "fromCharCode"
            | "fromCodePoint"
            | "indexOf"
            | "substring"
            | "substr"
            | "map"
            | "filter"
            | "reduce"
            | "forEach"
            | "toString"
            | "valueOf"
            | "hasOwnProperty"
            | "defineProperty"
            | "getOwnPropertyDescriptor"
            | "createElement"
            | "appendChild"
            | "addEventListener"
            | "removeEventListener"
            | "getAttribute"
            | "setAttribute"
            | "querySelector"
            | "fetch"
            | "XMLHttpRequest"
            | "WebSocket"
            | "postMessage"
            | "localStorage"
            | "sessionStorage"
            | "navigator"
            | "document"
            | "window"
            | "eval"
            | "Function"
            | "atob"
            | "btoa"
            | "setTimeout"
            | "setInterval"
            | "parseInt"
            | "decodeURIComponent"
            | "encodeURIComponent"
    )
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

fn materialize_signal(raw: &RawSignal, lines: &[usize]) -> Signal {
    Signal {
        kind: raw.kind.to_string(),
        weight: raw.weight,
        start: raw.start,
        end: raw.end,
        line: line_for(lines, raw.start as usize),
        subject: raw.subject.clone(),
        detail: raw.detail.clone(),
    }
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

fn cluster_signals(
    source: &str,
    raw: &[RawSignal],
    window_bytes: usize,
    min_score: u32,
    min_signals: usize,
    max_clusters: usize,
) -> Vec<Cluster> {
    #[derive(Debug, Clone)]
    struct Candidate {
        score: u32,
        density_per_kib: f64,
        start: u32,
        end: u32,
        left: usize,
        right: usize,
    }

    if raw.is_empty() || max_clusters == 0 {
        return Vec::new();
    }

    let mut signals = raw.to_vec();
    signals.sort_by_key(|signal| (signal.start, signal.end));

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
                .map(|&count| 3 + count.saturating_sub(3) as u32)
                .sum::<u32>();
            let mut score =
                weight_sum + (kind_counts.len().saturating_sub(1) as u32) * 2 + repeated_bonus;

            let start = signals[left].start;
            let end = signals[right - 1].end;
            let span = end.saturating_sub(start).max(1);
            if span as usize <= window_bytes / 4 {
                score += 3;
            } else if span as usize <= window_bytes / 2 {
                score += 1;
            }

            if score >= min_score {
                candidates.push(Candidate {
                    score,
                    density_per_kib: score as f64 * 1024.0 / span as f64,
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

    candidates.sort_by(|a, b| {
        b.score
            .cmp(&a.score)
            .then_with(|| b.density_per_kib.total_cmp(&a.density_per_kib))
            .then_with(|| a.start.cmp(&b.start))
    });

    let mut selected_candidates: Vec<Candidate> = Vec::with_capacity(max_clusters);
    'candidate: for candidate in candidates {
        for existing in &selected_candidates {
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
        selected_candidates.push(candidate);
        if selected_candidates.len() >= max_clusters {
            break;
        }
    }

    let lines = line_starts(source);
    let mut selected = Vec::with_capacity(selected_candidates.len());
    for candidate in selected_candidates {
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

        selected.push(Cluster {
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

fn parse_source<'a>(
    allocator: &'a Allocator,
    source: &'a str,
    path: &Path,
) -> (oxc_ast::ast::Program<'a>, usize, bool) {
    let source_type = match path.extension().and_then(|ext| ext.to_str()) {
        Some("cjs") => SourceType::cjs(),
        _ => SourceType::mjs(),
    };
    let parsed = Parser::new(allocator, source, source_type).parse();
    let diagnostics = parsed.diagnostics.len();
    (parsed.program, diagnostics, parsed.panicked)
}

fn scan_file(path: &Path, args: &Args) -> Result<FileReport> {
    let source = fs::read_to_string(path)
        .with_context(|| format!("reading JavaScript {}", path.display()))?;
    let allocator = Allocator::default();
    let (program, diagnostics, panicked) = parse_source(&allocator, &source, path);

    let mut collector = Collector {
        source: &source,
        blob_min_len: args.blob_min_len,
        signals: Vec::new(),
    };
    if !panicked {
        collector.visit_program(&program);
    }

    let signals = normalize_signals(collector.signals);
    let mut signal_kinds = BTreeMap::new();
    for signal in &signals {
        *signal_kinds.entry(signal.kind.to_string()).or_default() += 1;
    }
    let clusters = cluster_signals(
        &source,
        &signals,
        args.window_bytes,
        args.min_score,
        args.min_signals,
        args.max_clusters,
    );
    let lines = line_starts(&source);
    let top_score = clusters.first().map(|cluster| cluster.score).unwrap_or(0);

    Ok(FileReport {
        input: path.display().to_string(),
        bytes: source.len(),
        diagnostics,
        panicked,
        signal_count: signals.len(),
        signal_kinds,
        top_score,
        clusters,
        signals: args.include_signals.then(|| {
            signals
                .iter()
                .map(|signal| materialize_signal(signal, &lines))
                .collect()
        }),
    })
}

fn is_js_file(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|ext| ext.to_str()),
        Some("js" | "mjs" | "cjs" | "jsx")
    )
}

fn collect_paths(path: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    let metadata =
        fs::symlink_metadata(path).with_context(|| format!("stat {}", path.display()))?;
    if metadata.is_file() {
        if is_js_file(path) {
            out.push(path.to_path_buf());
        }
        return Ok(());
    }
    if !metadata.is_dir() {
        return Ok(());
    }

    let mut entries = fs::read_dir(path)
        .with_context(|| format!("reading directory {}", path.display()))?
        .collect::<std::io::Result<Vec<_>>>()?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let child = entry.path();
        let meta = fs::symlink_metadata(&child)?;
        if meta.file_type().is_symlink() {
            continue;
        }
        if meta.is_dir() {
            collect_paths(&child, out)?;
        } else if meta.is_file() && is_js_file(&child) {
            out.push(child);
        }
    }
    Ok(())
}

fn print_text(report: &Report) {
    for file in report.files.iter().filter(|file| !file.clusters.is_empty()) {
        println!(
            "\n{}  bytes={} signals={} top_score={} diagnostics={}{}",
            file.input,
            file.bytes,
            file.signal_count,
            file.top_score,
            file.diagnostics,
            if file.panicked { " PANICKED" } else { "" }
        );
        for (index, cluster) in file.clusters.iter().enumerate() {
            let kinds = cluster
                .kinds
                .iter()
                .map(|(kind, count)| format!("{kind}×{count}"))
                .collect::<Vec<_>>()
                .join(", ");
            let repeated = if cluster.repeated_subjects.is_empty() {
                String::new()
            } else {
                format!(
                    " repeated=[{}]",
                    cluster
                        .repeated_subjects
                        .iter()
                        .take(4)
                        .map(|item| format!("{}×{}", item.subject, item.count))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            println!(
                "  #{:<2} score={:<3} density={:>6.1}/KiB L{}-{} @{:x}-{:x} signals={} {}{}",
                index + 1,
                cluster.score,
                cluster.density_per_kib,
                cluster.start_line,
                cluster.end_line,
                cluster.start,
                cluster.end,
                cluster.signal_count,
                kinds,
                repeated,
            );
            for signal in cluster.signals.iter().take(6) {
                println!(
                    "       w{:<2} L{:<5} {:<24} {}{}",
                    signal.weight,
                    signal.line,
                    signal.kind,
                    signal.detail,
                    signal
                        .subject
                        .as_deref()
                        .map(|subject| format!(" [{}]", subject))
                        .unwrap_or_default()
                );
            }
            if cluster.signals.len() > 6 {
                println!(
                    "       … {} more evidence point(s)",
                    cluster.signals.len() - 6
                );
            }
            println!("       {}", cluster.snippet);
        }
    }

    println!(
        "\nSUS summary: {} file(s) scanned; {} with clusters; {} cluster(s)",
        report.files_scanned, report.files_with_clusters, report.total_clusters
    );
}

fn main() -> Result<()> {
    let args = Args::parse();
    if args.window_bytes < 64 {
        anyhow::bail!("--window-bytes must be at least 64");
    }

    let mut paths = Vec::new();
    for input in &args.inputs {
        collect_paths(input, &mut paths)?;
    }
    paths.sort();
    paths.dedup();

    let mut files = Vec::with_capacity(paths.len());
    for path in &paths {
        files.push(scan_file(path, &args)?);
    }
    files.sort_by(|a, b| {
        b.top_score
            .cmp(&a.top_score)
            .then_with(|| a.input.cmp(&b.input))
    });

    let files_with_clusters = files
        .iter()
        .filter(|file| !file.clusters.is_empty())
        .count();
    let total_clusters = files.iter().map(|file| file.clusters.len()).sum();
    let report = Report {
        schema: "js-sus-scan/v1",
        window_bytes: args.window_bytes,
        min_score: args.min_score,
        min_signals: args.min_signals,
        files_scanned: files.len(),
        files_with_clusters,
        total_clusters,
        files,
    };

    if args.json {
        println!("{}", serde_json::to_string(&report)?);
    } else {
        print_text(&report);
    }
    Ok(())
}
