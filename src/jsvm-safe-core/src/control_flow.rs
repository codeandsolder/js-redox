//! Proof-oriented control-flow recovery.
//!
//! This module owns the coupled dispatcher/reference-state proof engines:
//! ordered switch dispatch, deterministic reference-identity tables, symbolic
//! state simulation, and reference/arithmetic state unflattening. The central
//! collector remains in `lib.rs`; these methods operate on it so replacement
//! scheduling and source-protection policy stay centralized.

use crate::numeric::exact_u32;
use crate::value_eval::{
    canonical_array_index, eval, eval_binary, eval_logical_left, eval_unary_value,
    eval_with_resolver, identical_primitive_value, inert_literal_value, js_to_uint32,
    strict_primitive_equal, string_literal_value, template_element_value, LogicalStep, Value,
};
use crate::{
    binding_facts::BindingFacts, direct_identifier_name, fragment, js_parse_int,
    symbol_has_only_read_references, symbol_of, ArithmeticStateProof, Collector,
};
use oxc_ast::ast::{
    ArrayExpressionElement, BindingPattern, Expression, IdentifierReference, Statement,
    VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::{GetSpan, Span};
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::collections::{HashMap, HashSet};

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

pub fn collect_reference_spans(program: &oxc_ast::ast::Program<'_>) -> HashMap<ReferenceId, Span> {
    let mut collector = ReferenceSpanCollector::default();
    collector.visit_program(program);
    collector.spans
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ReferenceIdentityTable {
    rows: u32,
    columns: u32,
    root_row: u32,
    column_multiplier: u32,
    row_multiplier: u32,
    salt_left: u32,
    salt_right: u32,
    pub(super) construction_start: usize,
    pub(super) construction_end: usize,
}

impl ReferenceIdentityTable {
    fn row_for(&self, row: u32, column: u32) -> Option<u32> {
        if row >= self.rows || column >= self.columns || !self.rows.is_power_of_two() {
            return None;
        }
        let column_term = js_to_uint32(f64::from(self.column_multiplier) * f64::from(column));
        let row_term = js_to_uint32(f64::from(self.row_multiplier) * f64::from(row));
        let salt_term = js_to_uint32(f64::from(self.salt_left) * f64::from(self.salt_right));
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

struct ReferenceIdentityPatterns {
    row: regex::Regex,
    timer: regex::Regex,
    outer: regex::Regex,
    fill: regex::Regex,
    root: regex::Regex,
}

fn reference_identity_patterns() -> Option<ReferenceIdentityPatterns> {
    let identifier = r"[A-Za-z_$][A-Za-z0-9_$]*";
    let ws = r"\s*";
    Some(ReferenceIdentityPatterns {
        row: regex::Regex::new(&format!(
            r"(?P<table>{identifier}){ws}={ws}\[\]{ws},{ws}(?P<idx>{identifier}){ws}={ws}0{ws};{ws}(?P<test>{identifier}){ws}<{ws}(?P<rows>\d+){ws};{ws}(?P<update>{identifier}){ws}\+\+{ws}\){ws}(?P<table2>{identifier}){ws}\[{ws}(?P<idx2>{identifier}){ws}\]{ws}={ws}new{ws}Array{ws}\({ws}(?P<columns>\d+){ws}\)"
        )).ok()?,
        timer: regex::Regex::new(&format!(
            r"(?P<timer>{identifier}){ws}={ws}function{ws}\({ws}(?P<arg>{identifier}){ws}\){ws}\{{{ws}setTimeout{ws}\({ws}(?P<arg2>{identifier}){ws},{ws}0{ws}\){ws};?{ws}\}}"
        )).ok()?,
        outer: regex::Regex::new(&format!(
            r"for{ws}\({ws}var\s+(?P<loop>{identifier}){ws}={ws}0{ws};{ws}(?P<test>{identifier}){ws}<{ws}(?P<chunks>\d+){ws};{ws}(?P<update>{identifier}){ws}\+\+{ws}\){ws}\({ws}\(?{ws}(?P<callback>{identifier}){ws}\)?{ws}=>{ws}\{{{ws}(?P<timer>{identifier}){ws}\({ws}function{ws}\({ws}\){ws}\{{"
        )).ok()?,
        fill: regex::Regex::new(&format!(
            r"for{ws}\({ws}var\s+(?P<t>{identifier}){ws}={ws}(?P<chunk>\d+){ws}\*{ws}(?P<callback>{identifier}){ws},{ws}(?P<n>{identifier}){ws}={ws}Math{ws}\.{ws}min{ws}\({ws}(?P<t2>{identifier}){ws}\+{ws}(?P<chunk2>\d+){ws},{ws}(?P<columns>\d+){ws}\){ws},{ws}(?P<column>{identifier}){ws}={ws}(?P<t3>{identifier}){ws};{ws}(?P<column2>{identifier}){ws}<{ws}(?P<n2>{identifier}){ws};{ws}(?P<column3>{identifier}){ws}\+\+{ws}\){ws}for{ws}\({ws}(?P<row>{identifier}){ws}={ws}0{ws};{ws}(?P<row2>{identifier}){ws}<{ws}(?P<rows>\d+){ws};{ws}(?P<row3>{identifier}){ws}\+\+{ws}\){ws}(?P<table>{identifier}){ws}\[{ws}(?P<row4>{identifier}){ws}\]{ws}\[{ws}(?P<column4>{identifier}){ws}\]{ws}={ws}(?P<table2>{identifier}){ws}\[{ws}\({ws}(?P<a>\d+){ws}\*{ws}(?P<column5>{identifier}){ws}\^{ws}(?P<b>\d+){ws}\*{ws}(?P<row5>{identifier}){ws}\^{ws}(?P<c>\d+){ws}\*{ws}(?P<k>\d+){ws}\){ws}>>>{ws}0{ws}&{ws}(?P<mask>\d+){ws}-{ws}1{ws}\]"
        )).ok()?,
        root: regex::Regex::new(&format!(
            r"(?P<timer>{identifier}){ws}\({ws}function{ws}\({ws}\){ws}\{{{ws}(?P<target>{identifier}){ws}={ws}(?P<table>{identifier}){ws}\[{ws}(?P<root>\d+){ws}\]{ws};?{ws}\}}{ws}\)"
        )).ok()?,
    })
}

fn capture_str<'h>(captures: &regex::Captures<'h>, name: &str) -> Option<&'h str> {
    captures.name(name).map(|capture| capture.as_str())
}

fn capture_u32(captures: &regex::Captures<'_>, name: &str) -> Option<u32> {
    capture_str(captures, name)?.parse().ok()
}

#[derive(Debug)]
struct ReferenceIdentityShape {
    table_name: String,
    target_name: String,
    rows: u32,
    columns: u32,
    root_row: u32,
    column_multiplier: u32,
    row_multiplier: u32,
    salt_left: u32,
    salt_right: u32,
    window_start: usize,
    window_end: usize,
    construction_start: usize,
    construction_end: usize,
}

#[derive(Debug)]
struct ReferenceIdentityFill {
    column_multiplier: u32,
    row_multiplier: u32,
    salt_left: u32,
    salt_right: u32,
}

fn parse_reference_identity_fill(
    fill_caps: &regex::Captures<'_>,
    callback_name: &str,
    table_name: &str,
    rows: u32,
    columns: u32,
    chunks: u32,
) -> Option<ReferenceIdentityFill> {
    if capture_str(fill_caps, "callback")? != callback_name
        || capture_str(fill_caps, "table")? != table_name
        || capture_str(fill_caps, "table2")? != table_name
    {
        return None;
    }
    let t_name = capture_str(fill_caps, "t")?;
    let n_name = capture_str(fill_caps, "n")?;
    let column_name = capture_str(fill_caps, "column")?;
    let row_name = capture_str(fill_caps, "row")?;
    if capture_str(fill_caps, "t2")? != t_name
        || capture_str(fill_caps, "t3")? != t_name
        || capture_str(fill_caps, "n2")? != n_name
        || capture_str(fill_caps, "column2")? != column_name
        || capture_str(fill_caps, "column3")? != column_name
        || capture_str(fill_caps, "column4")? != column_name
        || capture_str(fill_caps, "column5")? != column_name
        || capture_str(fill_caps, "row2")? != row_name
        || capture_str(fill_caps, "row3")? != row_name
        || capture_str(fill_caps, "row4")? != row_name
        || capture_str(fill_caps, "row5")? != row_name
    {
        return None;
    }

    let chunk = capture_u32(fill_caps, "chunk")?;
    if chunk == 0
        || capture_u32(fill_caps, "chunk2")? != chunk
        || capture_u32(fill_caps, "columns")? != columns
        || capture_u32(fill_caps, "rows")? != rows
        || capture_u32(fill_caps, "mask")? != rows
        || chunks.checked_mul(chunk) != Some(columns)
    {
        return None;
    }

    Some(ReferenceIdentityFill {
        column_multiplier: capture_u32(fill_caps, "a")?,
        row_multiplier: capture_u32(fill_caps, "b")?,
        salt_left: capture_u32(fill_caps, "c")?,
        salt_right: capture_u32(fill_caps, "k")?,
    })
}

fn parse_reference_identity_shape(
    source: &str,
    patterns: &ReferenceIdentityPatterns,
    row_caps: &regex::Captures<'_>,
) -> Option<ReferenceIdentityShape> {
    let row_match = row_caps.get(0)?;
    let table_name = capture_str(row_caps, "table")?;
    let row_index = capture_str(row_caps, "idx")?;
    if capture_str(row_caps, "test")? != row_index
        || capture_str(row_caps, "update")? != row_index
        || capture_str(row_caps, "idx2")? != row_index
        || capture_str(row_caps, "table2")? != table_name
    {
        return None;
    }
    let rows = capture_u32(row_caps, "rows")?;
    let columns = capture_u32(row_caps, "columns")?;
    if rows < 2 || columns < 2 || !rows.is_power_of_two() {
        return None;
    }

    let window_start = row_match.start().saturating_sub(256);
    let window_end = (row_match.end() + 1800).min(source.len());
    let window = source.get(window_start..window_end)?;

    let timer_caps = patterns.timer.captures(window)?;
    if capture_str(&timer_caps, "arg")? != capture_str(&timer_caps, "arg2")? {
        return None;
    }
    let timer_name = capture_str(&timer_caps, "timer")?;

    let outer_caps = patterns.outer.captures(window)?;
    let outer_loop = capture_str(&outer_caps, "loop")?;
    if capture_str(&outer_caps, "test")? != outer_loop
        || capture_str(&outer_caps, "update")? != outer_loop
        || capture_str(&outer_caps, "timer")? != timer_name
    {
        return None;
    }
    let callback_name = capture_str(&outer_caps, "callback")?;
    let chunks = capture_u32(&outer_caps, "chunks")?;

    let fill_caps = patterns.fill.captures(window)?;
    let fill = parse_reference_identity_fill(
        &fill_caps,
        callback_name,
        table_name,
        rows,
        columns,
        chunks,
    )?;

    let root_caps = patterns.root.captures(window)?;
    if capture_str(&root_caps, "timer")? != timer_name
        || capture_str(&root_caps, "table")? != table_name
    {
        return None;
    }
    let root_row = capture_u32(&root_caps, "root")?;
    if root_row >= rows {
        return None;
    }

    let construction_start = window_start
        + timer_caps
            .get(0)?
            .start()
            .min(row_match.start() - window_start);
    let construction_end = window_start + root_caps.get(0)?.end();
    Some(ReferenceIdentityShape {
        table_name: table_name.to_string(),
        target_name: capture_str(&root_caps, "target")?.to_string(),
        rows,
        columns,
        root_row,
        column_multiplier: fill.column_multiplier,
        row_multiplier: fill.row_multiplier,
        salt_left: fill.salt_left,
        salt_right: fill.salt_right,
        window_start,
        window_end,
        construction_start,
        construction_end,
    })
}

struct SyncReferenceIdentityPatterns {
    builder: regex::Regex,
    helper: regex::Regex,
}

fn sync_reference_identity_patterns() -> Option<SyncReferenceIdentityPatterns> {
    let identifier = r"[A-Za-z_$][A-Za-z0-9_$]*";
    let ws = r"\s*";
    Some(SyncReferenceIdentityPatterns {
        builder: regex::Regex::new(&format!(
            r"(?P<target>{identifier}){ws}={ws}function{ws}\({ws}(?P<row_param>{identifier}){ws}\){ws}\{{{ws}var\s+[^;]*?(?P<table>{identifier}){ws}={ws}\[\]{ws};{ws}for{ws}\({ws}(?P<init_row>{identifier}){ws}={ws}0{ws};{ws}(?P<init_test>{identifier}){ws}<{ws}(?P<rows>\d+){ws};{ws}(?P<init_update>{identifier}){ws}\+\+{ws}\){ws}(?P<table_init>{identifier}){ws}\[{ws}(?P<init_index>{identifier}){ws}\]{ws}={ws}new{ws}Array{ws}\({ws}(?P<columns>\d+){ws}\){ws};{ws}for{ws}\({ws}(?P<column>{identifier}){ws}={ws}0{ws};{ws}(?P<column_test>{identifier}){ws}<{ws}(?P<columns2>\d+){ws};{ws}(?P<column_update>{identifier}){ws}\+\+{ws}\){ws}for{ws}\({ws}(?P<row>{identifier}){ws}={ws}0{ws};{ws}(?P<row_test>{identifier}){ws}<{ws}(?P<rows2>\d+){ws};{ws}(?P<row_update>{identifier}){ws}\+\+{ws}\){ws}(?P<table_fill>{identifier}){ws}\[{ws}(?P<row_index>{identifier}){ws}\]{ws}\[{ws}(?P<column_index>{identifier}){ws}\]{ws}={ws}(?P<table_lookup>{identifier}){ws}\[{ws}(?P<helper>{identifier}){ws}\({ws}(?P<row_multiplier>\d+){ws},{ws}(?P<column_arg>{identifier}){ws},{ws}(?P<row_arg>{identifier}){ws},{ws}(?P<salt_left>\d+){ws},{ws}(?P<salt_right>\d+){ws},{ws}(?P<column_multiplier>\d+){ws},{ws}(?P<mask>\d+){ws}\){ws}\]{ws};{ws}return{ws}(?P<table_return>{identifier}){ws}\[{ws}(?P<root>\d+){ws}\]{ws};?{ws}\}}{ws}\({ws}\)"
        )).ok()?,
        helper: regex::Regex::new(&format!(
            r"function{ws}(?P<helper>{identifier}){ws}\({ws}(?P<p0>{identifier}){ws},{ws}(?P<p1>{identifier}){ws},{ws}(?P<p2>{identifier}){ws},{ws}(?P<p3>{identifier}){ws},{ws}(?P<p4>{identifier}){ws},{ws}(?P<p5>{identifier}){ws},{ws}(?P<p6>{identifier}){ws},{ws}(?P<p7>{identifier}){ws}\){ws}\{{{ws}return{ws}\({ws}(?P<t1a>{identifier}){ws}\*{ws}(?P<t1b>{identifier}){ws}\^{ws}(?P<t2a>{identifier}){ws}\*{ws}(?P<t2b>{identifier}){ws}\^{ws}(?P<t3a>{identifier}){ws}\*{ws}(?P<t3b>{identifier}){ws}\){ws}>>>{ws}0{ws}&{ws}(?P<mask_param>{identifier}){ws}-{ws}1{ws};?{ws}\}}"
        )).ok()?,
    })
}

fn reference_symbol_at_span(
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
    span: Span,
) -> Option<SymbolId> {
    reference_spans
        .iter()
        .find_map(|(reference_id, candidate)| {
            (*candidate == span)
                .then(|| scoping.get_reference(*reference_id).symbol_id())
                .flatten()
        })
}

fn helper_formula_matches(helper_caps: &regex::Captures<'_>) -> bool {
    let Some(p0) = capture_str(helper_caps, "p0") else {
        return false;
    };
    let Some(p1) = capture_str(helper_caps, "p1") else {
        return false;
    };
    let Some(p2) = capture_str(helper_caps, "p2") else {
        return false;
    };
    let Some(p3) = capture_str(helper_caps, "p3") else {
        return false;
    };
    let Some(p4) = capture_str(helper_caps, "p4") else {
        return false;
    };
    let Some(p5) = capture_str(helper_caps, "p5") else {
        return false;
    };
    let Some(p6) = capture_str(helper_caps, "p6") else {
        return false;
    };
    capture_str(helper_caps, "t1a") == Some(p1)
        && capture_str(helper_caps, "t1b") == Some(p5)
        && capture_str(helper_caps, "t2a") == Some(p2)
        && capture_str(helper_caps, "t2b") == Some(p0)
        && capture_str(helper_caps, "t3a") == Some(p3)
        && capture_str(helper_caps, "t3b") == Some(p4)
        && capture_str(helper_caps, "mask_param") == Some(p6)
}

fn parse_sync_reference_identity_shape(
    source: &str,
    patterns: &SyncReferenceIdentityPatterns,
    builder_caps: &regex::Captures<'_>,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Option<(SymbolId, ReferenceIdentityTable)> {
    let builder_match = builder_caps.get(0)?;
    let table_name = capture_str(builder_caps, "table")?;
    let row_param = capture_str(builder_caps, "row_param")?;
    let init_row = capture_str(builder_caps, "init_row")?;
    let column = capture_str(builder_caps, "column")?;
    let row = capture_str(builder_caps, "row")?;
    if capture_str(builder_caps, "init_test")? != init_row
        || capture_str(builder_caps, "init_update")? != init_row
        || capture_str(builder_caps, "table_init")? != table_name
        || capture_str(builder_caps, "init_index")? != init_row
        || capture_str(builder_caps, "column_test")? != column
        || capture_str(builder_caps, "column_update")? != column
        || capture_str(builder_caps, "row_test")? != row
        || capture_str(builder_caps, "row_update")? != row
        || row != row_param
        || capture_str(builder_caps, "table_fill")? != table_name
        || capture_str(builder_caps, "row_index")? != row
        || capture_str(builder_caps, "column_index")? != column
        || capture_str(builder_caps, "table_lookup")? != table_name
        || capture_str(builder_caps, "column_arg")? != column
        || capture_str(builder_caps, "row_arg")? != row
        || capture_str(builder_caps, "table_return")? != table_name
    {
        return None;
    }
    let rows = capture_u32(builder_caps, "rows")?;
    let columns = capture_u32(builder_caps, "columns")?;
    if rows < 2
        || columns < 2
        || !rows.is_power_of_two()
        || capture_u32(builder_caps, "rows2")? != rows
        || capture_u32(builder_caps, "columns2")? != columns
        || capture_u32(builder_caps, "mask")? != rows
    {
        return None;
    }
    let root_row = capture_u32(builder_caps, "root")?;
    if root_row >= rows {
        return None;
    }

    let helper_name = capture_str(builder_caps, "helper")?;
    let helper_caps = patterns.helper.captures_iter(source).find(|caps| {
        capture_str(caps, "helper") == Some(helper_name) && helper_formula_matches(caps)
    })?;
    let helper_match = helper_caps.get(0)?;
    let helper_decl_symbol = unique_symbol_named_near(
        scoping,
        helper_name,
        u32::try_from(helper_match.start()).ok()?,
        u32::try_from(helper_match.end()).ok()?,
    )?;
    let helper_capture = builder_caps.name("helper")?;
    let helper_ref_span = Span::new(
        u32::try_from(helper_capture.start()).ok()?,
        u32::try_from(helper_capture.end()).ok()?,
    );
    if reference_symbol_at_span(scoping, reference_spans, helper_ref_span)
        != Some(helper_decl_symbol)
        || scoping
            .get_resolved_reference_ids(helper_decl_symbol)
            .iter()
            .any(|reference_id| scoping.get_reference(*reference_id).is_write())
    {
        return None;
    }

    let start = u32::try_from(builder_match.start()).ok()?;
    let end = u32::try_from(builder_match.end()).ok()?;
    let target_name = capture_str(builder_caps, "target")?;
    let target_symbol = unique_symbol_named_near(scoping, target_name, start, end)?;
    let table_symbol = unique_symbol_named_near(scoping, table_name, start, end)?;
    if scoping
        .get_resolved_reference_ids(table_symbol)
        .iter()
        .any(|reference_id| {
            reference_spans
                .get(reference_id)
                .is_none_or(|span| span.start < start || span.end > end)
        })
        || !symbol_has_only_read_references(scoping, target_symbol)
    {
        return None;
    }

    let descriptor = ReferenceIdentityTable {
        rows,
        columns,
        root_row,
        column_multiplier: capture_u32(builder_caps, "column_multiplier")?,
        row_multiplier: capture_u32(builder_caps, "row_multiplier")?,
        salt_left: capture_u32(builder_caps, "salt_left")?,
        salt_right: capture_u32(builder_caps, "salt_right")?,
        construction_start: builder_match.start(),
        construction_end: builder_match.end(),
    };
    let valid = (0..descriptor.rows)
        .all(|row| (0..descriptor.columns).all(|column| descriptor.row_for(row, column).is_some()));
    valid.then_some((target_symbol, descriptor))
}

fn detect_sync_reference_identity_tables(
    source: &str,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<SymbolId, ReferenceIdentityTable> {
    let Some(patterns) = sync_reference_identity_patterns() else {
        return HashMap::new();
    };
    patterns
        .builder
        .captures_iter(source)
        .filter_map(|caps| {
            parse_sync_reference_identity_shape(source, &patterns, &caps, scoping, reference_spans)
        })
        .collect()
}

fn prove_reference_identity_shape(
    shape: &ReferenceIdentityShape,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> Option<(SymbolId, ReferenceIdentityTable)> {
    let absolute_start = u32::try_from(shape.window_start).ok()?;
    let absolute_end = u32::try_from(shape.window_end).ok()?;
    let construction_end = u32::try_from(shape.construction_end).ok()?;
    let target_symbol =
        unique_symbol_named_near(scoping, &shape.target_name, absolute_start, absolute_end)?;
    let table_symbol =
        unique_symbol_named_near(scoping, &shape.table_name, absolute_start, absolute_end)?;
    if scoping
        .get_resolved_reference_ids(table_symbol)
        .iter()
        .any(|reference_id| {
            reference_spans
                .get(reference_id)
                .is_none_or(|span| span.start < absolute_start || span.end > construction_end)
        })
    {
        return None;
    }
    let target_writes = scoping
        .get_resolved_reference_ids(target_symbol)
        .iter()
        .filter(|reference_id| scoping.get_reference(**reference_id).is_write())
        .count();
    if target_writes != 1 {
        return None;
    }

    let descriptor = ReferenceIdentityTable {
        rows: shape.rows,
        columns: shape.columns,
        root_row: shape.root_row,
        column_multiplier: shape.column_multiplier,
        row_multiplier: shape.row_multiplier,
        salt_left: shape.salt_left,
        salt_right: shape.salt_right,
        construction_start: shape.construction_start,
        construction_end: shape.construction_end,
    };
    let valid = (0..descriptor.rows)
        .all(|row| (0..descriptor.columns).all(|column| descriptor.row_for(row, column).is_some()));
    valid.then_some((target_symbol, descriptor))
}

pub fn detect_reference_identity_tables(
    source: &str,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<SymbolId, ReferenceIdentityTable> {
    let mut tables = if let Some(patterns) = reference_identity_patterns() {
        patterns
            .row
            .captures_iter(source)
            .filter_map(|row_caps| parse_reference_identity_shape(source, &patterns, &row_caps))
            .filter_map(|shape| prove_reference_identity_shape(&shape, scoping, reference_spans))
            .collect::<HashMap<_, _>>()
    } else {
        HashMap::new()
    };
    for (symbol, descriptor) in
        detect_sync_reference_identity_tables(source, scoping, reference_spans)
    {
        match tables.get(&symbol) {
            Some(existing) if existing != &descriptor => {
                tables.remove(&symbol);
            }
            Some(_) => {}
            None => {
                tables.insert(symbol, descriptor);
            }
        }
    }
    tables
}

pub fn reference_identity(
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
    let first = exact_u32(first)?;
    let second = exact_u32(second)?;
    Some((symbol, table.identity_for(first, second)?))
}

/// Exact scalar cells and existing own array slots in one simulated activation.
/// An opaque evaluation forgets non-state facts; it cannot write a private,
/// nonescaping dispatcher binding except through an explicitly modeled write.
#[derive(Clone)]
struct ArithmeticEnvironment<'c> {
    scoping: &'c Scoping,
    bindings: &'c BindingFacts,
    state: SymbolId,
    values: HashMap<SymbolId, Value>,
    arrays: HashSet<SymbolId>,
    slots: HashMap<(SymbolId, u32), Option<Value>>,
    reflective_activation: bool,
    per_iteration_binding: bool,
    immediate_depth: usize,
}

#[derive(Clone, Copy)]
enum ArithmeticLocation {
    Binding(SymbolId),
    Slot(SymbolId, u32),
}

impl ArithmeticEnvironment<'_> {
    fn symbol(&self, id: &IdentifierReference<'_>) -> Option<SymbolId> {
        self.bindings
            .resolved_symbol(self.scoping, id.reference_id.get()?)
    }

    fn trackable(&self, symbol: SymbolId) -> bool {
        self.scoping.symbol_flags(symbol).is_variable()
            && self.bindings.is_private(self.scoping, symbol)
            && !self
                .bindings
                .is_mapped_arguments_exposed(self.scoping, symbol)
    }

    fn member_location(
        &self,
        member: &oxc_ast::ast::ComputedMemberExpression<'_>,
    ) -> Option<ArithmeticLocation> {
        if member.optional {
            return None;
        }
        let Expression::Identifier(id) = member.object.without_parentheses() else {
            return None;
        };
        let symbol = self.symbol(id)?;
        let index = canonical_array_index(&self.eval(&member.expression)?)?;
        self.slots
            .contains_key(&(symbol, index))
            .then_some(ArithmeticLocation::Slot(symbol, index))
    }

    fn read(&self, location: ArithmeticLocation) -> Option<Value> {
        match location {
            ArithmeticLocation::Binding(symbol) => self.values.get(&symbol).cloned(),
            ArithmeticLocation::Slot(symbol, index) => self.slots.get(&(symbol, index))?.clone(),
        }
    }

    fn eval(&self, expression: &Expression<'_>) -> Option<Value> {
        eval_with_resolver(expression, &|expr| match expr {
            Expression::Identifier(id) => self.read(ArithmeticLocation::Binding(self.symbol(id)?)),
            Expression::ComputedMemberExpression(member) => {
                self.read(self.member_location(member)?)
            }
            _ => None,
        })
    }

    fn set(&mut self, location: ArithmeticLocation, value: Option<Value>) {
        match location {
            ArithmeticLocation::Binding(symbol) => {
                self.slots.retain(|(owner, _), _| *owner != symbol);
                if let Some(value) = value.filter(|_| self.trackable(symbol)) {
                    self.values.insert(symbol, value);
                } else {
                    self.values.remove(&symbol);
                }
            }
            ArithmeticLocation::Slot(symbol, index) => {
                if let Some(slot) = self.slots.get_mut(&(symbol, index)) {
                    *slot = value;
                }
            }
        }
    }

    fn invalidate_opaque(&mut self) -> Option<()> {
        // An opaque call can expose a sloppy immediate function through
        // legacy caller reflection, allowing its captured state cell to escape.
        if self.reflective_activation {
            return None;
        }
        self.values.retain(|symbol, _| *symbol == self.state);
        self.slots.clear();
        Some(())
    }

    fn retire_scope(&mut self, scope: ScopeId) {
        let bindings = self.scoping.get_bindings(scope);
        self.values
            .retain(|symbol, _| !bindings.values().any(|binding| binding == symbol));
        self.slots
            .retain(|(symbol, _), _| !bindings.values().any(|binding| binding == symbol));
    }

    // Unknown values are not necessarily unknown effects. The shared
    // evaluator proves concrete primitives; these additional expressions
    // never call user code even when their resulting value is unknown.
    fn non_reentrant_expression(&self, expression: &Expression<'_>) -> bool {
        if self.eval(expression).is_some() || inert_literal_value(expression) {
            return true;
        }
        match expression.without_parentheses() {
            Expression::Identifier(id) => {
                self.symbol(id).is_some_and(|symbol| self.trackable(symbol))
            }
            Expression::BinaryExpression(binary)
                if matches!(binary.operator.as_str(), "===" | "!==") =>
            {
                self.non_reentrant_expression(&binary.left)
                    && self.non_reentrant_expression(&binary.right)
            }
            Expression::LogicalExpression(logical) => {
                self.non_reentrant_expression(&logical.left)
                    && self.non_reentrant_expression(&logical.right)
            }
            Expression::ConditionalExpression(conditional) => {
                self.non_reentrant_expression(&conditional.test)
                    && self.non_reentrant_expression(&conditional.consequent)
                    && self.non_reentrant_expression(&conditional.alternate)
            }
            Expression::UnaryExpression(unary)
                if matches!(unary.operator.as_str(), "!" | "void" | "typeof") =>
            {
                self.non_reentrant_expression(&unary.argument)
            }
            Expression::SequenceExpression(sequence) => sequence
                .expressions
                .iter()
                .all(|expression| self.non_reentrant_expression(expression)),
            _ => false,
        }
    }

    fn join(&mut self, other: &Self) {
        self.values.retain(|symbol, value| {
            other
                .values
                .get(symbol)
                .is_some_and(|right| identical_primitive_value(value, right))
        });
        self.slots.retain(|key, value| {
            let Some(right) = other.slots.get(key) else {
                return false;
            };
            if !value
                .as_ref()
                .zip(right.as_ref())
                .is_some_and(|(left, right)| identical_primitive_value(left, right))
            {
                *value = None;
            }
            true
        });
    }

    fn state_value(&self) -> Option<&Value> {
        self.values.get(&self.state)
    }

    fn opaque_state_access(&self, visit: impl FnOnce(&mut StateUseProbe<'_>)) -> bool {
        let mut probe = StateUseProbe::new(
            self.scoping,
            self.state,
            self.per_iteration_binding,
            StateUseMode::Opaque,
        );
        visit(&mut probe);
        probe.found
    }

    fn opaque_expression(&mut self, expression: &Expression<'_>) -> Option<()> {
        if self.opaque_state_access(|probe| probe.visit_expression(expression)) {
            return None;
        }
        if self.non_reentrant_expression(expression) {
            return Some(());
        }
        self.invalidate_opaque()
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum StateUseMode {
    /// Any reference matters when legacy caller reflection can expose an invocation.
    Any,
    /// An opaque evaluation must not write the state or escape a per-iteration cell.
    Opaque,
    /// Recognized immediate calls are not deferred activations.
    Deferred,
}

struct StateUseProbe<'c> {
    scoping: &'c Scoping,
    state: SymbolId,
    per_iteration_binding: bool,
    mode: StateUseMode,
    deferred_depth: usize,
    found: bool,
}

impl<'c> StateUseProbe<'c> {
    const fn new(
        scoping: &'c Scoping,
        state: SymbolId,
        per_iteration_binding: bool,
        mode: StateUseMode,
    ) -> Self {
        Self {
            scoping,
            state,
            per_iteration_binding,
            mode,
            deferred_depth: 0,
            found: false,
        }
    }

    // Field keys and decorators execute during class definition; a non-static
    // initializer executes later, when an instance is constructed.
    fn visit_field_initializer(&mut self, value: Option<&Expression<'_>>, is_static: bool) {
        if let Some(value) = value {
            let depth = usize::from(!is_static);
            self.deferred_depth += depth;
            self.visit_expression(value);
            self.deferred_depth -= depth;
        }
    }
}

impl<'a> Visit<'a> for StateUseProbe<'_> {
    fn visit_expression(&mut self, expression: &Expression<'a>) {
        if self.mode == StateUseMode::Deferred {
            if let Some(invocation) = iife_body(expression, self.scoping) {
                self.visit_function_body(invocation.body);
                return;
            }
        }
        walk::walk_expression(self, expression);
    }

    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        let Some(reference) = id.reference_id.get() else {
            return;
        };
        let reference = self.scoping.get_reference(reference);
        if reference.symbol_id() != Some(self.state) {
            return;
        }
        let deferred = self.deferred_depth > 0;
        self.found |= self.mode == StateUseMode::Any
            || ((self.mode == StateUseMode::Opaque || deferred)
                && (reference.is_write() || (self.per_iteration_binding && deferred)));
    }

    fn visit_function(&mut self, node: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        self.deferred_depth += 1;
        walk::walk_function(self, node, flags);
        self.deferred_depth -= 1;
    }

    fn visit_arrow_function_expression(
        &mut self,
        node: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        self.deferred_depth += 1;
        walk::walk_arrow_function_expression(self, node);
        self.deferred_depth -= 1;
    }

    fn visit_property_definition(&mut self, node: &oxc_ast::ast::PropertyDefinition<'a>) {
        self.visit_decorators(&node.decorators);
        self.visit_property_key(&node.key);
        self.visit_field_initializer(node.value.as_ref(), node.r#static);
    }

    fn visit_accessor_property(&mut self, node: &oxc_ast::ast::AccessorProperty<'a>) {
        self.visit_decorators(&node.decorators);
        self.visit_property_key(&node.key);
        self.visit_field_initializer(node.value.as_ref(), node.r#static);
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

#[derive(Debug)]
enum ArithmeticCaseOutcome {
    Flow(StateFlow),
    Conditional {
        test: String,
        consequent: Value,
        alternate: Value,
    },
}

struct ArithmeticBranchResult {
    chunks: Vec<String>,
    state_path: Vec<String>,
    termination: String,
    register_reads_rewritten: usize,
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
    break_depth: usize,
    continue_depth: usize,
}

impl LoopControlDetector {
    fn walk_loop(&mut self, walk: impl FnOnce(&mut Self)) {
        self.break_depth += 1;
        self.continue_depth += 1;
        walk(self);
        self.continue_depth -= 1;
        self.break_depth -= 1;
    }
}

impl<'a> Visit<'a> for LoopControlDetector {
    fn visit_break_statement(&mut self, it: &oxc_ast::ast::BreakStatement<'a>) {
        if it.label.is_some() || self.break_depth == 0 {
            self.found = true;
        }
    }

    fn visit_continue_statement(&mut self, it: &oxc_ast::ast::ContinueStatement<'a>) {
        if it.label.is_some() || self.continue_depth == 0 {
            self.found = true;
        }
    }

    fn visit_switch_statement(&mut self, it: &oxc_ast::ast::SwitchStatement<'a>) {
        self.break_depth += 1;
        walk::walk_switch_statement(self, it);
        self.break_depth -= 1;
    }

    fn visit_for_statement(&mut self, it: &oxc_ast::ast::ForStatement<'a>) {
        self.walk_loop(|this| walk::walk_for_statement(this, it));
    }

    fn visit_while_statement(&mut self, it: &oxc_ast::ast::WhileStatement<'a>) {
        self.walk_loop(|this| walk::walk_while_statement(this, it));
    }

    fn visit_do_while_statement(&mut self, it: &oxc_ast::ast::DoWhileStatement<'a>) {
        self.walk_loop(|this| walk::walk_do_while_statement(this, it));
    }

    fn visit_for_in_statement(&mut self, it: &oxc_ast::ast::ForInStatement<'a>) {
        self.walk_loop(|this| walk::walk_for_in_statement(this, it));
    }

    fn visit_for_of_statement(&mut self, it: &oxc_ast::ast::ForOfStatement<'a>) {
        self.walk_loop(|this| walk::walk_for_of_statement(this, it));
    }

    fn visit_function(&mut self, _it: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {
        // Nested function control flow cannot target the surrounding statement.
    }

    fn visit_arrow_function_expression(&mut self, _it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
        // Nested function control flow cannot target the surrounding statement.
    }
}

pub fn statement_has_loop_control(stmt: &Statement<'_>) -> bool {
    let mut detector = LoopControlDetector::default();
    detector.visit_statement(stmt);
    detector.found
}

pub fn direct_assignment_name<'a>(
    target: &'a oxc_ast::ast::AssignmentTarget<'a>,
) -> Option<&'a str> {
    match target {
        oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.as_str()),
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct ImmediateInvocation<'a> {
    body: &'a oxc_ast::ast::FunctionBody<'a>,
    reflective: bool,
}

fn iife_body<'a>(expr: &'a Expression<'a>, scoping: &Scoping) -> Option<ImmediateInvocation<'a>> {
    match expr {
        Expression::ParenthesizedExpression(p) => iife_body(&p.expression, scoping),
        Expression::UnaryExpression(u)
            if matches!(u.operator.as_str(), "!" | "void" | "+" | "-" | "~") =>
        {
            iife_body(&u.argument, scoping)
        }
        Expression::CallExpression(call) if !call.optional && call.arguments.is_empty() => {
            match call.callee.without_parentheses() {
                Expression::FunctionExpression(fun)
                    if fun.id.is_none()
                        && !fun.r#async
                        && !fun.generator
                        && fun.params.items.is_empty()
                        && fun.params.rest.is_none() =>
                {
                    let body = fun.body.as_ref()?;
                    (!body
                        .statements
                        .iter()
                        .any(|statement| statement_mentions(statement, "arguments")))
                    .then_some(ImmediateInvocation {
                        body,
                        reflective: !scoping.scope_flags(fun.scope_id.get()?).is_strict_mode(),
                    })
                }
                Expression::ArrowFunctionExpression(fun)
                    if !fun.r#async && fun.params.items.is_empty() && fun.params.rest.is_none() =>
                {
                    let oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) = &fun.body else {
                        return None;
                    };
                    Some(ImmediateInvocation {
                        body,
                        reflective: false,
                    })
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn assignment_location(
    env: &ArithmeticEnvironment<'_>,
    target: &oxc_ast::ast::AssignmentTarget<'_>,
) -> Option<ArithmeticLocation> {
    simple_assignment_location(env, target.as_simple_assignment_target()?)
}

fn simple_assignment_location(
    env: &ArithmeticEnvironment<'_>,
    target: &oxc_ast::ast::SimpleAssignmentTarget<'_>,
) -> Option<ArithmeticLocation> {
    match target {
        oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(id) => {
            let symbol = env.symbol(id)?;
            env.trackable(symbol)
                .then_some(ArithmeticLocation::Binding(symbol))
        }
        oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member) => {
            env.member_location(member)
        }
        _ => None,
    }
}

type ExpressionFlow = (StateFlow, Option<Value>);

fn simulate_assignment(
    assign: &oxc_ast::ast::AssignmentExpression<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<ExpressionFlow> {
    let location = assignment_location(env, &assign.left);
    let operator = assign.operator.as_str();
    // The Reference and any compound GetValue precede RHS evaluation.
    let old = location.and_then(|location| env.read(location));
    if location.is_none() {
        if env.opaque_state_access(|probe| probe.visit_assignment_target(&assign.left)) {
            return None;
        }
        env.invalidate_opaque()?;
    }
    if let Some(logical) = operator
        .strip_suffix('=')
        .filter(|op| matches!(*op, "&&" | "||" | "??"))
    {
        if let Some(old) = old.as_ref() {
            match eval_logical_left(logical, old.clone())? {
                LogicalStep::Value(value) => return Some((StateFlow::Normal, Some(value))),
                LogicalStep::EvaluateRight => {}
            }
        } else {
            // The assignment is short-circuited on one path. Join the
            // unchanged environment with the evaluation and write path.
            let mut taken = env.clone();
            let (flow, value) = simulate_expression(&assign.right, &mut taken)?;
            if flow == StateFlow::Normal {
                if let Some(location) = location {
                    taken.set(location, value);
                } else {
                    taken.invalidate_opaque()?;
                }
            }
            return join_expression_paths(env, (StateFlow::Normal, None), taken, (flow, None));
        }
    }
    let (flow, right) = simulate_expression(&assign.right, env)?;
    if flow != StateFlow::Normal {
        return Some((flow, None));
    }
    let value = if matches!(operator, "=" | "&&=" | "||=" | "??=") {
        right
    } else if let Some(op) = operator.strip_suffix('=') {
        old.as_ref()
            .zip(right.as_ref())
            .and_then(|(left, right)| eval_binary(op, left, right))
    } else {
        None
    };
    if let Some(location) = location {
        if value.is_none() && operator != "=" {
            env.invalidate_opaque()?;
        }
        env.set(location, value.clone());
    } else {
        // An unproven PutValue can execute user code.
        env.invalidate_opaque()?;
    }
    Some((StateFlow::Normal, value))
}

fn simulate_update(
    update: &oxc_ast::ast::UpdateExpression<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<ExpressionFlow> {
    let Some(location) = simple_assignment_location(env, &update.argument) else {
        if env.opaque_state_access(|probe| probe.visit_simple_assignment_target(&update.argument)) {
            return None;
        }
        env.invalidate_opaque()?;
        return Some((StateFlow::Normal, None));
    };
    let Some(old) = env.read(location) else {
        env.invalidate_opaque()?;
        env.set(location, None);
        return Some((StateFlow::Normal, None));
    };
    let old = old.number();
    let next = match update.operator.as_str() {
        "++" => old + 1.0,
        "--" => old - 1.0,
        _ => return None,
    };
    env.set(location, Some(Value::Number(next)));
    Some((
        StateFlow::Normal,
        Some(Value::Number(if update.prefix { next } else { old })),
    ))
}

/// All bindings declared inside an immediate invocation belong to a fresh
/// activation. Retire their facts on entry and exit, never by source spelling.
#[derive(Default)]
struct ActivationBindings(HashSet<SymbolId>);
impl<'a> Visit<'a> for ActivationBindings {
    fn visit_binding_identifier(&mut self, id: &oxc_ast::ast::BindingIdentifier<'a>) {
        self.0.extend(id.symbol_id.get());
    }
}

fn simulate_immediate_invocation(
    invocation: ImmediateInvocation<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<ExpressionFlow> {
    let body = invocation.body;
    let previous = env.reflective_activation;
    let mut probe = StateUseProbe::new(
        env.scoping,
        env.state,
        env.per_iteration_binding,
        StateUseMode::Any,
    );
    probe.visit_function_body(body);
    env.reflective_activation |= invocation.reflective && probe.found;
    let mut locals = ActivationBindings::default();
    locals.visit_function_body(body);
    env.values.retain(|symbol, _| !locals.0.contains(symbol));
    env.slots
        .retain(|(symbol, _), _| !locals.0.contains(symbol));
    env.immediate_depth += 1;
    let flow = simulate_statements(&body.statements, env)?;
    env.immediate_depth -= 1;
    env.reflective_activation = previous;
    env.values.retain(|symbol, _| !locals.0.contains(symbol));
    env.slots
        .retain(|(symbol, _), _| !locals.0.contains(symbol));
    match flow {
        StateFlow::Throw => Some((StateFlow::Throw, None)),
        StateFlow::Normal | StateFlow::Return => Some((StateFlow::Normal, None)),
        StateFlow::Break | StateFlow::Continue => None,
    }
}

fn join_expression_paths<'c>(
    env: &mut ArithmeticEnvironment<'c>,
    left: ExpressionFlow,
    alternate: ArithmeticEnvironment<'c>,
    right: ExpressionFlow,
) -> Option<ExpressionFlow> {
    match (left.0, right.0) {
        (StateFlow::Normal, StateFlow::Normal) => {
            env.join(&alternate);
            let value = left.1.filter(|value| {
                right
                    .1
                    .as_ref()
                    .is_some_and(|other| identical_primitive_value(value, other))
            });
            Some((StateFlow::Normal, value))
        }
        (StateFlow::Normal, StateFlow::Throw) => Some(left),
        (StateFlow::Throw, StateFlow::Normal) => {
            // Preserve only the reaching normal path. An abrupt path's
            // effects are still in the original, retained expression.
            env.values = alternate.values;
            env.slots = alternate.slots;
            Some(right)
        }
        (StateFlow::Throw, StateFlow::Throw) => Some((StateFlow::Throw, None)),
        _ => None,
    }
}

fn simulate_binary(
    binary: &oxc_ast::ast::BinaryExpression<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<ExpressionFlow> {
    let (flow, left) = simulate_expression(&binary.left, env)?;
    if flow != StateFlow::Normal {
        return Some((flow, None));
    }
    let (flow, right) = simulate_expression(&binary.right, env)?;
    if flow != StateFlow::Normal {
        return Some((flow, None));
    }
    let operator = binary.operator.as_str();
    let value = left
        .as_ref()
        .zip(right.as_ref())
        .and_then(|(left, right)| eval_binary(operator, left, right));
    if value.is_none() && !matches!(operator, "===" | "!==") {
        // The unproved operands may have observable coercion behavior.
        env.invalidate_opaque()?;
    }
    Some((StateFlow::Normal, value))
}

fn simulate_logical(
    logical: &oxc_ast::ast::LogicalExpression<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<ExpressionFlow> {
    let (flow, left) = simulate_expression(&logical.left, env)?;
    if flow != StateFlow::Normal {
        return Some((flow, None));
    }
    if let Some(left) = left {
        return match eval_logical_left(logical.operator.as_str(), left)? {
            LogicalStep::Value(value) => Some((StateFlow::Normal, Some(value))),
            LogicalStep::EvaluateRight => simulate_expression(&logical.right, env),
        };
    }
    let mut alternate = env.clone();
    let right = simulate_expression(&logical.right, &mut alternate)?;
    join_expression_paths(env, (StateFlow::Normal, None), alternate, right)
}

fn simulate_expression(
    expr: &Expression<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<ExpressionFlow> {
    if let Some(value) = env.eval(expr) {
        return Some((StateFlow::Normal, Some(value)));
    }
    match expr {
        Expression::ParenthesizedExpression(p) => simulate_expression(&p.expression, env),
        Expression::SequenceExpression(seq) => {
            let mut result = (StateFlow::Normal, None);
            for item in &seq.expressions {
                result = simulate_expression(item, env)?;
                if result.0 != StateFlow::Normal {
                    break;
                }
            }
            Some(result)
        }
        Expression::AssignmentExpression(assign) => simulate_assignment(assign, env),
        Expression::UpdateExpression(update) => simulate_update(update, env),
        Expression::BinaryExpression(binary) => simulate_binary(binary, env),
        Expression::LogicalExpression(logical) => simulate_logical(logical, env),
        Expression::ConditionalExpression(branch) => {
            let (flow, test) = simulate_expression(&branch.test, env)?;
            if flow != StateFlow::Normal {
                return Some((flow, None));
            }
            if let Some(test) = test {
                return simulate_expression(
                    if test.truthy() {
                        &branch.consequent
                    } else {
                        &branch.alternate
                    },
                    env,
                );
            }
            let mut alternate = env.clone();
            let left = simulate_expression(&branch.consequent, env)?;
            let right = simulate_expression(&branch.alternate, &mut alternate)?;
            join_expression_paths(env, left, alternate, right)
        }
        Expression::UnaryExpression(unary)
            if matches!(
                unary.operator.as_str(),
                "void" | "!" | "+" | "-" | "~" | "typeof"
            ) =>
        {
            let (flow, value) = simulate_expression(&unary.argument, env)?;
            if flow != StateFlow::Normal {
                return Some((flow, None));
            }
            if unary.operator.as_str() == "void" {
                return Some((flow, Some(Value::Undefined)));
            }
            let value = value
                .as_ref()
                .and_then(|value| eval_unary_value(unary.operator.as_str(), value));
            if value.is_none() && matches!(unary.operator.as_str(), "+" | "-" | "~") {
                // ToNumeric of an unproved object may invoke user code.
                env.invalidate_opaque()?;
            }
            Some((flow, value))
        }
        _ => {
            if let Some(invocation) = iife_body(expr, env.scoping) {
                return simulate_immediate_invocation(invocation, env);
            }
            env.opaque_expression(expr)?;
            Some((StateFlow::Normal, None))
        }
    }
}

#[derive(Clone, Copy)]
enum SwitchSelection {
    Case(usize),
    NoMatch,
}

/// Unknown selector evaluation and a proven no-match are distinct outcomes.
fn select_switch_case(
    switch: &oxc_ast::ast::SwitchStatement<'_>,
    env: &ArithmeticEnvironment<'_>,
) -> Option<SwitchSelection> {
    let discriminant = env.eval(&switch.discriminant)?;
    let mut default = None;
    for (index, case) in switch.cases.iter().enumerate() {
        let Some(test) = &case.test else {
            default = Some(index);
            continue;
        };
        if strict_primitive_equal(&discriminant, &env.eval(test)?) {
            return Some(SwitchSelection::Case(index));
        }
    }
    Some(default.map_or(SwitchSelection::NoMatch, SwitchSelection::Case))
}

fn simulate_switch(
    switch: &oxc_ast::ast::SwitchStatement<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<StateFlow> {
    let scope = switch.scope_id.get()?;
    env.retire_scope(scope);
    let SwitchSelection::Case(start) = select_switch_case(switch, env)? else {
        return Some(StateFlow::Normal);
    };
    for case in switch.cases.iter().skip(start) {
        for stmt in &case.consequent {
            match simulate_statement(stmt, env)? {
                StateFlow::Normal => {}
                StateFlow::Break => {
                    env.retire_scope(scope);
                    return Some(StateFlow::Normal);
                }
                flow => {
                    env.retire_scope(scope);
                    return Some(flow);
                }
            }
        }
    }
    env.retire_scope(scope);
    Some(StateFlow::Normal)
}

fn initialize_register_array(
    symbol: SymbolId,
    array: &oxc_ast::ast::ArrayExpression<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<StateFlow> {
    // Sparse holes and spread tails do not establish an own data property.
    // Never infer a value from writing an index which might hit a prototype setter.
    let mut slots = Vec::new();
    for (index, element) in array.elements.iter().enumerate() {
        match element {
            ArrayExpressionElement::Elision(_) => {}
            ArrayExpressionElement::SpreadElement(_) => return None,
            _ => {
                let (flow, value) = simulate_expression(element.as_expression()?, env)?;
                if flow != StateFlow::Normal {
                    return Some(flow);
                }
                slots.push((u32::try_from(index).ok()?, value));
            }
        }
    }
    env.set(ArithmeticLocation::Binding(symbol), None);
    env.slots.extend(
        slots
            .into_iter()
            .map(|(index, value)| ((symbol, index), value)),
    );
    Some(StateFlow::Normal)
}

fn simulate_declaration(
    declaration: &oxc_ast::ast::VariableDeclaration<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<StateFlow> {
    if !matches!(
        declaration.kind,
        VariableDeclarationKind::Var
            | VariableDeclarationKind::Let
            | VariableDeclarationKind::Const
    ) {
        return None;
    }
    for d in &declaration.declarations {
        let BindingPattern::BindingIdentifier(id) = &d.id else {
            return None;
        };
        let symbol = id.symbol_id.get()?;
        if let Some(init) = &d.init {
            if env.arrays.contains(&symbol) {
                if let Expression::ArrayExpression(array) = init {
                    if array
                        .elements
                        .iter()
                        .any(|element| matches!(element, ArrayExpressionElement::SpreadElement(_)))
                    {
                        env.opaque_expression(init)?;
                        env.set(ArithmeticLocation::Binding(symbol), None);
                        continue;
                    }
                    let flow = initialize_register_array(symbol, array, env)?;
                    if flow != StateFlow::Normal {
                        return Some(flow);
                    }
                    continue;
                }
            }
            let (flow, value) = simulate_expression(init, env)?;
            if flow != StateFlow::Normal {
                return Some(flow);
            }
            if !env.trackable(symbol) {
                env.invalidate_opaque()?;
            }
            env.set(ArithmeticLocation::Binding(symbol), value);
        } else if declaration.kind != VariableDeclarationKind::Var {
            env.set(ArithmeticLocation::Binding(symbol), Some(Value::Undefined));
        }
        // A var declaration without initializer performs no runtime write.
    }
    Some(StateFlow::Normal)
}

#[derive(Default)]
struct LocalReturnProbe(bool);

impl<'a> Visit<'a> for LocalReturnProbe {
    fn visit_return_statement(&mut self, _: &oxc_ast::ast::ReturnStatement<'a>) {
        self.0 = true;
    }

    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: ScopeFlags) {}
    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}
}

fn simulate_statement(
    stmt: &Statement<'_>,
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<StateFlow> {
    match stmt {
        Statement::BlockStatement(block) => {
            let scope = block.scope_id.get()?;
            env.retire_scope(scope);
            let flow = simulate_statements(&block.body, env)?;
            env.retire_scope(scope);
            Some(flow)
        }
        Statement::VariableDeclaration(decl) => simulate_declaration(decl, env),
        Statement::ExpressionStatement(es) => {
            simulate_expression(&es.expression, env).map(|(flow, _)| flow)
        }
        Statement::IfStatement(branch) => {
            let (flow, test) = simulate_expression(&branch.test, env)?;
            if flow != StateFlow::Normal {
                return Some(flow);
            }
            if let Some(test) = test {
                if test.truthy() {
                    return simulate_statement(&branch.consequent, env);
                }
                return branch
                    .alternate
                    .as_ref()
                    .map_or(Some(StateFlow::Normal), |alt| simulate_statement(alt, env));
            }
            let mut alternate = env.clone();
            let yes_flow = simulate_statement(&branch.consequent, env)?;
            let no_flow = branch
                .alternate
                .as_ref()
                .map_or(Some(StateFlow::Normal), |alt| {
                    simulate_statement(alt, &mut alternate)
                })?;
            match (yes_flow, no_flow) {
                (StateFlow::Normal, StateFlow::Normal) => {
                    env.join(&alternate);
                    Some(StateFlow::Normal)
                }
                (StateFlow::Normal, StateFlow::Return | StateFlow::Throw) => {
                    Some(StateFlow::Normal)
                }
                (StateFlow::Return | StateFlow::Throw, StateFlow::Normal) => {
                    *env = alternate;
                    Some(StateFlow::Normal)
                }
                (left, right) if left == right => {
                    env.join(&alternate);
                    Some(left)
                }
                _ => None,
            }
        }
        Statement::SwitchStatement(switch) => simulate_switch(switch, env),
        Statement::TryStatement(_) => {
            if env.opaque_state_access(|probe| probe.visit_statement(stmt))
                || statement_has_loop_control(stmt)
            {
                return None;
            }
            if env.immediate_depth > 0 {
                let mut returns = LocalReturnProbe::default();
                returns.visit_statement(stmt);
                if returns.0 {
                    return None;
                }
            }
            env.invalidate_opaque()?;
            Some(StateFlow::Normal)
        }
        Statement::BreakStatement(brk) if brk.label.is_none() => Some(StateFlow::Break),
        Statement::ContinueStatement(cont) if cont.label.is_none() => Some(StateFlow::Continue),
        Statement::ReturnStatement(ret) => {
            if let Some(argument) = &ret.argument {
                let (flow, _) = simulate_expression(argument, env)?;
                if flow != StateFlow::Normal {
                    return Some(flow);
                }
            }
            Some(StateFlow::Return)
        }
        Statement::ThrowStatement(thrown) => {
            simulate_expression(&thrown.argument, env)?;
            Some(StateFlow::Throw)
        }
        Statement::EmptyStatement(_) => Some(StateFlow::Normal),
        Statement::DebuggerStatement(_) => {
            // A debugger can mutate the suspended activation.
            None
        }
        _ => None,
    }
}

fn simulate_statements(
    statements: &[Statement<'_>],
    env: &mut ArithmeticEnvironment<'_>,
) -> Option<StateFlow> {
    for stmt in statements {
        let flow = simulate_statement(stmt, env)?;
        if flow != StateFlow::Normal {
            return Some(flow);
        }
    }
    Some(StateFlow::Normal)
}

/// Match a pure primitive exit test against its exact lexical state cell.
fn dispatcher_exit_test(
    test: &Expression<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<(SymbolId, &'static str)> {
    let Expression::BinaryExpression(binary) = test.without_parentheses() else {
        return None;
    };
    if !matches!(binary.operator.as_str(), "!=" | "!==") {
        return None;
    }
    let ((Expression::Identifier(state), terminal) | (terminal, Expression::Identifier(state))) = (
        binary.left.without_parentheses(),
        binary.right.without_parentheses(),
    ) else {
        return None;
    };
    let symbol = facts.resolved_symbol(scoping, state.reference_id.get()?)?;
    let terminal = eval(terminal)?;
    Some((
        symbol,
        if matches!(terminal, Value::Undefined) {
            "undefined"
        } else {
            "loop_test"
        },
    ))
}

fn resolved_refs_within(
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
    symbol: SymbolId,
    spans: &[Span],
) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| {
            reference_spans
                .get(reference_id)
                .is_some_and(|reference_span| {
                    spans.iter().any(|span| {
                        reference_span.start >= span.start && reference_span.end <= span.end
                    })
                })
        })
}

#[derive(Default)]
struct RegisterArrayShapeCollector {
    candidates: Vec<SymbolId>,
    numeric_member_refs: HashSet<ReferenceId>,
    function_depth: usize,
}

impl RegisterArrayShapeCollector {
    fn record_numeric_member(&mut self, it: &oxc_ast::ast::ComputedMemberExpression<'_>) {
        if it.optional
            || eval(&it.expression)
                .as_ref()
                .and_then(canonical_array_index)
                .is_none()
        {
            return;
        }
        let Expression::Identifier(object) = &it.object else {
            return;
        };
        if let Some(reference_id) = object.reference_id.get() {
            self.numeric_member_refs.insert(reference_id);
        }
    }
}

impl<'a> Visit<'a> for RegisterArrayShapeCollector {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        if self.function_depth == 0
            && matches!(
                it.kind,
                VariableDeclarationKind::Var
                    | VariableDeclarationKind::Let
                    | VariableDeclarationKind::Const
            )
        {
            for declaration in &it.declarations {
                let BindingPattern::BindingIdentifier(id) = &declaration.id else {
                    continue;
                };
                let Some(Expression::ArrayExpression(_)) = &declaration.init else {
                    continue;
                };
                let Some(symbol) = id.symbol_id.get() else {
                    continue;
                };
                self.candidates.push(symbol);
            }
        }
        walk::walk_variable_declaration(self, it);
    }

    fn visit_computed_member_expression(
        &mut self,
        it: &oxc_ast::ast::ComputedMemberExpression<'a>,
    ) {
        self.record_numeric_member(it);
        walk::walk_computed_member_expression(self, it);
    }

    fn visit_assignment_expression(&mut self, it: &oxc_ast::ast::AssignmentExpression<'a>) {
        if let oxc_ast::ast::AssignmentTarget::ComputedMemberExpression(member) = &it.left {
            self.record_numeric_member(member);
        }
        walk::walk_assignment_expression(self, it);
    }

    fn visit_update_expression(&mut self, it: &oxc_ast::ast::UpdateExpression<'a>) {
        if let oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member) = &it.argument
        {
            self.record_numeric_member(member);
        }
        walk::walk_update_expression(self, it);
    }

    fn visit_function(&mut self, it: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        self.function_depth += 1;
        walk::walk_function(self, it, flags);
        self.function_depth -= 1;
    }

    fn visit_arrow_function_expression(&mut self, it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
        self.function_depth += 1;
        walk::walk_arrow_function_expression(self, it);
        self.function_depth -= 1;
    }
}

struct KnownRegisterReadCollector<'c, 'e> {
    env: &'e ArithmeticEnvironment<'c>,
    replacements: Vec<(Span, String)>,
}

impl<'a> Visit<'a> for KnownRegisterReadCollector<'_, '_> {
    fn visit_computed_member_expression(
        &mut self,
        it: &oxc_ast::ast::ComputedMemberExpression<'a>,
    ) {
        if let Some(text) = self
            .env
            .member_location(it)
            .and_then(|location| self.env.read(location))
            .and_then(|value| value.render_expression())
        {
            self.replacements.push((it.span, text));
            return;
        }
        walk::walk_computed_member_expression(self, it);
    }
    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: ScopeFlags) {}
    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReferenceCaseFlow {
    Normal,
    Continue,
    Break,
    Return,
    Throw,
}

struct ReferenceStateSetup {
    state_var: String,
    table_symbol: SymbolId,
    current: u32,
    chunks: Vec<String>,
    env: HashMap<String, Value>,
}

fn render_block(chunks: &[String]) -> String {
    format!("{{\n{}\n}}", chunks.join("\n"))
}

struct ArithmeticEntry {
    symbol: SymbolId,
    initial: Value,
    init_text: Option<String>,
    per_iteration_binding: bool,
}

struct ArithmeticStateSetup<'a> {
    state_symbol: SymbolId,
    per_iteration_binding: bool,
    state_var: String,
    completion_live: bool,
    hoisted: String,
    initial: Value,
    init_text: Option<String>,
    test: &'a Expression<'a>,
    loop_termination: &'static str,
    selector_stmts: &'a [Statement<'a>],
    body_scope: ScopeId,
    switch: &'a oxc_ast::ast::SwitchStatement<'a>,
    register_arrays: HashSet<SymbolId>,
}

fn arithmetic_state_result(
    span: Span,
    state_var: &str,
    state_path: Vec<String>,
    chunks: &[String],
    termination: &str,
    register_reads_rewritten: usize,
) -> (String, ArithmeticStateProof) {
    (
        render_block(chunks),
        ArithmeticStateProof {
            iteration: 0,
            input_start: span.start as usize,
            input_end: span.end as usize,
            state_var: state_var.to_string(),
            state_path,
            termination: termination.to_string(),
            register_reads_rewritten,
            branch_test: None,
            branch_paths: Vec::new(),
            branch_terminations: Vec::new(),
        },
    )
}

impl Collector<'_, '_> {
    fn stable_global_alias(&self, expression: &Expression<'_>) -> bool {
        symbol_of(self.scoping, expression)
            .is_some_and(|symbol| self.global_object_aliases.contains(&symbol))
    }

    fn reference_state_builtin_call(
        &self,
        call: &oxc_ast::ast::CallExpression<'_>,
        env: &HashMap<String, Value>,
    ) -> Option<Value> {
        if call.optional || call.arguments.iter().any(oxc_ast::ast::Argument::is_spread) {
            return None;
        }
        if let Some(symbol) = symbol_of(self.scoping, &call.callee) {
            let function = self.pure_functions.get(&symbol)?;
            let values = call
                .arguments
                .iter()
                .map(|argument| self.reference_state_eval(argument.as_expression()?, env))
                .collect::<Option<Vec<_>>>()?;
            return function.evaluate(&values);
        }
        if !self.standard_numeric_builtins {
            return None;
        }
        let Expression::StaticMemberExpression(member) = &call.callee else {
            return None;
        };
        if member.optional {
            return None;
        }
        let property = member.property.name.as_str();
        if self.stable_global_alias(&member.object) {
            return match property {
                "Number" if call.arguments.len() == 1 => Some(Value::Number(
                    self.reference_state_eval(call.arguments[0].as_expression()?, env)?
                        .number(),
                )),
                "parseInt" if matches!(call.arguments.len(), 1 | 2) => {
                    let value =
                        self.reference_state_eval(call.arguments[0].as_expression()?, env)?;
                    let radix = if call.arguments.len() == 2 {
                        exact_u32(
                            self.reference_state_eval(call.arguments[1].as_expression()?, env)?
                                .number(),
                        )?
                    } else {
                        0
                    };
                    js_parse_int(&value.js_string(), radix).map(Value::Number)
                }
                _ => None,
            };
        }
        let Expression::StaticMemberExpression(namespace) = &member.object else {
            return None;
        };
        if namespace.optional
            || namespace.property.name.as_str() != "Math"
            || !self.stable_global_alias(&namespace.object)
            || call.arguments.len() != 1
        {
            return None;
        }
        let value = self
            .reference_state_eval(call.arguments[0].as_expression()?, env)?
            .number();
        let result = match property {
            "floor" => value.floor(),
            "ceil" => value.ceil(),
            "trunc" => value.trunc(),
            _ => return None,
        };
        Some(Value::Number(result))
    }

    fn reference_state_eval(
        &self,
        expression: &Expression<'_>,
        env: &HashMap<String, Value>,
    ) -> Option<Value> {
        if let Some((_symbol, identity)) =
            reference_identity(expression, self.scoping, self.reference_identity_tables)
        {
            return Some(Value::Number(f64::from(identity)));
        }
        match expression {
            Expression::Identifier(identifier) => env.get(identifier.name.as_str()).cloned(),
            Expression::StringLiteral(value) => string_literal_value(value).map(Value::String),
            Expression::NumericLiteral(value) => Some(Value::Number(value.value)),
            Expression::BooleanLiteral(value) => Some(Value::Bool(value.value)),
            Expression::NullLiteral(_) => Some(Value::Null),
            Expression::TemplateLiteral(value) if value.expressions.is_empty() => value
                .quasis
                .first()
                .and_then(template_element_value)
                .map(Value::String),
            Expression::ParenthesizedExpression(value) => {
                self.reference_state_eval(&value.expression, env)
            }
            Expression::UnaryExpression(unary) => eval_unary_value(
                unary.operator.as_str(),
                &self.reference_state_eval(&unary.argument, env)?,
            ),
            Expression::BinaryExpression(value) => eval_binary(
                value.operator.as_str(),
                &self.reference_state_eval(&value.left, env)?,
                &self.reference_state_eval(&value.right, env)?,
            ),
            Expression::LogicalExpression(value) => match eval_logical_left(
                value.operator.as_str(),
                self.reference_state_eval(&value.left, env)?,
            )? {
                LogicalStep::Value(result) => Some(result),
                LogicalStep::EvaluateRight => self.reference_state_eval(&value.right, env),
            },
            Expression::ConditionalExpression(value) => {
                let test = self.reference_state_eval(&value.test, env)?.truthy();
                self.reference_state_eval(
                    if test {
                        &value.consequent
                    } else {
                        &value.alternate
                    },
                    env,
                )
            }
            Expression::CallExpression(call) => self.reference_state_builtin_call(call, env),
            _ => None,
        }
    }

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

    fn clean_reference_state_expression(
        &self,
        expression: &Expression<'_>,
        state_var: &str,
        table_symbol: SymbolId,
        env: &mut HashMap<String, Value>,
    ) -> Option<(Vec<String>, Option<u32>)> {
        if let Some(next) = self.reference_state_assignment(expression, state_var, table_symbol) {
            return Some((Vec::new(), Some(next)));
        }
        match expression {
            Expression::ParenthesizedExpression(parenthesized) => self
                .clean_reference_state_expression(
                    &parenthesized.expression,
                    state_var,
                    table_symbol,
                    env,
                ),
            Expression::SequenceExpression(sequence) => {
                let mut chunks = Vec::new();
                let mut next_state = None;
                for item in &sequence.expressions {
                    let (mut item_chunks, next) =
                        self.clean_reference_state_expression(item, state_var, table_symbol, env)?;
                    chunks.append(&mut item_chunks);
                    if let Some(next) = next {
                        next_state = Some(next);
                    }
                }
                Some((chunks, next_state))
            }
            Expression::ConditionalExpression(conditional)
                if expression_mentions(expression, state_var) =>
            {
                let test = self.reference_state_eval(&conditional.test, env)?.truthy();
                self.clean_reference_state_expression(
                    if test {
                        &conditional.consequent
                    } else {
                        &conditional.alternate
                    },
                    state_var,
                    table_symbol,
                    env,
                )
            }
            Expression::AssignmentExpression(assignment) => {
                if expression_mentions(expression, state_var) {
                    return None;
                }
                if assignment.operator.as_str() == "=" {
                    if let Some(name) = direct_assignment_name(&assignment.left) {
                        if let Some(value) = self.reference_state_eval(&assignment.right, env) {
                            env.insert(name.to_string(), value);
                        } else {
                            env.remove(name);
                        }
                    }
                }
                Some((
                    vec![format!("{};", fragment(self.source, expression.span()))],
                    None,
                ))
            }
            _ => {
                if expression_mentions(expression, state_var) {
                    return None;
                }
                Some((
                    vec![format!("{};", fragment(self.source, expression.span()))],
                    None,
                ))
            }
        }
    }

    fn update_reference_state_environment_from_declaration(
        &self,
        declaration: &oxc_ast::ast::VariableDeclaration<'_>,
        env: &mut HashMap<String, Value>,
    ) -> Option<()> {
        if declaration.kind != VariableDeclarationKind::Var {
            return None;
        }
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                return None;
            };
            if let Some(initializer) = &declarator.init {
                if let Some(value) = self.reference_state_eval(initializer, env) {
                    env.insert(identifier.name.to_string(), value);
                } else {
                    env.remove(identifier.name.as_str());
                }
            } else {
                env.insert(identifier.name.to_string(), Value::Undefined);
            }
        }
        Some(())
    }

    fn clean_reference_state_statement(
        &self,
        stmt: &Statement<'_>,
        state_var: &str,
        table_symbol: SymbolId,
        env: &mut HashMap<String, Value>,
    ) -> Option<(String, Option<u32>, ReferenceCaseFlow)> {
        match stmt {
            Statement::BlockStatement(block) => {
                let mut chunks = Vec::new();
                let mut next_state = None;
                for child in &block.body {
                    let (text, next, flow) =
                        self.clean_reference_state_statement(child, state_var, table_symbol, env)?;
                    if !text.trim().is_empty() {
                        chunks.push(text);
                    }
                    if let Some(next) = next {
                        next_state = Some(next);
                    }
                    if flow != ReferenceCaseFlow::Normal {
                        return Some((render_block(&chunks), next_state, flow));
                    }
                }
                Some((render_block(&chunks), next_state, ReferenceCaseFlow::Normal))
            }
            Statement::ExpressionStatement(expression) => {
                let (chunks, next) = self.clean_reference_state_expression(
                    &expression.expression,
                    state_var,
                    table_symbol,
                    env,
                )?;
                Some((chunks.join("\n"), next, ReferenceCaseFlow::Normal))
            }
            Statement::VariableDeclaration(declaration) => {
                if statement_mentions(stmt, state_var) {
                    return None;
                }
                self.update_reference_state_environment_from_declaration(declaration, env)?;
                Some((
                    fragment(self.source, stmt.span()).to_string(),
                    None,
                    ReferenceCaseFlow::Normal,
                ))
            }
            Statement::IfStatement(branch) if statement_mentions(stmt, state_var) => {
                let test = self.reference_state_eval(&branch.test, env)?.truthy();
                if test {
                    self.clean_reference_state_statement(
                        &branch.consequent,
                        state_var,
                        table_symbol,
                        env,
                    )
                } else if let Some(alternate) = &branch.alternate {
                    self.clean_reference_state_statement(alternate, state_var, table_symbol, env)
                } else {
                    Some((String::new(), None, ReferenceCaseFlow::Normal))
                }
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

    fn reference_state_setup(
        &self,
        it: &oxc_ast::ast::ForStatement<'_>,
    ) -> Option<ReferenceStateSetup> {
        if it.update.is_some() || !matches!(eval(it.test.as_ref()?), Some(Value::Bool(true))) {
            return None;
        }
        let oxc_ast::ast::ForStatementInit::VariableDeclaration(init_decl) = it.init.as_ref()?
        else {
            return None;
        };
        if init_decl.kind != VariableDeclarationKind::Var || init_decl.declarations.is_empty() {
            return None;
        }

        let mut state = None;
        for (index, declaration) in init_decl.declarations.iter().enumerate() {
            let Some(init) = &declaration.init else {
                continue;
            };
            let Some((table_symbol, identity)) =
                reference_identity(init, self.scoping, self.reference_identity_tables)
            else {
                continue;
            };
            if state.is_some() {
                return None;
            }
            let BindingPattern::BindingIdentifier(id) = &declaration.id else {
                return None;
            };
            state = Some((
                index,
                id.symbol_id.get()?,
                id.name.to_string(),
                table_symbol,
                identity,
            ));
        }
        let (state_index, state_symbol, state_var, table_symbol, current) = state?;
        if !resolved_refs_within(self.scoping, self.reference_spans, state_symbol, &[it.span]) {
            return None;
        }
        if init_decl.declarations.iter().any(|declaration| {
            declaration.init.as_ref().is_some_and(|init| {
                expression_mentions(init, &state_var)
                    && direct_identifier_name(init) != Some(state_var.as_str())
            })
        }) {
            return None;
        }

        let other_declarations = init_decl
            .declarations
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != state_index)
            .collect::<Vec<_>>();
        let chunks = if other_declarations.is_empty() {
            Vec::new()
        } else {
            vec![format!(
                "var {};",
                other_declarations
                    .iter()
                    .map(|(_, declaration)| fragment(self.source, declaration.span))
                    .collect::<Vec<_>>()
                    .join(",")
            )]
        };
        let mut env = HashMap::new();
        for (_, declaration) in other_declarations {
            let BindingPattern::BindingIdentifier(identifier) = &declaration.id else {
                return None;
            };
            if let Some(initializer) = &declaration.init {
                if let Some(value) = self.reference_state_eval(initializer, &env) {
                    env.insert(identifier.name.to_string(), value);
                }
            }
        }
        Some(ReferenceStateSetup {
            state_var,
            table_symbol,
            current,
            chunks,
            env,
        })
    }

    fn reference_state_switch<'a>(
        &self,
        it: &'a oxc_ast::ast::ForStatement<'a>,
        state_var: &str,
        table_symbol: SymbolId,
    ) -> Option<(
        &'a [Statement<'a>],
        &'a oxc_ast::ast::SwitchStatement<'a>,
        HashMap<u32, usize>,
    )> {
        let Statement::BlockStatement(body) = &it.body else {
            return None;
        };
        if body.body.len() < 2 {
            return None;
        }
        let Statement::BreakStatement(outer_break) = body.body.last()? else {
            return None;
        };
        if outer_break.label.is_some() {
            return None;
        }
        let switch_index = body.body.len().checked_sub(2)?;
        let Statement::SwitchStatement(switch) = &body.body[switch_index] else {
            return None;
        };
        if direct_identifier_name(&switch.discriminant) != Some(state_var) {
            return None;
        }
        let prefix = &body.body[..switch_index];
        if prefix.iter().any(|statement| {
            statement_mentions(statement, state_var) || statement_has_loop_control(statement)
        }) {
            return None;
        }

        let mut cases = HashMap::new();
        for (index, case) in switch.cases.iter().enumerate() {
            let (symbol, identity) = reference_identity(
                case.test.as_ref()?,
                self.scoping,
                self.reference_identity_tables,
            )?;
            if symbol != table_symbol {
                return None;
            }
            cases.entry(identity).or_insert(index);
        }
        Some((prefix, switch, cases))
    }

    fn simulate_reference_state(
        &self,
        prefix: &[Statement<'_>],
        switch: &oxc_ast::ast::SwitchStatement<'_>,
        cases: &HashMap<u32, usize>,
        setup: ReferenceStateSetup,
    ) -> Option<String> {
        let ReferenceStateSetup {
            state_var,
            table_symbol,
            mut current,
            mut chunks,
            mut env,
        } = setup;
        let mut seen = HashSet::new();
        for _ in 0..256 {
            if !seen.insert(current) {
                return None;
            }
            let Some(start) = cases.get(&current).copied() else {
                return Some(render_block(&chunks));
            };

            for statement in prefix {
                let (text, next, flow) = self.clean_reference_state_statement(
                    statement,
                    &state_var,
                    table_symbol,
                    &mut env,
                )?;
                if next.is_some() || flow != ReferenceCaseFlow::Normal {
                    return None;
                }
                if !text.trim().is_empty() {
                    chunks.push(text);
                }
            }

            let mut next_state = None;
            let mut flow = ReferenceCaseFlow::Normal;
            'cases: for case in switch.cases.iter().skip(start) {
                for stmt in &case.consequent {
                    let (text, next, stmt_flow) = self.clean_reference_state_statement(
                        stmt,
                        &state_var,
                        table_symbol,
                        &mut env,
                    )?;
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
                ReferenceCaseFlow::Continue => current = next_state?,
                ReferenceCaseFlow::Break
                | ReferenceCaseFlow::Return
                | ReferenceCaseFlow::Throw
                | ReferenceCaseFlow::Normal => return Some(render_block(&chunks)),
            }
        }
        None
    }

    pub(super) fn reference_state_replacement(
        &self,
        it: &oxc_ast::ast::ForStatement<'_>,
    ) -> Option<String> {
        let setup = self.reference_state_setup(it)?;
        let (prefix, switch, cases) =
            self.reference_state_switch(it, &setup.state_var, setup.table_symbol)?;
        self.simulate_reference_state(prefix, switch, &cases, setup)
    }

    /// Record an entry fact only when the same statement-list traversal that
    /// proves while initialization reaches this loop. Textual precedence
    /// alone says nothing about a conditional initializer or a later entry
    /// from an enclosing repeated region.
    pub(super) fn record_external_arithmetic_entry(
        &mut self,
        it: &oxc_ast::ast::ForStatement<'_>,
        reaching: &HashMap<SymbolId, (f64, Span)>,
    ) {
        if let Some((symbol, value)) = self.prove_external_arithmetic_entry(it, reaching) {
            self.external_arithmetic_entries
                .insert(it.span, (symbol, value));
        }
    }

    fn prove_external_arithmetic_entry(
        &self,
        it: &oxc_ast::ast::ForStatement<'_>,
        reaching: &HashMap<SymbolId, (f64, Span)>,
    ) -> Option<(SymbolId, f64)> {
        if it.init.is_some() || it.update.is_some() {
            return None;
        }
        let (symbol, _) = dispatcher_exit_test(
            it.test.as_ref()?,
            self.scoping,
            &self.constants.initialization,
        )?;
        let &(value, init_span) = reaching.get(&symbol)?;
        if !self.reaching_state_is_stable(symbol, init_span, it.span)
            || !resolved_refs_within(
                self.scoping,
                self.reference_spans,
                symbol,
                &[init_span, it.span],
            )
            || self
                .scoping
                .get_resolved_reference_ids(symbol)
                .iter()
                .any(|&reference| {
                    self.constants
                        .initialization
                        .resolved_symbol(self.scoping, reference)
                        != Some(symbol)
                })
        {
            return None;
        }
        Some((symbol, value))
    }

    fn confined_register_arrays(&self, it: &oxc_ast::ast::ForStatement<'_>) -> HashSet<SymbolId> {
        let mut collector = RegisterArrayShapeCollector::default();
        collector.visit_for_statement(it);
        collector
            .candidates
            .into_iter()
            .filter(|&symbol| {
                let binding_scope = self.scoping.symbol_scope_id(symbol);
                let references = self.scoping.get_resolved_reference_ids(symbol);
                self.constants
                    .initialization
                    .is_private(self.scoping, symbol)
                    && !self
                        .constants
                        .initialization
                        .is_mapped_arguments_exposed(self.scoping, symbol)
                    && !references.is_empty()
                    && references.iter().all(|&reference_id| {
                        collector.numeric_member_refs.contains(&reference_id)
                            && self
                                .constants
                                .initialization
                                .resolved_symbol(self.scoping, reference_id)
                                == Some(symbol)
                            && self.reference_spans.get(&reference_id).is_some_and(|span| {
                                it.span.start <= span.start && span.end <= it.span.end
                            })
                            && {
                                let reference = self.scoping.get_reference(reference_id);
                                Self::same_function_or_descendant_block_scope(
                                    self.scoping,
                                    reference.scope_id(),
                                    binding_scope,
                                ) || (reference.is_read()
                                    && !reference.is_write()
                                    && !reference.flags().is_member_write_target())
                            }
                    })
            })
            .collect()
    }

    fn render_statement_with_env(
        &self,
        stmt: &Statement<'_>,
        env: &ArithmeticEnvironment<'_>,
    ) -> (String, usize) {
        let span = stmt.span();
        let mut text = fragment(self.source, span).to_string();
        // Rewrite only an independently pure evaluation region. A read
        // later in a compound statement can observe an earlier mutation.
        let candidate = match stmt {
            Statement::ExpressionStatement(es) => {
                if let Expression::AssignmentExpression(assign) =
                    es.expression.without_parentheses()
                {
                    match assignment_location(env, &assign.left) {
                        Some(ArithmeticLocation::Binding(_)) => Some(&assign.right),
                        _ => None,
                    }
                } else {
                    Some(&es.expression)
                }
            }
            Statement::VariableDeclaration(decl) if decl.declarations.len() == 1 => {
                decl.declarations[0].init.as_ref()
            }
            _ => None,
        }
        .filter(|expression| env.eval(expression).is_some());
        let mut collector = KnownRegisterReadCollector {
            env,
            replacements: Vec::new(),
        };
        if let Some(expression) = candidate {
            collector.visit_expression(expression);
        }
        collector
            .replacements
            .sort_by_key(|(span, _)| std::cmp::Reverse(span.start));
        let rewritten = collector.replacements.len();
        for (replacement_span, replacement) in collector.replacements {
            let start = (replacement_span.start - span.start) as usize;
            let end = (replacement_span.end - span.start) as usize;
            text.replace_range(start..end, &replacement);
        }
        // Statements from distinct cases/iterations were never adjacent
        // in the source. Prevent a new automatic semicolon continuation.
        text.push_str("\n;");
        (text, rewritten)
    }

    fn arithmetic_entry(
        &self,
        it: &oxc_ast::ast::ForStatement<'_>,
        tested_symbol: SymbolId,
    ) -> Option<ArithmeticEntry> {
        let (state_symbol, initial, init_text) = match it.init.as_ref() {
            Some(oxc_ast::ast::ForStatementInit::VariableDeclaration(init_decl)) => {
                if !matches!(
                    init_decl.kind,
                    VariableDeclarationKind::Var | VariableDeclarationKind::Let
                ) || init_decl.declarations.len() != 1
                {
                    return None;
                }
                let state_decl = &init_decl.declarations[0];
                let BindingPattern::BindingIdentifier(state_id) = &state_decl.id else {
                    return None;
                };
                let state_symbol = state_id.symbol_id.get()?;
                let initial = eval(state_decl.init.as_ref()?)?;
                initial.render()?;
                if !resolved_refs_within(
                    self.scoping,
                    self.reference_spans,
                    state_symbol,
                    &[it.span],
                ) {
                    return None;
                }
                (
                    state_symbol,
                    initial,
                    Some(format!("{};", fragment(self.source, init_decl.span))),
                )
            }
            None => {
                let &(symbol, initial_number) = self.external_arithmetic_entries.get(&it.span)?;
                (symbol, Value::Number(initial_number), None)
            }
            _ => return None,
        };
        if state_symbol != tested_symbol {
            return None;
        }

        let facts = &self.constants.initialization;
        if !facts.is_private(self.scoping, state_symbol)
            || facts.is_mapped_arguments_exposed(self.scoping, state_symbol)
            || !self.scoping.symbol_redeclarations(state_symbol).is_empty()
            || self
                .scoping
                .get_resolved_reference_ids(state_symbol)
                .iter()
                .any(|&reference| {
                    facts.resolved_symbol(self.scoping, reference) != Some(state_symbol)
                })
        {
            return None;
        }
        // Only direct immediate activations may write the state from a
        // nested function. Deferred writers could change it during opaque
        // code or after a later iteration. A for-let cell additionally may
        // not escape through a deferred reader of an earlier iteration.
        let per_iteration_binding = matches!(it.init.as_ref(), Some(oxc_ast::ast::ForStatementInit::VariableDeclaration(decl)) if decl.kind == VariableDeclarationKind::Let);
        let mut activation = StateUseProbe::new(
            self.scoping,
            state_symbol,
            per_iteration_binding,
            StateUseMode::Deferred,
        );
        activation.visit_for_statement(it);
        if activation.found {
            return None;
        }
        Some(ArithmeticEntry {
            symbol: state_symbol,
            initial,
            init_text,
            per_iteration_binding,
        })
    }

    fn arithmetic_state_setup<'a>(
        &self,
        it: &'a oxc_ast::ast::ForStatement<'a>,
        completion_live: bool,
    ) -> Option<ArithmeticStateSetup<'a>> {
        if it.update.is_some() {
            return None;
        }
        let test = it.test.as_ref()?;
        let (tested_symbol, loop_termination) =
            dispatcher_exit_test(test, self.scoping, &self.constants.initialization)?;
        let ArithmeticEntry {
            symbol: state_symbol,
            initial,
            init_text,
            per_iteration_binding,
        } = self.arithmetic_entry(it, tested_symbol)?;
        let Statement::BlockStatement(body) = &it.body else {
            return None;
        };
        if body.body.is_empty() {
            return None;
        }
        let (switch_stmt, selector_stmts) = body.body.split_last()?;
        let Statement::SwitchStatement(switch) = switch_stmt else {
            return None;
        };
        if !selector_stmts.iter().all(
            |stmt| matches!(stmt, Statement::VariableDeclaration(decl) if matches!(decl.kind, VariableDeclarationKind::Var | VariableDeclarationKind::Let | VariableDeclarationKind::Const)),
        ) || !self.scoping.get_bindings(switch.scope_id.get()?).is_empty() {
            return None;
        }

        let mut hoisted = crate::if_ladder_structure::HoistedVars::default();
        hoisted.visit_statement(&it.body);
        if hoisted.function_declaration {
            return None;
        }
        let hoisted = if hoisted.names.is_empty() {
            String::new()
        } else {
            format!(
                "var {};",
                hoisted.names.into_iter().collect::<Vec<_>>().join(", ")
            )
        };
        Some(ArithmeticStateSetup {
            state_symbol,
            per_iteration_binding,
            state_var: self.scoping.symbol_name(state_symbol).to_owned(),
            completion_live,
            hoisted,
            initial,
            init_text,
            test,
            loop_termination,
            selector_stmts,
            body_scope: body.scope_id.get()?,
            switch,
            register_arrays: self.confined_register_arrays(it),
        })
    }

    fn conditional_state_split(
        &self,
        stmt: &Statement<'_>,
        env: &ArithmeticEnvironment<'_>,
    ) -> Option<(String, Value, Value)> {
        let Statement::ExpressionStatement(expression_stmt) = stmt else {
            return None;
        };
        let Expression::AssignmentExpression(assignment) = &expression_stmt.expression else {
            return None;
        };
        if assignment.operator.as_str() != "="
            || !matches!(assignment_location(env, &assignment.left), Some(ArithmeticLocation::Binding(symbol)) if symbol == env.state)
        {
            return None;
        }
        let Expression::ConditionalExpression(conditional) = &assignment.right else {
            return None;
        };
        // A state assignment keeps its primitive type: switch uses strict
        // equality, so "3" must not be modeled as the Number 3. Retain the
        // complete safely evaluated value for both branches.
        if env.eval(&conditional.test).is_some()
            || env.opaque_state_access(|probe| probe.visit_expression(&conditional.test))
        {
            return None;
        }
        let consequent = eval(&conditional.consequent)?;
        let alternate = eval(&conditional.alternate)?;
        if identical_primitive_value(&consequent, &alternate) {
            return None;
        }
        consequent.render()?;
        alternate.render()?;
        Some((
            fragment(self.source, conditional.test.span()).to_string(),
            consequent,
            alternate,
        ))
    }

    fn simulate_arithmetic_case(
        &self,
        switch: &oxc_ast::ast::SwitchStatement<'_>,
        start: usize,
        env: &mut ArithmeticEnvironment<'_>,
        chunks: &mut Vec<String>,
    ) -> Option<(ArithmeticCaseOutcome, usize)> {
        let mut flow = StateFlow::Normal;
        let mut register_reads_rewritten = 0;
        'cases: for (case_index, case) in switch.cases.iter().enumerate().skip(start) {
            for (statement_index, stmt) in case.consequent.iter().enumerate() {
                match stmt {
                    Statement::BreakStatement(brk) if brk.label.is_none() => {
                        break 'cases;
                    }
                    Statement::ContinueStatement(cont) if cont.label.is_none() => {
                        flow = StateFlow::Continue;
                        break 'cases;
                    }
                    _ => {
                        if let Some((test, consequent, alternate)) =
                            self.conditional_state_split(stmt, env)
                        {
                            let tail = &case.consequent[statement_index + 1..];
                            if tail.iter().all(|tail_stmt| {
                                matches!(tail_stmt, Statement::BreakStatement(brk) if brk.label.is_none())
                            }) && (!tail.is_empty() || case_index + 1 == switch.cases.len()) {
                                return Some((
                                    ArithmeticCaseOutcome::Conditional {
                                        test,
                                        consequent,
                                        alternate,
                                    },
                                    register_reads_rewritten,
                                ));
                            }
                            // A divergent intermediate state need not split
                            // the dispatcher: the remaining statements (or
                            // switch fallthrough) may re-establish one value.
                        }
                        if statement_has_loop_control(stmt) {
                            return None;
                        }
                        let (rendered, rewritten) = self.render_statement_with_env(stmt, env);
                        register_reads_rewritten += rewritten;
                        let stmt_flow = simulate_statement(stmt, env)?;
                        chunks.push(rendered);
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
        Some((ArithmeticCaseOutcome::Flow(flow), register_reads_rewritten))
    }

    /// Model and render selector initializers in source order and count only
    /// register reads whose value was actually proven and substituted.
    fn arithmetic_selector_statements(
        &self,
        setup: &ArithmeticStateSetup<'_>,
        env: &mut ArithmeticEnvironment<'_>,
        chunks: &mut Vec<String>,
    ) -> Option<usize> {
        let mut register_reads_rewritten = 0;
        for selector_stmt in setup.selector_stmts {
            let Statement::VariableDeclaration(_) = selector_stmt else {
                return None;
            };
            let (rendered, rewritten) = self.render_statement_with_env(selector_stmt, env);
            register_reads_rewritten += rewritten;
            if simulate_statement(selector_stmt, env)? != StateFlow::Normal {
                return None;
            }
            chunks.push(rendered);
        }
        Some(register_reads_rewritten)
    }

    fn arithmetic_iteration(
        &self,
        setup: &ArithmeticStateSetup<'_>,
        env: &mut ArithmeticEnvironment<'_>,
        chunks: &mut Vec<String>,
    ) -> Option<(ArithmeticCaseOutcome, usize)> {
        env.retire_scope(setup.body_scope);
        let mut rewritten = self.arithmetic_selector_statements(setup, env, chunks)?;
        if setup.completion_live {
            chunks.push("void 0;".to_owned());
        }
        let SwitchSelection::Case(start) = select_switch_case(setup.switch, env)? else {
            return Some((ArithmeticCaseOutcome::Flow(StateFlow::Normal), rewritten));
        };
        let (outcome, reads) = self.simulate_arithmetic_case(setup.switch, start, env, chunks)?;
        rewritten += reads;
        Some((outcome, rewritten))
    }

    fn finish_arithmetic_branch(
        &self,
        setup: &ArithmeticStateSetup<'_>,
        base_env: &ArithmeticEnvironment<'_>,
        target: Value,
    ) -> Option<ArithmeticBranchResult> {
        let target_text = target.render()?;
        let mut env = base_env.clone();
        // Evaluating an arbitrary runtime branch condition may call user code or
        // mutate any previously known non-state value. The conditional assignment
        // itself overwrites the dispatcher state afterwards, so retain no other
        // abstract facts across that boundary.
        env.invalidate_opaque()?;
        env.set(
            ArithmeticLocation::Binding(setup.state_symbol),
            Some(target),
        );
        let mut chunks = vec![format!("{} = {target_text};", setup.state_var)];
        let mut state_path = Vec::new();
        let mut seen_states = HashSet::new();
        let mut register_reads_rewritten = 0;

        for _ in 0..256 {
            if !env.eval(setup.test)?.truthy() {
                return Some(ArithmeticBranchResult {
                    chunks,
                    state_path,
                    termination: setup.loop_termination.to_string(),
                    register_reads_rewritten,
                });
            }
            let state_key = env.state_value()?.render()?;
            if !seen_states.insert(state_key.clone()) {
                return None;
            }
            state_path.push(state_key);

            let mut iteration = Vec::new();
            let (outcome, rewritten) =
                self.arithmetic_iteration(setup, &mut env, &mut iteration)?;
            chunks.push(render_block(&iteration));
            register_reads_rewritten += rewritten;
            let ArithmeticCaseOutcome::Flow(flow) = outcome else {
                return None;
            };
            if matches!(flow, StateFlow::Return | StateFlow::Throw) {
                return Some(ArithmeticBranchResult {
                    chunks,
                    state_path,
                    termination: if flow == StateFlow::Return {
                        "return"
                    } else {
                        "throw"
                    }
                    .to_string(),
                    register_reads_rewritten,
                });
            }
            if flow == StateFlow::Break {
                return None;
            }

            // All supported primitive states may have matching switch cases
            // on the following iteration. Undefined is not an unconditional
            // exit: only the actual for-loop condition can terminate the loop.
            env.state_value()?.render()?;
        }
        None
    }

    fn arithmetic_environment(
        &self,
        setup: &ArithmeticStateSetup<'_>,
    ) -> ArithmeticEnvironment<'_> {
        ArithmeticEnvironment {
            scoping: self.scoping,
            bindings: &self.constants.initialization,
            state: setup.state_symbol,
            values: HashMap::from([(setup.state_symbol, setup.initial.clone())]),
            arrays: setup.register_arrays.clone(),
            slots: HashMap::new(),
            reflective_activation: false,
            per_iteration_binding: setup.per_iteration_binding,
            immediate_depth: 0,
        }
    }

    pub(super) fn arithmetic_state_replacement(
        &self,
        it: &oxc_ast::ast::ForStatement<'_>,
        completion_live: bool,
    ) -> Option<(String, ArithmeticStateProof)> {
        let setup = self.arithmetic_state_setup(it, completion_live)?;
        let mut env = self.arithmetic_environment(&setup);
        let mut chunks = setup.init_text.iter().cloned().collect::<Vec<_>>();
        if !setup.hoisted.is_empty() {
            chunks.push(setup.hoisted.clone());
        }
        if completion_live {
            chunks.push("void 0;".to_owned());
        }
        let mut seen_states = HashSet::new();
        let mut state_path = Vec::new();
        let mut register_reads_rewritten = 0;

        for _ in 0..256 {
            if !env.eval(setup.test)?.truthy() {
                return Some(arithmetic_state_result(
                    it.span,
                    &setup.state_var,
                    state_path,
                    &chunks,
                    setup.loop_termination,
                    register_reads_rewritten,
                ));
            }
            let state_key = env.state_value()?.render()?;
            if !seen_states.insert(state_key.clone()) {
                return None;
            }
            state_path.push(state_key);

            let mut iteration = Vec::new();
            let (outcome, rewritten) =
                self.arithmetic_iteration(&setup, &mut env, &mut iteration)?;
            register_reads_rewritten += rewritten;
            let flow = match outcome {
                ArithmeticCaseOutcome::Flow(flow) => {
                    chunks.push(render_block(&iteration));
                    flow
                }
                ArithmeticCaseOutcome::Conditional {
                    test,
                    consequent,
                    alternate,
                } => {
                    let consequent_branch =
                        self.finish_arithmetic_branch(&setup, &env, consequent)?;
                    let alternate_branch =
                        self.finish_arithmetic_branch(&setup, &env, alternate)?;
                    register_reads_rewritten += consequent_branch.register_reads_rewritten
                        + alternate_branch.register_reads_rewritten;
                    let conditional = format!(
                        "if ({test}) {} else {}",
                        render_block(&consequent_branch.chunks),
                        render_block(&alternate_branch.chunks)
                    );
                    iteration.push(conditional);
                    chunks.push(render_block(&iteration));
                    let (text, mut proof) = arithmetic_state_result(
                        it.span,
                        &setup.state_var,
                        state_path,
                        &chunks,
                        "conditional",
                        register_reads_rewritten,
                    );
                    proof.branch_test = Some(test);
                    proof.branch_paths =
                        vec![consequent_branch.state_path, alternate_branch.state_path];
                    proof.branch_terminations =
                        vec![consequent_branch.termination, alternate_branch.termination];
                    return Some((text, proof));
                }
            };
            if matches!(flow, StateFlow::Return | StateFlow::Throw) {
                let termination = if flow == StateFlow::Return {
                    "return"
                } else {
                    "throw"
                };
                return Some(arithmetic_state_result(
                    it.span,
                    &setup.state_var,
                    state_path,
                    &chunks,
                    termination,
                    register_reads_rewritten,
                ));
            }
            if flow == StateFlow::Break {
                return None;
            }

            // Repeat only with a precisely modeled, renderable JS state.
            // The next evaluation of setup.test determines whether the loop
            // exits; a typed or undefined value is not itself an exit.
            env.state_value()?.render()?;
        }
        None
    }
}

#[cfg(test)]
mod arithmetic_entry_tests {
    use crate::{deobfuscate, SafeTransformResult};
    use work_budget::WorkBudget;

    // The containing function discards loop Completion; these fixtures isolate
    // entry and switch-control proofs from the separate live-value question.
    const CASES: &[(&str, &str, bool)] = &[
        ("direct", "var s=2;for(;s!==5;){switch(s){case 2:out.push('A');s=4;break;case 4:out.push('B');s=5;break;}}", true),
        ("assignment", "let s;s=-2;for(;s!==5;){switch(s){case -2:out.push('A');s=5;break;}}", true),
        ("conditional", "if(flag)var s=2;for(;s!==5;){switch(s){case 2:out.push('A');s=5;break;default:out.push('U');s=5;break;}}", false),
        ("repeated", "var s=2;for(let i=0;i<2;i++){for(;s!==5;){switch(s){case 2:out.push('A');s=5;break;}}}", false),
        ("reset", "for(let i=0;i<2;i++){var s=2;for(;s!==5;){switch(s){case 2:out.push('A');s=5;break;}}}", true),
        ("nested", "var s=2;out.push('before');{for(;s!==5;){switch(s){case 2:out.push('A');s=5;break;}}}", true),
        ("fallthrough", "var s=2;for(;s!==5;){switch(s){case 2:s=flag?3:4;case 3:out.push('fall');s=5;break;case 4:out.push('wrong');s=5;break;}}", true),
        ("last_case", "var s=2;for(;s!==5;){switch(s){case 3:out.push('A');s=5;break;case 4:out.push('B');s=5;break;case 2:s=flag?3:4;}}", true),
        ("arguments", "var s=2;out.push(arguments[0]);for(;s!==5;){switch(s){case 2:out.push('A');s=5;break;}}", true),
        ("redeclared", "var s=2;var s=flag?3:2;for(;s!==5;){switch(s){case 2:out.push('A');s=5;break;case 3:out.push('B');s=5;break;}}", false),
    ];

    fn recover_case(
        body: &str,
        expected: bool,
    ) -> Result<(String, SafeTransformResult), Box<dyn std::error::Error>> {
        let source =
            format!("function run(flag){{let out=[];{body}return out.join(',');}}run(flag);");
        let recovered = deobfuscate(
            &source,
            12,
            &WorkBudget::unlimited("arithmetic-entry-proof"),
        )?
        .ok_or_else(|| std::io::Error::other("valid source not recovered"))?;
        assert_eq!(
            recovered
                .transforms
                .contains_key("arithmetic_state_unflatten"),
            expected,
            "{source}: {:?}: {}",
            recovered.transforms,
            recovered.source
        );
        Ok((source, recovered))
    }

    #[test]
    fn arithmetic_dispatch_requires_reaching_entry_and_no_unmodeled_fallthrough(
    ) -> Result<(), Box<dyn std::error::Error>> {
        for &(_, body, expected) in CASES {
            recover_case(body, expected)?;
        }
        Ok(())
    }

    #[test]
    #[ignore = "requires Node; compare arithmetic entry and fallthrough semantics"]
    fn node_confirms_arithmetic_entry_and_fallthrough() -> Result<(), Box<dyn std::error::Error>> {
        use std::process::Command;
        let harness = r"
const vm=require('node:vm');
const source=process.argv[1];
for(const flag of [false,true]){
  for(const code of [source,'eval('+JSON.stringify(source)+')']){
    const options={};options.timeout=1500;
    console.log(JSON.stringify(vm.runInNewContext(code,{flag},options)));
  }
}
";
        for &(name, body, expected) in CASES {
            let (source, recovered) = recover_case(body, expected)?;
            let observe = |code: &str| -> Result<Vec<u8>, Box<dyn std::error::Error>> {
                let output = Command::new("node").args(["-e", harness, code]).output()?;
                assert!(output.status.success(), "{name}: {output:?}");
                Ok(output.stdout)
            };
            assert_eq!(
                observe(&source)?,
                observe(&recovered.source)?,
                "{name}: {}",
                recovered.source
            );
        }
        Ok(())
    }
}

#[cfg(test)]
mod live_arithmetic_tests {
    use crate::{deobfuscate, SafeTransformResult};
    use work_budget::WorkBudget;

    // Every successful reconstruction must preserve both arbitrary runtime
    // expression values and the switch's independent undefined accumulator.
    const CASES: &[(&str, bool)] = &[
        ("for(let s=1;s!==9;){switch(s){case 1:s=9;push('abc');break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:s=2;push('abc');continue;case 2:s=9;var x;break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:s=2;push('abc');continue;case 2:var x=(s=9,[]);break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:var x=(s=9,[]);;break;}}", true),
        ("for(let s=9;s!==9;){switch(s){case 1:push('never');s=9;break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:s=flag?2:3;break;case 2:s=9;push('T');break;case 3:var x=(s=9,[]);break;}}", true),
        ("for(let s=1;s!==9;){let low=s&3;switch(low){case 1:s=2;push('first');break;case 2:s=9;(-0);break;}}", true),
        ("for(let s=1;s!==9;){let next=(s=9,0);switch(next){case 1:push('never');break;}}", true),
        ("for(let s='first';s!==null;){switch(s){case 'first':s=true;continue;case true:s=null;({x:1});break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:if(flag){s=9;push('T');}else{s=9;push('F');}break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:s=9;try{if(flag)throw new TypeError('x');push('T');}catch(e){push(e.name);}finally{push('finally');}break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:{let s=2;push(s);}s=9;break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:!function(){let s=2;push(s);}();s=9;break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:var hidden=3;s=2;break;case 2:var hidden;s=hidden+6;break;}}", false),
        // Object-backed script var can invoke an accessor on a state write.
        ("for(var s=1;s!==9;){switch(s){case 1:s=9;break;}}", false),
        // Deferred writes and captured per-iteration cells are not interchangeable.
        ("for(let s=1;s!==9;){switch(s){case 1:push(()=>s);s=9;break;}}", false),
        ("for(let s=1;s!==9;){switch(s){case 1:var change=()=>{s=2};change();break;case 2:s=9;break;}}", false),
        // The first branch can execute an unknown setter rather than define an own slot.
        ("for(let s=1;s!==9;){let regs=[];switch(s){case 1:regs[0]=9;s=regs[0];break;}}", false),
        ("for(let s=1;s!==9;){let regs=[9];switch(s){case 1:s=regs[0];break;}}", true),
        ("var saved;function capture(){saved=capture.caller;}for(let s=1;s!==9;){switch(s){case 1:!function(){capture();push(s);s=2;}();break;case 2:s=9;break;}}saved();", false),
        ("for(let s=1;s!==9;){switch(s){case 1:!function(){'use strict';push(s);s=9;}();break;}}", true),
        ("var saved;function capture(){saved=capture.caller;}for(let s=1;s!==9;){switch(s){case 1:try{!function(){capture();push(s);}();}finally{}s=2;break;case 2:s=9;break;}}saved();", false),
        ("for(let s=1;s!==9;){switch(s){case 1:!function(){try{if(flag)return;}finally{}s=2;}();s=s===1?9:3;break;case 3:s=9;break;}}", false),
        ("for(let s=1;s!==9;){switch(s){case 1:push((s=2)+7);s=9;break;}}", false),
        ("for(let s=1;s!==9;){switch(s){case 1:(s=2)+(s=9);break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:s=(flag?(s=3,9):9);break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:flag&&(s=2);s=9;break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:s=flag?2:3;s=9;break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:s=0;s||=9;break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:s=1;s&&=9;break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:s=null;s??=9;break;}}", true),
        ("for(let s=1;s!==9;){switch(s){case 1:var C=class{x=s};s=9;break;}}new C().x;", false),
        ("for(let s=1;s!==9;){switch(s){case 1:var C=class{static x=s};s=9;break;}}C.x;", true),
        // The switch's lexical environment is shared even across unselected cases.
        ("for(let s=1;s!==9;){switch(s){case 1:s=9;push(x);break;case 2:let x=1;break;}}", false),
    ];

    fn recover(
        source: &str,
        expected: bool,
    ) -> Result<SafeTransformResult, Box<dyn std::error::Error>> {
        let recovered = deobfuscate(source, 16, &WorkBudget::unlimited("live-arithmetic-proof"))?
            .ok_or_else(|| std::io::Error::other("valid source not recovered"))?;
        assert_eq!(
            recovered
                .transforms
                .contains_key("arithmetic_state_unflatten"),
            expected,
            "{source}: {:?}: {}",
            recovered.transforms,
            recovered.source
        );
        Ok(recovered)
    }

    #[test]
    fn arithmetic_dispatchers_preserve_observable_switch_completion(
    ) -> Result<(), Box<dyn std::error::Error>> {
        for &(source, expected) in CASES {
            recover(source, expected)?;
        }
        Ok(())
    }

    #[test]
    #[ignore = "requires Node; compare arbitrary completion values and retained effects"]
    fn node_confirms_live_arithmetic_dispatchers() -> Result<(), Box<dyn std::error::Error>> {
        use std::process::Command;
        let harness = r"
const vm=require('node:vm');
const source=process.argv[1];
for(const flag of [false,true]){
  for(const code of [source,'eval('+JSON.stringify(source)+')']){
    const effects=[];
    const context={flag,push(value){effects.push(typeof value==='function'?'function':value);return String(value).length;}};
    const options={};options.timeout=1500;
    try {
      const value=vm.runInNewContext(code,context,options);
      console.log(JSON.stringify({type:typeof value,value,negativeZero:Object.is(value,-0),effects}));
    }catch(error){
      console.log(JSON.stringify({type:'throw',name:error.name,effects}));
    }
  }
}
";
        for &(source, expected) in CASES {
            let recovered = recover(source, expected)?;
            let observe = |code: &str| -> Result<Vec<u8>, Box<dyn std::error::Error>> {
                let output = Command::new("node").args(["-e", harness, code]).output()?;
                assert!(output.status.success(), "{output:?}");
                Ok(output.stdout)
            };
            assert_eq!(
                observe(source)?,
                observe(&recovered.source)?,
                "{source} -> {}",
                recovered.source
            );
        }
        Ok(())
    }
}
