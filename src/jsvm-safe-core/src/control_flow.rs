//! Proof-oriented control-flow recovery.
//!
//! This module owns the coupled dispatcher/reference-state proof engines:
//! ordered switch dispatch, deterministic reference-identity tables, symbolic
//! state simulation, and reference/arithmetic state unflattening. The central
//! collector remains in `lib.rs`; these methods operate on it so replacement
//! scheduling and source-protection policy stay centralized.

use crate::numeric::exact_u32;
use crate::value_eval::{
    eval, eval_binary, js_to_int32, js_to_uint32, known_bool, same_value, string_literal_value,
    template_element_value, Value,
};
use crate::{
    array_element, direct_identifier_name, fragment, js_parse_int, symbol_of, ArithmeticStateProof,
    Collector,
};
use oxc_ast::ast::{BindingPattern, Expression, Statement, VariableDeclarationKind};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::{GetSpan, Span};
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::{HashMap, HashSet};

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
            let separator = separator.value.as_str()?;
            if separator.len() != 1 || !separator.is_ascii() {
                return None;
            }
            let order = source
                .value
                .as_str()?
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

pub fn collect_dispatch_bindings(
    program: &oxc_ast::ast::Program<'_>,
) -> (HashMap<SymbolId, Vec<String>>, HashSet<SymbolId>) {
    let mut collector = DispatchBindingCollector::default();
    collector.visit_program(program);
    (collector.orders, collector.zero_counters)
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
        || scoping
            .get_resolved_reference_ids(target_symbol)
            .iter()
            .any(|reference_id| {
                let reference = scoping.get_reference(*reference_id);
                reference.is_write() || reference.flags().is_member_write_target()
            })
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
    shape: ReferenceIdentityShape,
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
            .filter_map(|shape| prove_reference_identity_shape(shape, scoping, reference_spans))
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

fn single_resolved_reference(scoping: &Scoping, symbol: SymbolId, expected: ReferenceId) -> bool {
    let refs = scoping.get_resolved_reference_ids(symbol);
    refs.len() == 1 && refs[0] == expected
}

struct OrderedSwitchReplacement {
    text: String,
    order_symbol: SymbolId,
    counter_symbol: SymbolId,
}

impl Collector<'_, '_> {
    fn ordered_switch_body_replacement(
        &self,
        body: &Statement<'_>,
    ) -> Option<OrderedSwitchReplacement> {
        let Statement::BlockStatement(body) = body else {
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

        Some(OrderedSwitchReplacement {
            text: format!("{{\n{}\n}}", chunks.join("\n")),
            order_symbol,
            counter_symbol,
        })
    }

    pub(super) fn ordered_switch_while_replacement(
        &self,
        it: &oxc_ast::ast::WhileStatement<'_>,
    ) -> Option<String> {
        if known_bool(&it.test) != Some(true) {
            return None;
        }
        Some(self.ordered_switch_body_replacement(&it.body)?.text)
    }

    pub(super) fn ordered_switch_for_replacement(
        &self,
        it: &oxc_ast::ast::ForStatement<'_>,
    ) -> Option<String> {
        if it.update.is_some()
            || it
                .test
                .as_ref()
                .is_some_and(|test| known_bool(test) != Some(true))
        {
            return None;
        }

        let replacement = self.ordered_switch_body_replacement(&it.body)?;
        let Some(init) = &it.init else {
            return Some(replacement.text);
        };
        let oxc_ast::ast::ForStatementInit::VariableDeclaration(declaration) = init else {
            return None;
        };
        // The dispatch counter is incremented by the selector. A `const`
        // declaration would throw at runtime, so replacing that loop would
        // incorrectly turn invalid source into valid straight-line code.
        if declaration.kind == VariableDeclarationKind::Const || declaration.declarations.len() != 2
        {
            return None;
        }

        let mut saw_order = false;
        let mut saw_counter = false;
        for declarator in &declaration.declarations {
            let BindingPattern::BindingIdentifier(id) = &declarator.id else {
                return None;
            };
            let symbol = id.symbol_id.get()?;
            let init = declarator.init.as_ref()?;
            if symbol == replacement.order_symbol {
                if static_dispatch_order(init) != self.dispatch_orders.get(&symbol).cloned() {
                    return None;
                }
                saw_order = true;
            } else if symbol == replacement.counter_symbol {
                if !matches!(eval(init), Some(Value::Number(n)) if n == 0.0) {
                    return None;
                }
                saw_counter = true;
            } else {
                return None;
            }
        }
        (saw_order && saw_counter).then_some(replacement.text)
    }
}

const REGISTER_MARKER_PREFIX: &str = "\0register:";
const REGISTER_SLOT_PREFIX: &str = "\0slot:";

fn register_marker(name: &str) -> String {
    format!("{REGISTER_MARKER_PREFIX}{name}")
}

fn register_slot(name: &str, index: u32) -> String {
    format!("{REGISTER_SLOT_PREFIX}{name}:{index}")
}

fn register_active(env: &HashMap<String, Value>, name: &str) -> bool {
    env.contains_key(&register_marker(name))
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
        Expression::StringLiteral(v) => string_literal_value(v).map(Value::String),
        Expression::NumericLiteral(v) => Some(Value::Number(v.value)),
        Expression::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        Expression::NullLiteral(_) => Some(Value::Null),
        Expression::TemplateLiteral(v) if v.expressions.is_empty() => v
            .quasis
            .first()
            .and_then(template_element_value)
            .map(Value::String),
        Expression::ParenthesizedExpression(v) => eval_with_env(&v.expression, env),
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::Identifier(object) = &member.object else {
                return None;
            };
            if !register_active(env, object.name.as_str()) {
                return None;
            }
            let index = eval_with_env(&member.expression, env)
                .and_then(|value| value.number())
                .and_then(exact_u32)?;
            env.get(&register_slot(object.name.as_str(), index))
                .cloned()
        }
        Expression::UnaryExpression(v) => {
            let op = v.operator.as_str();
            if op == "!" {
                return eval_with_env(&v.argument, env).map(|value| Value::Bool(!value.truthy()));
            }
            if op == "void" {
                eval_with_env(&v.argument, env)?;
                return Some(Value::Undefined);
            }
            let value = eval_with_env(&v.argument, env)?;
            match op {
                "+" => value.number().map(Value::Number),
                "-" => value.number().map(|number| Value::Number(-number)),
                "~" => value
                    .number()
                    .map(|number| Value::Number(f64::from(!js_to_int32(number)))),
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
                "&&" if left.truthy() => eval_with_env(&v.right, env),
                "&&" => Some(left),
                "||" if left.truthy() => Some(left),
                "||" => eval_with_env(&v.right, env),
                "??" if matches!(left, Value::Null | Value::Undefined) => {
                    eval_with_env(&v.right, env)
                }
                "??" => Some(left),
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

#[derive(Debug)]
enum ArithmeticCaseOutcome {
    Flow(StateFlow),
    Conditional {
        test: String,
        consequent: f64,
        alternate: f64,
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

fn computed_register_slot(
    member: &oxc_ast::ast::ComputedMemberExpression<'_>,
    env: &HashMap<String, Value>,
) -> Option<(String, u32)> {
    if member.optional {
        return None;
    }
    let Expression::Identifier(object) = &member.object else {
        return None;
    };
    if !register_active(env, object.name.as_str()) {
        return None;
    }
    let index = eval_with_env(&member.expression, env)
        .and_then(|value| value.number())
        .and_then(exact_u32)?;
    Some((object.name.to_string(), index))
}

fn direct_assignment_slot(
    target: &oxc_ast::ast::AssignmentTarget<'_>,
    env: &HashMap<String, Value>,
) -> Option<(String, u32)> {
    let oxc_ast::ast::AssignmentTarget::ComputedMemberExpression(member) = target else {
        return None;
    };
    computed_register_slot(member, env)
}

fn direct_update_slot(
    target: &oxc_ast::ast::SimpleAssignmentTarget<'_>,
    env: &HashMap<String, Value>,
) -> Option<(String, u32)> {
    let oxc_ast::ast::SimpleAssignmentTarget::ComputedMemberExpression(member) = target else {
        return None;
    };
    computed_register_slot(member, env)
}

fn clear_register_slots(env: &mut HashMap<String, Value>, name: &str) {
    let prefix = format!("{REGISTER_SLOT_PREFIX}{name}:");
    env.retain(|key, _| !key.starts_with(&prefix));
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
    let retained = env
        .iter()
        .filter(|(key, _)| {
            key.as_str() == state_var
                || key.starts_with(REGISTER_MARKER_PREFIX)
                || key.starts_with(REGISTER_SLOT_PREFIX)
        })
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect::<Vec<_>>();
    env.clear();
    env.extend(retained);
}

fn invalidate_opaque_state(env: &mut HashMap<String, Value>, state_var: &str) {
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
                    if !fun.r#async && fun.params.items.is_empty() =>
                {
                    let oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) = &fun.body else {
                        return None;
                    };
                    body.directives.is_empty().then_some(&**body)
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
    register_arrays: &HashSet<String>,
) -> Option<StateFlow> {
    match expr {
        Expression::ParenthesizedExpression(p) => {
            simulate_expression(&p.expression, state_var, env, register_arrays)
        }
        Expression::SequenceExpression(seq) => {
            for item in &seq.expressions {
                let flow = simulate_expression(item, state_var, env, register_arrays)?;
                if flow != StateFlow::Normal {
                    return Some(flow);
                }
            }
            Some(StateFlow::Normal)
        }
        Expression::AssignmentExpression(assign) => {
            if let Some((name, index)) = direct_assignment_slot(&assign.left, env) {
                let slot = register_slot(&name, index);
                apply_known_assignment(assign.operator.as_str(), &slot, &assign.right, env);
                return Some(StateFlow::Normal);
            }
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
            if let Some((name, index)) = direct_update_slot(&update.argument, env) {
                let slot = register_slot(&name, index);
                let Some(Value::Number(current)) = env.get(&slot).cloned() else {
                    env.remove(&slot);
                    return Some(StateFlow::Normal);
                };
                let next = match update.operator.as_str() {
                    "++" => current + 1.0,
                    "--" => current - 1.0,
                    _ => return None,
                };
                env.insert(slot, Value::Number(next));
                return Some(StateFlow::Normal);
            }
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
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "delete" => {
            if let Expression::ComputedMemberExpression(member) = &unary.argument {
                if let Some((name, index)) = computed_register_slot(member, env) {
                    env.remove(&register_slot(&name, index));
                    return Some(StateFlow::Normal);
                }
            }
            if expression_mentions(expr, state_var) {
                return None;
            }
            invalidate_non_state(env, state_var);
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
                let flow =
                    simulate_statements(&body.statements, state_var, &mut nested, register_arrays)?;

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
    register_arrays: &HashSet<String>,
) -> Option<StateFlow> {
    let start = select_switch_case(switch, env)?;
    for case in switch.cases.iter().skip(start) {
        for stmt in &case.consequent {
            match simulate_statement(stmt, state_var, env, register_arrays)? {
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
    register_arrays: &HashSet<String>,
) -> Option<StateFlow> {
    match stmt {
        Statement::BlockStatement(block) => {
            simulate_statements(&block.body, state_var, env, register_arrays)
        }
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
                    if register_arrays.contains(id.name.as_str())
                        && matches!(init, Expression::ArrayExpression(_))
                    {
                        clear_register_slots(env, id.name.as_str());
                        env.insert(register_marker(id.name.as_str()), Value::Bool(true));
                    }
                } else {
                    env.insert(id.name.to_string(), Value::Undefined);
                }
            }
            Some(StateFlow::Normal)
        }
        Statement::ExpressionStatement(es) => {
            simulate_expression(&es.expression, state_var, env, register_arrays)
        }
        Statement::IfStatement(branch) => {
            let test = eval_with_env(&branch.test, env)?.truthy();
            if test {
                simulate_statement(&branch.consequent, state_var, env, register_arrays)
            } else if let Some(alt) = &branch.alternate {
                simulate_statement(alt, state_var, env, register_arrays)
            } else {
                Some(StateFlow::Normal)
            }
        }
        Statement::SwitchStatement(switch) => {
            simulate_switch(switch, state_var, env, register_arrays)
        }
        Statement::TryStatement(_) => {
            if statement_mentions(stmt, state_var) || statement_has_loop_control(stmt) {
                return None;
            }
            // Preserve opaque exception behavior verbatim. The try/catch may mutate
            // arbitrary non-state locals or register slots, so only the proven
            // dispatcher state survives abstract interpretation across it.
            invalidate_opaque_state(env, state_var);
            Some(StateFlow::Normal)
        }
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
    register_arrays: &HashSet<String>,
) -> Option<StateFlow> {
    for stmt in statements {
        let flow = simulate_statement(stmt, state_var, env, register_arrays)?;
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

#[derive(Default)]
struct RegisterArrayShapeCollector {
    candidates: Vec<(SymbolId, String)>,
    numeric_member_refs: HashSet<ReferenceId>,
    function_depth: usize,
}

impl RegisterArrayShapeCollector {
    fn record_numeric_member(&mut self, it: &oxc_ast::ast::ComputedMemberExpression<'_>) {
        if it.optional
            || eval(&it.expression)
                .and_then(|value| value.number())
                .and_then(exact_u32)
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
        if self.function_depth == 0 && it.kind == VariableDeclarationKind::Var {
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
                self.candidates.push((symbol, id.name.to_string()));
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
    scoping: &'c Scoping,
    env: &'e HashMap<String, Value>,
    replacements: Vec<(Span, String)>,
}

impl<'a> Visit<'a> for KnownRegisterReadCollector<'_, '_> {
    fn visit_computed_member_expression(
        &mut self,
        it: &oxc_ast::ast::ComputedMemberExpression<'a>,
    ) {
        if !it.optional {
            if let Expression::Identifier(object) = &it.object {
                if let Some(reference_id) = object.reference_id.get() {
                    let reference = self.scoping.get_reference(reference_id);
                    if reference.is_read()
                        && !reference.is_write()
                        && !reference.flags().is_member_write_target()
                        && register_active(self.env, object.name.as_str())
                    {
                        if let Some(index) = eval_with_env(&it.expression, self.env)
                            .and_then(|value| value.number())
                            .and_then(exact_u32)
                        {
                            if let Some(text) = self
                                .env
                                .get(&register_slot(object.name.as_str(), index))
                                .and_then(Value::render)
                            {
                                self.replacements.push((it.span, text));
                                return;
                            }
                        }
                    }
                }
            }
        }
        walk::walk_computed_member_expression(self, it);
    }

    fn visit_function(&mut self, _it: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(&mut self, _it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
    }
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

struct ArithmeticStateSetup<'a> {
    state_var: String,
    initial_number: f64,
    init_text: Option<String>,
    test: &'a Expression<'a>,
    loop_termination: &'static str,
    selector_stmts: &'a [Statement<'a>],
    switch: &'a oxc_ast::ast::SwitchStatement<'a>,
    register_arrays: HashSet<String>,
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
                "Number" if call.arguments.len() == 1 => self
                    .reference_state_eval(call.arguments[0].as_expression()?, env)?
                    .number()
                    .map(Value::Number),
                "parseInt" if matches!(call.arguments.len(), 1 | 2) => {
                    let value =
                        self.reference_state_eval(call.arguments[0].as_expression()?, env)?;
                    let radix = if call.arguments.len() == 2 {
                        self.reference_state_eval(call.arguments[1].as_expression()?, env)?
                            .number()
                            .and_then(exact_u32)?
                    } else {
                        10
                    };
                    js_parse_int(&value.js_string()?, radix).map(Value::Number)
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
            .number()?;
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
            Expression::UnaryExpression(unary) => {
                if unary.operator.as_str() == "!" {
                    return self
                        .reference_state_eval(&unary.argument, env)
                        .map(|value| Value::Bool(!value.truthy()));
                }
                if unary.operator.as_str() == "void" {
                    self.reference_state_eval(&unary.argument, env)?;
                    return Some(Value::Undefined);
                }
                let value = self.reference_state_eval(&unary.argument, env)?;
                match unary.operator.as_str() {
                    "+" => value.number().map(Value::Number),
                    "-" => value.number().map(|number| Value::Number(-number)),
                    "~" => value
                        .number()
                        .map(|number| Value::Number(f64::from(!js_to_int32(number)))),
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
            Expression::BinaryExpression(value) => eval_binary(
                value.operator.as_str(),
                self.reference_state_eval(&value.left, env)?,
                self.reference_state_eval(&value.right, env)?,
            ),
            Expression::LogicalExpression(value) => {
                let left = self.reference_state_eval(&value.left, env)?;
                match value.operator.as_str() {
                    "&&" if left.truthy() => self.reference_state_eval(&value.right, env),
                    "&&" => Some(left),
                    "||" if left.truthy() => Some(left),
                    "||" => self.reference_state_eval(&value.right, env),
                    "??" if matches!(left, Value::Null | Value::Undefined) => {
                        self.reference_state_eval(&value.right, env)
                    }
                    "??" => Some(left),
                    _ => None,
                }
            }
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
        if !resolved_refs_within(self.scoping, self.reference_spans, state_symbol, it.span) {
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

    fn external_arithmetic_state(
        &self,
        test: &Expression<'_>,
        loop_span: Span,
    ) -> Option<(String, f64)> {
        let Expression::BinaryExpression(binary) = test else {
            return None;
        };
        if !matches!(binary.operator.as_str(), "!=" | "!==") {
            return None;
        }

        let (state_expr, terminal_expr) = match (
            direct_identifier_name(&binary.left),
            direct_identifier_name(&binary.right),
        ) {
            (Some(_), None) => (&binary.left, &binary.right),
            (None, Some(_)) => (&binary.right, &binary.left),
            _ => return None,
        };
        let state_var = direct_identifier_name(state_expr)?.to_string();
        let state_symbol = symbol_of(self.scoping, state_expr)?;
        let initializer = self.var_number_initializers.get(&state_symbol)?;
        if initializer.available_after > loop_span.start
            || !matches!(
                eval(terminal_expr),
                Some(Value::Number(number)) if number.is_finite() && number.fract() == 0.0
            )
            || !resolved_refs_within(self.scoping, self.reference_spans, state_symbol, loop_span)
        {
            return None;
        }
        Some((state_var, initializer.value))
    }

    fn confined_register_arrays(&self, it: &oxc_ast::ast::ForStatement<'_>) -> HashSet<String> {
        let mut collector = RegisterArrayShapeCollector::default();
        collector.visit_for_statement(it);
        collector
            .candidates
            .into_iter()
            .filter_map(|(symbol, name)| {
                let binding_scope = self.scoping.symbol_scope_id(symbol);
                let references = self.scoping.get_resolved_reference_ids(symbol);
                (!references.is_empty()
                    && references.iter().all(|reference_id| {
                        collector.numeric_member_refs.contains(reference_id)
                            && self.reference_spans.get(reference_id).is_some_and(|span| {
                                it.span.start <= span.start && span.end <= it.span.end
                            })
                            && {
                                let reference = self.scoping.get_reference(*reference_id);
                                Self::same_function_or_descendant_block_scope(
                                    self.scoping,
                                    reference.scope_id(),
                                    binding_scope,
                                ) || (reference.is_read()
                                    && !reference.is_write()
                                    && !reference.flags().is_member_write_target())
                            }
                    }))
                .then_some(name)
            })
            .collect()
    }

    fn render_statement_with_env(
        &self,
        stmt: &Statement<'_>,
        env: &HashMap<String, Value>,
    ) -> (String, usize) {
        let span = stmt.span();
        let mut text = fragment(self.source, span).to_string();
        let mut collector = KnownRegisterReadCollector {
            scoping: self.scoping,
            env,
            replacements: Vec::new(),
        };
        collector.visit_statement(stmt);
        collector
            .replacements
            .sort_by_key(|(replacement_span, _)| std::cmp::Reverse(replacement_span.start));
        let mut rewritten = 0;
        for (replacement_span, replacement) in collector.replacements {
            if replacement_span.start < span.start || replacement_span.end > span.end {
                continue;
            }
            let start = (replacement_span.start - span.start) as usize;
            let end = (replacement_span.end - span.start) as usize;
            if text.is_char_boundary(start) && text.is_char_boundary(end) {
                text.replace_range(start..end, &replacement);
                rewritten += 1;
            }
        }
        (text, rewritten)
    }

    fn arithmetic_state_setup<'a>(
        &self,
        it: &'a oxc_ast::ast::ForStatement<'a>,
    ) -> Option<ArithmeticStateSetup<'a>> {
        if it.update.is_some() {
            return None;
        }
        let test = it.test.as_ref()?;
        let (state_var, initial_number, init_text, loop_termination) = match it.init.as_ref() {
            Some(oxc_ast::ast::ForStatementInit::VariableDeclaration(init_decl)) => {
                if init_decl.kind != VariableDeclarationKind::Var
                    || init_decl.declarations.len() != 1
                {
                    return None;
                }
                let state_decl = &init_decl.declarations[0];
                let BindingPattern::BindingIdentifier(state_id) = &state_decl.id else {
                    return None;
                };
                let state_symbol = state_id.symbol_id.get()?;
                let state_var = state_id.name.to_string();
                let Value::Number(initial_number) = eval(state_decl.init.as_ref()?)? else {
                    return None;
                };
                if !initial_number.is_finite()
                    || initial_number.fract() != 0.0
                    || !state_undefined_test(test, &state_var)
                    || !resolved_refs_within(
                        self.scoping,
                        self.reference_spans,
                        state_symbol,
                        it.span,
                    )
                {
                    return None;
                }
                (
                    state_var,
                    initial_number,
                    Some(format!("{};", fragment(self.source, init_decl.span))),
                    "undefined",
                )
            }
            None => {
                let (state_var, initial_number) = self.external_arithmetic_state(test, it.span)?;
                (state_var, initial_number, None, "loop_test")
            }
            _ => return None,
        };

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
            |stmt| matches!(stmt, Statement::VariableDeclaration(decl) if decl.kind == VariableDeclarationKind::Var),
        ) {
            return None;
        }

        Some(ArithmeticStateSetup {
            state_var,
            initial_number,
            init_text,
            test,
            loop_termination,
            selector_stmts,
            switch,
            register_arrays: self.confined_register_arrays(it),
        })
    }

    fn conditional_state_split(
        &self,
        stmt: &Statement<'_>,
        state_var: &str,
    ) -> Option<(String, f64, f64)> {
        let Statement::ExpressionStatement(expression_stmt) = stmt else {
            return None;
        };
        let Expression::AssignmentExpression(assignment) = &expression_stmt.expression else {
            return None;
        };
        if assignment.operator.as_str() != "="
            || direct_assignment_name(&assignment.left) != Some(state_var)
        {
            return None;
        }
        let Expression::ConditionalExpression(conditional) = &assignment.right else {
            return None;
        };
        let consequent = eval(&conditional.consequent)?.number()?;
        let alternate = eval(&conditional.alternate)?.number()?;
        if !consequent.is_finite()
            || consequent.fract() != 0.0
            || !alternate.is_finite()
            || alternate.fract() != 0.0
        {
            return None;
        }
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
        state_var: &str,
        env: &mut HashMap<String, Value>,
        chunks: &mut Vec<String>,
        register_arrays: &HashSet<String>,
    ) -> Option<(ArithmeticCaseOutcome, usize)> {
        let mut flow = StateFlow::Normal;
        let mut register_reads_rewritten = 0;
        'cases: for case in switch.cases.iter().skip(start) {
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
                            self.conditional_state_split(stmt, state_var)
                        {
                            let tail = &case.consequent[statement_index + 1..];
                            if !tail.iter().all(|tail_stmt| {
                                matches!(tail_stmt, Statement::BreakStatement(brk) if brk.label.is_none())
                            }) {
                                return None;
                            }
                            return Some((
                                ArithmeticCaseOutcome::Conditional {
                                    test,
                                    consequent,
                                    alternate,
                                },
                                register_reads_rewritten,
                            ));
                        }
                        let (rendered, rewritten) = if matches!(stmt, Statement::TryStatement(_)) {
                            (fragment(self.source, stmt.span()).to_string(), 0)
                        } else {
                            self.render_statement_with_env(stmt, env)
                        };
                        register_reads_rewritten += rewritten;
                        let stmt_flow = simulate_statement(stmt, state_var, env, register_arrays)?;
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

    fn finish_arithmetic_branch(
        &self,
        setup: &ArithmeticStateSetup<'_>,
        base_env: &HashMap<String, Value>,
        target: f64,
    ) -> Option<ArithmeticBranchResult> {
        let target_text = Value::Number(target).render()?;
        let mut env = base_env.clone();
        // Evaluating an arbitrary runtime branch condition may call user code or
        // mutate any previously known non-state value. The conditional assignment
        // itself overwrites the dispatcher state afterwards, so retain no other
        // abstract facts across that boundary.
        invalidate_opaque_state(&mut env, &setup.state_var);
        env.insert(setup.state_var.clone(), Value::Number(target));
        let mut chunks = vec![format!("{} = {target_text};", setup.state_var)];
        let mut state_path = Vec::new();
        let mut seen_states = HashSet::new();
        let mut register_reads_rewritten = 0;

        for _ in 0..256 {
            if !eval_with_env(setup.test, &env)?.truthy() {
                return Some(ArithmeticBranchResult {
                    chunks,
                    state_path,
                    termination: setup.loop_termination.to_string(),
                    register_reads_rewritten,
                });
            }
            let state_key = env.get(&setup.state_var)?.render()?;
            if !seen_states.insert(state_key.clone()) {
                return None;
            }
            state_path.push(state_key);

            for selector_stmt in setup.selector_stmts {
                let Statement::VariableDeclaration(_) = selector_stmt else {
                    return None;
                };
                let (rendered, rewritten) = self.render_statement_with_env(selector_stmt, &env);
                register_reads_rewritten += rewritten;
                simulate_statement(
                    selector_stmt,
                    &setup.state_var,
                    &mut env,
                    &setup.register_arrays,
                )?;
                chunks.push(rendered);
            }

            let start = select_switch_case(setup.switch, &env)?;
            let (outcome, rewritten) = self.simulate_arithmetic_case(
                setup.switch,
                start,
                &setup.state_var,
                &mut env,
                &mut chunks,
                &setup.register_arrays,
            )?;
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

            match env.get(&setup.state_var) {
                Some(Value::Undefined) => {
                    return Some(ArithmeticBranchResult {
                        chunks,
                        state_path,
                        termination: "undefined".to_string(),
                        register_reads_rewritten,
                    });
                }
                Some(Value::Number(number)) if number.is_finite() && number.fract() == 0.0 => {}
                _ => return None,
            }
        }
        None
    }

    pub(super) fn arithmetic_state_replacement(
        &self,
        it: &oxc_ast::ast::ForStatement<'_>,
    ) -> Option<(String, ArithmeticStateProof)> {
        let setup = self.arithmetic_state_setup(it)?;
        let mut env = HashMap::new();
        env.insert(setup.state_var.clone(), Value::Number(setup.initial_number));
        let mut chunks = setup.init_text.iter().cloned().collect::<Vec<_>>();
        let mut seen_states = HashSet::new();
        let mut state_path = Vec::new();
        let mut register_reads_rewritten = 0;

        for _ in 0..256 {
            if !eval_with_env(setup.test, &env)?.truthy() {
                return Some(arithmetic_state_result(
                    it.span,
                    &setup.state_var,
                    state_path,
                    &chunks,
                    setup.loop_termination,
                    register_reads_rewritten,
                ));
            }
            let state_key = env.get(&setup.state_var)?.render()?;
            if !seen_states.insert(state_key.clone()) {
                return None;
            }
            state_path.push(state_key);

            for selector_stmt in setup.selector_stmts {
                let Statement::VariableDeclaration(_decl) = selector_stmt else {
                    return None;
                };
                let (rendered, rewritten) = self.render_statement_with_env(selector_stmt, &env);
                register_reads_rewritten += rewritten;
                simulate_statement(
                    selector_stmt,
                    &setup.state_var,
                    &mut env,
                    &setup.register_arrays,
                )?;
                chunks.push(rendered);
            }

            let start = select_switch_case(setup.switch, &env)?;
            let (outcome, rewritten) = self.simulate_arithmetic_case(
                setup.switch,
                start,
                &setup.state_var,
                &mut env,
                &mut chunks,
                &setup.register_arrays,
            )?;
            register_reads_rewritten += rewritten;
            let flow = match outcome {
                ArithmeticCaseOutcome::Flow(flow) => flow,
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
                    chunks.push(conditional);
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

            match env.get(&setup.state_var) {
                Some(Value::Undefined) => {
                    return Some(arithmetic_state_result(
                        it.span,
                        &setup.state_var,
                        state_path,
                        &chunks,
                        "undefined",
                        register_reads_rewritten,
                    ));
                }
                Some(Value::Number(number)) if number.is_finite() && number.fract() == 0.0 => {}
                _ => return None,
            }
        }
        None
    }
}
