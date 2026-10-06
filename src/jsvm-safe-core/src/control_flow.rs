//! Proof-oriented control-flow recovery.
//!
//! This module owns the coupled dispatcher/reference-state proof engines:
//! ordered switch dispatch, deterministic reference-identity tables, symbolic
//! state simulation, and reference/arithmetic state unflattening. The central
//! collector remains in `lib.rs`; these methods operate on it so replacement
//! scheduling and source-protection policy stay centralized.

use crate::value_eval::{
    eval, eval_binary, eval_with_resolver, js_to_uint32, known_bool, same_value, Value,
};
use crate::{
    array_element, direct_identifier_name, fragment, symbol_of, ArithmeticStateProof, Collector,
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

#[derive(Debug, Clone)]
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

pub fn detect_reference_identity_tables(
    source: &str,
    scoping: &Scoping,
    reference_spans: &HashMap<ReferenceId, Span>,
) -> HashMap<SymbolId, ReferenceIdentityTable> {
    let identifier = r"[A-Za-z_$][A-Za-z0-9_$]*";
    let ws = r"\s*";
    let Some(row_re) = regex::Regex::new(&format!(
        r"(?P<table>{identifier}){ws}={ws}\[\]{ws},{ws}(?P<idx>{identifier}){ws}={ws}0{ws};{ws}(?P<test>{identifier}){ws}<{ws}(?P<rows>\d+){ws};{ws}(?P<update>{identifier}){ws}\+\+{ws}\){ws}(?P<table2>{identifier}){ws}\[{ws}(?P<idx2>{identifier}){ws}\]{ws}={ws}new{ws}Array{ws}\({ws}(?P<columns>\d+){ws}\)"
    )).ok() else {
        return HashMap::new();
    };
    let Some(timer_re) = regex::Regex::new(&format!(
        r"(?P<timer>{identifier}){ws}={ws}function{ws}\({ws}(?P<arg>{identifier}){ws}\){ws}\{{{ws}setTimeout{ws}\({ws}(?P<arg2>{identifier}){ws},{ws}0{ws}\){ws};?{ws}\}}"
    )).ok() else {
        return HashMap::new();
    };
    let Some(outer_re) = regex::Regex::new(&format!(
        r"for{ws}\({ws}var\s+(?P<loop>{identifier}){ws}={ws}0{ws};{ws}(?P<test>{identifier}){ws}<{ws}(?P<chunks>\d+){ws};{ws}(?P<update>{identifier}){ws}\+\+{ws}\){ws}\({ws}\(?{ws}(?P<callback>{identifier}){ws}\)?{ws}=>{ws}\{{{ws}(?P<timer>{identifier}){ws}\({ws}function{ws}\({ws}\){ws}\{{"
    )).ok() else {
        return HashMap::new();
    };
    let Some(fill_re) = regex::Regex::new(&format!(
        r"for{ws}\({ws}var\s+(?P<t>{identifier}){ws}={ws}(?P<chunk>\d+){ws}\*{ws}(?P<callback>{identifier}){ws},{ws}(?P<n>{identifier}){ws}={ws}Math{ws}\.{ws}min{ws}\({ws}(?P<t2>{identifier}){ws}\+{ws}(?P<chunk2>\d+){ws},{ws}(?P<columns>\d+){ws}\){ws},{ws}(?P<column>{identifier}){ws}={ws}(?P<t3>{identifier}){ws};{ws}(?P<column2>{identifier}){ws}<{ws}(?P<n2>{identifier}){ws};{ws}(?P<column3>{identifier}){ws}\+\+{ws}\){ws}for{ws}\({ws}(?P<row>{identifier}){ws}={ws}0{ws};{ws}(?P<row2>{identifier}){ws}<{ws}(?P<rows>\d+){ws};{ws}(?P<row3>{identifier}){ws}\+\+{ws}\){ws}(?P<table>{identifier}){ws}\[{ws}(?P<row4>{identifier}){ws}\]{ws}\[{ws}(?P<column4>{identifier}){ws}\]{ws}={ws}(?P<table2>{identifier}){ws}\[{ws}\({ws}(?P<a>\d+){ws}\*{ws}(?P<column5>{identifier}){ws}\^{ws}(?P<b>\d+){ws}\*{ws}(?P<row5>{identifier}){ws}\^{ws}(?P<c>\d+){ws}\*{ws}(?P<k>\d+){ws}\){ws}>>>{ws}0{ws}&{ws}(?P<mask>\d+){ws}-{ws}1{ws}\]"
    )).ok() else {
        return HashMap::new();
    };
    let Some(root_re) = regex::Regex::new(&format!(
        r"(?P<timer>{identifier}){ws}\({ws}function{ws}\({ws}\){ws}\{{{ws}(?P<target>{identifier}){ws}={ws}(?P<table>{identifier}){ws}\[{ws}(?P<root>\d+){ws}\]{ws};?{ws}\}}{ws}\)"
    )).ok() else {
        return HashMap::new();
    };

    macro_rules! capture {
        ($captures:expr, $name:literal) => {
            match $captures.name($name) {
                Some(capture) => capture.as_str(),
                None => continue,
            }
        };
    }
    macro_rules! capture_match {
        ($captures:expr, $index:expr) => {
            match $captures.get($index) {
                Some(capture) => capture,
                None => continue,
            }
        };
    }

    let mut out = HashMap::new();
    for row_caps in row_re.captures_iter(source) {
        let row_match = capture_match!(row_caps, 0);
        let table_name = capture!(row_caps, "table");
        let row_index = capture!(row_caps, "idx");
        if capture!(row_caps, "test") != row_index
            || capture!(row_caps, "update") != row_index
            || capture!(row_caps, "idx2") != row_index
            || capture!(row_caps, "table2") != table_name
        {
            continue;
        }
        let Ok(rows) = capture!(row_caps, "rows").parse::<u32>() else {
            continue;
        };
        let Ok(columns) = capture!(row_caps, "columns").parse::<u32>() else {
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
        if capture!(timer_caps, "arg") != capture!(timer_caps, "arg2") {
            continue;
        }
        let timer_name = capture!(timer_caps, "timer");

        let Some(outer_caps) = outer_re.captures(window) else {
            continue;
        };
        let outer_loop = capture!(outer_caps, "loop");
        if capture!(outer_caps, "test") != outer_loop
            || capture!(outer_caps, "update") != outer_loop
            || capture!(outer_caps, "timer") != timer_name
        {
            continue;
        }
        let callback_name = capture!(outer_caps, "callback");
        let Ok(chunks) = capture!(outer_caps, "chunks").parse::<u32>() else {
            continue;
        };

        let Some(fill_caps) = fill_re.captures(window) else {
            continue;
        };
        if capture!(fill_caps, "callback") != callback_name
            || capture!(fill_caps, "table") != table_name
            || capture!(fill_caps, "table2") != table_name
        {
            continue;
        }
        let t_name = capture!(fill_caps, "t");
        let n_name = capture!(fill_caps, "n");
        let column_name = capture!(fill_caps, "column");
        let row_name = capture!(fill_caps, "row");
        if capture!(fill_caps, "t2") != t_name
            || capture!(fill_caps, "t3") != t_name
            || capture!(fill_caps, "n2") != n_name
            || capture!(fill_caps, "column2") != column_name
            || capture!(fill_caps, "column3") != column_name
            || capture!(fill_caps, "column4") != column_name
            || capture!(fill_caps, "column5") != column_name
            || capture!(fill_caps, "row2") != row_name
            || capture!(fill_caps, "row3") != row_name
            || capture!(fill_caps, "row4") != row_name
            || capture!(fill_caps, "row5") != row_name
        {
            continue;
        }

        let Ok(chunk) = capture!(fill_caps, "chunk").parse::<u32>() else {
            continue;
        };
        let Ok(chunk2) = capture!(fill_caps, "chunk2").parse::<u32>() else {
            continue;
        };
        let Ok(fill_columns) = capture!(fill_caps, "columns").parse::<u32>() else {
            continue;
        };
        let Ok(fill_rows) = capture!(fill_caps, "rows").parse::<u32>() else {
            continue;
        };
        let Ok(mask) = capture!(fill_caps, "mask").parse::<u32>() else {
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
        if capture!(root_caps, "timer") != timer_name || capture!(root_caps, "table") != table_name
        {
            continue;
        }
        let target_name = capture!(root_caps, "target");
        let Ok(root_row) = capture!(root_caps, "root").parse::<u32>() else {
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

        let construction_end = (window_start + capture_match!(root_caps, 0).end()) as u32;
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
            + capture_match!(timer_caps, 0)
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
    if !first.is_finite()
        || !second.is_finite()
        || first.fract() != 0.0
        || second.fract() != 0.0
        || first < 0.0
        || second < 0.0
        || first > f64::from(u32::MAX)
        || second > f64::from(u32::MAX)
    {
        return None;
    }
    Some((symbol, table.identity_for(first as u32, second as u32)?))
}

fn single_resolved_reference(scoping: &Scoping, symbol: SymbolId, expected: ReferenceId) -> bool {
    let refs = scoping.get_resolved_reference_ids(symbol);
    refs.len() == 1 && refs[0] == expected
}

impl Collector<'_, '_> {
    pub(super) fn ordered_switch_replacement(
        &self,
        it: &oxc_ast::ast::WhileStatement<'_>,
    ) -> Option<String> {
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
    eval_with_resolver(expr, &|id| {
        if id.name.as_str() == "undefined" {
            Some(Value::Undefined)
        } else {
            env.get(id.name.as_str()).cloned()
        }
    })
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

    pub(super) fn reference_state_replacement(
        &self,
        it: &oxc_ast::ast::ForStatement<'_>,
    ) -> Option<String> {
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

    pub(super) fn arithmetic_state_replacement(
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
