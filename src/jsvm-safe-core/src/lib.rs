mod decoder;
mod decoder_encoding;
mod proxy;
mod pure_function;
mod selector;
mod value_eval;

use decoder::{detect_decoders, detect_direct_table_decoders, Decoder};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, BindingPattern, CallExpression, ComputedMemberExpression,
    Expression, ExpressionStatement, IfStatement, LogicalExpression, Statement,
    StaticMemberExpression, UnaryExpression, VariableDeclarationKind, WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_semantic::{ReferenceId, Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use proxy::{
    collect_proxy_objects, proxy_literal_kind, static_proxy_member, ProxyObject, ProxyProperty,
};
use pure_function::{collect_pure_functions, PureFunction};
use selector::{collect_selector_dispatchers, SelectorDispatcher};
use std::collections::{BTreeMap, HashMap, HashSet};
use value_eval::{
    eval, eval_binary, eval_logical, eval_unary, eval_with_resolver, js_to_uint32, known_bool,
    same_value, Value,
};

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

fn direct_identifier_name<'a>(expr: &'a Expression<'a>) -> Option<&'a str> {
    match expr {
        Expression::Identifier(id) => Some(id.name.as_str()),
        _ => None,
    }
}

#[derive(Debug, Clone)]
struct ConstBinding {
    value: Value,
    available_after: u32,
}

fn eval_with_constants<'a>(
    expr: &Expression<'a>,
    scoping: &Scoping,
    constants: &HashMap<SymbolId, ConstBinding>,
) -> Option<Value> {
    eval_with_resolver(expr, &|id| {
        let reference_id = id.reference_id.get()?;
        let reference = scoping.get_reference(reference_id);
        if !reference.is_read()
            || reference.is_write()
            || reference.flags().is_member_write_target()
        {
            return None;
        }
        let binding = constants.get(&reference.symbol_id()?)?;
        (id.span.start >= binding.available_after).then(|| binding.value.clone())
    })
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

fn eval_with_env<'a>(expr: &Expression<'a>, env: &HashMap<String, Value>) -> Option<Value> {
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
                    .and_then(|object| object.get(it.property.name.as_str()))
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
                        .and_then(|object| object.get(&property))
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
                    .and_then(|object| object.get(&key))
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
                    .and_then(|object| object.get(&key))
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
                    .and_then(|object| object.get(&key))
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
                    .and_then(|object| object.get(&key))
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
                    .and_then(|object| object.get(&key))
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
                    let values = it
                        .arguments
                        .iter()
                        .map(eval_static_argument)
                        .collect::<Option<Vec<_>>>();
                    if let Some(values) = values {
                        if let Some(text) =
                            function.evaluate(&values).and_then(|value| value.render())
                        {
                            self.push(it.span, text, "pure_function_eval");
                            walk::walk_call_expression(self, it);
                            return;
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

fn parse_as<'a>(
    allocator: &'a Allocator,
    source: &'a str,
    source_type: SourceType,
) -> Option<oxc_ast::ast::Program<'a>> {
    let parsed = Parser::new(allocator, source, source_type).parse();
    (!parsed.panicked && parsed.diagnostics.is_empty()).then_some(parsed.program)
}

#[derive(Default)]
struct WithStatementDetector {
    found: bool,
}

impl<'a> Visit<'a> for WithStatementDetector {
    fn visit_with_statement(&mut self, _statement: &WithStatement<'a>) {
        self.found = true;
    }
}

fn contains_with_statement(program: &oxc_ast::ast::Program<'_>) -> bool {
    let mut detector = WithStatementDetector::default();
    detector.visit_program(program);
    detector.found
}

fn semantically_valid_source_type(source: &str) -> Option<SourceType> {
    // Browser-captured `.js` is normally either a classic Script or an ES
    // Module. Let Oxc resolve that from syntax first, then pin the resolved
    // Program source type for every rewrite iteration. CommonJS is only a
    // fallback for genuinely CJS-only syntax such as top-level `return`.
    for source_type in [SourceType::unambiguous(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let Some(program) = parse_as(&allocator, source, source_type) else {
            continue;
        };
        if contains_with_statement(&program) {
            continue;
        }
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if semantic_ret.diagnostics.is_empty() {
            return Some(program.source_type);
        }
    }
    None
}

fn transform_once(
    source: &str,
    source_type: SourceType,
    counts: &mut Counts,
    arithmetic_state_proofs: &mut Vec<ArithmeticStateProof>,
    iteration: usize,
) -> Option<String> {
    let allocator = Allocator::default();
    let program = parse_as(&allocator, source, source_type)?;
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
    // Select a source mode only after both parsing and semantic validation. Some
    // legacy browser scripts parse as modules but are invalid under module
    // strictness (for example duplicate top-level function declarations) while
    // remaining valid classic scripts/CommonJS. Preserve that distinction.
    let source_type = semantically_valid_source_type(source)?;

    let mut current = source.to_string();
    let mut counts = Counts::default();
    let mut iterations = 0usize;
    let mut arithmetic_state_proofs = Vec::new();

    for iteration in 1..=max_iterations {
        let next = transform_once(
            &current,
            source_type,
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
