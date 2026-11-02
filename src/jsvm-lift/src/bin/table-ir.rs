use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::ast::{BindingPattern, Expression, Statement};
use oxc_span::{GetSpan, SourceType};
use rolldown_redox::ecmascript::parse_program;
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    fs,
    path::PathBuf,
};

use jsvm_lift::semantic_ir::{classify_effect, IrOp};

#[derive(ClapParser, Debug)]
#[command(about = "Infer function-table VM ABI roles and lift handler statements into semantic IR")]
struct Args {
    source: PathBuf,
    scan: PathBuf,
    #[arg(long)]
    output: PathBuf,
}

#[derive(Debug, Deserialize)]
struct ScanReport {
    #[serde(default)]
    handler_function_tables: Vec<HandlerTable>,
    #[serde(default)]
    byte_transducers: Vec<ByteTransducer>,
    #[serde(default)]
    table_vms: Vec<TableVm>,
}

#[derive(Debug, Deserialize)]
struct HandlerTable {
    binding: String,
    start: u32,
    end: u32,
    function_values: usize,
    handlers: Vec<HandlerSlot>,
}

#[derive(Debug, Deserialize)]
struct HandlerSlot {
    key: String,
    start: u32,
    end: u32,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct ByteTransducer {
    function_id: String,
    binding: Option<String>,
    transition_table: String,
    state_source: String,
    byte_stream: String,
    pc_source: String,
    state_target: String,
    state_result_index: usize,
    opcode_result_index: usize,
}

#[derive(Debug, Clone, Deserialize)]
struct TableVm {
    dispatcher_function_id: String,
    handler_table: String,
    handler_count: usize,
    producer_method: Option<String>,
    linked_transducer_function_id: Option<String>,
    architecture: String,
}

#[derive(Debug, Default, Clone, Serialize)]
struct MethodStats {
    calls: usize,
    arg_counts: BTreeMap<usize, usize>,
}

#[derive(Debug, Default, Clone, Serialize)]
struct PropertyStats {
    appearances: usize,
    direct_calls: usize,
    direct_arg_counts: BTreeMap<usize, usize>,
    indexed: usize,
    length_reads: usize,
    length_writes: usize,
    push_calls: usize,
    slice_calls: usize,
    object_writes: usize,
    mutations: usize,
    bytecode_indices: usize,
    methods: BTreeMap<String, MethodStats>,
}

#[derive(Debug, Serialize)]
struct HandlerStatementIr {
    source: String,
    normalized: String,
    ir: IrOp,
}

#[derive(Debug, Serialize)]
struct HandlerIr {
    key: String,
    start: u32,
    end: u32,
    parameter: Option<String>,
    semantic_hash: String,
    op_kinds: Vec<String>,
    statements: Vec<HandlerStatementIr>,
}

#[derive(Debug, Serialize)]
struct TableVmIr {
    dispatcher_function_id: String,
    handler_table: String,
    handler_count: usize,
    architecture: String,
    producer_method: Option<String>,
    linked_transducer: Option<ByteTransducer>,
    role_bindings: BTreeMap<String, String>,
    method_bindings: BTreeMap<String, String>,
    property_stats: BTreeMap<String, PropertyStats>,
    handlers: Vec<HandlerIr>,
}

#[derive(Debug, Serialize)]
struct Output {
    schema: &'static str,
    source: String,
    vms: Vec<TableVmIr>,
}

const fn is_ident_char(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_' || c == b'$'
}

fn replace_ident(text: &str, old: &str, new: &str) -> String {
    if old.is_empty() {
        return text.to_string();
    }
    let bytes = text.as_bytes();
    let needle = old.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut cursor = 0usize;
    let mut i = 0usize;
    while i + needle.len() <= bytes.len() {
        if &bytes[i..i + needle.len()] == needle
            && (i == 0 || !is_ident_char(bytes[i - 1]))
            && (i + needle.len() == bytes.len() || !is_ident_char(bytes[i + needle.len()]))
        {
            out.push_str(&text[cursor..i]);
            out.push_str(new);
            i += needle.len();
            cursor = i;
        } else {
            i += 1;
        }
    }
    out.push_str(&text[cursor..]);
    out
}

fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

fn first_param(raw: &str) -> Option<String> {
    let wrapped = format!("({raw})");
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &wrapped, SourceType::cjs());
    if !parsed.is_clean() || parsed.program.body.len() != 1 {
        return None;
    }
    let Statement::ExpressionStatement(es) = &parsed.program.body[0] else {
        return None;
    };
    let mut expr = &es.expression;
    while let Expression::ParenthesizedExpression(p) = expr {
        expr = &p.expression;
    }
    let params = match expr {
        Expression::FunctionExpression(fun) => &fun.params,
        Expression::ArrowFunctionExpression(fun) => &fun.params,
        _ => return None,
    };
    let first = params.items.first()?;
    match &first.pattern {
        BindingPattern::BindingIdentifier(id) => Some(id.name.to_string()),
        _ => None,
    }
}

fn body_statements(raw: &str) -> Vec<String> {
    let wrapped = format!("({raw})");
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &wrapped, SourceType::cjs());
    if !parsed.is_clean() || parsed.program.body.len() != 1 {
        return vec![raw.to_string()];
    }
    let Statement::ExpressionStatement(es) = &parsed.program.body[0] else {
        return vec![raw.to_string()];
    };
    let mut expr = &es.expression;
    while let Expression::ParenthesizedExpression(p) = expr {
        expr = &p.expression;
    }
    let statements = match expr {
        Expression::FunctionExpression(fun) => fun.body.as_ref().map(|b| b.statements.as_slice()),
        Expression::ArrowFunctionExpression(fun) => match &fun.body {
            oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) => Some(body.statements.as_slice()),
            _ => None,
        },
        _ => None,
    };
    let Some(statements) = statements else {
        return vec![raw.to_string()];
    };
    statements
        .iter()
        .filter_map(|stmt| {
            wrapped
                .get(stmt.span().start as usize..stmt.span().end as usize)
                .map(str::to_string)
        })
        .collect()
}

fn property_occurrences(raw: &str, param: &str) -> BTreeSet<String> {
    let text = compact(raw);
    let prefix = format!("{param}.");
    let bytes = text.as_bytes();
    let mut out = BTreeSet::new();
    let mut from = 0usize;
    while let Some(rel) = text[from..].find(&prefix) {
        let start = from + rel + prefix.len();
        let mut end = start;
        while end < bytes.len() && is_ident_char(bytes[end]) {
            end += 1;
        }
        if end > start {
            out.insert(text[start..end].to_string());
        }
        from = end.max(start + 1);
    }
    out
}

fn count_occurrences(text: &str, needle: &str) -> usize {
    if needle.is_empty() {
        return 0;
    }
    text.match_indices(needle).count()
}

fn call_arg_count(text: &str, open: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    if bytes.get(open) != Some(&b'(') {
        return None;
    }
    let mut depth = 0i32;
    let mut commas = 0usize;
    let mut any = false;
    let mut quote = None::<u8>;
    let mut escape = false;
    for &b in &bytes[open + 1..] {
        if let Some(q) = quote {
            any = true;
            if escape {
                escape = false;
            } else if b == b'\x5c' {
                escape = true;
            } else if b == q {
                quote = None;
            }
            continue;
        }
        match b {
            b'\x27' | b'\x22' | b'\x60' => {
                quote = Some(b);
                any = true;
            }
            b'(' | b'[' | b'{' => {
                depth += 1;
                any = true;
            }
            b')' if depth == 0 => return Some(if any { commas + 1 } else { 0 }),
            b')' | b']' | b'}' => {
                depth -= 1;
                any = true;
            }
            b',' if depth == 0 => {
                commas += 1;
                any = true;
            }
            b if !b.is_ascii_whitespace() => any = true,
            _ => {}
        }
    }
    None
}

fn collect_property_stats(
    raws: &[(String, String)],
    byte_stream: Option<&str>,
) -> BTreeMap<String, PropertyStats> {
    let mut out: BTreeMap<String, PropertyStats> = BTreeMap::new();
    for (raw, param) in raws {
        let text = compact(raw);
        for prop in property_occurrences(raw, param) {
            let stats = out.entry(prop.clone()).or_default();
            let base = format!("{param}.{prop}");
            stats.appearances += count_occurrences(&text, &base);
            let direct_prefix = format!("{base}(");
            let mut direct_from = 0usize;
            while let Some(rel) = text[direct_from..].find(&direct_prefix) {
                let open = direct_from + rel + base.len();
                stats.direct_calls += 1;
                if let Some(argc) = call_arg_count(&text, open) {
                    *stats.direct_arg_counts.entry(argc).or_default() += 1;
                }
                direct_from = open + 1;
            }
            stats.indexed += count_occurrences(&text, &format!("{base}["));
            stats.length_reads += count_occurrences(&text, &format!("{base}.length"));
            for op in ["=", "+=", "-=", "*=", "/=", "++", "--"] {
                stats.mutations += count_occurrences(&text, &format!("{base}{op}"));
            }
            for op in ["=", "+=", "-=", "++", "--"] {
                stats.length_writes += count_occurrences(&text, &format!("{base}.length{op}"));
            }
            stats.push_calls += count_occurrences(&text, &format!("{base}.push("));
            stats.slice_calls += count_occurrences(&text, &format!("{base}.slice("));
            stats.object_writes += count_occurrences(&text, &format!("{base}={{"));
            if let Some(bs) = byte_stream {
                stats.bytecode_indices += count_occurrences(&text, &format!("{bs}[{base}"));
            }

            let method_prefix = format!("{base}.");
            let bytes = text.as_bytes();
            let mut from = 0usize;
            while let Some(rel) = text[from..].find(&method_prefix) {
                let start = from + rel + method_prefix.len();
                let mut end = start;
                while end < bytes.len() && is_ident_char(bytes[end]) {
                    end += 1;
                }
                if end > start && bytes.get(end) == Some(&b'(') {
                    let method = text[start..end].to_string();
                    if !matches!(method.as_str(), "push" | "slice") {
                        let entry = stats.methods.entry(method).or_default();
                        entry.calls += 1;
                        if let Some(argc) = call_arg_count(&text, end) {
                            *entry.arg_counts.entry(argc).or_default() += 1;
                        }
                    }
                }
                from = end.max(start + 1);
            }
        }
    }
    out
}

fn this_property(raw: &str) -> Option<String> {
    let tail = raw.trim().strip_prefix("this.")?;
    let end = tail
        .bytes()
        .position(|b| !is_ident_char(b))
        .unwrap_or(tail.len());
    (end > 0).then(|| tail[..end].to_string())
}

fn state_property(transducer: Option<&ByteTransducer>) -> Option<String> {
    this_property(&transducer?.state_target)
}

fn pc_property(transducer: Option<&ByteTransducer>) -> Option<String> {
    this_property(&transducer?.pc_source)
}

fn best_property<F>(
    stats: &BTreeMap<String, PropertyStats>,
    excluded: &HashSet<String>,
    score: F,
) -> Option<String>
where
    F: Fn(&PropertyStats) -> usize,
{
    stats
        .iter()
        .filter(|(name, s)| !excluded.contains(*name) && s.direct_calls == 0)
        .map(|(name, s)| (score(s), name))
        .filter(|(score, _)| *score > 0)
        .max_by(|a, b| a.0.cmp(&b.0).then_with(|| b.1.cmp(a.1)))
        .map(|(_, name)| name.clone())
}

fn infer_roles(
    stats: &BTreeMap<String, PropertyStats>,
    transducer: Option<&ByteTransducer>,
) -> BTreeMap<String, String> {
    let mut roles = BTreeMap::new();
    let mut used = HashSet::new();

    if let Some(state) = state_property(transducer) {
        if stats.contains_key(&state) {
            used.insert(state.clone());
            roles.insert("opcode_state".into(), state);
        }
    }

    if let Some(ip) = pc_property(transducer).filter(|p| stats.contains_key(p)) {
        used.insert(ip.clone());
        roles.insert("ip".into(), ip);
    } else if let Some(ip) = best_property(stats, &used, |s| {
        if s.bytecode_indices == 0 {
            0
        } else {
            s.bytecode_indices * 50 + s.mutations * 4 + s.appearances
        }
    }) {
        used.insert(ip.clone());
        roles.insert("ip".into(), ip);
    }

    if let Some(stack) = best_property(stats, &used, |s| {
        if s.length_reads + s.length_writes < 4 && s.push_calls < 4 {
            return 0;
        }
        s.indexed * 5
            + s.length_reads * 4
            + s.length_writes * 8
            + s.push_calls * 6
            + s.slice_calls * 4
    }) {
        used.insert(stack.clone());
        roles.insert("stack".into(), stack);
    }

    if let Some(registers) = best_property(stats, &used, |s| {
        let calls = s.methods.values().map(|m| m.calls).sum::<usize>();
        if calls < 8 || s.methods.len() < 2 {
            0
        } else {
            calls * 10 + s.appearances
        }
    }) {
        used.insert(registers.clone());
        roles.insert("registers".into(), registers);
    }

    if let Some(control) = best_property(stats, &used, |s| {
        if s.object_writes == 0 {
            0
        } else {
            s.object_writes * 30 + s.appearances
        }
    }) {
        used.insert(control.clone());
        roles.insert("control".into(), control);
    }

    if let Some(control_stack) = best_property(stats, &used, |s| {
        let zero_arg: usize = s
            .methods
            .values()
            .map(|m| m.arg_counts.get(&0).copied().unwrap_or(0))
            .sum();
        let one_arg: usize = s
            .methods
            .values()
            .map(|m| m.arg_counts.get(&1).copied().unwrap_or(0))
            .sum();
        let helper_stack = zero_arg > 0 && one_arg > 0 && s.length_reads > 0 && s.indexed > 0;
        if s.push_calls == 0 && !helper_stack {
            0
        } else {
            s.push_calls * 15 + s.length_reads * 5 + s.indexed * 2 + zero_arg * 4 + one_arg * 4
        }
    }) {
        roles.insert("control_stack".into(), control_stack);
    }

    roles
}

fn infer_method_bindings(
    stats: &BTreeMap<String, PropertyStats>,
    roles: &BTreeMap<String, String>,
    producer_method: Option<&str>,
    has_transducer: bool,
) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    if let Some(method) = producer_method {
        out.insert(
            format!("ctx.{method}"),
            if has_transducer {
                "read_opcode"
            } else {
                "read_byte"
            }
            .into(),
        );
    }

    let mut getter: Option<(usize, String)> = None;
    let mut setter: Option<(usize, String)> = None;
    for (name, s) in stats {
        if s.direct_calls == 0 || producer_method == Some(name.as_str()) {
            continue;
        }
        let one = s.direct_arg_counts.get(&1).copied().unwrap_or(0);
        let many: usize = s
            .direct_arg_counts
            .iter()
            .filter(|(n, _)| **n >= 2)
            .map(|(_, c)| *c)
            .sum();
        if one > many && one > 0 && getter.as_ref().is_none_or(|(best, _)| one > *best) {
            getter = Some((one, name.clone()));
        }
        if many > one && many > 0 && setter.as_ref().is_none_or(|(best, _)| many > *best) {
            setter = Some((many, name.clone()));
        }
    }
    if let Some((_, method)) = getter {
        out.insert(format!("ctx.{method}"), "reg_get".into());
    }
    if let Some((_, method)) = setter {
        out.insert(format!("ctx.{method}"), "reg_set".into());
    }

    if let Some(registers) = roles.get("registers") {
        if let Some(reg_stats) = stats.get(registers) {
            for (method, m) in &reg_stats.methods {
                let one = m.arg_counts.get(&1).copied().unwrap_or(0);
                let many: usize = m
                    .arg_counts
                    .iter()
                    .filter(|(n, _)| **n >= 2)
                    .map(|(_, c)| *c)
                    .sum();
                let role = if one > many && one > 0 {
                    "reg_get"
                } else if many > 0 {
                    "reg_set"
                } else {
                    "reg_method"
                };
                out.insert(format!("registers.{method}"), role.into());
            }
        }
    }
    out
}

fn normalize_statement(
    source: &str,
    param: Option<&str>,
    roles: &BTreeMap<String, String>,
    methods: &BTreeMap<String, String>,
    byte_stream: Option<&str>,
) -> String {
    let mut out = source.to_string();
    let Some(param) = param else {
        if let Some(bs) = byte_stream {
            out = replace_ident(&out, bs, "bytecode");
        }
        return out;
    };

    if let Some(registers) = roles.get("registers") {
        for (from, to) in methods {
            if let Some(method) = from.strip_prefix("registers.") {
                out = out.replace(&format!("{param}.{registers}.{method}"), to);
            }
        }
    }

    for (from, role) in methods {
        if let Some(method) = from.strip_prefix("ctx.") {
            out = out.replace(&format!("{param}.{method}"), role);
        }
    }

    let mut role_pairs: Vec<_> = roles.iter().collect();
    role_pairs.sort_by_key(|(role, _)| std::cmp::Reverse(role.len()));
    for (role, original) in role_pairs {
        out = out.replace(&format!("{param}.{original}"), role);
    }

    if let Some(bs) = byte_stream {
        out = replace_ident(&out, bs, "bytecode");
    }
    replace_ident(&out, param, "ctx")
}

fn matching_table<'a>(report: &'a ScanReport, vm: &TableVm) -> Option<&'a HandlerTable> {
    report
        .handler_function_tables
        .iter()
        .filter(|table| {
            table.binding == vm.handler_table && table.function_values == vm.handler_count
        })
        .min_by_key(|table| table.end.saturating_sub(table.start))
}

fn lift_handlers(
    source: &str,
    table: &HandlerTable,
    roles: &BTreeMap<String, String>,
    methods: &BTreeMap<String, String>,
    byte_stream: Option<&str>,
) -> Vec<HandlerIr> {
    table
        .handlers
        .iter()
        .filter_map(|slot| {
            let start = slot.start as usize;
            let end = (slot.end as usize).min(source.len());
            let raw = source.get(start..end)?;
            let parameter = first_param(raw);
            let mut signature = Vec::new();
            let statements = body_statements(raw)
                .into_iter()
                .map(|statement| {
                    let normalized = normalize_statement(
                        &statement,
                        parameter.as_deref(),
                        roles,
                        methods,
                        byte_stream,
                    );
                    let ir = classify_effect(&normalized);
                    signature.push(format!("{}:{}", ir.kind, ir.shape_hash));
                    HandlerStatementIr {
                        source: statement,
                        normalized,
                        ir,
                    }
                })
                .collect::<Vec<_>>();
            Some(HandlerIr {
                key: slot.key.clone(),
                start: slot.start,
                end: slot.end,
                parameter,
                semantic_hash: format!(
                    "{:016x}",
                    jsvm_lift::fnv1a64(signature.join("|").as_bytes())
                ),
                op_kinds: statements
                    .iter()
                    .map(|statement| statement.ir.kind.clone())
                    .collect(),
                statements,
            })
        })
        .collect()
}

fn lift_table_vm(source: &str, report: &ScanReport, vm: &TableVm) -> Option<TableVmIr> {
    let table = matching_table(report, vm)?;
    let linked = vm.linked_transducer_function_id.as_deref().and_then(|id| {
        report
            .byte_transducers
            .iter()
            .find(|transducer| transducer.function_id == id)
    });
    let byte_stream = linked.map(|transducer| transducer.byte_stream.as_str());

    let raw_for_stats = table
        .handlers
        .iter()
        .filter_map(|slot| {
            let raw = source.get(slot.start as usize..(slot.end as usize).min(source.len()))?;
            first_param(raw).map(|parameter| (raw.to_string(), parameter))
        })
        .collect::<Vec<_>>();
    let property_stats = collect_property_stats(&raw_for_stats, byte_stream);
    let roles = infer_roles(&property_stats, linked);
    let methods = infer_method_bindings(
        &property_stats,
        &roles,
        vm.producer_method.as_deref(),
        linked.is_some(),
    );
    let handlers = lift_handlers(source, table, &roles, &methods, byte_stream);

    Some(TableVmIr {
        dispatcher_function_id: vm.dispatcher_function_id.clone(),
        handler_table: vm.handler_table.clone(),
        handler_count: vm.handler_count,
        architecture: vm.architecture.clone(),
        producer_method: vm.producer_method.clone(),
        linked_transducer: linked.cloned(),
        role_bindings: roles,
        method_bindings: methods,
        property_stats,
        handlers,
    })
}

fn lift_table_vms(source: &str, report: &ScanReport) -> Vec<TableVmIr> {
    let mut seen = HashSet::new();
    report
        .table_vms
        .iter()
        .filter(|vm| {
            seen.insert((
                vm.handler_table.clone(),
                vm.handler_count,
                vm.linked_transducer_function_id.clone(),
            ))
        })
        .filter_map(|vm| lift_table_vm(source, report, vm))
        .collect()
}

fn print_summary(output: &Output, output_path: &std::path::Path) {
    let handler_count: usize = output.vms.iter().map(|vm| vm.handlers.len()).sum();
    let statement_count: usize = output
        .vms
        .iter()
        .flat_map(|vm| &vm.handlers)
        .map(|handler| handler.statements.len())
        .sum();
    let raw_count = output
        .vms
        .iter()
        .flat_map(|vm| &vm.handlers)
        .flat_map(|handler| &handler.statements)
        .filter(|statement| matches!(statement.ir.kind.as_str(), "raw_js" | "raw_expression"))
        .count();
    println!(
        "table IR VMs {} handlers {} statements {} classified {} raw {}",
        output.vms.len(),
        handler_count,
        statement_count,
        statement_count.saturating_sub(raw_count),
        raw_count
    );
    for vm in &output.vms {
        println!(
            "{} handlers={} roles={:?} methods={:?}",
            vm.handler_table,
            vm.handlers.len(),
            vm.role_bindings,
            vm.method_bindings
        );
    }
    println!("wrote {}", output_path.display());
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.source)
        .with_context(|| format!("reading {}", args.source.display()))?;
    let report: ScanReport = serde_json::from_str(
        fs::read_to_string(&args.scan)
            .with_context(|| format!("reading {}", args.scan.display()))?
            .trim(),
    )
    .with_context(|| format!("parsing {}", args.scan.display()))?;
    let output = Output {
        schema: "jsvm-table-ir/v0",
        source: args.source.display().to_string(),
        vms: lift_table_vms(&source, &report),
    };
    fs::write(
        &args.output,
        format!("{}\n", serde_json::to_string_pretty(&output)?),
    )
    .with_context(|| format!("writing {}", args.output.display()))?;
    print_summary(&output, &args.output);
    Ok(())
}
