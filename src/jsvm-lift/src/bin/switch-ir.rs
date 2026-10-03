use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::ast::{Expression, Statement};
use oxc_parser::Parser;
use oxc_span::{GetSpan, SourceType};
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs,
    path::PathBuf,
};

#[path = "../semantic_ir.rs"]
mod semantic_ir;
use semantic_ir::{classify_effect, IrOp};

#[derive(ClapParser, Debug)]
#[command(about = "Infer direct-switch VM roles and lift switch handlers into semantic IR")]
struct Args {
    source: PathBuf,
    scan: PathBuf,
    #[arg(long)]
    output: PathBuf,
}

#[derive(Debug, Deserialize)]
struct ScanReport {
    #[serde(default)]
    direct_switch_maps: Vec<DirectSwitchMap>,
    #[serde(default)]
    functions: Vec<FunctionInfo>,
}

#[derive(Debug, Clone, Deserialize)]
struct FunctionInfo {
    id: String,
    name: Option<String>,
    start: u32,
    end: u32,
}

#[derive(Debug, Clone, Deserialize)]
struct DirectSwitchMap {
    parent_function_id: String,
    start: u32,
    end: u32,
    selector: String,
    numeric_cases: usize,
    opcode_max: u64,
    #[serde(default)]
    vm_evidence_score: u32,
    #[serde(default)]
    vm_reasons: Vec<String>,
    #[serde(default)]
    confirmed_vm: bool,
    handlers: Vec<DirectSwitchHandler>,
}

#[derive(Debug, Clone, Deserialize)]
struct DirectSwitchHandler {
    key: Option<u64>,
    key_source: Option<String>,
    #[serde(default)]
    semantic: Vec<String>,
    terminal: String,
}

#[derive(Debug, Serialize)]
struct HandlerEffectIr {
    source: String,
    normalized: String,
    ir: IrOp,
}

#[derive(Debug, Serialize)]
struct SwitchHandlerIr {
    opcode: Option<u64>,
    key_source: Option<String>,
    terminal: String,
    semantic_label: String,
    semantic_hash: String,
    coarse_semantic_hash: String,
    op_kinds: Vec<String>,
    effects: Vec<HandlerEffectIr>,
}

#[derive(Debug, Serialize)]
struct SwitchVmIr {
    parent_function_id: String,
    function_name: Option<String>,
    function_start: u32,
    function_end: u32,
    switch_start: u32,
    switch_end: u32,
    selector: String,
    selector_style: String,
    numeric_cases: usize,
    opcode_max: u64,
    vm_evidence_score: u32,
    vm_reasons: Vec<String>,
    role_bindings: BTreeMap<String, String>,
    helper_bindings: BTreeMap<String, String>,
    handlers: Vec<SwitchHandlerIr>,
}

#[derive(Debug, Serialize)]
struct Output {
    schema: &'static str,
    source: String,
    vms: Vec<SwitchVmIr>,
}

fn fnv1a64(data: &[u8]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for byte in data {
        h ^= u64::from(*byte);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn is_ident_char(c: char) -> bool {
    c == '_' || c == '$' || c.is_ascii_alphanumeric()
}

fn replace_ident(source: &str, from: &str, to: &str) -> String {
    if from.is_empty() || from == to {
        return source.to_string();
    }
    let mut out = String::with_capacity(source.len());
    let mut from_at = 0usize;
    while let Some(rel) = source[from_at..].find(from) {
        let start = from_at + rel;
        let end = start + from.len();
        let before = source[..start].chars().next_back();
        let after = source[end..].chars().next();
        if before.is_none_or(|c| !is_ident_char(c)) && after.is_none_or(|c| !is_ident_char(c)) {
            out.push_str(&source[from_at..start]);
            out.push_str(to);
            from_at = end;
        } else {
            out.push_str(&source[from_at..end]);
            from_at = end;
        }
    }
    out.push_str(&source[from_at..]);
    out
}

fn function_source<'a>(source: &'a str, f: &FunctionInfo) -> &'a str {
    source
        .get(f.start as usize..(f.end as usize).min(source.len()))
        .unwrap_or_default()
}

fn all_semantics(map: &DirectSwitchMap) -> String {
    map.handlers
        .iter()
        .flat_map(|handler| handler.semantic.iter())
        .cloned()
        .collect::<Vec<_>>()
        .join("\n")
}

fn indexed_selector(selector: &str) -> Option<(String, String)> {
    let re =
        Regex::new(r"^\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\[\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\]\s*$")
            .unwrap();
    let caps = re.captures(selector)?;
    Some((caps[1].to_string(), caps[2].to_string()))
}

fn call_selector(selector: &str) -> Option<String> {
    let re = Regex::new(r"^\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\(\s*\)\s*$").unwrap();
    re.captures(selector).map(|caps| caps[1].to_string())
}

fn dominant_stack_pair(text: &str) -> Option<(String, String)> {
    let pre = Regex::new(r"([A-Za-z_$][A-Za-z0-9_$]*)\s*\[\s*--\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\]")
        .unwrap();
    let post =
        Regex::new(r"([A-Za-z_$][A-Za-z0-9_$]*)\s*\[\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\+\+\s*\]")
            .unwrap();
    let mut counts: HashMap<(String, String), usize> = HashMap::new();
    for caps in pre.captures_iter(text).chain(post.captures_iter(text)) {
        *counts
            .entry((caps[1].to_string(), caps[2].to_string()))
            .or_default() += 1;
    }
    counts
        .into_iter()
        .max_by_key(|(_, count)| *count)
        .filter(|(_, count)| *count >= 4)
        .map(|(pair, _)| pair)
}

fn dominant_ip(text: &str, excluded: &HashSet<String>) -> Option<String> {
    let re = Regex::new(r"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*(?:\+\+|--|\+=|-=)").unwrap();
    let mut counts: HashMap<String, usize> = HashMap::new();
    for caps in re.captures_iter(text) {
        let name = caps[1].to_string();
        if !excluded.contains(&name) {
            *counts.entry(name).or_default() += 1;
        }
    }
    counts
        .into_iter()
        .max_by_key(|(_, count)| *count)
        .filter(|(_, count)| *count >= 3)
        .map(|(name, _)| name)
}

fn empty_array_candidates(function: &str) -> Vec<String> {
    let re = Regex::new(r"\b([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*\[\s*\]").unwrap();
    let mut out = Vec::new();
    for caps in re.captures_iter(function) {
        let value = caps[1].to_string();
        if !out.contains(&value) {
            out.push(value);
        }
    }
    out
}

fn identifier_count(text: &str, ident: &str) -> usize {
    if ident.is_empty() {
        return 0;
    }
    let pattern = format!(r"\b{}\b", regex::escape(ident));
    Regex::new(&pattern).unwrap().find_iter(text).count()
}

fn named_function_body<'a>(source: &'a str, name: &str) -> Option<&'a str> {
    let marker = format!("function {name}(");
    let start = source.find(&marker)?;
    let open = source[start..].find('{')? + start;
    let bytes = source.as_bytes();
    let mut depth = 0usize;
    let mut quote = None::<u8>;
    let mut escaped = false;

    for (i, &b) in bytes.iter().enumerate().skip(open) {
        if let Some(q) = quote {
            if escaped {
                escaped = false;
            } else if b == b'\\' {
                escaped = true;
            } else if b == q {
                quote = None;
            }
            continue;
        }
        match b {
            b'\'' | b'"' | 0x60 => quote = Some(b),
            b'{' => depth += 1,
            b'}' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return source.get(open + 1..i);
                }
            }
            _ => {}
        }
    }
    None
}

fn call_family_roles(
    function_prefix: &str,
    semantics: &str,
    selector_helper: &str,
) -> (BTreeMap<String, String>, BTreeMap<String, String>) {
    let mut roles = BTreeMap::new();
    let mut helpers = BTreeMap::new();
    helpers.insert("read_byte".into(), selector_helper.to_string());

    let read_re = Regex::new(
        r"return\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*\[\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\+\+\s*\]\s*\^\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\[",
    )
    .unwrap();
    if let Some(caps) = read_re.captures(function_prefix) {
        roles.insert("bytecode".into(), caps[1].to_string());
        roles.insert("ip".into(), caps[2].to_string());
        roles.insert("decode_key".into(), caps[3].to_string());
    }

    let arrays = empty_array_candidates(function_prefix);
    if !arrays.is_empty() {
        let mut ranked = arrays
            .iter()
            .map(|name| (identifier_count(semantics, name), name.clone()))
            .collect::<Vec<_>>();
        ranked.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
        if let Some((_, stack)) = ranked.first() {
            roles.insert("stack".into(), stack.clone());
        }
        if let Some((_, control)) = ranked.get(1) {
            roles.insert("control_stack".into(), control.clone());
        }
    }

    let fn_re = Regex::new(r"function\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*\(([^)]*)\)").unwrap();
    let declarations = fn_re
        .captures_iter(function_prefix)
        .map(|caps| {
            let name = caps[1].to_string();
            let argc = if caps[2].trim().is_empty() {
                0
            } else {
                caps[2].split(',').count()
            };
            (name, argc)
        })
        .collect::<Vec<_>>();

    if let Some(stack) = roles.get("stack") {
        for (name, argc) in &declarations {
            if name == selector_helper {
                continue;
            }
            let Some(body) = named_function_body(function_prefix, name) else {
                continue;
            };
            if identifier_count(body, stack) == 0 {
                continue;
            }
            if *argc == 1 && identifier_count(semantics, name) >= 4 {
                helpers.entry("stack_push".into()).or_insert(name.clone());
            } else if *argc == 0
                && body.contains("return")
                && identifier_count(semantics, name) >= 4
            {
                helpers.entry("stack_pop".into()).or_insert(name.clone());
            }
        }
    }

    for (name, argc) in &declarations {
        if *argc != 0 || name == selector_helper {
            continue;
        }
        let Some(body) = named_function_body(function_prefix, name) else {
            continue;
        };
        let read_calls = identifier_count(body, selector_helper);
        if read_calls >= 2 && body.contains("<<8") {
            helpers.entry("read_u16".into()).or_insert(name.clone());
        }
    }
    if let Some(read_u16) = helpers.get("read_u16").cloned() {
        for (name, argc) in &declarations {
            if *argc != 0 || name == selector_helper || name == &read_u16 {
                continue;
            }
            let Some(body) = named_function_body(function_prefix, name) else {
                continue;
            };
            if identifier_count(body, &read_u16) > 0 && identifier_count(body, selector_helper) > 0
            {
                helpers.entry("read_string".into()).or_insert(name.clone());
            }
        }
    }

    let in_re = Regex::new(r"\bin\s+([A-Za-z_$][A-Za-z0-9_$]*)").unwrap();
    for (name, argc) in &declarations {
        if *argc != 1 {
            continue;
        }
        let Some(body) = named_function_body(function_prefix, name) else {
            continue;
        };
        if !body.contains("throw Error") {
            continue;
        }
        let envs = in_re
            .captures_iter(body)
            .map(|caps| caps[1].to_string())
            .collect::<Vec<_>>();
        if let Some(env) = envs.first() {
            helpers.entry("env_lookup".into()).or_insert(name.clone());
            roles.entry("env".into()).or_insert_with(|| env.clone());
        }
        if let Some(fallback) = envs.get(1) {
            roles
                .entry("env_fallback".into())
                .or_insert_with(|| fallback.clone());
        }
    }

    (roles, helpers)
}

fn indexed_family_roles(
    map: &DirectSwitchMap,
    semantics: &str,
) -> (BTreeMap<String, String>, BTreeMap<String, String>) {
    let mut roles = BTreeMap::new();
    let helpers = BTreeMap::new();

    if let Some((table, raw_opcode)) = indexed_selector(&map.selector) {
        roles.insert("opcode_map".into(), table);
        roles.insert("raw_opcode".into(), raw_opcode);
    }

    let mut excluded = HashSet::new();
    if let Some((stack, sp)) = dominant_stack_pair(semantics) {
        excluded.insert(sp.clone());
        roles.insert("stack".into(), stack);
        roles.insert("sp".into(), sp);
    }
    if let Some(ip) = dominant_ip(semantics, &excluded) {
        roles.insert("ip".into(), ip);
    }

    (roles, helpers)
}

fn normalize(
    source: &str,
    roles: &BTreeMap<String, String>,
    helpers: &BTreeMap<String, String>,
) -> String {
    let mut out = source.to_string();

    // Helper calls first so their original names do not get captured by another role.
    let helper_targets = [
        ("stack_push", "stack_push"),
        ("stack_pop", "stack_pop"),
        ("read_byte", "read_byte"),
        ("read_u16", "read_u16"),
        ("read_string", "read_string"),
        ("env_lookup", "env_lookup"),
    ];
    for (role, canonical) in helper_targets {
        if let Some(original) = helpers.get(role) {
            out = replace_ident(&out, original, canonical);
        }
    }

    // Longest originals first avoids pathological substring churn even though replacement is bounded.
    let mut role_pairs = roles.iter().collect::<Vec<_>>();
    role_pairs.sort_by_key(|(_, original)| std::cmp::Reverse(original.len()));
    for (role, original) in role_pairs {
        out = replace_ident(&out, original, role);
    }
    out
}

fn fragment(source: &str, start: u32, end: u32) -> String {
    source
        .get(start as usize..(end as usize).min(source.len()))
        .unwrap_or_default()
        .to_string()
}

fn split_effects(source: &str) -> Vec<String> {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, SourceType::cjs()).parse();
    if parsed.panicked || !parsed.diagnostics.is_empty() || parsed.program.body.len() != 1 {
        return vec![source.to_string()];
    }

    let statement = &parsed.program.body[0];
    let statements: Vec<&Statement<'_>> = match statement {
        Statement::BlockStatement(block) => block.body.iter().collect(),
        _ => vec![statement],
    };

    let mut out = Vec::new();
    for statement in statements {
        if let Statement::ExpressionStatement(es) = statement {
            if let Expression::SequenceExpression(seq) = &es.expression {
                for expr in &seq.expressions {
                    out.push(fragment(source, expr.span().start, expr.span().end));
                }
                continue;
            }
        }
        out.push(fragment(
            source,
            statement.span().start,
            statement.span().end,
        ));
    }
    if out.is_empty() {
        vec![source.to_string()]
    } else {
        out
    }
}

fn regex_is(pattern: &str, text: &str) -> bool {
    Regex::new(pattern).is_ok_and(|re| re.is_match(text))
}

fn infer_semantic_label(
    selector_style: &str,
    terminal: &str,
    effects: &[HandlerEffectIr],
) -> String {
    let parts = effects
        .iter()
        .map(|effect| effect.normalized.trim().trim_end_matches(';'))
        .collect::<Vec<_>>();
    let text = parts.join(" ; ");
    let kinds = effects
        .iter()
        .map(|effect| effect.ir.kind.as_str())
        .collect::<Vec<_>>();

    if selector_style == "indexed" {
        if parts.is_empty() {
            return "nop".into();
        }
        if text.contains("stack[--sp]?") && text.contains("ip") {
            if regex_is(r"\?ip=[^:]+:ip\+\+", &text) {
                return "jump_if_truthy".into();
            }
            if regex_is(r"\?ip\+\+:ip=", &text) {
                return "jump_if_falsy".into();
            }
            return "conditional_jump".into();
        }
        if parts.len() == 1 && regex_is(r"^ip=[^;]+$", parts[0]) {
            return "jump".into();
        }
        if parts.contains(&"stack[--sp]") {
            return "pop".into();
        }
        if text.contains("stack[sp-1]") && text.contains("stack[sp++]=e") {
            return "dup".into();
        }
        if text.contains("stack[sp++]=null") {
            return "push_null".into();
        }
        if text.contains("stack[sp++]=void 0") {
            return "push_undefined".into();
        }
        if text.contains("e+1n") && text.contains("stack[sp++]=") {
            return "increment".into();
        }
        if text.contains("e-1n") && text.contains("stack[sp++]=") {
            return "decrement".into();
        }
        if regex_is(r"stack\[sp\+\+\]=typeof e===v\?e:\+e", &text) {
            return "to_number".into();
        }
        if (text.contains("Reflect.set")
            || regex_is(
                r"\b[A-Za-z_$][A-Za-z0-9_$]*\[[^\]]+\]=e(?:\s*[;,]|\s*$)",
                &text,
            ))
            && text.contains("stack[sp++]=e")
        {
            return "property_set".into();
        }
        if text.contains("stack[sp++]=t[e]") || text.contains("stack[sp++]=e[t]") {
            return "property_get".into();
        }
        if let Some(caps) = Regex::new(r"stack\[sp\+\+\]=t(===|!==|==|!=|<=|>=|<|>|\+|-|\*|/|%)e")
            .ok()
            .and_then(|re| re.captures(&text))
        {
            return match &caps[1] {
                "===" => "strict_eq",
                "!==" => "strict_neq",
                "==" => "loose_eq",
                "!=" => "loose_neq",
                "<" => "lt",
                "<=" => "lte",
                ">" => "gt",
                ">=" => "gte",
                "+" => "add",
                "-" => "sub",
                "*" => "mul",
                "/" => "div",
                "%" => "mod",
                _ => "binary_op",
            }
            .into();
        }
        if kinds.first() == Some(&"computed_store") {
            return "slot_store".into();
        }
        if kinds == ["stack_store", "ip_advance"] {
            return "slot_load".into();
        }
        return "indexed_unknown".into();
    }

    if parts.is_empty() {
        return "nop".into();
    }
    if text.contains("yield") {
        return "yield".into();
    }
    if parts.iter().any(|part| part.starts_with("throw ")) {
        return "throw".into();
    }
    if terminal == "return" {
        return if !text.contains("stack_pop()") && text.contains("stack[") {
            "return_peek".into()
        } else {
            "return".into()
        };
    }
    if regex_is(r"stack_pop\(\)\|\|\(ip=", &text) {
        return "jump_if_falsy".into();
    }
    if regex_is(r"stack_pop\(\)&&\(ip=", &text) {
        return "jump_if_truthy".into();
    }
    if parts.len() == 1 && parts[0] == "ip=read_u16()" {
        return "jump".into();
    }
    if parts.len() == 1 && parts[0] == "stack_pop()" {
        return "pop".into();
    }
    if text.contains("control_stack.pop()") {
        return "control_pop".into();
    }
    if text.contains("control_stack")
        && (text.contains(".push({") || regex_is(r"control_stack\[[^\]]+\]\(\{", &text))
    {
        return "control_push".into();
    }
    if text.contains("for(") && text.contains("=env;") && text.contains("||env)[") {
        return "env_store".into();
    }
    if text.contains("Object")
        && text.contains("(env)")
        && text.contains("function(...e)")
        && text.contains("ip+=")
    {
        return "closure_create".into();
    }
    if (text.contains("Reflect.") || text.contains("Reflect["))
        && text.contains("stack_push")
        && text.contains("stack_pop()")
    {
        return "construct".into();
    }
    if text.contains("stack_push(function(){switch(read_byte())") {
        return "push_literal".into();
    }
    if text.contains("if(!stack") && text.contains("stack_push(stack[") {
        return "dup".into();
    }
    if text.contains("for(")
        && regex_is(r"=2\*", &text)
        && regex_is(r"=\{\}", &text)
        && text.contains("stack_push")
    {
        return "object_from_pairs".into();
    }
    if text.contains("stack_push(env_lookup(read_string()))") {
        return "env_load".into();
    }
    if text.contains("env_lookup(") && text.contains("stack_push") && text.contains("...") {
        return "env_call".into();
    }
    if text.contains(" in env?") && text.contains("env_fallback") && text.contains("stack_push") {
        return "env_load_soft".into();
    }
    if text.contains(" in ") && text.contains("throw Error") && text.contains("stack_push") {
        return "global_load_checked".into();
    }
    if regex_is(r"\[[^\]]+\]=[^;]+", &text) && text.contains("stack_push") {
        return "property_set".into();
    }

    // Method calls survive in several equivalent encodings:
    // receiver[prop].call(receiver, ...args), receiver[prop][decoded_call](receiver,...),
    // or a member saved to a temporary before decoded invocation.
    if text.contains("read_string()") && text.contains("stack_push") && text.contains("...") {
        if text.contains(".call(")
            || regex_is(
                r"[A-Za-z_$][A-Za-z0-9_$]*\[[^\]]+\]\[[^\]]+\]\([A-Za-z_$][A-Za-z0-9_$]*,\.\.\.",
                &text,
            )
        {
            return "method_call".into();
        }
        if let Some(caps) =
            Regex::new(r",([A-Za-z_$][A-Za-z0-9_$]*)=([A-Za-z_$][A-Za-z0-9_$]*)\[[^\]]+\]")
                .ok()
                .and_then(|re| re.captures(&text))
        {
            let temp = regex::escape(&caps[1]);
            let receiver = regex::escape(&caps[2]);
            let pattern = format!(r"stack_push\({temp}\[[^\]]+\]\({receiver},\.\.\.");
            if regex_is(&pattern, &text) {
                return "method_call".into();
            }
        }
    }
    if text.contains("read_string()")
        && text.contains("stack_push")
        && regex_is(r"stack_push\([^;]*\[[^\]]+\]\)", &text)
    {
        return "property_get".into();
    }
    if regex_is(r"stack_push\([^;]*\[[^\]]+\]\)", &text) && text.contains("stack_pop()") {
        return "property_get".into();
    }
    if text.contains("stack_push([") && text.contains("...") {
        return "spread_concat".into();
    }
    if text.contains("read_u16()")
        && text.contains("stack_push(")
        && (text.contains("splice(") || regex_is(r"stack\[[^\]]+\]\(", &text))
    {
        return "collect_args".into();
    }
    if text.contains("stack_push") && text.contains("...") && text.contains("stack_pop()") {
        return "call".into();
    }
    if text.contains("read_byte()")
        && text.contains("stack_push")
        && regex_is(r"\[[A-Za-z_$][A-Za-z0-9_$]*\]\(", &text)
    {
        return "operator_dispatch".into();
    }
    if kinds == ["dynamic_call"] {
        return "control_pop".into();
    }
    if text.contains("stack_push") {
        return "push_value".into();
    }
    "call_unknown".into()
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

    let functions: HashMap<_, _> = report
        .functions
        .iter()
        .map(|f| (f.id.as_str(), f))
        .collect();

    let mut vms = Vec::new();
    for map in report.direct_switch_maps.iter().filter(|m| m.confirmed_vm) {
        let Some(function) = functions.get(map.parent_function_id.as_str()).copied() else {
            continue;
        };
        let function_text = function_source(&source, function);
        let semantics = all_semantics(map);

        let prefix_len = map
            .start
            .saturating_sub(function.start)
            .min(function.end.saturating_sub(function.start)) as usize;
        let function_prefix = function_text.get(..prefix_len).unwrap_or(function_text);

        let (selector_style, roles, helpers) = if let Some(helper) = call_selector(&map.selector) {
            let (roles, helpers) = call_family_roles(function_prefix, &semantics, &helper);
            ("call".to_string(), roles, helpers)
        } else {
            let (roles, helpers) = indexed_family_roles(map, &semantics);
            ("indexed".to_string(), roles, helpers)
        };

        let mut handlers = Vec::new();
        for handler in &map.handlers {
            let mut effects = Vec::new();
            let mut signature = Vec::new();
            for semantic in &handler.semantic {
                for effect in split_effects(semantic) {
                    let normalized = normalize(&effect, &roles, &helpers);
                    let ir = classify_effect(&normalized);
                    signature.push(format!("{}:{}", ir.kind, ir.shape_hash));
                    effects.push(HandlerEffectIr {
                        source: effect,
                        normalized,
                        ir,
                    });
                }
            }
            signature.push(format!("terminal:{}", handler.terminal));
            let semantic_label = infer_semantic_label(&selector_style, &handler.terminal, &effects);
            let semantic_hash = format!("{:016x}", fnv1a64(signature.join("|").as_bytes()));
            let coarse_semantic_hash = format!("{:016x}", fnv1a64(semantic_label.as_bytes()));
            handlers.push(SwitchHandlerIr {
                opcode: handler.key,
                key_source: handler.key_source.clone(),
                terminal: handler.terminal.clone(),
                semantic_label,
                semantic_hash,
                coarse_semantic_hash,
                op_kinds: effects
                    .iter()
                    .map(|effect| effect.ir.kind.clone())
                    .collect(),
                effects,
            });
        }

        vms.push(SwitchVmIr {
            parent_function_id: map.parent_function_id.clone(),
            function_name: function.name.clone(),
            function_start: function.start,
            function_end: function.end,
            switch_start: map.start,
            switch_end: map.end,
            selector: map.selector.clone(),
            selector_style,
            numeric_cases: map.numeric_cases,
            opcode_max: map.opcode_max,
            vm_evidence_score: map.vm_evidence_score,
            vm_reasons: map.vm_reasons.clone(),
            role_bindings: roles,
            helper_bindings: helpers,
            handlers,
        });
    }

    let output = Output {
        schema: "jsvm-switch-ir/v0",
        source: args.source.display().to_string(),
        vms,
    };
    fs::write(
        &args.output,
        format!("{}\n", serde_json::to_string_pretty(&output)?),
    )
    .with_context(|| format!("writing {}", args.output.display()))?;

    let handler_count: usize = output.vms.iter().map(|vm| vm.handlers.len()).sum();
    let effect_count: usize = output
        .vms
        .iter()
        .flat_map(|vm| &vm.handlers)
        .map(|handler| handler.effects.len())
        .sum();
    let raw_count: usize = output
        .vms
        .iter()
        .flat_map(|vm| &vm.handlers)
        .flat_map(|handler| &handler.effects)
        .filter(|effect| matches!(effect.ir.kind.as_str(), "raw_js" | "raw_expression"))
        .count();
    println!(
        "switch IR VMs {} handlers {} effects {} classified {} raw {}",
        output.vms.len(),
        handler_count,
        effect_count,
        effect_count.saturating_sub(raw_count),
        raw_count
    );
    for vm in &output.vms {
        println!(
            "{} {:?} style={} handlers={} roles={:?} helpers={:?}",
            vm.parent_function_id,
            vm.function_name,
            vm.selector_style,
            vm.handlers.len(),
            vm.role_bindings,
            vm.helper_bindings,
        );
    }
    println!("wrote {}", args.output.display());
    Ok(())
}
