use crate::analysis_artifacts::{load_artifact, write_artifact, JSVM_INDEX};
use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use serde_json::{json, Map, Value};
use std::{
    collections::BTreeMap,
    fs,
    path::{Component, Path, PathBuf},
};

const SWITCH_IR_SCHEMA: &str = "jsvm-switch-ir/v0";
const TABLE_IR_SCHEMA: &str = "jsvm-table-ir/v0";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaterializeSummary {
    pub devirtualized_units: usize,
    pub switch_vms: usize,
    pub table_vms: usize,
}

#[derive(Debug, Deserialize)]
struct SwitchIrDocument {
    schema: String,
    #[serde(default)]
    vms: Vec<SwitchVm>,
}

#[derive(Debug, Deserialize)]
struct SwitchVm {
    parent_function_id: String,
    function_name: Option<String>,
    function_start: u64,
    function_end: u64,
    switch_start: u64,
    switch_end: u64,
    selector: String,
    selector_style: String,
    #[serde(default)]
    role_bindings: BTreeMap<String, String>,
    #[serde(default)]
    helper_bindings: BTreeMap<String, String>,
    #[serde(default)]
    handlers: Vec<SwitchHandler>,
}

#[derive(Debug, Deserialize)]
struct SwitchHandler {
    opcode: Option<u64>,
    semantic_label: String,
    semantic_hash: String,
    coarse_semantic_hash: String,
    #[serde(default)]
    effects: Vec<SwitchEffect>,
}

#[derive(Debug, Deserialize)]
struct SwitchEffect {
    #[serde(default)]
    source: String,
    #[serde(default)]
    normalized: String,
}

#[derive(Debug, Deserialize)]
struct TableIrDocument {
    schema: String,
    #[serde(default)]
    vms: Vec<TableVm>,
}

#[derive(Debug, Deserialize, Serialize)]
struct TableVm {
    dispatcher_function_id: String,
    handler_table: String,
    handler_count: usize,
    architecture: String,
    producer_method: Option<String>,
    linked_transducer: Option<Value>,
    #[serde(default)]
    role_bindings: BTreeMap<String, String>,
    #[serde(default)]
    method_bindings: BTreeMap<String, String>,
    #[serde(default)]
    handlers: Vec<TableHandler>,
}

#[derive(Debug, Deserialize, Serialize)]
struct TableHandler {
    key: String,
    start: u64,
    end: u64,
    parameter: Option<String>,
    semantic_hash: String,
    #[serde(default)]
    op_kinds: Vec<String>,
    #[serde(default)]
    statements: Vec<TableStatement>,
}

#[derive(Debug, Deserialize, Serialize)]
struct TableStatement {
    #[serde(default)]
    source: String,
    #[serde(default)]
    normalized: String,
    #[serde(default)]
    ir: Value,
}

fn safe_name(value: Option<&str>) -> String {
    let mut out = String::new();
    let mut pending_dash = false;
    for ch in value.unwrap_or("anon").chars() {
        if ch.is_ascii_alphanumeric() || matches!(ch, '.' | '_' | '-') {
            if pending_dash && !out.is_empty() {
                out.push('-');
            }
            pending_dash = false;
            out.push(ch);
        } else {
            pending_dash = true;
        }
    }
    let trimmed = out.trim_matches('-');
    let limited = trimmed.chars().take(80).collect::<String>();
    if limited.is_empty() {
        "anon".to_owned()
    } else {
        limited
    }
}

fn pseudo_for(label: &str) -> String {
    match label {
        "nop" => "no operation".into(),
        "pop" => "discard(pop())".into(),
        "dup" => "push(peek())".into(),
        "push_null" => "push(null)".into(),
        "push_undefined" => "push(undefined)".into(),
        "increment" => "push(to_numeric(pop()) + 1)".into(),
        "decrement" => "push(to_numeric(pop()) - 1)".into(),
        "to_number" => "push(to_numeric(pop()))".into(),
        "add" => "rhs = pop(); lhs = pop(); push(lhs + rhs)".into(),
        "sub" => "rhs = pop(); lhs = pop(); push(lhs - rhs)".into(),
        "mul" => "rhs = pop(); lhs = pop(); push(lhs * rhs)".into(),
        "div" => "rhs = pop(); lhs = pop(); push(lhs / rhs)".into(),
        "mod" => "rhs = pop(); lhs = pop(); push(lhs % rhs)".into(),
        "lt" => "rhs = pop(); lhs = pop(); push(lhs < rhs)".into(),
        "lte" => "rhs = pop(); lhs = pop(); push(lhs <= rhs)".into(),
        "gt" => "rhs = pop(); lhs = pop(); push(lhs > rhs)".into(),
        "gte" => "rhs = pop(); lhs = pop(); push(lhs >= rhs)".into(),
        "strict_eq" => "rhs = pop(); lhs = pop(); push(lhs === rhs)".into(),
        "strict_neq" => "rhs = pop(); lhs = pop(); push(lhs !== rhs)".into(),
        "loose_eq" => "rhs = pop(); lhs = pop(); push(lhs == rhs)".into(),
        "loose_neq" => "rhs = pop(); lhs = pop(); push(lhs != rhs)".into(),
        "property_get" => "key = pop(); object = pop(); push(object[key])".into(),
        "property_set" => {
            "value = pop(); key/object = pop operands; object[key] = value; push(value)".into()
        }
        "slot_load" => "push(vm_slot[operand])".into(),
        "slot_store" => "vm_slot[operand] = pop()".into(),
        "jump" => "ip = branch_target".into(),
        "jump_if_truthy" => "if (pop()) ip = branch_target; else advance()".into(),
        "jump_if_falsy" => "if (!pop()) ip = branch_target; else advance()".into(),
        "conditional_jump" => "branch on pop() and update ip".into(),
        "env_load" => "push(resolve_lexical(read_string()))".into(),
        "env_load_soft" => "push(env[name] ?? fallback_env[name] ?? undefined)".into(),
        "global_load_checked" => "require named global; push(global[name])".into(),
        "env_store" => "assign nearest lexical owner of name".into(),
        "env_call" => "fn = resolve_lexical(name); push(fn(...args))".into(),
        "call" => "fn = pop(); push(fn(...args))".into(),
        "method_call" => {
            "receiver = pop(); method = receiver[name]; push(method.call(receiver, ...args))".into()
        }
        "construct" => "ctor = pop(); push(Reflect.construct(ctor, args))".into(),
        "operator_dispatch" => {
            "operator = operator_table[read_byte()]; push(operator(...operands))".into()
        }
        "collect_args" => "push(pop_n(read_u16()))".into(),
        "spread_concat" => "push([...lhs, ...rhs])".into(),
        "object_from_pairs" => {
            "pairs = pop_n(2 * read_u16()); push(object_from_pairs(pairs))".into()
        }
        "push_literal" => "decode literal from bytecode and push it".into(),
        "closure_create" => "capture lexical environment; push nested VM-backed function".into(),
        "control_push" => "push exception/control frame".into(),
        "control_pop" => "pop exception/control frame".into(),
        "yield" => "value = yield pop(); push(value)".into(),
        "return" => "return stack empty ? undefined : pop()".into(),
        "return_peek" => "return stack empty ? undefined : peek()".into(),
        "throw" => "throw pop()".into(),
        "push_value" => "push(value)".into(),
        _ => format!("semantic operation: {label}"),
    }
}

fn control_for(label: &str) -> &'static str {
    match label {
        "jump" => "jump",
        "jump_if_truthy" | "jump_if_falsy" | "conditional_jump" => "conditional_branch",
        "return" | "return_peek" => "return",
        "throw" => "throw",
        "yield" => "yield",
        _ => "fallthrough",
    }
}

fn checked_project_path(project: &Path, relative: &str, label: &str) -> Result<PathBuf> {
    if relative.is_empty() || relative.contains('\\') {
        bail!("{label}: expected a non-empty project-relative POSIX path");
    }
    let bytes = relative.as_bytes();
    if bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':' {
        bail!("{label}: drive-qualified path is not allowed");
    }
    let path = Path::new(relative);
    if path.is_absolute()
        || path.components().any(|component| {
            matches!(
                component,
                Component::ParentDir | Component::RootDir | Component::Prefix(_)
            )
        })
    {
        bail!("{label}: path must stay inside the capture project");
    }
    Ok(project.join(path))
}

fn read_switch_ir(project: &Path, relative: &str) -> Result<SwitchIrDocument> {
    let path = checked_project_path(project, relative, "switch_ir")?;
    let document: SwitchIrDocument = serde_json::from_str(
        &fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?,
    )
    .with_context(|| format!("parsing {}", path.display()))?;
    if document.schema != SWITCH_IR_SCHEMA {
        bail!(
            "{}: expected schema {SWITCH_IR_SCHEMA:?}, got {:?}",
            path.display(),
            document.schema
        );
    }
    Ok(document)
}

fn read_table_ir(project: &Path, relative: &str) -> Result<TableIrDocument> {
    let path = checked_project_path(project, relative, "table_ir")?;
    let document: TableIrDocument = serde_json::from_str(
        &fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?,
    )
    .with_context(|| format!("parsing {}", path.display()))?;
    if document.schema != TABLE_IR_SCHEMA {
        bail!(
            "{}: expected schema {TABLE_IR_SCHEMA:?}, got {:?}",
            path.display(),
            document.schema
        );
    }
    Ok(document)
}

fn optional_text<'a>(object: &'a Map<String, Value>, key: &str) -> Option<&'a str> {
    object.get(key).and_then(Value::as_str)
}

fn field(object: &Map<String, Value>, key: &str) -> Value {
    object.get(key).cloned().unwrap_or(Value::Null)
}

fn render_switch_pseudocode(vm: &SwitchVm, provenance: &Map<String, Value>) -> String {
    let function_name = vm.function_name.as_deref().unwrap_or("<anonymous>");
    let url = optional_text(provenance, "url").unwrap_or("None");
    let mut lines = vec![
        "Generated semantic pseudocode for a captured JavaScript VM.".to_owned(),
        "This is analyst-oriented approximate semantics, NOT an executable replacement.".to_owned(),
        String::new(),
        format!("resource: {url}"),
        format!("function: {function_name} ({})", vm.parent_function_id),
        format!(
            "selector style: {}  selector: {}",
            vm.selector_style, vm.selector
        ),
        format!("function span: {}..{}", vm.function_start, vm.function_end),
        format!("switch span: {}..{}", vm.switch_start, vm.switch_end),
        String::new(),
        "roles:".to_owned(),
    ];
    for (role, original) in &vm.role_bindings {
        lines.push(format!("  {role:16} <- {original}"));
    }
    if !vm.helper_bindings.is_empty() {
        lines.push("helpers:".to_owned());
        for (role, original) in &vm.helper_bindings {
            lines.push(format!("  {role:16} <- {original}"));
        }
    }
    lines.push(String::new());

    let mut handlers = vm.handlers.iter().collect::<Vec<_>>();
    handlers.sort_by_key(|handler| (handler.opcode.is_none(), handler.opcode.unwrap_or(u64::MAX)));
    for handler in handlers {
        let key = handler
            .opcode
            .map_or_else(|| "default".to_owned(), |opcode| opcode.to_string());
        let label = &handler.semantic_label;
        lines.extend([
            format!("opcode {key:>7}  {label}  [{}]", control_for(label)),
            format!("  pseudo: {}", pseudo_for(label)),
            format!("  exact semantic hash:  {}", handler.semantic_hash),
            format!("  coarse semantic hash: {}", handler.coarse_semantic_hash),
        ]);
        let normalized = handler
            .effects
            .iter()
            .map(|effect| effect.normalized.as_str())
            .collect::<Vec<_>>();
        let original = handler
            .effects
            .iter()
            .map(|effect| effect.source.as_str())
            .collect::<Vec<_>>();
        if !normalized.is_empty() {
            lines.push("  normalized:".to_owned());
            lines.extend(normalized.iter().map(|line| format!("    {line}")));
        }
        if original != normalized && !original.is_empty() {
            lines.push("  original:".to_owned());
            lines.extend(original.iter().map(|line| format!("    {line}")));
        }
        lines.push(String::new());
    }
    format!("{}\n", lines.join("\n").trim_end())
}

fn render_table_pseudocode(vm: &TableVm, provenance: &Map<String, Value>) -> String {
    let url = optional_text(provenance, "url").unwrap_or("None");
    let mut lines = vec![
        "Generated semantic pseudocode for a captured function-table JavaScript VM.".to_owned(),
        "This is analyst-oriented approximate semantics, NOT an executable replacement.".to_owned(),
        String::new(),
        format!("resource: {url}"),
        format!("handler table: {}", vm.handler_table),
        format!("dispatcher: {}", vm.dispatcher_function_id),
        format!("architecture: {}", vm.architecture),
        format!("handlers: {}", vm.handlers.len()),
        String::new(),
        "roles:".to_owned(),
    ];
    for (role, original) in &vm.role_bindings {
        lines.push(format!("  {role:20} <- {original}"));
    }
    if !vm.method_bindings.is_empty() {
        lines.push("methods:".to_owned());
        for (original, role) in &vm.method_bindings {
            lines.push(format!("  {role:20} <- {original}"));
        }
    }
    lines.push(String::new());

    let mut handlers = vm.handlers.iter().collect::<Vec<_>>();
    handlers.sort_by(|left, right| {
        let left_num = left.key.parse::<i128>();
        let right_num = right.key.parse::<i128>();
        match (left_num, right_num) {
            (Ok(left), Ok(right)) => left.cmp(&right),
            (Ok(_), Err(_)) => std::cmp::Ordering::Less,
            (Err(_), Ok(_)) => std::cmp::Ordering::Greater,
            (Err(_), Err(_)) => left.key.cmp(&right.key),
        }
    });
    for handler in handlers {
        lines.extend([
            format!(
                "handler {}  semantic={}",
                handler.key, handler.semantic_hash
            ),
            format!("  op kinds: {}", handler.op_kinds.join(", ")),
        ]);
        for statement in &handler.statements {
            let kind = statement
                .ir
                .get("kind")
                .and_then(Value::as_str)
                .unwrap_or("unknown");
            let normalized = if statement.normalized.is_empty() {
                &statement.source
            } else {
                &statement.normalized
            };
            lines.push(format!("  [{kind}] {normalized}"));
        }
        lines.push(String::new());
    }
    format!("{}\n", lines.join("\n").trim_end())
}

fn write_js_module(path: &Path, header: &str, pseudo_name: &str, payload: &Value) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    let encoded = serde_json::to_string_pretty(payload)?;
    fs::write(
        path,
        format!(
            "// {header}\n// Provenance-preserving analyst output; not an executable replacement.\n// Human-first listing: {pseudo_name}\nexport default {encoded};\n"
        ),
    )
    .with_context(|| format!("writing {}", path.display()))
}

fn materialize_switch_vms(
    project: &Path,
    row: &Map<String, Value>,
    scan_id: u64,
    relative_ir: &str,
) -> Result<Vec<Value>> {
    let ir = read_switch_ir(project, relative_ir)?;
    let mut units = Vec::new();
    for (index, vm) in ir.vms.iter().enumerate() {
        let ordinal = index + 1;
        let stem = safe_name(
            vm.function_name
                .as_deref()
                .or(Some(vm.parent_function_id.as_str())),
        );
        let base = PathBuf::from("src/_devirtualized")
            .join(format!("{scan_id:04}"))
            .join(format!("switch-vm-{ordinal:02}-{stem}"));
        let rel = base.with_extension("js");
        let pseudo_rel = base.with_extension("pseudo.txt");
        let out = project.join(&rel);
        let pseudo_out = project.join(&pseudo_rel);

        let mut provenance = Map::new();
        for key in [
            "resource_id",
            "url",
            "raw_path",
            "path",
            "analysis_origin",
            "report",
        ] {
            provenance.insert(key.to_owned(), field(row, key));
        }
        let captured_raw = provenance.remove("raw_path").unwrap_or(Value::Null);
        let analysis_path = provenance.remove("path").unwrap_or(Value::Null);
        let scan_report = provenance.remove("report").unwrap_or(Value::Null);
        provenance.insert("captured_raw_path".into(), captured_raw);
        provenance.insert("analysis_path".into(), analysis_path);
        provenance.insert("scan_report".into(), scan_report);
        provenance.insert("switch_ir".into(), Value::String(relative_ir.to_owned()));
        provenance.insert(
            "parent_function_id".into(),
            Value::String(vm.parent_function_id.clone()),
        );
        provenance.insert("function_start".into(), Value::from(vm.function_start));
        provenance.insert("function_end".into(), Value::from(vm.function_end));
        provenance.insert("switch_start".into(), Value::from(vm.switch_start));
        provenance.insert("switch_end".into(), Value::from(vm.switch_end));

        let handlers = vm
            .handlers
            .iter()
            .map(|handler| {
                let label = &handler.semantic_label;
                json!({
                    "opcode": handler.opcode,
                    "label": label,
                    "control": control_for(label),
                    "pseudocode": pseudo_for(label),
                    "semantic_hash": handler.semantic_hash,
                    "coarse_semantic_hash": handler.coarse_semantic_hash,
                    "normalized": handler.effects.iter().map(|effect| effect.normalized.clone()).collect::<Vec<_>>(),
                    "original": handler.effects.iter().map(|effect| effect.source.clone()).collect::<Vec<_>>(),
                })
            })
            .collect::<Vec<_>>();
        let opcode_map = vm
            .handlers
            .iter()
            .filter_map(|handler| {
                handler.opcode.map(|opcode| {
                    (
                        opcode.to_string(),
                        Value::String(handler.semantic_label.clone()),
                    )
                })
            })
            .collect::<Map<String, Value>>();
        let payload = json!({
            "schema": "jsvm-readable-switch-module/v1",
            "provenance": provenance,
            "function_name": vm.function_name,
            "selector": vm.selector,
            "selector_style": vm.selector_style,
            "role_bindings": vm.role_bindings,
            "helper_bindings": vm.helper_bindings,
            "opcode_map": opcode_map,
            "handlers": handlers,
        });
        let pseudo_name = pseudo_rel
            .file_name()
            .and_then(|value| value.to_str())
            .context("generated pseudocode path is not UTF-8")?;
        write_js_module(
            &out,
            "Generated semantic view of a captured JavaScript VM.",
            pseudo_name,
            &payload,
        )?;
        fs::write(&pseudo_out, render_switch_pseudocode(vm, &provenance))
            .with_context(|| format!("writing {}", pseudo_out.display()))?;

        units.push(json!({
            "vm_kind": "direct_switch",
            "parent_scan_id": scan_id,
            "resource_id": field(row, "resource_id"),
            "vm_ordinal": ordinal,
            "parent_function_id": vm.parent_function_id,
            "function_name": vm.function_name,
            "function_start": vm.function_start,
            "function_end": vm.function_end,
            "switch_start": vm.switch_start,
            "switch_end": vm.switch_end,
            "selector_style": vm.selector_style,
            "handler_count": vm.handlers.len(),
            "source_path": rel.to_string_lossy(),
            "pseudocode_path": pseudo_rel.to_string_lossy(),
            "ir_path": relative_ir,
        }));
    }
    Ok(units)
}

fn materialize_table_vms(
    project: &Path,
    row: &Map<String, Value>,
    scan_id: u64,
    relative_ir: &str,
) -> Result<Vec<Value>> {
    let ir = read_table_ir(project, relative_ir)?;
    let mut units = Vec::new();
    for (index, vm) in ir.vms.iter().enumerate() {
        let ordinal = index + 1;
        let stem = safe_name(Some(&vm.handler_table));
        let base = PathBuf::from("src/_devirtualized")
            .join(format!("{scan_id:04}"))
            .join(format!("table-vm-{ordinal:02}-{stem}"));
        let rel = base.with_extension("js");
        let pseudo_rel = base.with_extension("pseudo.txt");
        let out = project.join(&rel);
        let pseudo_out = project.join(&pseudo_rel);

        let mut provenance = Map::new();
        provenance.insert("resource_id".into(), field(row, "resource_id"));
        provenance.insert("url".into(), field(row, "url"));
        provenance.insert("captured_raw_path".into(), field(row, "raw_path"));
        provenance.insert("analysis_path".into(), field(row, "path"));
        provenance.insert("analysis_origin".into(), field(row, "analysis_origin"));
        provenance.insert("scan_report".into(), field(row, "report"));
        provenance.insert("table_ir".into(), Value::String(relative_ir.to_owned()));
        provenance.insert("parent_scan_id".into(), Value::from(scan_id));

        let payload = json!({
            "schema": "jsvm-readable-table-module/v1",
            "provenance": provenance,
            "dispatcher_function_id": vm.dispatcher_function_id,
            "handler_table": vm.handler_table,
            "handler_count": vm.handler_count,
            "architecture": vm.architecture,
            "producer_method": vm.producer_method,
            "linked_transducer": vm.linked_transducer,
            "role_bindings": vm.role_bindings,
            "method_bindings": vm.method_bindings,
            "handlers": vm.handlers,
        });
        let pseudo_name = pseudo_rel
            .file_name()
            .and_then(|value| value.to_str())
            .context("generated pseudocode path is not UTF-8")?;
        write_js_module(
            &out,
            "Generated semantic view of a captured function-table JavaScript VM.",
            pseudo_name,
            &payload,
        )?;
        fs::write(&pseudo_out, render_table_pseudocode(vm, &provenance))
            .with_context(|| format!("writing {}", pseudo_out.display()))?;

        units.push(json!({
            "vm_kind": "function_table",
            "parent_scan_id": scan_id,
            "resource_id": field(row, "resource_id"),
            "vm_ordinal": ordinal,
            "parent_function_id": vm.dispatcher_function_id,
            "function_name": Value::Null,
            "handler_table": vm.handler_table,
            "architecture": vm.architecture,
            "handler_count": vm.handlers.len(),
            "source_path": rel.to_string_lossy(),
            "pseudocode_path": pseudo_rel.to_string_lossy(),
            "ir_path": relative_ir,
        }));
    }
    Ok(units)
}

pub fn materialize_project(project: &Path) -> Result<MaterializeSummary> {
    let Some(mut index) = load_artifact(project, JSVM_INDEX, true)? else {
        return Ok(MaterializeSummary {
            devirtualized_units: 0,
            switch_vms: 0,
            table_vms: 0,
        });
    };
    let object = index
        .as_object_mut()
        .context("JS VM analysis index root must be an object")?;
    let rows = object
        .get_mut("code_units")
        .and_then(Value::as_array_mut)
        .context("JS VM analysis index code_units must be an array")?;

    let mut all_units = Vec::new();
    let mut switch_vms = 0_usize;
    let mut table_vms = 0_usize;
    for (row_index, row) in rows.iter_mut().enumerate() {
        let row = row
            .as_object_mut()
            .with_context(|| format!("code_units[{row_index}] must be an object"))?;
        row.remove("devirtualized_units");
        let scan_id = row
            .get("scan_id")
            .and_then(Value::as_u64)
            .with_context(|| {
                format!("code_units[{row_index}].scan_id must be a non-negative integer")
            })?;
        let switch_ir = row
            .get("switch_ir")
            .and_then(Value::as_str)
            .map(ToOwned::to_owned);
        let table_ir = row
            .get("table_ir")
            .and_then(Value::as_str)
            .map(ToOwned::to_owned);

        let mut units = Vec::new();
        if let Some(relative) = switch_ir {
            let created = materialize_switch_vms(project, row, scan_id, &relative)?;
            switch_vms += created.len();
            units.extend(created);
        }
        if let Some(relative) = table_ir {
            let created = materialize_table_vms(project, row, scan_id, &relative)?;
            table_vms += created.len();
            units.extend(created);
        }
        row.insert("devirtualized_units".into(), Value::Array(units.clone()));
        all_units.extend(units);
    }
    object.insert(
        "devirtualized_units".into(),
        Value::Array(all_units.clone()),
    );
    write_artifact(project, JSVM_INDEX, &index)?;
    Ok(MaterializeSummary {
        devirtualized_units: all_units.len(),
        switch_vms,
        table_vms,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis_artifacts::{write_artifact, JSVM_INDEX};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn test_project() -> Result<PathBuf> {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let path =
            std::env::temp_dir().join(format!("jsvm-materialize-{}-{nonce}", std::process::id()));
        fs::create_dir_all(path.join("analysis/jsvm"))?;
        Ok(path)
    }

    #[test]
    fn materializes_switch_and_table_views_and_updates_index() -> Result<()> {
        let project = test_project()?;
        let result = (|| -> Result<()> {
            let index = json!({
                "schema": JSVM_INDEX.schema,
                "code_units": [{
                    "scan_id": 7,
                    "resource_id": 42,
                    "url": "https://example.test/app.js",
                    "raw_path": "resources/app.js",
                    "path": "src/app.js",
                    "analysis_origin": "safe_deobfuscated",
                    "report": "analysis/jsvm/0007.json",
                    "switch_ir": "analysis/jsvm/0007.switch.json",
                    "table_ir": "analysis/jsvm/0007.table.json"
                }],
                "dynamic_code_units": []
            });
            write_artifact(&project, JSVM_INDEX, &index)?;
            fs::write(
                project.join("analysis/jsvm/0007.switch.json"),
                serde_json::to_string_pretty(&json!({
                    "schema": SWITCH_IR_SCHEMA,
                    "source": "src/app.js",
                    "vms": [{
                        "parent_function_id": "fn:1",
                        "function_name": "dispatch weird/name",
                        "function_start": 10,
                        "function_end": 90,
                        "switch_start": 30,
                        "switch_end": 80,
                        "selector": "ops[ip]",
                        "selector_style": "indexed",
                        "role_bindings": {"ip": "i"},
                        "helper_bindings": {},
                        "handlers": [{
                            "opcode": 3,
                            "semantic_label": "add",
                            "semantic_hash": "exact",
                            "coarse_semantic_hash": "coarse",
                            "effects": [{"source": "a+b", "normalized": "lhs+rhs", "ir": {"kind": "binary"}}]
                        }]
                    }]
                }))?,
            )?;
            fs::write(
                project.join("analysis/jsvm/0007.table.json"),
                serde_json::to_string_pretty(&json!({
                    "schema": TABLE_IR_SCHEMA,
                    "source": "src/app.js",
                    "vms": [{
                        "dispatcher_function_id": "fn:2",
                        "handler_table": "handlers",
                        "handler_count": 1,
                        "architecture": "function_table",
                        "producer_method": null,
                        "linked_transducer": null,
                        "role_bindings": {"control_stack": "frames"},
                        "method_bindings": {"ctx.getByte": "read_byte"},
                        "handlers": [{
                            "key": "0",
                            "start": 100,
                            "end": 120,
                            "parameter": "ctx",
                            "semantic_hash": "table-exact",
                            "op_kinds": ["read_byte"],
                            "statements": [{"source": "ctx.getByte()", "normalized": "read_byte()", "ir": {"kind": "read_byte"}}]
                        }]
                    }]
                }))?,
            )?;

            let summary = materialize_project(&project)?;
            assert_eq!(
                summary,
                MaterializeSummary {
                    devirtualized_units: 2,
                    switch_vms: 1,
                    table_vms: 1,
                }
            );
            let switch_path =
                project.join("src/_devirtualized/0007/switch-vm-01-dispatch-weird-name.js");
            let table_path = project.join("src/_devirtualized/0007/table-vm-01-handlers.js");
            assert!(switch_path.is_file());
            assert!(table_path.is_file());
            let switch_text = fs::read_to_string(switch_path)?;
            assert!(switch_text.contains("jsvm-readable-switch-module/v1"));
            assert!(switch_text.contains("rhs = pop(); lhs = pop(); push(lhs + rhs)"));
            let pseudo = fs::read_to_string(
                project.join("src/_devirtualized/0007/switch-vm-01-dispatch-weird-name.pseudo.txt"),
            )?;
            assert!(pseudo.contains("opcode       3  add  [fallthrough]"));

            let updated = load_artifact(&project, JSVM_INDEX, false)?
                .context("updated JS VM index missing")?;
            assert_eq!(
                updated
                    .get("devirtualized_units")
                    .and_then(Value::as_array)
                    .map(Vec::len),
                Some(2)
            );
            assert_eq!(
                updated
                    .get("code_units")
                    .and_then(Value::as_array)
                    .and_then(|rows| rows.first())
                    .and_then(|row| row.get("devirtualized_units"))
                    .and_then(Value::as_array)
                    .map(Vec::len),
                Some(2)
            );
            Ok(())
        })();
        let cleanup = fs::remove_dir_all(&project);
        result?;
        cleanup?;
        Ok(())
    }

    #[test]
    fn refuses_ir_paths_that_escape_the_project() -> Result<()> {
        let project = test_project()?;
        let result = (|| -> Result<()> {
            let index = json!({
                "schema": JSVM_INDEX.schema,
                "code_units": [{"scan_id": 0, "switch_ir": "../escape.json"}],
                "dynamic_code_units": []
            });
            write_artifact(&project, JSVM_INDEX, &index)?;
            assert!(materialize_project(&project).is_err());
            Ok(())
        })();
        let cleanup = fs::remove_dir_all(&project);
        result?;
        cleanup?;
        Ok(())
    }
}
