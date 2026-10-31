use crate::{
    analysis_artifacts::{
        load_artifact, write_artifact, DEOBFUSCATION, WASM_INDEX, WASM_JS_BOUNDARY,
    },
    content_dedup::sha256_path,
    wasm_import_semantics::{proven_wasm_import_semantics, proven_wasm_import_semantics_for},
};
use anyhow::{Context, Result};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
};
use wasm_redox::fresh_eval::{
    evaluate_fresh_i32_call, evaluate_fresh_i32_sequence, FreshEvalOutcome, FreshI32Arg,
    FreshI32CallRequest, FreshTableGrowRequest,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmJsBoundarySummary {
    pub host_effect_pairs: usize,
    pub proven_js_set_u32_shapes: usize,
    pub copied_input_candidates: usize,
    pub proven_js_typed_array_copy_semantics: usize,
    pub proven_module_memory_identities: usize,
    pub proven_destination_load_interpretations: usize,
}

fn read_json(path: &Path) -> Result<Value> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    serde_json::from_str(&text).with_context(|| format!("parsing {}", path.display()))
}

fn array_field<'a>(value: &'a Value, field: &str) -> &'a [Value] {
    value
        .get(field)
        .and_then(Value::as_array)
        .map_or(&[], Vec::as_slice)
}

fn string_field<'a>(value: &'a Value, field: &str) -> Option<&'a str> {
    value.get(field).and_then(Value::as_str)
}

fn usize_field(value: &Value, field: &str) -> Option<usize> {
    value
        .get(field)
        .and_then(Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
}

fn u32_field(value: &Value, field: &str) -> Option<u32> {
    value
        .get(field)
        .and_then(Value::as_u64)
        .and_then(|value| u32::try_from(value).ok())
}

fn i64_field(value: &Value, field: &str) -> Option<i64> {
    value.get(field).and_then(Value::as_i64)
}

fn bool_field(value: &Value, field: &str) -> Option<bool> {
    value.get(field).and_then(Value::as_bool)
}

fn object_with(value: &Value, field: &str, replacement: Value) -> Value {
    let mut cloned = value.clone();
    if let Some(object) = cloned.as_object_mut() {
        object.insert(field.to_owned(), replacement);
    }
    cloned
}

fn exact_module_usage_proofs(usages: &[Value], module_sha256: Option<&str>) -> Vec<Value> {
    let Some(module_sha256) = module_sha256 else {
        return Vec::new();
    };
    usages
        .iter()
        .filter_map(|usage| {
            let exact_sites = array_field(usage, "instantiation_sites")
                .iter()
                .filter(|site| {
                    bool_field(site, "exact_import_object_identity_proven") == Some(true)
                        && bool_field(site, "exact_module_identity_proven") == Some(true)
                        && string_field(site, "module_sha256") == Some(module_sha256)
                })
                .cloned()
                .collect::<Vec<_>>();
            (!exact_sites.is_empty())
                .then(|| object_with(usage, "instantiation_sites", Value::Array(exact_sites)))
        })
        .collect()
}

fn site_identity(site: &Value) -> (Option<i64>, Option<i64>, Option<&str>) {
    (
        i64_field(site, "start"),
        i64_field(site, "end"),
        string_field(site, "module_sha256"),
    )
}

fn common_exact_binding_proofs(
    left_usages: &[Value],
    right_usages: &[Value],
    module_sha256: Option<&str>,
) -> Vec<Value> {
    let left = exact_module_usage_proofs(left_usages, module_sha256);
    let right = exact_module_usage_proofs(right_usages, module_sha256);
    let mut proofs = Vec::new();
    for lhs in &left {
        for rhs in &right {
            if string_field(lhs, "import_object") != string_field(rhs, "import_object") {
                continue;
            }
            let right_sites = array_field(rhs, "instantiation_sites")
                .iter()
                .map(site_identity)
                .collect::<HashSet<_>>();
            let common_sites = array_field(lhs, "instantiation_sites")
                .iter()
                .filter(|site| right_sites.contains(&site_identity(site)))
                .cloned()
                .collect::<Vec<_>>();
            if common_sites.is_empty() {
                continue;
            }
            proofs.push(json!({
                "import_object": lhs.get("import_object").cloned().unwrap_or(Value::Null),
                "left_import_module": lhs.get("import_module").cloned().unwrap_or(Value::Null),
                "left_import_name": lhs.get("import_name").cloned().unwrap_or(Value::Null),
                "right_import_module": rhs.get("import_module").cloned().unwrap_or(Value::Null),
                "right_import_name": rhs.get("import_name").cloned().unwrap_or(Value::Null),
                "instantiation_sites": common_sites,
            }));
        }
    }
    proofs
}

fn matching_handler(
    document: &Value,
    import_module: &str,
    import_name: &str,
    kind: &str,
) -> Vec<Value> {
    array_field(document, "handler_semantics")
        .iter()
        .filter(|handler| {
            string_field(handler, "import_module") == Some(import_module)
                && string_field(handler, "import_name") == Some(import_name)
                && string_field(handler, "kind") == Some(kind)
        })
        .cloned()
        .collect()
}

fn exact_usage_matches_binding(usage: &Value, binding_proofs: &[Value]) -> bool {
    let usage_sites = array_field(usage, "instantiation_sites")
        .iter()
        .map(site_identity)
        .collect::<HashSet<_>>();
    binding_proofs.iter().any(|binding| {
        string_field(usage, "import_object") == string_field(binding, "import_object")
            && array_field(binding, "instantiation_sites")
                .iter()
                .any(|site| usage_sites.contains(&site_identity(site)))
    })
}

fn source_length_barrier_proofs(
    document: &Value,
    function_imports: &[Value],
    candidate: &Value,
    module_sha256: Option<&str>,
    binding_proofs: &[Value],
) -> Vec<Value> {
    let mut barrier_indices = BTreeSet::new();
    for load in array_field(candidate, "destination_loads") {
        for index in array_field(load, "source_length_import_barriers") {
            let Some(index) = index.as_u64().and_then(|value| usize::try_from(value).ok()) else {
                continue;
            };
            barrier_indices.insert(index);
        }
    }
    let mut proofs = Vec::new();
    for index in barrier_indices {
        let Some(imported) = function_imports.get(index) else {
            return Vec::new();
        };
        let (Some(import_module), Some(import_name)) = (
            string_field(imported, "module"),
            string_field(imported, "name"),
        ) else {
            return Vec::new();
        };
        let handlers = matching_handler(document, import_module, import_name, "property_getter")
            .into_iter()
            .filter(|handler| {
                string_field(handler, "property") == Some("length")
                    && bool_field(handler, "standard_builtin_semantics_required") == Some(true)
            })
            .collect::<Vec<_>>();
        let [handler] = handlers.as_slice() else {
            return Vec::new();
        };
        let usages = array_field(document, "import_object_usages")
            .iter()
            .filter(|usage| {
                string_field(usage, "import_module") == Some(import_module)
                    && string_field(usage, "import_name") == Some(import_name)
                    && i64_field(usage, "assignment_start")
                        == i64_field(handler, "assignment_start")
                    && i64_field(usage, "assignment_end") == i64_field(handler, "assignment_end")
            })
            .cloned()
            .collect::<Vec<_>>();
        let exact = exact_module_usage_proofs(&usages, module_sha256)
            .into_iter()
            .filter(|usage| exact_usage_matches_binding(usage, binding_proofs))
            .collect::<Vec<_>>();
        let [binding] = exact.as_slice() else {
            return Vec::new();
        };
        proofs.push(json!({
            "function_import": index,
            "import_module": import_module,
            "import_name": import_name,
            "handler": handler,
            "binding": binding,
        }));
    }
    proofs
}

fn fixed_uint32_source_lengths(
    memory_proofs: &[Value],
    export_name: Option<&str>,
    source_parameter: Option<usize>,
) -> Option<Vec<usize>> {
    let export_name = export_name?;
    let source_parameter = source_parameter?;
    let mut lengths = Vec::new();
    for proof in memory_proofs {
        let matching_calls = array_field(proof, "export_calls")
            .iter()
            .filter(|call| string_field(call, "export_name") == Some(export_name))
            .collect::<Vec<_>>();
        if matching_calls.is_empty() {
            return None;
        }
        for call in matching_calls {
            let argument_lengths = array_field(call, "static_uint32_array_argument_lengths");
            let length = argument_lengths.get(source_parameter)?.as_u64()?;
            lengths.push(usize::try_from(length).ok()?);
        }
    }
    (!lengths.is_empty()).then_some(lengths)
}

fn fixed_uint32_source_length_lower_bound(
    memory_proofs: &[Value],
    export_name: Option<&str>,
    source_parameter: Option<usize>,
) -> Option<usize> {
    fixed_uint32_source_lengths(memory_proofs, export_name, source_parameter)?
        .into_iter()
        .min()
}

fn fixed_uint32_source_length_exact(
    memory_proofs: &[Value],
    export_name: Option<&str>,
    source_parameter: Option<usize>,
) -> Option<usize> {
    let lengths = fixed_uint32_source_lengths(memory_proofs, export_name, source_parameter)?;
    let first = *lengths.first()?;
    lengths
        .iter()
        .all(|length| *length == first)
        .then_some(first)
}

fn interpreted_destination_loads(
    candidate: &Value,
    module_memory_proofs: &[Value],
    export_name: Option<&str>,
    byte_integrity_proven: bool,
    base_alignment_proven: bool,
) -> (Vec<Value>, Option<usize>) {
    let loads = array_field(candidate, "destination_loads");
    let source_parameter = usize_field(candidate, "source_entry_parameter");
    let source_length =
        fixed_uint32_source_length_lower_bound(module_memory_proofs, export_name, source_parameter);
    if loads.is_empty()
        || source_length.is_none()
        || !byte_integrity_proven
        || !base_alignment_proven
        || usize_field(candidate, "destination_element_index_shift") != Some(2)
    {
        return (Vec::new(), source_length);
    }
    let Some(source_length) = source_length else {
        return (Vec::new(), None);
    };
    let mut interpreted = Vec::new();
    for load in loads {
        let Some(offset) = usize_field(load, "byte_offset") else {
            return (Vec::new(), Some(source_length));
        };
        if offset % 4 != 0 {
            return (Vec::new(), Some(source_length));
        }
        let source_index = offset / 4;
        if source_index >= source_length {
            return (Vec::new(), Some(source_length));
        }
        interpreted.push(json!({
            "load_value": load.get("value").cloned().unwrap_or(Value::Null),
            "load_block": load.get("block").cloned().unwrap_or(Value::Null),
            "load_instruction_index": load.get("instruction_index").cloned().unwrap_or(Value::Null),
            "memory": load.get("memory").cloned().unwrap_or(Value::Null),
            "byte_offset": offset,
            "source_parameter": source_parameter,
            "source_element_index": source_index,
            "source_conversion": "ToUint32",
            "little_endian_typed_array_storage_required": true,
        }));
    }
    (interpreted, Some(source_length))
}

fn semantic_ir_runtime_values(
    expression: &Value,
    runtime_by_value: &BTreeMap<i64, Value>,
) -> Option<BTreeSet<i64>> {
    let kind = string_field(expression, "kind")?;
    match kind {
        "i32_const" => {
            u32_field(expression, "value")?;
            Some(BTreeSet::new())
        }
        "argument" => {
            usize_field(expression, "index")?;
            Some(BTreeSet::new())
        }
        "runtime" => {
            let value = i64_field(expression, "value")?;
            let name = string_field(expression, "name")?;
            let binding = runtime_by_value.get(&value)?;
            (string_field(binding, "name") == Some(name)).then(|| BTreeSet::from([value]))
        }
        "symbol" => string_field(expression, "name").map(|_| BTreeSet::new()),
        "ssa_value" => {
            let value = i64_field(expression, "value")?;
            (value >= 0).then(BTreeSet::new)
        }
        "opaque" => string_field(expression, "expression").map(|_| BTreeSet::new()),
        "operation" => {
            let value = i64_field(expression, "value")?;
            if value < 0 || string_field(expression, "operator").is_none() {
                return None;
            }
            let arguments = expression.get("arguments")?.as_array()?;
            let mut values = BTreeSet::new();
            for argument in arguments {
                values.extend(semantic_ir_runtime_values(argument, runtime_by_value)?);
            }
            Some(values)
        }
        _ => None,
    }
}

fn semantic_ir_ssa_shape(expression: &Value) -> Option<(BTreeSet<i64>, BTreeSet<i64>)> {
    fn visit(
        node: &Value,
        definitions: &mut BTreeSet<i64>,
        references: &mut BTreeSet<i64>,
    ) -> bool {
        let Some(kind) = string_field(node, "kind") else {
            return false;
        };
        match kind {
            "ssa_value" => {
                let Some(value) = i64_field(node, "value") else {
                    return false;
                };
                if value < 0 {
                    return false;
                }
                references.insert(value);
                true
            }
            "operation" => {
                let Some(value) = i64_field(node, "value") else {
                    return false;
                };
                let Some(arguments) = node.get("arguments").and_then(Value::as_array) else {
                    return false;
                };
                if value < 0 || !definitions.insert(value) {
                    return false;
                }
                arguments
                    .iter()
                    .all(|argument| visit(argument, definitions, references))
            }
            "i32_const" | "argument" | "runtime" | "symbol" | "opaque" => true,
            _ => false,
        }
    }

    let mut definitions = BTreeSet::new();
    let mut references = BTreeSet::new();
    if !visit(expression, &mut definitions, &mut references) || !references.is_subset(&definitions)
    {
        return None;
    }
    Some((definitions, references))
}

fn semantic_runtime_graph(
    analysis: &Value,
) -> Option<(BTreeMap<i64, Value>, BTreeMap<i64, Vec<i64>>, Vec<Value>)> {
    let bindings = analysis.get("runtime_bindings")?.as_array()?;
    let returns = analysis.get("returns")?.as_array()?;
    let mut runtime_by_value = BTreeMap::new();
    let mut graph = BTreeMap::new();

    for binding in bindings {
        let value = i64_field(binding, "value")?;
        if value < 0
            || string_field(binding, "name").is_none()
            || string_field(binding, "expression").is_none()
            || !binding.get("semantic_ir").is_some_and(Value::is_object)
            || !binding
                .get("normalized_semantic_ir")
                .is_some_and(Value::is_object)
            || runtime_by_value.contains_key(&value)
        {
            return None;
        }
        let dependencies = binding.get("runtime_dependencies")?.as_array()?;
        let mut deps = Vec::with_capacity(dependencies.len());
        let mut unique = BTreeSet::new();
        for dependency in dependencies {
            let dependency = dependency.as_i64()?;
            if dependency < 0 || !unique.insert(dependency) {
                return None;
            }
            deps.push(dependency);
        }
        runtime_by_value.insert(value, binding.clone());
        graph.insert(value, deps);
    }

    if graph
        .values()
        .flatten()
        .any(|dependency| !runtime_by_value.contains_key(dependency))
    {
        return None;
    }

    for (value, binding) in &runtime_by_value {
        for field in ["semantic_ir", "normalized_semantic_ir"] {
            let dependencies = semantic_ir_runtime_values(binding.get(field)?, &runtime_by_value)?;
            let expected = graph.get(value)?.iter().copied().collect::<BTreeSet<_>>();
            if dependencies != expected || semantic_ir_ssa_shape(binding.get(field)?).is_none() {
                return None;
            }
        }
    }

    let mut normalized_returns = Vec::new();
    for report in returns {
        let value = i64_field(report, "value")?;
        if value < 0
            || string_field(report, "expression").is_none()
            || !report.get("semantic_ir").is_some_and(Value::is_object)
            || !report
                .get("normalized_semantic_ir")
                .is_some_and(Value::is_object)
        {
            return None;
        }
        let dependencies = report.get("runtime_dependencies")?.as_array()?;
        let mut deps = BTreeSet::new();
        for dependency in dependencies {
            let dependency = dependency.as_i64()?;
            if dependency < 0
                || !runtime_by_value.contains_key(&dependency)
                || !deps.insert(dependency)
            {
                return None;
            }
        }
        for field in ["semantic_ir", "normalized_semantic_ir"] {
            if semantic_ir_runtime_values(report.get(field)?, &runtime_by_value)? != deps
                || semantic_ir_ssa_shape(report.get(field)?).is_none()
            {
                return None;
            }
        }
        normalized_returns.push(report.clone());
    }

    let mut state = BTreeMap::<i64, u8>::new();
    fn visit(value: i64, graph: &BTreeMap<i64, Vec<i64>>, state: &mut BTreeMap<i64, u8>) -> bool {
        match state.get(&value).copied().unwrap_or(0) {
            1 => return false,
            2 => return true,
            _ => {}
        }
        state.insert(value, 1);
        let Some(dependencies) = graph.get(&value) else {
            return false;
        };
        if !dependencies
            .iter()
            .all(|dependency| visit(*dependency, graph, state))
        {
            return false;
        }
        state.insert(value, 2);
        true
    }
    if !graph
        .keys()
        .copied()
        .all(|value| visit(value, &graph, &mut state))
    {
        return None;
    }
    Some((runtime_by_value, graph, normalized_returns))
}

fn runtime_dependency_closure(graph: &BTreeMap<i64, Vec<i64>>, roots: &[i64]) -> Option<Vec<i64>> {
    fn visit(
        value: i64,
        graph: &BTreeMap<i64, Vec<i64>>,
        closure: &mut BTreeSet<i64>,
        visiting: &mut BTreeSet<i64>,
    ) -> bool {
        if visiting.contains(&value) {
            return false;
        }
        if closure.contains(&value) {
            return true;
        }
        let Some(dependencies) = graph.get(&value) else {
            return false;
        };
        visiting.insert(value);
        closure.insert(value);
        if !dependencies
            .iter()
            .all(|dependency| visit(*dependency, graph, closure, visiting))
        {
            return false;
        }
        visiting.remove(&value);
        true
    }

    let mut closure = BTreeSet::new();
    let mut visiting = BTreeSet::new();
    if !roots
        .iter()
        .all(|root| visit(*root, graph, &mut closure, &mut visiting))
    {
        return None;
    }
    Some(closure.into_iter().collect())
}

fn source_word_dependency_summary(overlay: &Value) -> Value {
    json!({
        "load_value": overlay.get("load_value").cloned().unwrap_or(Value::Null),
        "runtime_binding": overlay.get("runtime_binding").cloned().unwrap_or(Value::Null),
        "source_parameter": overlay.get("source_parameter").cloned().unwrap_or(Value::Null),
        "source_element_index": overlay.get("source_element_index").cloned().unwrap_or(Value::Null),
        "source_conversion": overlay.get("source_conversion").cloned().unwrap_or(Value::Null),
    })
}

fn source_word_semantic_ir(
    expression: &Value,
    runtime_by_value: &BTreeMap<i64, Value>,
    graph: &BTreeMap<i64, Vec<i64>>,
    source_by_value: &BTreeMap<i64, Value>,
) -> Option<Value> {
    match string_field(expression, "kind")? {
        "runtime" => {
            let value = i64_field(expression, "value")?;
            let name = string_field(expression, "name")?;
            let binding = runtime_by_value.get(&value)?;
            if string_field(binding, "name") != Some(name) {
                return None;
            }
            if let Some(direct) = source_by_value.get(&value) {
                let mut summary = source_word_dependency_summary(direct);
                summary
                    .as_object_mut()?
                    .insert("kind".into(), "source_word".into());
                return Some(summary);
            }
            let closure = runtime_dependency_closure(graph, &[value])?;
            let mut source_dependencies = closure
                .iter()
                .filter_map(|dependency| source_by_value.get(dependency))
                .map(source_word_dependency_summary)
                .collect::<Vec<_>>();
            source_dependencies.sort_by_key(|row| {
                (
                    usize_field(row, "source_parameter").unwrap_or(usize::MAX),
                    usize_field(row, "source_element_index").unwrap_or(usize::MAX),
                    i64_field(row, "load_value").unwrap_or(i64::MAX),
                )
            });
            Some(json!({
                "kind": "runtime",
                "value": value,
                "name": name,
                "source_word_dependencies": source_dependencies,
            }))
        }
        "operation" => {
            let value = i64_field(expression, "value")?;
            if value < 0 {
                return None;
            }
            let operator = string_field(expression, "operator")?;
            let arguments = expression.get("arguments")?.as_array()?;
            let transformed = arguments
                .iter()
                .map(|argument| {
                    source_word_semantic_ir(argument, runtime_by_value, graph, source_by_value)
                })
                .collect::<Option<Vec<_>>>()?;
            Some(json!({
                "kind": "operation",
                "value": value,
                "operator": operator,
                "arguments": transformed,
            }))
        }
        "i32_const" | "argument" | "symbol" | "ssa_value" | "opaque" => Some(expression.clone()),
        _ => None,
    }
}

fn render_source_word_semantic_ir(expression: &Value) -> Option<String> {
    match string_field(expression, "kind")? {
        "i32_const" => Some(format!("0x{:08x}", u32_field(expression, "value")?)),
        "argument" => Some(format!("$arg{}", usize_field(expression, "index")?)),
        "runtime" | "symbol" => Some(string_field(expression, "name")?.to_owned()),
        "source_word" => Some(format!(
            "source_u32(arg{}, {})",
            usize_field(expression, "source_parameter")?,
            usize_field(expression, "source_element_index")?
        )),
        "ssa_value" => Some(format!("v{}", usize_field(expression, "value")?)),
        "opaque" => Some(string_field(expression, "expression")?.to_owned()),
        "operation" => {
            let operator = string_field(expression, "operator")?;
            let args = expression
                .get("arguments")?
                .as_array()?
                .iter()
                .map(render_source_word_semantic_ir)
                .collect::<Option<Vec<_>>>()?;
            if operator == "wasm.memory_grow" && args.len() == 2 {
                return Some(format!(
                    "wasm.memory_grow({}, externref_slot={})",
                    args[0], args[1]
                ));
            }
            if operator == "i32eqz" && args.len() == 1 {
                return Some(format!("is_zero({})", args[0]));
            }
            if args.len() == 2 {
                let (left, right) = (&args[0], &args[1]);
                let rendered = match operator {
                    "i32add" => Some(format!("wrapping_add({left}, {right})")),
                    "i32sub" => Some(format!("wrapping_sub({left}, {right})")),
                    "i32mul" => Some(format!("wrapping_mul({left}, {right})")),
                    "i32and" => Some(format!("({left} & {right})")),
                    "i32or" => Some(format!("({left} | {right})")),
                    "i32xor" => Some(format!("({left} ^ {right})")),
                    "i32shl" => Some(format!("({left} << {right})")),
                    "i32shrs" => Some(format!("ashr({left}, {right})")),
                    "i32shru" => Some(format!("({left} >> {right})")),
                    "i32rotl" => Some(format!("rotl({left}, {right})")),
                    "i32rotr" => Some(format!("rotr({left}, {right})")),
                    "i32eq" => Some(format!("({left} == {right})")),
                    "i32ne" => Some(format!("({left} != {right})")),
                    "i32ltu" => Some(format!("ult({left}, {right})")),
                    "i32leu" => Some(format!("ule({left}, {right})")),
                    "i32gtu" => Some(format!("ugt({left}, {right})")),
                    "i32geu" => Some(format!("uge({left}, {right})")),
                    "i32lts" => Some(format!("slt({left}, {right})")),
                    "i32les" => Some(format!("sle({left}, {right})")),
                    "i32gts" => Some(format!("sgt({left}, {right})")),
                    "i32ges" => Some(format!("sge({left}, {right})")),
                    _ => None,
                };
                if rendered.is_some() {
                    return rendered;
                }
            }
            Some(format!("{operator}({})", args.join(", ")))
        }
        _ => None,
    }
}

fn source_word_semantic_overlay(
    analysis: &Value,
    destination_load_interpretations: &[Value],
) -> (Vec<Value>, Vec<Value>, bool) {
    let Some((runtime_by_value, graph, returns)) = semantic_runtime_graph(analysis) else {
        return (Vec::new(), Vec::new(), false);
    };
    let mut overlays = Vec::new();
    let mut source_by_value = BTreeMap::new();
    for interpretation in destination_load_interpretations {
        let (Some(value), Some(source_parameter), Some(source_index)) = (
            i64_field(interpretation, "load_value"),
            usize_field(interpretation, "source_parameter"),
            usize_field(interpretation, "source_element_index"),
        ) else {
            return (Vec::new(), Vec::new(), false);
        };
        let Some(binding) = runtime_by_value.get(&value) else {
            return (Vec::new(), Vec::new(), false);
        };
        if source_by_value.contains_key(&value) {
            return (Vec::new(), Vec::new(), false);
        }
        let overlay = json!({
            "load_value": value,
            "runtime_binding": binding.get("name").cloned().unwrap_or(Value::Null),
            "runtime_expression": binding.get("expression").cloned().unwrap_or(Value::Null),
            "runtime_semantic_ir": binding.get("semantic_ir").cloned().unwrap_or(Value::Null),
            "normalized_runtime_semantic_ir": binding.get("normalized_semantic_ir").cloned().unwrap_or(Value::Null),
            "runtime_dependencies": binding.get("runtime_dependencies").cloned().unwrap_or(Value::Null),
            "source_parameter": source_parameter,
            "source_element_index": source_index,
            "source_conversion": interpretation.get("source_conversion").cloned().unwrap_or(Value::Null),
            "semantic_expression": format!("source_u32(arg{source_parameter}, {source_index})"),
        });
        source_by_value.insert(value, overlay.clone());
        overlays.push(overlay);
    }
    if overlays.is_empty() {
        return (Vec::new(), Vec::new(), true);
    }

    let mut return_semantics = Vec::new();
    for report in returns {
        let Some(direct_dependencies) =
            report.get("runtime_dependencies").and_then(Value::as_array)
        else {
            return (overlays, Vec::new(), false);
        };
        let Some(roots) = direct_dependencies
            .iter()
            .map(Value::as_i64)
            .collect::<Option<Vec<_>>>()
        else {
            return (overlays, Vec::new(), false);
        };
        let Some(transitive_dependencies) = runtime_dependency_closure(&graph, &roots) else {
            return (overlays, Vec::new(), false);
        };
        let mut source_dependencies = transitive_dependencies
            .iter()
            .filter_map(|value| source_by_value.get(value).cloned())
            .collect::<Vec<_>>();
        source_dependencies.sort_by_key(|row| {
            (
                usize_field(row, "source_parameter").unwrap_or(usize::MAX),
                usize_field(row, "source_element_index").unwrap_or(usize::MAX),
                i64_field(row, "load_value").unwrap_or(i64::MAX),
            )
        });
        let Some(annotated_ir) = report.get("semantic_ir").and_then(|ir| {
            source_word_semantic_ir(ir, &runtime_by_value, &graph, &source_by_value)
        }) else {
            return (overlays, Vec::new(), false);
        };
        let Some(normalized_annotated_ir) = report.get("normalized_semantic_ir").and_then(|ir| {
            source_word_semantic_ir(ir, &runtime_by_value, &graph, &source_by_value)
        }) else {
            return (overlays, Vec::new(), false);
        };
        let Some(raw_source_word_expression) = render_source_word_semantic_ir(&annotated_ir) else {
            return (overlays, Vec::new(), false);
        };
        let Some(source_word_expression) = render_source_word_semantic_ir(&normalized_annotated_ir)
        else {
            return (overlays, Vec::new(), false);
        };
        return_semantics.push(json!({
            "return_value": report.get("value").cloned().unwrap_or(Value::Null),
            "expression": report.get("expression").cloned().unwrap_or(Value::Null),
            "semantic_ir": report.get("semantic_ir").cloned().unwrap_or(Value::Null),
            "normalized_semantic_ir": report.get("normalized_semantic_ir").cloned().unwrap_or(Value::Null),
            "source_word_semantic_ir": annotated_ir,
            "normalized_source_word_semantic_ir": normalized_annotated_ir,
            "runtime_dependencies": report.get("runtime_dependencies").cloned().unwrap_or(Value::Null),
            "transitive_runtime_dependencies": transitive_dependencies,
            "source_word_dependencies": source_dependencies,
            "raw_source_word_expression": raw_source_word_expression,
            "source_word_expression": source_word_expression,
        }));
    }
    (overlays, return_semantics, true)
}

fn matching_module_memory_proofs(
    document: &Value,
    import_module: Option<&str>,
    import_name: Option<&str>,
    module_sha256: Option<&str>,
    export_name: Option<&str>,
    binding_proofs: &[Value],
    report: &Value,
    candidate: &Value,
) -> Vec<Value> {
    let (Some(import_module), Some(import_name), Some(module_sha256), Some(export_name)) =
        (import_module, import_name, module_sha256, export_name)
    else {
        return Vec::new();
    };
    let load_memories = array_field(candidate, "destination_loads")
        .iter()
        .filter_map(|load| usize_field(load, "memory"))
        .collect::<BTreeSet<_>>();
    if load_memories.len() != 1 {
        return Vec::new();
    }
    let Some(load_memory) = load_memories.iter().next().copied() else {
        return Vec::new();
    };
    let binding_sites = binding_proofs
        .iter()
        .flat_map(|proof| {
            array_field(proof, "instantiation_sites")
                .iter()
                .map(move |site| {
                    (
                        string_field(proof, "import_object").map(ToOwned::to_owned),
                        i64_field(site, "start"),
                        i64_field(site, "end"),
                        string_field(site, "module_sha256").map(ToOwned::to_owned),
                    )
                })
        })
        .collect::<HashSet<_>>();
    let mut matches = Vec::new();
    for proof in array_field(document, "module_memory_identity_proofs") {
        if string_field(proof, "import_module") != Some(import_module)
            || string_field(proof, "import_name") != Some(import_name)
        {
            continue;
        }
        let Some(site) = proof.get("instantiation_site") else {
            continue;
        };
        let site_key = (
            string_field(proof, "import_object").map(ToOwned::to_owned),
            i64_field(site, "start"),
            i64_field(site, "end"),
            string_field(site, "module_sha256").map(ToOwned::to_owned),
        );
        if !binding_sites.contains(&site_key)
            || string_field(site, "module_sha256") != Some(module_sha256)
            || !array_field(proof, "export_calls")
                .iter()
                .any(|call| string_field(call, "export_name") == Some(export_name))
        {
            continue;
        }
        let Some(memory_export_name) = string_field(proof, "memory_export_name") else {
            continue;
        };
        let memory_exports = array_field(report, "exports")
            .iter()
            .filter(|exported| {
                string_field(exported, "kind") == Some("memory")
                    && string_field(exported, "name") == Some(memory_export_name)
                    && usize_field(exported, "index") == Some(load_memory)
            })
            .cloned()
            .collect::<Vec<_>>();
        let [memory_export] = memory_exports.as_slice() else {
            continue;
        };
        let mut matched = proof.clone();
        if let Some(object) = matched.as_object_mut() {
            object.insert("memory_export".into(), memory_export.clone());
        }
        matches.push(matched);
    }
    matches
}

fn verified_module_bytes(project: &Path, module: &Value) -> Option<(PathBuf, String, Vec<u8>)> {
    let binary_path = string_field(module, "binary_path")?;
    let module_sha256 = string_field(module, "sha256")?;
    let binary = project.join(binary_path);
    if !binary.is_file() || sha256_path(&binary).ok()?.as_str() != module_sha256 {
        return None;
    }
    let bytes = fs::read(&binary).ok()?;
    Some((PathBuf::from(binary_path), module_sha256.to_owned(), bytes))
}

fn fresh_destination_alignment_proof(
    project: &Path,
    module: &Value,
    report: &Value,
    function_imports: &[Value],
    document: &Value,
    candidate: &Value,
    module_memory_proofs: &[Value],
    binding_proofs: &[Value],
    export_name: Option<&str>,
) -> Option<Value> {
    let recipe = candidate
        .get("fresh_destination_base_recipe")?
        .as_object()?;
    let export_name = export_name?;
    let function = recipe
        .get("function")?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())?;
    let length_import_index = recipe
        .get("source_length_import_function")?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())?;
    let length_shift = recipe
        .get("source_length_byte_shift")?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())?;
    let element_shift = usize_field(candidate, "destination_element_index_shift")?;
    if length_shift != element_shift || length_shift != 2 {
        return None;
    }
    let alternate_bases = recipe.get("alternate_constant_bases")?.as_array()?;
    if alternate_bases.iter().any(|value| {
        value
            .as_u64()
            .is_none_or(|value| value > u64::from(u32::MAX) || value % 4 != 0)
    }) {
        return None;
    }
    let _length_import = function_imports.get(length_import_index)?;
    let source_parameter = usize_field(candidate, "source_entry_parameter");
    let exact_source_length = fixed_uint32_source_length_exact(
        module_memory_proofs,
        Some(export_name),
        source_parameter,
    )?;
    let exact_source_length_u32 = u32::try_from(exact_source_length).ok()?;
    if exact_source_length_u32 > (u32::MAX >> length_shift) {
        return None;
    }

    let mut exports_bindings = BTreeSet::new();
    for proof in module_memory_proofs {
        if string_field(proof, "initializer_only_wasm_export_call") != Some("__wbindgen_start")
            || bool_field(proof, "initializer_non_start_effects_memory_disjoint") != Some(true)
        {
            return None;
        }
        exports_bindings.insert(string_field(proof, "exports_binding")?.to_owned());
        let calls = array_field(proof, "export_calls");
        let first = calls.first()?;
        if string_field(first, "export_name") != Some(export_name) {
            return None;
        }
        let argument_lengths = array_field(first, "static_uint32_array_argument_lengths");
        let source_parameter = source_parameter?;
        if argument_lengths.get(source_parameter)?.as_u64()? != u64::from(exact_source_length_u32) {
            return None;
        }
    }
    if exports_bindings.len() != 1 {
        return None;
    }
    let exports_binding = exports_bindings.iter().next()?;

    let start_exports = array_field(report, "exports")
        .iter()
        .filter(|exported| {
            string_field(exported, "name") == Some("__wbindgen_start")
                && string_field(exported, "kind") == Some("function")
                && usize_field(exported, "index").is_some()
        })
        .cloned()
        .collect::<Vec<_>>();
    let [start_export] = start_exports.as_slice() else {
        return None;
    };
    let start_function = usize_field(start_export, "index")?;
    let start_import = function_imports.get(start_function)?;
    let start_module = string_field(start_import, "module")?;
    let start_name = string_field(start_import, "name")?;

    let table_exports = array_field(report, "exports")
        .iter()
        .filter(|exported| {
            string_field(exported, "kind") == Some("table")
                && string_field(exported, "name") == Some("__wbindgen_export_0")
        })
        .cloned()
        .collect::<Vec<_>>();
    let [table_export] = table_exports.as_slice() else {
        return None;
    };

    let normalized_handlers = array_field(document, "proof_normalized_handler_semantics")
        .iter()
        .filter(|handler| {
            string_field(handler, "import_module") == Some(start_module)
                && string_field(handler, "import_name") == Some(start_name)
                && string_field(handler, "kind") == Some("table_initializer_only")
                && string_field(handler, "exports_binding") == Some(exports_binding.as_str())
                && string_field(handler, "table_export") == Some("__wbindgen_export_0")
                && bool_field(handler, "standard_builtin_semantics_required") == Some(true)
                && bool_field(handler, "standard_webassembly_builtin_semantics_required")
                    == Some(true)
        })
        .cloned()
        .collect::<Vec<_>>();
    let [start_handler] = normalized_handlers.as_slice() else {
        return None;
    };

    let start_usages = array_field(document, "import_object_usages")
        .iter()
        .filter(|usage| {
            string_field(usage, "import_module") == Some(start_module)
                && string_field(usage, "import_name") == Some(start_name)
        })
        .cloned()
        .collect::<Vec<_>>();
    let exact_start_usages =
        exact_module_usage_proofs(&start_usages, string_field(module, "sha256"))
            .into_iter()
            .filter(|usage| exact_usage_matches_binding(usage, binding_proofs))
            .collect::<Vec<_>>();
    let [start_usage] = exact_start_usages.as_slice() else {
        return None;
    };

    let length_import = function_imports.get(length_import_index)?;
    if string_field(length_import, "module").is_none()
        || string_field(length_import, "name").is_none()
    {
        return None;
    }
    let (binary_path, module_sha256, bytes) = verified_module_bytes(project, module)?;
    let byte_count = exact_source_length_u32.checked_shl(u32::try_from(length_shift).ok()?)?;
    let evaluation = evaluate_fresh_i32_call(&bytes, function, &[byte_count], None);
    let result = evaluation.proven_result()?;
    if result % 4 != 0 {
        return None;
    }
    let trailing_zero_bits = if result == 0 {
        32
    } else {
        result.trailing_zeros()
    };
    Some(json!({
        "fresh_instance_state_required": true,
        "module_sha256": module_sha256,
        "binary_path": binary_path,
        "binary_sha256_verified": true,
        "source_uint32_array_length": exact_source_length,
        "allocator_byte_count": byte_count,
        "recipe": candidate.get("fresh_destination_base_recipe").cloned().unwrap_or(Value::Null),
        "start_export": start_export,
        "start_import": start_import,
        "start_import_object_usage": start_usage,
        "start_handler": start_handler,
        "table_export": table_export,
        "exports_binding": exports_binding,
        "standard_js_numeric_builtin_semantics_required": true,
        "standard_webassembly_builtin_semantics_required": true,
        "fresh_evaluation": evaluation,
        "evaluated_destination_base": result,
        "evaluated_destination_base_trailing_zero_bits": trailing_zero_bits,
    }))
}

fn access_is_disjoint_from_range(
    access: &Value,
    target_memory: usize,
    range_start: u64,
    range_end: u64,
) -> bool {
    let (Some(memory), Some(addr), Some(length)) = (
        usize_field(access, "memory"),
        access.get("addr").and_then(Value::as_u64),
        access.get("len").and_then(Value::as_u64),
    ) else {
        return false;
    };
    if memory != target_memory {
        return true;
    }
    let Some(access_end) = addr.checked_add(length) else {
        return false;
    };
    access_end <= range_start || range_end <= addr
}

fn fresh_cleanup_disjointness_proof(
    project: &Path,
    module: &Value,
    function_imports: &[Value],
    document: &Value,
    candidate: &Value,
    module_memory_proofs: &[Value],
    binding_proofs: &[Value],
    fresh_alignment_proof: Option<&Value>,
) -> Option<Value> {
    let recipe = candidate
        .get("fresh_cleanup_disjointness_recipe")?
        .as_object()?;
    let fresh_alignment_proof = fresh_alignment_proof?;
    let slot_allocator = recipe
        .get("slot_allocator_function")?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())?;
    let cleanup_function = recipe
        .get("cleanup_function")?
        .as_u64()
        .and_then(|value| usize::try_from(value).ok())?;
    if recipe.get("pre_copy_cleanup").and_then(Value::as_str) != Some("buffer")
        || recipe.get("post_copy_cleanups") != Some(&json!(["receiver", "memory"]))
    {
        return None;
    }
    let bypassed_imports = recipe
        .get("bypassed_setup_import_functions")?
        .as_array()?
        .iter()
        .map(|value| value.as_u64().and_then(|value| usize::try_from(value).ok()))
        .collect::<Option<Vec<_>>>()?;
    let memory_import_index = usize_field(candidate, "constructor_input_memory_import_function")?;
    if !bypassed_imports.contains(&memory_import_index)
        || bypassed_imports
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            .len()
            != 2
        || module_memory_proofs.is_empty()
    {
        return None;
    }
    let buffer_indices = bypassed_imports
        .iter()
        .copied()
        .filter(|index| *index != memory_import_index)
        .collect::<Vec<_>>();
    let [buffer_index] = buffer_indices.as_slice() else {
        return None;
    };
    let buffer_import = function_imports.get(*buffer_index)?;
    let buffer_module = string_field(buffer_import, "module")?;
    let buffer_name = string_field(buffer_import, "name")?;
    let binding_import_objects = binding_proofs
        .iter()
        .filter_map(|proof| string_field(proof, "import_object"))
        .collect::<BTreeSet<_>>();
    if binding_import_objects.len() != 1 {
        return None;
    }
    let binding_import_object = *binding_import_objects.iter().next()?;
    let buffer_handlers = matching_handler(document, buffer_module, buffer_name, "property_getter")
        .into_iter()
        .filter(|handler| {
            string_field(handler, "property") == Some("buffer")
                && bool_field(handler, "standard_builtin_semantics_required") == Some(true)
                && string_field(handler, "import_object") == Some(binding_import_object)
        })
        .collect::<Vec<_>>();
    let [buffer_handler] = buffer_handlers.as_slice() else {
        return None;
    };

    let destination_base = u32_field(fresh_alignment_proof, "evaluated_destination_base")?;
    let byte_count = u32_field(fresh_alignment_proof, "allocator_byte_count")?;
    if byte_count == 0 {
        return None;
    }
    let start_handler = fresh_alignment_proof.get("start_handler")?;
    let table_export = fresh_alignment_proof.get("table_export")?;
    let table_index = usize_field(table_export, "index")?;
    let grow_deltas = array_field(start_handler, "exact_grow_deltas")
        .iter()
        .map(|delta| delta.as_u64().and_then(|value| u32::try_from(value).ok()))
        .collect::<Option<Vec<_>>>()?;
    if grow_deltas.is_empty() {
        return None;
    }
    let destination_function = candidate
        .get("fresh_destination_base_recipe")
        .and_then(|recipe| usize_field(recipe, "function"))?;
    let calls = vec![
        FreshI32CallRequest {
            function_index: destination_function,
            i32_args: vec![FreshI32Arg::Literal { value: byte_count }],
        },
        FreshI32CallRequest {
            function_index: slot_allocator,
            i32_args: Vec::new(),
        },
        FreshI32CallRequest {
            function_index: slot_allocator,
            i32_args: Vec::new(),
        },
        FreshI32CallRequest {
            function_index: slot_allocator,
            i32_args: Vec::new(),
        },
        FreshI32CallRequest {
            function_index: cleanup_function,
            i32_args: vec![FreshI32Arg::StepResult { step: 2 }],
        },
        FreshI32CallRequest {
            function_index: cleanup_function,
            i32_args: vec![FreshI32Arg::StepResult { step: 3 }],
        },
        FreshI32CallRequest {
            function_index: cleanup_function,
            i32_args: vec![FreshI32Arg::StepResult { step: 1 }],
        },
    ];
    let table_grows = grow_deltas
        .iter()
        .map(|delta| FreshTableGrowRequest {
            table_index,
            delta: *delta,
        })
        .collect::<Vec<_>>();
    let (_, module_sha256, bytes) = verified_module_bytes(project, module)?;
    let evaluation = evaluate_fresh_i32_sequence(&bytes, &table_grows, &calls, None);
    if evaluation.outcome != FreshEvalOutcome::Returned || evaluation.steps.len() != calls.len() {
        return None;
    }
    if evaluation.steps.first()?.i32_result != Some(destination_base) {
        return None;
    }
    let slot_results = [1usize, 2, 3]
        .into_iter()
        .map(|index| evaluation.steps.get(index)?.i32_result)
        .collect::<Option<Vec<_>>>()?;
    if slot_results.iter().copied().collect::<BTreeSet<_>>().len() != 3 {
        return None;
    }
    let target_memories = array_field(candidate, "destination_loads")
        .iter()
        .filter_map(|load| usize_field(load, "memory"))
        .collect::<BTreeSet<_>>();
    if target_memories.len() != 1 {
        return None;
    }
    let target_memory = target_memories.iter().next().copied()?;
    let range_start = u64::from(destination_base);
    let range_end = range_start.checked_add(u64::from(byte_count))?;
    if range_end > 0x1_0000_0000 {
        return None;
    }
    let evaluation_value = serde_json::to_value(&evaluation).ok()?;
    let post_copy_accesses = array_field(&evaluation_value, "steps")
        .iter()
        .skip(5)
        .flat_map(|step| array_field(step, "memory_accesses").iter().cloned())
        .collect::<Vec<_>>();
    if !post_copy_accesses
        .iter()
        .all(|access| access_is_disjoint_from_range(access, target_memory, range_start, range_end))
    {
        return None;
    }
    let required_internal_barriers = array_field(candidate, "destination_loads")
        .iter()
        .flat_map(|load| array_field(load, "internal_memory_mutation_call_barriers"))
        .filter_map(Value::as_u64)
        .filter_map(|value| usize::try_from(value).ok())
        .collect::<BTreeSet<_>>();
    if required_internal_barriers != BTreeSet::from([cleanup_function]) {
        return None;
    }
    Some(json!({
        "fresh_instance_state_required": true,
        "module_sha256": module_sha256,
        "recipe": candidate.get("fresh_cleanup_disjointness_recipe").cloned().unwrap_or(Value::Null),
        "bypassed_setup_import_proofs": {
            "memory_import_function": memory_import_index,
            "module_memory_identity_proofs": module_memory_proofs,
            "buffer_import_function": buffer_index,
            "buffer_handler": buffer_handler,
            "exact_import_object": binding_import_object,
        },
        "initial_table_grows": table_grows,
        "protected_memory": target_memory,
        "protected_range_start": range_start,
        "protected_range_end": range_end,
        "copy_boundary_after_step": 4,
        "post_copy_steps": [5, 6],
        "fresh_sequence_evaluation": evaluation,
        "post_copy_memory_accesses": post_copy_accesses,
        "post_copy_accesses_disjoint_from_copied_range": true,
    }))
}

fn semantics_for_source(source: &Path) -> Result<Value> {
    let text =
        fs::read_to_string(source).with_context(|| format!("reading {}", source.display()))?;
    serde_json::to_value(proven_wasm_import_semantics(&text))
        .context("serializing JS WASM semantics")
}

fn targeted_semantics_for_source(
    source: &Path,
    import_module: &str,
    import_name: &str,
    offset: u32,
) -> Result<Value> {
    let text =
        fs::read_to_string(source).with_context(|| format!("reading {}", source.display()))?;
    serde_json::to_value(proven_wasm_import_semantics_for(
        &text,
        import_module,
        import_name,
        offset,
    ))
    .context("serializing targeted JS WASM semantics")
}

fn matching_usages(document: &Value, import_module: &str, import_name: &str) -> Vec<Value> {
    array_field(document, "import_object_usages")
        .iter()
        .filter(|usage| {
            string_field(usage, "import_module") == Some(import_module)
                && string_field(usage, "import_name") == Some(import_name)
        })
        .cloned()
        .collect()
}

pub fn correlate_project(project: &Path) -> Result<WasmJsBoundarySummary> {
    let wasm_index = load_artifact(project, WASM_INDEX, false)?
        .context("WASM index is required for WASM/JS boundary correlation")?;
    let deob = load_artifact(project, DEOBFUSCATION, false)?
        .context("deobfuscation artifact is required for WASM/JS boundary correlation")?;
    let deob_by_raw = array_field(&deob, "units")
        .iter()
        .filter_map(|unit| {
            let raw = string_field(unit, "raw_path")?;
            let output = string_field(unit, "output_path")?;
            (i64_field(unit, "exit") == Some(0)).then(|| (raw.to_owned(), output.to_owned()))
        })
        .collect::<BTreeMap<_, _>>();

    let mut targeted_cache = HashMap::<(String, String, String, u32), Value>::new();
    let mut full_cache = HashMap::<String, Value>::new();
    let mut host_effect_rows = Vec::<Value>::new();
    let mut copied_input_rows = Vec::<Value>::new();
    let mut skipped_modules = Vec::<Value>::new();
    let mut carrier_sources = BTreeSet::<String>::new();

    for module in array_field(&wasm_index, "modules") {
        if string_field(module, "status") != Some("ok")
            || string_field(module, "deep_path").is_none()
        {
            continue;
        }
        let deep_path =
            project.join(string_field(module, "deep_path").context("missing deep path")?);
        let report_path =
            project.join(string_field(module, "report_path").context("missing report path")?);
        let deep = read_json(&deep_path)?;
        let report = read_json(&report_path)?;
        let function_imports = array_field(&report, "imports")
            .iter()
            .filter(|imported| string_field(imported, "kind") == Some("function"))
            .cloned()
            .collect::<Vec<_>>();
        if string_field(&deep, "schema") != Some("wasm-redox/deep-v14") {
            skipped_modules.push(json!({
                "sha256": module.get("sha256").cloned().unwrap_or(Value::Null),
                "schema": deep.get("schema").cloned().unwrap_or(Value::Null),
                "reason": "host-effect/read proof requires wasm-redox/deep-v14",
            }));
            continue;
        }

        let mut carrier_candidates = Vec::<String>::new();
        for origin in array_field(module, "origins") {
            let Some(raw) = string_field(origin, "source_path") else {
                continue;
            };
            let Some(output) = deob_by_raw.get(raw) else {
                continue;
            };
            if !carrier_candidates.contains(output) {
                carrier_candidates.push(output.clone());
            }
        }

        for export in array_field(&deep, "exports") {
            let analysis = export.get("analysis").unwrap_or(&Value::Null);
            let export_name = string_field(export, "export");

            for pair in array_field(analysis, "opaque_host_effect_memory_reads") {
                let host_import = pair.get("host_import").cloned().unwrap_or(Value::Null);
                let host_import_function = usize_field(pair, "host_import_function");
                let raw_import = host_import_function
                    .and_then(|index| function_imports.get(index))
                    .and_then(|imported| string_field(imported, "name"));
                let raw_module = host_import_function
                    .and_then(|index| function_imports.get(index))
                    .and_then(|imported| string_field(imported, "module"));
                let offset = u32_field(pair, "offset");
                let mut proofs = Vec::new();
                let mut usage_proofs = Vec::new();

                if let (Some(raw_module), Some(raw_import), Some(offset)) =
                    (raw_module, raw_import, offset)
                {
                    for relative in &carrier_candidates {
                        let source = project.join(relative);
                        if !source.is_file() {
                            continue;
                        }
                        carrier_sources.insert(relative.clone());
                        let key = (
                            relative.clone(),
                            raw_module.to_owned(),
                            raw_import.to_owned(),
                            offset,
                        );
                        if !targeted_cache.contains_key(&key) {
                            targeted_cache.insert(
                                key.clone(),
                                targeted_semantics_for_source(
                                    &source, raw_module, raw_import, offset,
                                )?,
                            );
                        }
                        let probe = targeted_cache.get(&key).context("missing targeted cache")?;
                        let writes = array_field(probe, "shapes");
                        anyhow::ensure!(
                            writes.len() <= 1,
                            "ambiguous JS WASM-import proof for {}: {}@{}",
                            source.display(),
                            raw_import,
                            offset
                        );
                        if let Some(write) = writes.first() {
                            let mut proof = write.clone();
                            proof
                                .as_object_mut()
                                .context("write proof must be object")?
                                .insert("source_path".into(), relative.clone().into());
                            proofs.push(proof);
                        }
                        for usage in array_field(probe, "import_object_usages") {
                            let mut proof = usage.clone();
                            proof
                                .as_object_mut()
                                .context("usage proof must be object")?
                                .insert("source_path".into(), relative.clone().into());
                            usage_proofs.push(proof);
                        }
                    }
                }

                let exact_binding_proofs =
                    exact_module_usage_proofs(&usage_proofs, string_field(module, "sha256"));
                let mut relation = serde_json::Map::new();
                for field in [
                    "block",
                    "host_effect_value",
                    "host_wrapper_function",
                    "host_import_function",
                    "memory_read_value",
                    "memory_read_helper",
                    "base_value",
                    "runtime_binding",
                ] {
                    relation.insert(
                        field.into(),
                        pair.get(field).cloned().unwrap_or(Value::Null),
                    );
                }
                let mut row = json!({
                    "module_sha256": module.get("sha256").cloned().unwrap_or(Value::Null),
                    "export": export.get("export").cloned().unwrap_or(Value::Null),
                    "host_import": host_import,
                    "raw_host_import_module": raw_module,
                    "raw_host_import": raw_import,
                    "offset": offset,
                    "carrier_candidates": carrier_candidates,
                    "correlation_basis": "exact_import_module_and_name",
                    "js_import_object_instantiation_site_proven": usage_proofs.len() == 1,
                    "js_import_object_instantiation_site_proofs": usage_proofs,
                    "import_binding_identity_proven": exact_binding_proofs.len() == 1,
                    "import_binding_identity_proofs": exact_binding_proofs,
                    "import_binding_identity_limitation": if exact_binding_proofs.len() == 1 {
                        Value::Null
                    } else {
                        "no unique carrier proof ties this exact recovered module SHA to the exact import object at one WebAssembly instantiation site".into()
                    },
                    "js_set_u32_shape_proven": proofs.len() == 1,
                    "js_set_u32_shape_proofs": proofs,
                    "wasm_relation": Value::Object(relation),
                });
                let mut ambiguities = Vec::new();
                if proofs.len() > 1 {
                    row["js_set_u32_shape_proven"] = false.into();
                    ambiguities.push("multiple carrier sources prove the same import write/offset");
                }
                if usage_proofs.len() > 1 {
                    row["js_import_object_instantiation_site_proven"] = false.into();
                    ambiguities.push(
                        "multiple carrier sources prove import-object WebAssembly instantiation sites",
                    );
                }
                if exact_binding_proofs.len() > 1 {
                    row["import_binding_identity_proven"] = false.into();
                    ambiguities.push(
                        "multiple carrier sources prove exact module/import-object binding identity",
                    );
                }
                if !ambiguities.is_empty() {
                    row["ambiguity"] = ambiguities.join("; ").into();
                }
                host_effect_rows.push(row);
            }

            for candidate in array_field(analysis, "externref_bulk_copy_candidates") {
                let set_import = usize_field(candidate, "set_import_function")
                    .and_then(|index| function_imports.get(index));
                let constructor_import = usize_field(candidate, "constructor_import_function")
                    .and_then(|index| function_imports.get(index));
                let memory_import =
                    usize_field(candidate, "constructor_input_memory_import_function")
                        .and_then(|index| function_imports.get(index));
                let set_module = set_import.and_then(|imported| string_field(imported, "module"));
                let set_name = set_import.and_then(|imported| string_field(imported, "name"));
                let constructor_module =
                    constructor_import.and_then(|imported| string_field(imported, "module"));
                let constructor_name =
                    constructor_import.and_then(|imported| string_field(imported, "name"));
                let memory_module =
                    memory_import.and_then(|imported| string_field(imported, "module"));
                let memory_name = memory_import.and_then(|imported| string_field(imported, "name"));

                let mut proofs = Vec::new();
                if let (
                    Some(set_module),
                    Some(set_name),
                    Some(constructor_module),
                    Some(constructor_name),
                ) = (set_module, set_name, constructor_module, constructor_name)
                {
                    for relative in &carrier_candidates {
                        let source = project.join(relative);
                        if !source.is_file() {
                            continue;
                        }
                        carrier_sources.insert(relative.clone());
                        if !full_cache.contains_key(relative) {
                            full_cache.insert(relative.clone(), semantics_for_source(&source)?);
                        }
                        let document = full_cache
                            .get(relative)
                            .context("missing full semantics cache")?;
                        let set_matches =
                            matching_handler(document, set_module, set_name, "typed_array_set");
                        let constructor_matches = matching_handler(
                            document,
                            constructor_module,
                            constructor_name,
                            "uint32_array_constructor",
                        )
                        .into_iter()
                        .filter(|handler| usize_field(handler, "element_width_bits") == Some(32))
                        .collect::<Vec<_>>();
                        if set_matches.len() != 1 || constructor_matches.len() != 1 {
                            continue;
                        }
                        let set_usages = matching_usages(document, set_module, set_name);
                        let constructor_usages =
                            matching_usages(document, constructor_module, constructor_name);
                        let binding_proofs = common_exact_binding_proofs(
                            &set_usages,
                            &constructor_usages,
                            string_field(module, "sha256"),
                        );
                        let memory_proofs = matching_module_memory_proofs(
                            document,
                            memory_module,
                            memory_name,
                            string_field(module, "sha256"),
                            export_name,
                            &binding_proofs,
                            &report,
                            candidate,
                        );
                        let length_barrier_proofs = source_length_barrier_proofs(
                            document,
                            &function_imports,
                            candidate,
                            string_field(module, "sha256"),
                            &binding_proofs,
                        );
                        proofs.push(json!({
                            "source_path": relative,
                            "set_handler": set_matches[0],
                            "constructor_handler": constructor_matches[0],
                            "import_binding_identity_proofs": binding_proofs,
                            "module_memory_identity_proofs": memory_proofs,
                            "source_length_barrier_proofs": length_barrier_proofs,
                        }));
                    }
                }

                let copied_binding_proofs = proofs
                    .iter()
                    .flat_map(|proof| {
                        let source = string_field(proof, "source_path")
                            .unwrap_or_default()
                            .to_owned();
                        array_field(proof, "import_binding_identity_proofs")
                            .iter()
                            .cloned()
                            .map(move |mut binding| {
                                if let Some(object) = binding.as_object_mut() {
                                    object.insert("source_path".into(), source.clone().into());
                                }
                                binding
                            })
                    })
                    .collect::<Vec<_>>();
                let module_memory_proofs = proofs
                    .iter()
                    .flat_map(|proof| {
                        let source = string_field(proof, "source_path")
                            .unwrap_or_default()
                            .to_owned();
                        array_field(proof, "module_memory_identity_proofs")
                            .iter()
                            .cloned()
                            .map(move |mut memory| {
                                if let Some(object) = memory.as_object_mut() {
                                    object.insert("source_path".into(), source.clone().into());
                                }
                                memory
                            })
                    })
                    .collect::<Vec<_>>();
                let module_memory_sources = module_memory_proofs
                    .iter()
                    .filter_map(|proof| string_field(proof, "source_path"))
                    .collect::<BTreeSet<_>>();
                let module_memory_proven = !module_memory_proofs.is_empty()
                    && module_memory_sources.len() == 1
                    && proofs.len() == 1
                    && copied_binding_proofs.len() == 1;
                let destination_loads = array_field(candidate, "destination_loads");
                let source_length_lower_bound = fixed_uint32_source_length_lower_bound(
                    if module_memory_proven {
                        &module_memory_proofs
                    } else {
                        &[]
                    },
                    export_name,
                    usize_field(candidate, "source_entry_parameter"),
                );
                let required_length_barriers = destination_loads
                    .iter()
                    .flat_map(|load| array_field(load, "source_length_import_barriers"))
                    .filter_map(Value::as_u64)
                    .filter_map(|value| usize::try_from(value).ok())
                    .collect::<BTreeSet<_>>();
                let length_barrier_proofs = proofs
                    .iter()
                    .flat_map(|proof| {
                        let source = string_field(proof, "source_path")
                            .unwrap_or_default()
                            .to_owned();
                        array_field(proof, "source_length_barrier_proofs")
                            .iter()
                            .cloned()
                            .map(move |mut barrier| {
                                if let Some(object) = barrier.as_object_mut() {
                                    object.insert("source_path".into(), source.clone().into());
                                }
                                barrier
                            })
                    })
                    .collect::<Vec<_>>();
                let proven_length_barriers = length_barrier_proofs
                    .iter()
                    .filter_map(|proof| usize_field(proof, "function_import"))
                    .collect::<BTreeSet<_>>();
                let required_internal_barriers = destination_loads
                    .iter()
                    .flat_map(|load| array_field(load, "internal_memory_mutation_call_barriers"))
                    .filter_map(Value::as_u64)
                    .filter_map(|value| usize::try_from(value).ok())
                    .collect::<BTreeSet<_>>();
                let base_destination_byte_integrity_proven = !destination_loads.is_empty()
                    && source_length_lower_bound.is_some()
                    && destination_loads.iter().all(|load| {
                        bool_field(load, "unresolved_intervening_memory_mutation") == Some(false)
                            && array_field(load, "other_import_call_barriers").is_empty()
                    })
                    && proven_length_barriers == required_length_barriers
                    && (required_length_barriers.is_empty() || proofs.len() == 1);
                let element_shift = usize_field(candidate, "destination_element_index_shift");
                let base_zero_bits =
                    usize_field(candidate, "destination_base_guaranteed_trailing_zero_bits");
                let static_destination_base_alignment_proven =
                    element_shift == Some(2) && base_zero_bits.is_some_and(|bits| bits >= 2);

                let mut fresh_alignment_proof = None;
                let mut fresh_document = None;
                if module_memory_proven && module_memory_sources.len() == 1 {
                    if let Some(source_path) = module_memory_sources.iter().next() {
                        fresh_document = full_cache.get(*source_path);
                        if let Some(document) = fresh_document {
                            fresh_alignment_proof = fresh_destination_alignment_proof(
                                project,
                                module,
                                &report,
                                &function_imports,
                                document,
                                candidate,
                                &module_memory_proofs,
                                &copied_binding_proofs,
                                export_name,
                            );
                        }
                    }
                }
                let destination_base_alignment_proven =
                    static_destination_base_alignment_proven || fresh_alignment_proof.is_some();
                let fresh_cleanup_proof = if base_destination_byte_integrity_proven
                    && !required_internal_barriers.is_empty()
                {
                    match (fresh_document, fresh_alignment_proof.as_ref()) {
                        (Some(document), Some(alignment)) => fresh_cleanup_disjointness_proof(
                            project,
                            module,
                            &function_imports,
                            document,
                            candidate,
                            &module_memory_proofs,
                            &copied_binding_proofs,
                            Some(alignment),
                        ),
                        _ => None,
                    }
                } else {
                    None
                };
                let destination_byte_integrity_proven = base_destination_byte_integrity_proven
                    && (required_internal_barriers.is_empty() || fresh_cleanup_proof.is_some());
                let (destination_load_interpretations, _) = interpreted_destination_loads(
                    candidate,
                    if module_memory_proven {
                        &module_memory_proofs
                    } else {
                        &[]
                    },
                    export_name,
                    destination_byte_integrity_proven,
                    destination_base_alignment_proven,
                );
                let destination_load_interpretation_proven = module_memory_proven
                    && destination_byte_integrity_proven
                    && !destination_load_interpretations.is_empty()
                    && destination_load_interpretations.len() == destination_loads.len();
                let (source_word_runtime_bindings, source_word_returns, runtime_graph_proven) =
                    if destination_load_interpretation_proven {
                        source_word_semantic_overlay(analysis, &destination_load_interpretations)
                    } else {
                        (Vec::new(), Vec::new(), false)
                    };
                let source_word_semantic_overlay_proven = destination_load_interpretation_proven
                    && !source_word_runtime_bindings.is_empty()
                    && source_word_runtime_bindings.len() == destination_load_interpretations.len();
                let source_word_return_dependencies_proven = source_word_semantic_overlay_proven
                    && runtime_graph_proven
                    && !source_word_returns.is_empty();

                let destination_alignment_basis = if static_destination_base_alignment_proven {
                    Value::String("static_ssa".into())
                } else if fresh_alignment_proof.is_some() {
                    Value::String("fresh_exact_evaluation".into())
                } else {
                    Value::Null
                };
                let destination_load_limitation = if destination_load_interpretation_proven {
                    Value::Null
                } else if !module_memory_proven {
                    "module-memory identity is not proven".into()
                } else if !destination_byte_integrity_proven {
                    "a potentially memory-mutating path exists between the proven Uint32Array.set and at least one destination load".into()
                } else if !destination_base_alignment_proven {
                    "the destination base is not proven aligned to the Uint32Array element width"
                        .into()
                } else {
                    "the exact carrier export-call argument is not proven to be a fixed-length Uint32Array covering every destination load".into()
                };
                let source_word_overlay_limitation = if source_word_semantic_overlay_proven {
                    Value::Null
                } else if !destination_load_interpretation_proven {
                    "destination-load interpretation is not proven".into()
                } else {
                    "the deep runtime-binding report does not preserve a unique binding for every interpreted load SSA value".into()
                };
                let source_word_return_limitation = if source_word_return_dependencies_proven {
                    Value::Null
                } else if !source_word_semantic_overlay_proven {
                    "source-word runtime binding identity is not proven".into()
                } else {
                    "the deep runtime dependency graph or semantic return records are missing, invalid, cyclic, or empty".into()
                };

                let mut row = json!({
                    "module_sha256": module.get("sha256").cloned().unwrap_or(Value::Null),
                    "export": export.get("export").cloned().unwrap_or(Value::Null),
                    "carrier_candidates": carrier_candidates,
                    "correlation_basis": "exact_import_module_and_name",
                    "raw_set_import_module": set_module,
                    "raw_set_import": set_name,
                    "raw_constructor_import_module": constructor_module,
                    "raw_constructor_import": constructor_name,
                    "raw_memory_import_module": memory_module,
                    "raw_memory_import": memory_name,
                    "wasm_structural_copy_candidate_proven": true,
                    "wasm_candidate": candidate,
                    "js_typed_array_copy_semantics_proven": proofs.len() == 1,
                    "js_typed_array_copy_semantics_proofs": proofs,
                    "import_binding_identity_proven": copied_binding_proofs.len() == 1,
                    "import_binding_identity_proofs": copied_binding_proofs,
                    "module_memory_identity_proven": module_memory_proven,
                    "module_memory_identity_proofs": module_memory_proofs,
                    "module_memory_identity_limitation": if module_memory_proven { Value::Null } else { "no unique carrier source proves that the constructor input comes from the exported memory of the exact module instance executing this copied-input export".into() },
                    "destination_byte_integrity_proven": destination_byte_integrity_proven,
                    "required_internal_memory_mutation_call_barriers": required_internal_barriers,
                    "fresh_cleanup_disjointness_proof": fresh_cleanup_proof,
                    "source_length_barrier_proofs": length_barrier_proofs,
                    "static_destination_base_alignment_proven": static_destination_base_alignment_proven,
                    "fresh_destination_base_alignment_proof": fresh_alignment_proof,
                    "destination_base_alignment_proven": destination_base_alignment_proven,
                    "destination_base_alignment_basis": destination_alignment_basis,
                    "destination_load_interpretation_proven": destination_load_interpretation_proven,
                    "destination_load_interpretations": destination_load_interpretations,
                    "source_word_semantic_overlay_proven": source_word_semantic_overlay_proven,
                    "source_word_runtime_bindings": source_word_runtime_bindings,
                    "runtime_dependency_graph_proven": runtime_graph_proven,
                    "source_word_return_dependencies_proven": source_word_return_dependencies_proven,
                    "source_word_returns": if source_word_return_dependencies_proven { Value::Array(source_word_returns) } else { Value::Array(Vec::new()) },
                    "source_word_return_dependencies_limitation": source_word_return_limitation,
                    "source_word_semantic_overlay_limitation": source_word_overlay_limitation,
                    "source_uint32_array_length_lower_bound": source_length_lower_bound,
                    "destination_load_interpretation_limitation": destination_load_limitation,
                    "destination_load_interpretation_contract": "each proven i32.load reads the unchanged Uint32Array.set destination word corresponding to ToUint32(source[index]); numeric equality requires little-endian typed-array storage",
                });
                if proofs.len() > 1 {
                    row["js_typed_array_copy_semantics_proven"] = false.into();
                    row["ambiguity"] =
                        "multiple carrier sources prove the same constructor/set import semantics"
                            .into();
                }
                if copied_binding_proofs.len() > 1 {
                    row["import_binding_identity_proven"] = false.into();
                    let prefix = string_field(&row, "ambiguity").unwrap_or_default();
                    row["ambiguity"] = format!(
                        "{}{}multiple exact module/import-object binding proofs",
                        prefix,
                        if prefix.is_empty() { "" } else { "; " }
                    )
                    .into();
                }
                if module_memory_sources.len() > 1 {
                    row["module_memory_identity_proven"] = false.into();
                    row["module_memory_identity_limitation"] =
                        "multiple carrier sources prove module-memory identity".into();
                    let prefix = string_field(&row, "ambiguity").unwrap_or_default();
                    row["ambiguity"] = format!(
                        "{}{}multiple module-memory carrier proofs",
                        prefix,
                        if prefix.is_empty() { "" } else { "; " }
                    )
                    .into();
                }
                copied_input_rows.push(row);
            }
        }
    }

    let module_count = host_effect_rows
        .iter()
        .chain(&copied_input_rows)
        .filter_map(|row| string_field(row, "module_sha256"))
        .collect::<BTreeSet<_>>()
        .len();
    let summary = json!({
        "host_effect_pairs": host_effect_rows.len(),
        "proven_js_set_u32_shapes": host_effect_rows.iter().filter(|row| bool_field(row, "js_set_u32_shape_proven") == Some(true)).count(),
        "proven_js_import_object_instantiation_sites": host_effect_rows.iter().filter(|row| bool_field(row, "js_import_object_instantiation_site_proven") == Some(true)).count(),
        "opaque_host_effect_pairs": host_effect_rows.iter().filter(|row| bool_field(row, "js_set_u32_shape_proven") != Some(true)).count(),
        "copied_input_candidates": copied_input_rows.len(),
        "proven_js_typed_array_copy_semantics": copied_input_rows.iter().filter(|row| bool_field(row, "js_typed_array_copy_semantics_proven") == Some(true)).count(),
        "proven_host_import_binding_identities": host_effect_rows.iter().filter(|row| bool_field(row, "import_binding_identity_proven") == Some(true)).count(),
        "proven_copied_input_binding_identities": copied_input_rows.iter().filter(|row| bool_field(row, "import_binding_identity_proven") == Some(true)).count(),
        "proven_module_memory_identities": copied_input_rows.iter().filter(|row| bool_field(row, "module_memory_identity_proven") == Some(true)).count(),
        "proven_destination_byte_integrities": copied_input_rows.iter().filter(|row| bool_field(row, "destination_byte_integrity_proven") == Some(true)).count(),
        "proven_destination_base_alignments": copied_input_rows.iter().filter(|row| bool_field(row, "destination_base_alignment_proven") == Some(true)).count(),
        "proven_destination_load_interpretations": copied_input_rows.iter().filter(|row| bool_field(row, "destination_load_interpretation_proven") == Some(true)).count(),
        "proven_source_word_semantic_overlays": copied_input_rows.iter().filter(|row| bool_field(row, "source_word_semantic_overlay_proven") == Some(true)).count(),
        "proven_source_word_return_dependencies": copied_input_rows.iter().filter(|row| bool_field(row, "source_word_return_dependencies_proven") == Some(true)).count(),
        "modules": module_count,
        "carrier_sources": carrier_sources.len(),
        "probe_invocations": targeted_cache.len() + full_cache.len(),
        "skipped_modules": skipped_modules.len(),
    });
    let document = json!({
        "schema": WASM_JS_BOUNDARY.schema,
        "wasm_schema_required": "wasm-redox/deep-v14",
        "js_schema": "jsvm-wasm-import-semantics/v8",
        "safe_static_only": true,
        "bounded_wasm_ir_interpretation": true,
        "source_word_semantic_overlay_contract": "deep runtime bindings and semantic returns preserve raw plus normalized structured semantic IR and exact SSA runtime-dependency edges. Boundary validation requires both IR forms to have the same exact runtime leaf set as the declared direct dependencies and to contain no duplicate definitions or dangling SSA references. Proven copied loads become source_word leaves in both boundary IR forms; unmatched runtime leaves retain exact identity plus transitive source-word provenance. Presentation is rendered from the validated structured IR; no $runtimeN text matching is used.",
        "correlation_contract": "cross-language claims require exact WASM import module+name matches. Host-effect writes and typed-array input-copy candidates remain independent evidence families; source-word interpretation additionally requires exact instance/exported-memory identity, path-complete destination-byte integrity, destination-base element alignment, and fixed Uint32Array source coverage. Fresh-state alignment may use bounded Waffle-IR interpretation only after rejecting module start functions, imported state, imported or indirect calls, recursion, and all table operations in the evaluated call graph.",
        "memory_write_interpretation": "DataView and typed-array interpretations require standard unmodified platform builtins; numeric equality between Uint32Array elements and WASM i32 loads additionally requires little-endian typed-array storage",
        "host_effect_rows": host_effect_rows,
        "copied_input_rows": copied_input_rows,
        "skipped_modules": skipped_modules,
        "summary": summary,
    });
    write_artifact(project, WASM_JS_BOUNDARY, &document)?;

    Ok(WasmJsBoundarySummary {
        host_effect_pairs: usize_field(&document["summary"], "host_effect_pairs").unwrap_or(0),
        proven_js_set_u32_shapes: usize_field(&document["summary"], "proven_js_set_u32_shapes")
            .unwrap_or(0),
        copied_input_candidates: usize_field(&document["summary"], "copied_input_candidates")
            .unwrap_or(0),
        proven_js_typed_array_copy_semantics: usize_field(
            &document["summary"],
            "proven_js_typed_array_copy_semantics",
        )
        .unwrap_or(0),
        proven_module_memory_identities: usize_field(
            &document["summary"],
            "proven_module_memory_identities",
        )
        .unwrap_or(0),
        proven_destination_load_interpretations: usize_field(
            &document["summary"],
            "proven_destination_load_interpretations",
        )
        .unwrap_or(0),
    })
}

#[cfg(test)]
mod tests {
    use super::source_word_semantic_overlay;
    use serde_json::json;

    #[test]
    fn source_word_overlay_tracks_transitive_runtime_dependencies() {
        let analysis = json!({
            "runtime_bindings": [
                {
                    "value": 10,
                    "name": "$runtime0",
                    "expression": "i32load<memory0, align=2, offset=8>($arg0)",
                    "semantic_ir": {
                        "kind": "operation",
                        "value": 10,
                        "operator": "i32load<memory0, align=2, offset=8>",
                        "arguments": [{"kind": "argument", "index": 0}],
                    },
                    "normalized_semantic_ir": {
                        "kind": "operation",
                        "value": 10,
                        "operator": "i32load<memory0, align=2, offset=8>",
                        "arguments": [{"kind": "argument", "index": 0}],
                    },
                    "runtime_dependencies": [],
                },
                {
                    "value": 20,
                    "name": "$runtime1",
                    "expression": "host.transform($runtime0)",
                    "semantic_ir": {
                        "kind": "operation",
                        "value": 20,
                        "operator": "host.transform",
                        "arguments": [{"kind": "runtime", "value": 10, "name": "$runtime0"}],
                    },
                    "normalized_semantic_ir": {
                        "kind": "operation",
                        "value": 20,
                        "operator": "host.transform",
                        "arguments": [{"kind": "runtime", "value": 10, "name": "$runtime0"}],
                    },
                    "runtime_dependencies": [10],
                },
            ],
            "returns": [{
                "value": 30,
                "expression": "$runtime1",
                "semantic_ir": {"kind": "runtime", "value": 20, "name": "$runtime1"},
                "normalized_semantic_ir": {"kind": "runtime", "value": 20, "name": "$runtime1"},
                "runtime_dependencies": [20],
            }],
        });
        let interpretations = vec![json!({
            "load_value": 10,
            "source_parameter": 0,
            "source_element_index": 2,
            "source_conversion": "ToUint32",
        })];
        let (bindings, returns, proven) = source_word_semantic_overlay(&analysis, &interpretations);
        assert!(proven);
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0]["load_value"], 10);
        assert_eq!(bindings[0]["semantic_expression"], "source_u32(arg0, 2)");
        assert_eq!(returns.len(), 1);
        let result = &returns[0];
        assert_eq!(result["runtime_dependencies"], json!([20]));
        assert_eq!(result["transitive_runtime_dependencies"], json!([10, 20]));
        assert_eq!(
            result["source_word_dependencies"][0]["source_element_index"],
            2
        );
        assert_eq!(result["raw_source_word_expression"], "$runtime1");
        assert_eq!(result["source_word_expression"], "$runtime1");
        assert_eq!(
            result["source_word_semantic_ir"],
            json!({
                "kind": "runtime",
                "value": 20,
                "name": "$runtime1",
                "source_word_dependencies": [{
                    "load_value": 10,
                    "runtime_binding": "$runtime0",
                    "source_parameter": 0,
                    "source_element_index": 2,
                    "source_conversion": "ToUint32",
                }],
            })
        );

        let mut inconsistent = analysis.clone();
        inconsistent["returns"][0]["semantic_ir"] =
            json!({"kind": "runtime", "value": 10, "name": "$runtime0"});
        let (bad_bindings, bad_returns, bad_graph) =
            source_word_semantic_overlay(&inconsistent, &interpretations);
        assert!(!bad_graph);
        assert!(bad_bindings.is_empty());
        assert!(bad_returns.is_empty());

        let mut normalization_mismatch = analysis.clone();
        normalization_mismatch["returns"][0]["normalized_semantic_ir"] =
            json!({"kind": "runtime", "value": 10, "name": "$runtime0"});
        let (bad_bindings, bad_returns, bad_graph) =
            source_word_semantic_overlay(&normalization_mismatch, &interpretations);
        assert!(!bad_graph);
        assert!(bad_bindings.is_empty());
        assert!(bad_returns.is_empty());

        let mut cyclic = analysis.clone();
        cyclic["runtime_bindings"][0]["runtime_dependencies"] = json!([20]);
        cyclic["runtime_bindings"][0]["semantic_ir"] =
            json!({"kind": "runtime", "value": 20, "name": "$runtime1"});
        cyclic["runtime_bindings"][0]["normalized_semantic_ir"] =
            cyclic["runtime_bindings"][0]["semantic_ir"].clone();
        cyclic["runtime_bindings"][1]["runtime_dependencies"] = json!([10]);
        cyclic["runtime_bindings"][1]["semantic_ir"] =
            json!({"kind": "runtime", "value": 10, "name": "$runtime0"});
        cyclic["runtime_bindings"][1]["normalized_semantic_ir"] =
            cyclic["runtime_bindings"][1]["semantic_ir"].clone();
        let (bad_bindings, bad_returns, bad_graph) =
            source_word_semantic_overlay(&cyclic, &interpretations);
        assert!(!bad_graph);
        assert!(bad_bindings.is_empty());
        assert!(bad_returns.is_empty());
    }
}
