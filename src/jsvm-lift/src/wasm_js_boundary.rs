use crate::{
    analysis_artifacts::{
        load_artifact, write_artifact, DEOBFUSCATION, WASM_INDEX, WASM_JS_BOUNDARY,
    },
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
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
use work_budget::WorkBudget;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmJsBoundarySummary {
    pub host_effect_pairs: usize,
    pub proven_js_set_u32_shapes: usize,
    pub copied_input_candidates: usize,
    pub proven_js_typed_array_copy_semantics: usize,
    pub proven_module_memory_identities: usize,
    pub proven_destination_load_interpretations: usize,
}

type RuntimeBindingMap = BTreeMap<i64, Value>;
type RuntimeDependencyGraph = BTreeMap<i64, Vec<i64>>;
type SemanticRuntimeGraph = (RuntimeBindingMap, RuntimeDependencyGraph, Vec<Value>);

struct ModuleMemoryMatchContext<'a> {
    document: &'a Value,
    module_sha256: Option<&'a str>,
    export_name: Option<&'a str>,
    binding_proofs: &'a [Value],
    report: &'a Value,
}

struct CopiedInputProofContext<'a> {
    project: &'a Path,
    module: &'a Value,
    report: &'a Value,
    function_imports: &'a [Value],
    document: &'a Value,
    module_memory_proofs: &'a [Value],
    binding_proofs: &'a [Value],
    export_name: Option<&'a str>,
    budget: &'a WorkBudget,
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

fn visit_runtime_dependency(
    value: i64,
    graph: &BTreeMap<i64, Vec<i64>>,
    state: &mut BTreeMap<i64, u8>,
) -> bool {
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
        .all(|dependency| visit_runtime_dependency(*dependency, graph, state))
    {
        return false;
    }
    state.insert(value, 2);
    true
}

fn semantic_runtime_graph(analysis: &Value) -> Option<SemanticRuntimeGraph> {
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
    if !graph
        .keys()
        .copied()
        .all(|value| visit_runtime_dependency(value, &graph, &mut state))
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
    context: &ModuleMemoryMatchContext<'_>,
    import_module: Option<&str>,
    import_name: Option<&str>,
    candidate: &Value,
) -> Vec<Value> {
    let (Some(import_module), Some(import_name), Some(module_sha256), Some(export_name)) = (
        import_module,
        import_name,
        context.module_sha256,
        context.export_name,
    ) else {
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
    let binding_sites = context
        .binding_proofs
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
    let mut matching_proofs = Vec::new();
    for proof in array_field(context.document, "module_memory_identity_proofs") {
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
        let memory_exports = array_field(context.report, "exports")
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
        let mut annotated_proof = proof.clone();
        if let Some(object) = annotated_proof.as_object_mut() {
            object.insert("memory_export".into(), memory_export.clone());
        }
        matching_proofs.push(annotated_proof);
    }
    matching_proofs
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

struct FreshAlignmentInputs {
    function: usize,
    length_import_index: usize,
    length_shift: usize,
    exact_source_length: usize,
    exact_source_length_u32: u32,
    exports_binding: String,
}

impl FreshAlignmentInputs {
    /// Reject malformed allocator recipes and require one disjoint-effects
    /// initializer source with the exact static `Uint32Array` argument length.
    fn verify(context: &CopiedInputProofContext<'_>, candidate: &Value) -> Option<Self> {
        let recipe = candidate
            .get("fresh_destination_base_recipe")?
            .as_object()?;
        let export_name = context.export_name?;
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
        let _length_import = context.function_imports.get(length_import_index)?;
        let source_parameter = usize_field(candidate, "source_entry_parameter");
        let exact_source_length = fixed_uint32_source_length_exact(
            context.module_memory_proofs,
            Some(export_name),
            source_parameter,
        )?;
        let exact_source_length_u32 = u32::try_from(exact_source_length).ok()?;
        if exact_source_length_u32 > (u32::MAX >> length_shift) {
            return None;
        }

        let mut exports_bindings = BTreeSet::new();
        for proof in context.module_memory_proofs {
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
            if argument_lengths.get(source_parameter)?.as_u64()?
                != u64::from(exact_source_length_u32)
            {
                return None;
            }
        }
        if exports_bindings.len() != 1 {
            return None;
        }
        let exports_binding = exports_bindings.iter().next()?.clone();
        Some(Self {
            function,
            length_import_index,
            length_shift,
            exact_source_length,
            exact_source_length_u32,
            exports_binding,
        })
    }
}

struct FreshStartEvidence {
    start_export: Value,
    start_import: Value,
    start_usage: Value,
    start_handler: Value,
    table_export: Value,
}

impl FreshStartEvidence {
    /// Require one exact start export, matching table-only normalized handler,
    /// and one import-object binding for the same module instance.
    fn verify(context: &CopiedInputProofContext<'_>, exports_binding: &str) -> Option<Self> {
        let start_exports = array_field(context.report, "exports")
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
        let start_import = context.function_imports.get(start_function)?;
        let start_module = string_field(start_import, "module")?;
        let start_name = string_field(start_import, "name")?;

        let table_exports = array_field(context.report, "exports")
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

        let normalized_handlers =
            array_field(context.document, "proof_normalized_handler_semantics")
                .iter()
                .filter(|handler| {
                    string_field(handler, "import_module") == Some(start_module)
                        && string_field(handler, "import_name") == Some(start_name)
                        && string_field(handler, "kind") == Some("table_initializer_only")
                        && string_field(handler, "exports_binding") == Some(exports_binding)
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

        let start_usages = array_field(context.document, "import_object_usages")
            .iter()
            .filter(|usage| {
                string_field(usage, "import_module") == Some(start_module)
                    && string_field(usage, "import_name") == Some(start_name)
            })
            .cloned()
            .collect::<Vec<_>>();
        let exact_start_usages =
            exact_module_usage_proofs(&start_usages, string_field(context.module, "sha256"))
                .into_iter()
                .filter(|usage| exact_usage_matches_binding(usage, context.binding_proofs))
                .collect::<Vec<_>>();
        let [start_usage] = exact_start_usages.as_slice() else {
            return None;
        };
        Some(Self {
            start_export: start_export.clone(),
            start_import: start_import.clone(),
            start_usage: start_usage.clone(),
            start_handler: start_handler.clone(),
            table_export: table_export.clone(),
        })
    }
}

fn fresh_destination_alignment_proof(
    context: &CopiedInputProofContext<'_>,
    candidate: &Value,
) -> Option<Value> {
    let FreshAlignmentInputs {
        function,
        length_import_index,
        length_shift,
        exact_source_length,
        exact_source_length_u32,
        exports_binding,
    } = FreshAlignmentInputs::verify(context, candidate)?;
    let FreshStartEvidence {
        start_export,
        start_import,
        start_usage,
        start_handler,
        table_export,
    } = FreshStartEvidence::verify(context, &exports_binding)?;
    let length_import = context.function_imports.get(length_import_index)?;
    if string_field(length_import, "module").is_none()
        || string_field(length_import, "name").is_none()
    {
        return None;
    }
    let (binary_path, module_sha256, bytes) =
        verified_module_bytes(context.project, context.module)?;
    let byte_count = exact_source_length_u32.checked_shl(u32::try_from(length_shift).ok()?)?;
    let evaluation =
        evaluate_fresh_i32_call(&bytes, function, &[byte_count], None, context.budget).ok()?;
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

struct FreshCleanupSetup {
    slot_allocator: usize,
    cleanup_function: usize,
    memory_import_index: usize,
    buffer_index: usize,
    buffer_handler: Value,
    binding_import_object: String,
}

impl FreshCleanupSetup {
    /// Only the exact single buffer getter from the same import object as
    /// memory may be bypassed during the bounded fresh cleanup sequence.
    fn verify(context: &CopiedInputProofContext<'_>, candidate: &Value) -> Option<Self> {
        let recipe = candidate
            .get("fresh_cleanup_disjointness_recipe")?
            .as_object()?;
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
        let memory_import_index =
            usize_field(candidate, "constructor_input_memory_import_function")?;
        if !bypassed_imports.contains(&memory_import_index)
            || bypassed_imports
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                .len()
                != 2
            || context.module_memory_proofs.is_empty()
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
        let buffer_import = context.function_imports.get(*buffer_index)?;
        let buffer_module = string_field(buffer_import, "module")?;
        let buffer_name = string_field(buffer_import, "name")?;
        let binding_import_objects = context
            .binding_proofs
            .iter()
            .filter_map(|proof| string_field(proof, "import_object"))
            .collect::<BTreeSet<_>>();
        if binding_import_objects.len() != 1 {
            return None;
        }
        let binding_import_object = (*binding_import_objects.iter().next()?).to_owned();
        let buffer_handlers = matching_handler(
            context.document,
            buffer_module,
            buffer_name,
            "property_getter",
        )
        .into_iter()
        .filter(|handler| {
            string_field(handler, "property") == Some("buffer")
                && bool_field(handler, "standard_builtin_semantics_required") == Some(true)
                && string_field(handler, "import_object") == Some(binding_import_object.as_str())
        })
        .collect::<Vec<_>>();
        let [buffer_handler] = buffer_handlers.as_slice() else {
            return None;
        };
        Some(Self {
            slot_allocator,
            cleanup_function,
            memory_import_index,
            buffer_index: *buffer_index,
            buffer_handler: buffer_handler.clone(),
            binding_import_object,
        })
    }
}

struct FreshCleanupSequence {
    destination_base: u32,
    byte_count: u32,
    calls: Vec<FreshI32CallRequest>,
    table_grows: Vec<FreshTableGrowRequest>,
}

impl FreshCleanupSequence {
    /// The exact call sequence allocates three independent slots and then
    /// frees them in observed order after the copy boundary.
    fn verify(
        candidate: &Value,
        fresh_alignment_proof: &Value,
        setup: &FreshCleanupSetup,
    ) -> Option<Self> {
        let slot_allocator = setup.slot_allocator;
        let cleanup_function = setup.cleanup_function;
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
        Some(Self {
            destination_base,
            byte_count,
            calls,
            table_grows,
        })
    }
}

struct FreshCleanupRange {
    target_memory: usize,
    range_start: u64,
    range_end: u64,
    post_copy_accesses: Vec<Value>,
}

impl FreshCleanupRange {
    /// Every post-copy access, not just each known write, must be disjoint
    /// from the exact protected destination region; missing fields fail shut.
    fn verify(
        candidate: &Value,
        cleanup_function: usize,
        destination_base: u32,
        byte_count: u32,
        evaluation_value: &Value,
    ) -> Option<Self> {
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
        let post_copy_accesses = array_field(evaluation_value, "steps")
            .iter()
            .skip(5)
            .flat_map(|step| array_field(step, "memory_accesses").iter().cloned())
            .collect::<Vec<_>>();
        if !post_copy_accesses.iter().all(|access| {
            access_is_disjoint_from_range(access, target_memory, range_start, range_end)
        }) {
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
        Some(Self {
            target_memory,
            range_start,
            range_end,
            post_copy_accesses,
        })
    }
}

fn fresh_cleanup_disjointness_proof(
    context: &CopiedInputProofContext<'_>,
    candidate: &Value,
    fresh_alignment_proof: Option<&Value>,
) -> Option<Value> {
    let setup = FreshCleanupSetup::verify(context, candidate)?;
    let alignment = fresh_alignment_proof?;
    let sequence = FreshCleanupSequence::verify(candidate, alignment, &setup)?;
    let (_, module_sha256, bytes) = verified_module_bytes(context.project, context.module)?;
    let evaluation = evaluate_fresh_i32_sequence(
        &bytes,
        &sequence.table_grows,
        &sequence.calls,
        None,
        context.budget,
    )
    .ok()?;
    if evaluation.outcome != FreshEvalOutcome::Returned
        || evaluation.steps.len() != sequence.calls.len()
    {
        return None;
    }
    if evaluation.steps.first()?.i32_result != Some(sequence.destination_base) {
        return None;
    }
    let slot_results = [1usize, 2, 3]
        .into_iter()
        .map(|index| evaluation.steps.get(index)?.i32_result)
        .collect::<Option<Vec<_>>>()?;
    if slot_results.iter().copied().collect::<BTreeSet<_>>().len() != 3 {
        return None;
    }
    let evaluation_value = serde_json::to_value(&evaluation).ok()?;
    let range = FreshCleanupRange::verify(
        candidate,
        setup.cleanup_function,
        sequence.destination_base,
        sequence.byte_count,
        &evaluation_value,
    )?;
    let FreshCleanupSetup {
        memory_import_index,
        buffer_index,
        buffer_handler,
        binding_import_object,
        ..
    } = setup;
    let FreshCleanupSequence { table_grows, .. } = sequence;
    let FreshCleanupRange {
        target_memory,
        range_start,
        range_end,
        post_copy_accesses,
    } = range;
    Some(json!({
        "fresh_instance_state_required": true,
        "module_sha256": module_sha256,
        "recipe": candidate.get("fresh_cleanup_disjointness_recipe").cloned().unwrap_or(Value::Null),
        "bypassed_setup_import_proofs": {
            "memory_import_function": memory_import_index,
            "module_memory_identity_proofs": context.module_memory_proofs,
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

fn semantics_for_source(source: &Path, budget: &WorkBudget) -> Result<Value> {
    let text =
        fs::read_to_string(source).with_context(|| format!("reading {}", source.display()))?;
    let analysis = proven_wasm_import_semantics(&text, budget)?;
    serde_json::to_value(analysis).context("serializing JS WASM semantics")
}

fn targeted_semantics_for_source(
    source: &Path,
    import_module: &str,
    import_name: &str,
    offset: u32,
    budget: &WorkBudget,
) -> Result<Value> {
    let text =
        fs::read_to_string(source).with_context(|| format!("reading {}", source.display()))?;
    let analysis =
        proven_wasm_import_semantics_for(&text, import_module, import_name, offset, budget)?;
    serde_json::to_value(analysis).context("serializing targeted JS WASM semantics")
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

/// Context-dependent handler shapes are not transferable to other
/// instantiations. Restrict the usage evidence to this assignment and to
/// the initialization witnesses for the exact sites.
fn contextual_handler_usages(usages: Vec<Value>, handler: &Value) -> Vec<Value> {
    let witnesses = array_field(handler, "initialization_witnesses");
    if witnesses.is_empty() {
        return usages;
    }
    let Some(assignment) =
        i64_field(handler, "assignment_start").zip(i64_field(handler, "assignment_end"))
    else {
        return Vec::new();
    };
    let proven_sites = witnesses
        .iter()
        .filter_map(|witness| i64_field(witness, "site_start").zip(i64_field(witness, "site_end")))
        .collect::<HashSet<_>>();
    usages
        .into_iter()
        .filter_map(|usage| {
            if i64_field(&usage, "assignment_start").zip(i64_field(&usage, "assignment_end"))
                != Some(assignment)
            {
                return None;
            }
            let sites = array_field(&usage, "instantiation_sites")
                .iter()
                .filter(|site| {
                    i64_field(site, "start")
                        .zip(i64_field(site, "end"))
                        .is_some_and(|span| proven_sites.contains(&span))
                })
                .cloned()
                .collect::<Vec<_>>();
            (!sites.is_empty())
                .then(|| object_with(&usage, "instantiation_sites", Value::Array(sites)))
        })
        .collect()
}

struct BoundaryExport<'a> {
    module: &'a Value,
    export: &'a Value,
    analysis: &'a Value,
    report: &'a Value,
    function_imports: &'a [Value],
    carrier_candidates: &'a [String],
}

struct HostEffectEvidence<'a> {
    raw_module: Option<&'a str>,
    raw_import: Option<&'a str>,
    offset: Option<u32>,
    proofs: Vec<Value>,
    usage_proofs: Vec<Value>,
}

#[derive(Clone, Copy)]
struct CopyImportNames<'a> {
    set_module: Option<&'a str>,
    set_name: Option<&'a str>,
    constructor_module: Option<&'a str>,
    constructor_name: Option<&'a str>,
    memory_module: Option<&'a str>,
    memory_name: Option<&'a str>,
}

impl<'a> CopyImportNames<'a> {
    fn from_candidate(function_imports: &'a [Value], candidate: &Value) -> Self {
        let set_import = usize_field(candidate, "set_import_function")
            .and_then(|index| function_imports.get(index));
        let constructor_import = usize_field(candidate, "constructor_import_function")
            .and_then(|index| function_imports.get(index));
        let memory_import = usize_field(candidate, "constructor_input_memory_import_function")
            .and_then(|index| function_imports.get(index));
        let set_module = set_import.and_then(|imported| string_field(imported, "module"));
        let set_name = set_import.and_then(|imported| string_field(imported, "name"));
        let constructor_module =
            constructor_import.and_then(|imported| string_field(imported, "module"));
        let constructor_name =
            constructor_import.and_then(|imported| string_field(imported, "name"));
        let memory_module = memory_import.and_then(|imported| string_field(imported, "module"));
        let memory_name = memory_import.and_then(|imported| string_field(imported, "name"));
        Self {
            set_module,
            set_name,
            constructor_module,
            constructor_name,
            memory_module,
            memory_name,
        }
    }
}

struct CopiedSourceEvidence {
    proofs: Vec<Value>,
    copied_binding_proofs: Vec<Value>,
    module_memory_proofs: Vec<Value>,
    module_memory_sources: BTreeSet<String>,
}

impl CopiedSourceEvidence {
    // Keep each source-local proof and its ordering, even when incomplete.
    fn annotate(proofs: &[Value], field: &str) -> Vec<Value> {
        proofs
            .iter()
            .flat_map(|proof| {
                let source = string_field(proof, "source_path")
                    .unwrap_or_default()
                    .to_owned();
                array_field(proof, field)
                    .iter()
                    .cloned()
                    .map(move |mut nested| {
                        if let Some(object) = nested.as_object_mut() {
                            object.insert("source_path".into(), source.clone().into());
                        }
                        nested
                    })
            })
            .collect()
    }

    fn new(proofs: Vec<Value>) -> Self {
        let copied_binding_proofs = Self::annotate(&proofs, "import_binding_identity_proofs");
        let module_memory_proofs = Self::annotate(&proofs, "module_memory_identity_proofs");
        let module_memory_sources = module_memory_proofs
            .iter()
            .filter_map(|proof| string_field(proof, "source_path").map(ToOwned::to_owned))
            .collect::<BTreeSet<_>>();
        Self {
            proofs,
            copied_binding_proofs,
            module_memory_proofs,
            module_memory_sources,
        }
    }

    // All exact instance evidence must come from a unique carrier.
    fn module_memory_proven(&self) -> bool {
        !self.module_memory_proofs.is_empty()
            && self.module_memory_sources.len() == 1
            && self.proofs.len() == 1
            && self.copied_binding_proofs.len() == 1
    }
}

struct CopyDestinationRequirements {
    source_length_lower_bound: Option<usize>,
    length_barrier_proofs: Vec<Value>,
    required_internal_barriers: BTreeSet<usize>,
    base_destination_byte_integrity_proven: bool,
    static_destination_base_alignment_proven: bool,
}

impl CopyDestinationRequirements {
    /// The pre-fresh-state proof requires every destination load to be
    /// covered by a fixed source length and all import barrier identities.
    fn assess(candidate: &Value, export_name: Option<&str>, source: &CopiedSourceEvidence) -> Self {
        let destination_loads = array_field(candidate, "destination_loads");
        let source_length_lower_bound = fixed_uint32_source_length_lower_bound(
            if source.module_memory_proven() {
                &source.module_memory_proofs
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
        let length_barrier_proofs =
            CopiedSourceEvidence::annotate(&source.proofs, "source_length_barrier_proofs");
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
            && (required_length_barriers.is_empty() || source.proofs.len() == 1);
        let element_shift = usize_field(candidate, "destination_element_index_shift");
        let base_zero_bits =
            usize_field(candidate, "destination_base_guaranteed_trailing_zero_bits");
        let static_destination_base_alignment_proven =
            element_shift == Some(2) && base_zero_bits.is_some_and(|bits| bits >= 2);
        Self {
            source_length_lower_bound,
            length_barrier_proofs,
            required_internal_barriers,
            base_destination_byte_integrity_proven,
            static_destination_base_alignment_proven,
        }
    }
}

struct FreshDestinationProof {
    alignment: Option<Value>,
    cleanup: Option<Value>,
}

impl FreshDestinationProof {
    const fn base_alignment_proven(&self, requirements: &CopyDestinationRequirements) -> bool {
        requirements.static_destination_base_alignment_proven || self.alignment.is_some()
    }

    fn byte_integrity_proven(&self, requirements: &CopyDestinationRequirements) -> bool {
        requirements.base_destination_byte_integrity_proven
            && (requirements.required_internal_barriers.is_empty() || self.cleanup.is_some())
    }
}

struct CopyWordInterpretation {
    destination_load_interpretations: Vec<Value>,
    source_word_runtime_bindings: Vec<Value>,
    source_word_returns: Vec<Value>,
    runtime_graph_proven: bool,
    destination_load_interpretation_proven: bool,
}

impl CopyWordInterpretation {
    /// Runtime bindings are considered only after exact module memory,
    /// unchanged destination bytes, alignment, and full load coverage.
    fn evaluate(
        candidate: &Value,
        analysis: &Value,
        export_name: Option<&str>,
        source: &CopiedSourceEvidence,
        requirements: &CopyDestinationRequirements,
        fresh: &FreshDestinationProof,
    ) -> Self {
        let module_memory_proven = source.module_memory_proven();
        let destination_byte_integrity_proven = fresh.byte_integrity_proven(requirements);
        let destination_base_alignment_proven = fresh.base_alignment_proven(requirements);
        let (destination_load_interpretations, _) = interpreted_destination_loads(
            candidate,
            if module_memory_proven {
                &source.module_memory_proofs
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
            && destination_load_interpretations.len()
                == array_field(candidate, "destination_loads").len();
        let (source_word_runtime_bindings, source_word_returns, runtime_graph_proven) =
            if destination_load_interpretation_proven {
                source_word_semantic_overlay(analysis, &destination_load_interpretations)
            } else {
                (Vec::new(), Vec::new(), false)
            };
        Self {
            destination_load_interpretations,
            source_word_runtime_bindings,
            source_word_returns,
            runtime_graph_proven,
            destination_load_interpretation_proven,
        }
    }

    const fn semantic_overlay_proven(&self) -> bool {
        self.destination_load_interpretation_proven
            && !self.source_word_runtime_bindings.is_empty()
            && self.source_word_runtime_bindings.len()
                == self.destination_load_interpretations.len()
    }

    const fn return_dependencies_proven(&self) -> bool {
        self.semantic_overlay_proven()
            && self.runtime_graph_proven
            && !self.source_word_returns.is_empty()
    }
}

struct CopyLimitations {
    destination_load: Value,
    source_word_overlay: Value,
    source_word_return: Value,
}

impl CopyLimitations {
    fn for_proofs(
        source: &CopiedSourceEvidence,
        requirements: &CopyDestinationRequirements,
        fresh: &FreshDestinationProof,
        interpretation: &CopyWordInterpretation,
    ) -> Self {
        let module_memory_proven = source.module_memory_proven();
        let destination_byte_integrity_proven = fresh.byte_integrity_proven(requirements);
        let destination_base_alignment_proven = fresh.base_alignment_proven(requirements);
        let destination_load_interpretation_proven =
            interpretation.destination_load_interpretation_proven;
        let source_word_semantic_overlay_proven = interpretation.semantic_overlay_proven();
        let source_word_return_dependencies_proven = interpretation.return_dependencies_proven();
        let destination_load_limitation = if destination_load_interpretation_proven {
            Value::Null
        } else if !module_memory_proven {
            "module-memory identity is not proven".into()
        } else if !destination_byte_integrity_proven {
            "a potentially memory-mutating path exists between the proven Uint32Array.set and at least one destination load".into()
        } else if !destination_base_alignment_proven {
            "the destination base is not proven aligned to the Uint32Array element width".into()
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
        Self {
            destination_load: destination_load_limitation,
            source_word_overlay: source_word_overlay_limitation,
            source_word_return: source_word_return_limitation,
        }
    }
}

struct BoundaryCorrelation<'a> {
    project: &'a Path,
    stage_budget: WorkBudget,
    deob_by_raw: BTreeMap<String, String>,
    targeted_cache: HashMap<(String, String, String, u32), Value>,
    full_cache: HashMap<String, Value>,
    host_effect_rows: Vec<Value>,
    copied_input_rows: Vec<Value>,
    skipped_modules: Vec<Value>,
    carrier_sources: BTreeSet<String>,
}

impl BoundaryCorrelation<'_> {
    fn process_module(&mut self, module: &Value) -> Result<()> {
        let (deep, report, function_imports, carrier_candidates) = {
            let project = self.project;
            let stage_budget = &self.stage_budget;
            let deob_by_raw = &self.deob_by_raw;
            let skipped_modules = &mut self.skipped_modules;
            stage_budget.checkpoint()?;
            if string_field(module, "status") != Some("ok")
                || string_field(module, "deep_path").is_none()
            {
                return Ok(());
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
                return Ok(());
            }

            let mut carrier_candidates = Vec::<String>::new();
            for origin in array_field(module, "origins") {
                stage_budget.checkpoint()?;
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
            (deep, report, function_imports, carrier_candidates)
        };
        for export in array_field(&deep, "exports") {
            self.stage_budget.checkpoint()?;
            let analysis = export.get("analysis").unwrap_or(&Value::Null);
            let scope = BoundaryExport {
                module,
                export,
                analysis,
                report: &report,
                function_imports: &function_imports,
                carrier_candidates: &carrier_candidates,
            };
            for pair in array_field(analysis, "opaque_host_effect_memory_reads") {
                self.stage_budget.checkpoint()?;
                let row = self.host_effect_pair(&scope, pair)?;
                self.host_effect_rows.push(row);
            }
            for candidate in array_field(analysis, "externref_bulk_copy_candidates") {
                self.stage_budget.checkpoint()?;
                let row = self.copied_input_candidate(&scope, candidate)?;
                self.copied_input_rows.push(row);
            }
        }
        Ok(())
    }

    fn host_effect_pair(&mut self, scope: &BoundaryExport<'_>, pair: &Value) -> Result<Value> {
        let function_imports = scope.function_imports;
        let carrier_candidates = scope.carrier_candidates;
        let project = self.project;
        let stage_budget = &self.stage_budget;
        let targeted_cache = &mut self.targeted_cache;
        let carrier_sources = &mut self.carrier_sources;
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

        if let (Some(raw_module), Some(raw_import), Some(offset)) = (raw_module, raw_import, offset)
        {
            for relative in carrier_candidates {
                stage_budget.checkpoint()?;
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
                    targeted_cache.insert(key.clone(), {
                        let budget = AnalysisOperation::WasmAnalysis
                            .under(stage_budget, source.display().to_string());
                        targeted_semantics_for_source(
                            &source, raw_module, raw_import, offset, &budget,
                        )?
                    });
                }
                let probe = targeted_cache.get(&key).context("missing targeted cache")?;
                let writes = array_field(probe, "shapes");
                anyhow::ensure!(
                    writes.len() <= 1,
                    "ambiguous JS WASM-import proof for {}: {raw_import}@{offset}",
                    source.display()
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

        Ok(Self::format_host_effect_row(
            scope,
            pair,
            HostEffectEvidence {
                raw_module,
                raw_import,
                offset,
                proofs,
                usage_proofs,
            },
        ))
    }

    fn format_host_effect_row(
        scope: &BoundaryExport<'_>,
        pair: &Value,
        evidence: HostEffectEvidence<'_>,
    ) -> Value {
        let module = scope.module;
        let export = scope.export;
        let carrier_candidates = scope.carrier_candidates;
        let HostEffectEvidence {
            raw_module,
            raw_import,
            offset,
            proofs,
            usage_proofs,
        } = evidence;
        let host_import = pair.get("host_import").cloned().unwrap_or(Value::Null);

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
            ambiguities
                .push("multiple carrier sources prove exact module/import-object binding identity");
        }
        if !ambiguities.is_empty() {
            row["ambiguity"] = ambiguities.join("; ").into();
        }
        row
    }

    // Proven source-specific handlers, instantiation binding and memory
    // edges are collected before interpreting any copied destination words.
    // Only complete, unique handler semantics are admissible source proofs.
    fn match_copied_source(
        scope: &BoundaryExport<'_>,
        candidate: &Value,
        names: CopyImportNames<'_>,
        relative: &str,
        document: &Value,
    ) -> Option<Value> {
        let CopyImportNames {
            set_module: Some(set_module),
            set_name: Some(set_name),
            constructor_module: Some(constructor_module),
            constructor_name: Some(constructor_name),
            memory_module,
            memory_name,
        } = names
        else {
            return None;
        };
        let module = scope.module;
        let report = scope.report;
        let function_imports = scope.function_imports;
        let export_name = string_field(scope.export, "export");
        let set_matches = matching_handler(document, set_module, set_name, "typed_array_set");
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
            return None;
        }
        let set_usages = matching_usages(document, set_module, set_name);
        let constructor_usages = contextual_handler_usages(
            matching_usages(document, constructor_module, constructor_name),
            &constructor_matches[0],
        );
        let binding_proofs = common_exact_binding_proofs(
            &set_usages,
            &constructor_usages,
            string_field(module, "sha256"),
        );
        if !array_field(&constructor_matches[0], "initialization_witnesses").is_empty()
            && binding_proofs.is_empty()
        {
            return None;
        }
        let memory_match_context = ModuleMemoryMatchContext {
            document,
            module_sha256: string_field(module, "sha256"),
            export_name,
            binding_proofs: &binding_proofs,
            report,
        };
        let memory_proofs = matching_module_memory_proofs(
            &memory_match_context,
            memory_module,
            memory_name,
            candidate,
        );
        let length_barrier_proofs = source_length_barrier_proofs(
            document,
            function_imports,
            candidate,
            string_field(module, "sha256"),
            &binding_proofs,
        );
        Some(json!({
            "source_path": relative,
            "set_handler": set_matches[0],
            "constructor_handler": constructor_matches[0],
            "import_binding_identity_proofs": binding_proofs,
            "module_memory_identity_proofs": memory_proofs,
            "source_length_barrier_proofs": length_barrier_proofs,
        }))
    }

    fn collect_copied_source_proofs(
        &mut self,
        scope: &BoundaryExport<'_>,
        candidate: &Value,
        names: CopyImportNames<'_>,
    ) -> Result<Vec<Value>> {
        let mut proofs = Vec::new();
        if names.set_module.is_some()
            && names.set_name.is_some()
            && names.constructor_module.is_some()
            && names.constructor_name.is_some()
        {
            for relative in scope.carrier_candidates {
                self.stage_budget.checkpoint()?;
                let source = self.project.join(relative);
                if !source.is_file() {
                    continue;
                }
                self.carrier_sources.insert(relative.clone());
                if !self.full_cache.contains_key(relative) {
                    let budget = AnalysisOperation::WasmAnalysis
                        .under(&self.stage_budget, source.display().to_string());
                    self.full_cache
                        .insert(relative.clone(), semantics_for_source(&source, &budget)?);
                }
                let document = self
                    .full_cache
                    .get(relative)
                    .context("missing full semantics cache")?;
                if let Some(proof) =
                    Self::match_copied_source(scope, candidate, names, relative, document)
                {
                    proofs.push(proof);
                }
            }
        }
        Ok(proofs)
    }

    /// The bounded fresh evaluator is only consulted after unique module
    /// memory identity; cleanup additionally requires an already validated
    /// base byte-integrity proof and an exact fresh alignment witness.
    fn fresh_destination_proofs(
        &self,
        scope: &BoundaryExport<'_>,
        candidate: &Value,
        source: &CopiedSourceEvidence,
        requirements: &CopyDestinationRequirements,
    ) -> Result<FreshDestinationProof> {
        let mut alignment = None;
        let mut fresh_document = None;
        if source.module_memory_proven() && source.module_memory_sources.len() == 1 {
            if let Some(source_path) = source.module_memory_sources.iter().next() {
                fresh_document = self.full_cache.get(source_path);
                if let Some(document) = fresh_document {
                    let context = CopiedInputProofContext {
                        project: self.project,
                        module: scope.module,
                        report: scope.report,
                        function_imports: scope.function_imports,
                        document,
                        module_memory_proofs: &source.module_memory_proofs,
                        binding_proofs: &source.copied_binding_proofs,
                        export_name: string_field(scope.export, "export"),
                        budget: &self.stage_budget,
                    };
                    self.stage_budget.checkpoint()?;
                    alignment = fresh_destination_alignment_proof(&context, candidate);
                    self.stage_budget.checkpoint()?;
                }
            }
        }
        let cleanup = if requirements.base_destination_byte_integrity_proven
            && !requirements.required_internal_barriers.is_empty()
        {
            match (fresh_document, alignment.as_ref()) {
                (Some(document), Some(alignment)) => {
                    let context = CopiedInputProofContext {
                        project: self.project,
                        module: scope.module,
                        report: scope.report,
                        function_imports: scope.function_imports,
                        document,
                        module_memory_proofs: &source.module_memory_proofs,
                        binding_proofs: &source.copied_binding_proofs,
                        export_name: string_field(scope.export, "export"),
                        budget: &self.stage_budget,
                    };
                    self.stage_budget.checkpoint()?;
                    let proof =
                        fresh_cleanup_disjointness_proof(&context, candidate, Some(alignment));
                    self.stage_budget.checkpoint()?;
                    proof
                }
                _ => None,
            }
        } else {
            None
        };
        Ok(FreshDestinationProof { alignment, cleanup })
    }

    fn copied_input_candidate(
        &mut self,
        scope: &BoundaryExport<'_>,
        candidate: &Value,
    ) -> Result<Value> {
        let names = CopyImportNames::from_candidate(scope.function_imports, candidate);
        let proofs = self.collect_copied_source_proofs(scope, candidate, names)?;
        let source = CopiedSourceEvidence::new(proofs);
        let requirements = CopyDestinationRequirements::assess(
            candidate,
            string_field(scope.export, "export"),
            &source,
        );
        let fresh = self.fresh_destination_proofs(scope, candidate, &source, &requirements)?;
        let interpretation = CopyWordInterpretation::evaluate(
            candidate,
            scope.analysis,
            string_field(scope.export, "export"),
            &source,
            &requirements,
            &fresh,
        );
        Ok(Self::format_copied_input_row(
            scope,
            candidate,
            names,
            source,
            requirements,
            fresh,
            interpretation,
        ))
    }

    // Ambiguous carriers remain visible in the report, but never become
    // an exact single-carrier source, binding or memory proof.
    fn add_copied_ambiguity(
        row: &mut Value,
        proof_count: usize,
        binding_count: usize,
        memory_source_count: usize,
    ) {
        if proof_count > 1 {
            row["js_typed_array_copy_semantics_proven"] = false.into();
            row["ambiguity"] =
                "multiple carrier sources prove the same constructor/set import semantics".into();
        }
        if binding_count > 1 {
            row["import_binding_identity_proven"] = false.into();
            let prefix = string_field(row, "ambiguity").unwrap_or_default();
            row["ambiguity"] = format!(
                "{prefix}{}multiple exact module/import-object binding proofs",
                if prefix.is_empty() { "" } else { "; " }
            )
            .into();
        }
        if memory_source_count > 1 {
            row["module_memory_identity_proven"] = false.into();
            row["module_memory_identity_limitation"] =
                "multiple carrier sources prove module-memory identity".into();
            let prefix = string_field(row, "ambiguity").unwrap_or_default();
            row["ambiguity"] = format!(
                "{prefix}{}multiple module-memory carrier proofs",
                if prefix.is_empty() { "" } else { "; " }
            )
            .into();
        }
    }

    // A source-local handler match is not, by itself, an exact memory proof.
    // Each separate proof condition is reflected in the final output row.
    fn format_copied_input_row(
        scope: &BoundaryExport<'_>,
        candidate: &Value,
        names: CopyImportNames<'_>,
        source: CopiedSourceEvidence,
        requirements: CopyDestinationRequirements,
        fresh: FreshDestinationProof,
        interpretation: CopyWordInterpretation,
    ) -> Value {
        let module = scope.module;
        let export = scope.export;
        let carrier_candidates = scope.carrier_candidates;
        let CopyImportNames {
            set_module,
            set_name,
            constructor_module,
            constructor_name,
            memory_module,
            memory_name,
        } = names;
        let limitations =
            CopyLimitations::for_proofs(&source, &requirements, &fresh, &interpretation);
        let module_memory_proven = source.module_memory_proven();
        let destination_base_alignment_proven = fresh.base_alignment_proven(&requirements);
        let destination_byte_integrity_proven = fresh.byte_integrity_proven(&requirements);
        let CopiedSourceEvidence {
            proofs,
            copied_binding_proofs,
            module_memory_proofs,
            module_memory_sources,
        } = source;
        let CopyDestinationRequirements {
            source_length_lower_bound,
            length_barrier_proofs,
            required_internal_barriers,
            static_destination_base_alignment_proven,
            ..
        } = requirements;
        let FreshDestinationProof {
            alignment: fresh_alignment_proof,
            cleanup: fresh_cleanup_proof,
        } = fresh;
        let source_word_semantic_overlay_proven = interpretation.semantic_overlay_proven();
        let source_word_return_dependencies_proven = interpretation.return_dependencies_proven();
        let CopyWordInterpretation {
            destination_load_interpretations,
            source_word_runtime_bindings,
            source_word_returns,
            runtime_graph_proven,
            destination_load_interpretation_proven,
        } = interpretation;
        let destination_alignment_basis = if static_destination_base_alignment_proven {
            Value::String("static_ssa".into())
        } else if fresh_alignment_proof.is_some() {
            Value::String("fresh_exact_evaluation".into())
        } else {
            Value::Null
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
            "source_word_return_dependencies_limitation": limitations.source_word_return,
            "source_word_semantic_overlay_limitation": limitations.source_word_overlay,
            "source_uint32_array_length_lower_bound": source_length_lower_bound,
            "destination_load_interpretation_limitation": limitations.destination_load,
            "destination_load_interpretation_contract": "each proven i32.load reads the unchanged Uint32Array.set destination word corresponding to ToUint32(source[index]); numeric equality requires little-endian typed-array storage",
        });
        Self::add_copied_ambiguity(
            &mut row,
            proofs.len(),
            copied_binding_proofs.len(),
            module_memory_sources.len(),
        );
        row
    }

    fn finish(self) -> Result<WasmJsBoundarySummary> {
        let Self {
            project,
            stage_budget,
            targeted_cache,
            full_cache,
            host_effect_rows,
            copied_input_rows,
            skipped_modules,
            carrier_sources,
            ..
        } = self;
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
            "js_schema": "jsvm-wasm-import-semantics/v9",
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
        stage_budget.checkpoint()?;
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
}

/// Correlate recovered WebAssembly module identities with JavaScript boundary usage.
///
/// # Errors
///
/// Fails when required WebAssembly/deobfuscation artifacts are unavailable or malformed, when
/// generated reports cannot be persisted, or when the analysis budget is exhausted.
pub fn correlate_project(
    project: &Path,
    budgets: &AnalysisBudgets,
) -> Result<WasmJsBoundarySummary> {
    let stage_budget = budgets.operation(
        AnalysisOperation::WasmAnalysis,
        format!("boundary:{}", project.display()),
    );
    stage_budget.checkpoint()?;
    let wasm_index = load_artifact(project, WASM_INDEX)
        .context("WASM index is required for WASM/JS boundary correlation")?;
    let deob = load_artifact(project, DEOBFUSCATION)
        .context("deobfuscation artifact is required for WASM/JS boundary correlation")?;
    let deob_by_raw = array_field(&deob, "units")
        .iter()
        .filter_map(|unit| {
            let raw = string_field(unit, "raw_path")?;
            let output = string_field(unit, "output_path")?;
            (i64_field(unit, "exit") == Some(0)).then(|| (raw.to_owned(), output.to_owned()))
        })
        .collect::<BTreeMap<_, _>>();
    let mut context = BoundaryCorrelation {
        project,
        stage_budget,
        deob_by_raw,
        targeted_cache: HashMap::new(),
        full_cache: HashMap::new(),
        host_effect_rows: Vec::new(),
        copied_input_rows: Vec::new(),
        skipped_modules: Vec::new(),
        carrier_sources: BTreeSet::new(),
    };
    for module in array_field(&wasm_index, "modules") {
        context.process_module(module)?;
    }
    context.finish()
}

#[cfg(test)]
mod tests {
    use super::{
        contextual_handler_usages, source_word_semantic_overlay, BoundaryCorrelation,
        BoundaryExport, CopiedSourceEvidence, CopyDestinationRequirements, CopyImportNames,
        CopyWordInterpretation, FreshCleanupRange, FreshCleanupSequence, FreshCleanupSetup,
        FreshDestinationProof,
    };
    use serde_json::{json, Value};

    #[test]
    fn fresh_cleanup_range_rejects_overlapping_or_unproven_post_copy_accesses() {
        let candidate = json!({
            "destination_loads": [{
                "memory": 0,
                "internal_memory_mutation_call_barriers": [7, 7]
            }]
        });
        let mut evaluation = json!({
            "steps": [
                {}, {}, {}, {}, {},
                {"memory_accesses":[
                    {"memory":0,"addr":8,"len":8},
                    {"memory":1,"addr":16,"len":8}
                ]},
                {"memory_accesses":[{"memory":0,"addr":24,"len":4}]}
            ]
        });
        let exact = FreshCleanupRange::verify(&candidate, 7, 16, 8, &evaluation);
        assert!(
            exact.is_some(),
            "adjacent and other-memory accesses are disjoint"
        );
        let Some(exact) = exact else {
            return;
        };
        assert_eq!(exact.target_memory, 0);
        assert_eq!((exact.range_start, exact.range_end), (16, 24));
        assert_eq!(exact.post_copy_accesses.len(), 3);

        evaluation["steps"][5]["memory_accesses"][0]["len"] = json!(9);
        assert!(
            FreshCleanupRange::verify(&candidate, 7, 16, 8, &evaluation).is_none(),
            "an access ending inside copied bytes is not disjoint"
        );

        evaluation["steps"][5]["memory_accesses"][0] = json!({"memory":0,"addr":8});
        assert!(
            FreshCleanupRange::verify(&candidate, 7, 16, 8, &evaluation).is_none(),
            "missing length must not be treated as disjoint"
        );

        evaluation["steps"][5]["memory_accesses"][0] = json!({"memory":0,"addr":8,"len":8});
        assert!(
            FreshCleanupRange::verify(&candidate, 9, 16, 8, &evaluation).is_none(),
            "the observed cleanup must be the exact required internal barrier"
        );
        assert!(
            FreshCleanupRange::verify(&candidate, 7, u32::MAX, 8, &evaluation).is_none(),
            "the copied range must fit in wasm32 memory"
        );
        let multiple_memories = json!({
            "destination_loads": [
                {"memory":0,"internal_memory_mutation_call_barriers":[7]},
                {"memory":1,"internal_memory_mutation_call_barriers":[7]}
            ]
        });
        assert!(
            FreshCleanupRange::verify(&multiple_memories, 7, 16, 8, &evaluation).is_none(),
            "one copied byte range cannot be justified across separate memories"
        );
    }

    #[test]
    fn fresh_cleanup_sequence_requires_exact_wasm_table_growth_and_nonempty_copy() {
        let setup = FreshCleanupSetup {
            slot_allocator: 3,
            cleanup_function: 4,
            memory_import_index: 0,
            buffer_index: 1,
            buffer_handler: json!({}),
            binding_import_object: "imports".to_owned(),
        };
        let candidate = json!({"fresh_destination_base_recipe":{"function":6}});
        let proof = json!({
            "evaluated_destination_base":16,
            "allocator_byte_count":8,
            "start_handler":{"exact_grow_deltas":[2]},
            "table_export":{"index":0}
        });
        let sequence = FreshCleanupSequence::verify(&candidate, &proof, &setup);
        assert!(sequence.is_some(), "complete exact cleanup recipe");
        let Some(sequence) = sequence else {
            return;
        };
        assert_eq!(sequence.destination_base, 16);
        assert_eq!(sequence.byte_count, 8);
        assert_eq!(sequence.calls.len(), 7);
        assert_eq!(sequence.table_grows.len(), 1);

        let mut bad = proof.clone();
        bad["allocator_byte_count"] = json!(0);
        assert!(FreshCleanupSequence::verify(&candidate, &bad, &setup).is_none());
        bad = proof;
        bad["start_handler"]["exact_grow_deltas"] = json!([]);
        assert!(FreshCleanupSequence::verify(&candidate, &bad, &setup).is_none());
        bad["start_handler"]["exact_grow_deltas"] = json!([u64::MAX]);
        assert!(FreshCleanupSequence::verify(&candidate, &bad, &setup).is_none());
    }

    #[test]
    fn copied_proof_stages_keep_ambiguous_carriers_and_missing_barriers_unproven() {
        let carrier = |path| {
            json!({
                "source_path": path,
                "import_binding_identity_proofs": [{"import_object":"imports"}],
                "module_memory_identity_proofs": [{"memory_export_name":"memory"}],
                "source_length_barrier_proofs": [{"function_import":7}]
            })
        };
        let unique = CopiedSourceEvidence::new(vec![carrier("src/a.js")]);
        assert!(unique.module_memory_proven());
        assert_eq!(unique.module_memory_proofs[0]["source_path"], "src/a.js");
        let source = CopiedSourceEvidence::new(vec![carrier("src/a.js"), carrier("src/b.js")]);
        assert!(!source.module_memory_proven());
        assert_eq!(source.module_memory_sources.len(), 2);
        let candidate = json!({
            "destination_element_index_shift": 2,
            "destination_base_guaranteed_trailing_zero_bits": 2,
            "destination_loads": [{
                "source_length_import_barriers": [7,9],
                "internal_memory_mutation_call_barriers": [3,3,5],
                "other_import_call_barriers": [],
                "unresolved_intervening_memory_mutation": false
            }]
        });
        let requirements = CopyDestinationRequirements::assess(&candidate, Some("copy"), &source);
        assert_eq!(
            requirements
                .required_internal_barriers
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            [3, 5]
        );
        assert!(requirements.static_destination_base_alignment_proven);
        assert!(!requirements.base_destination_byte_integrity_proven);
        let fresh = FreshDestinationProof {
            alignment: None,
            cleanup: None,
        };
        assert!(!fresh.byte_integrity_proven(&requirements));
        let analysis = json!({});
        let interpretation = CopyWordInterpretation::evaluate(
            &candidate,
            &analysis,
            Some("copy"),
            &source,
            &requirements,
            &fresh,
        );
        assert!(!interpretation.destination_load_interpretation_proven);
        assert!(!interpretation.semantic_overlay_proven());
        assert!(!interpretation.return_dependencies_proven());
        let module = json!({"sha256":"sha"});
        let export = json!({"export":"copy"});
        let report = json!({});
        let imports = Vec::new();
        let carriers = vec!["src/a.js".to_owned(), "src/b.js".to_owned()];
        let scope = BoundaryExport {
            module: &module,
            export: &export,
            analysis: &analysis,
            report: &report,
            function_imports: &imports,
            carrier_candidates: &carriers,
        };
        let names = CopyImportNames::from_candidate(&imports, &candidate);
        let row = BoundaryCorrelation::format_copied_input_row(
            &scope,
            &candidate,
            names,
            source,
            requirements,
            fresh,
            interpretation,
        );
        assert_eq!(row["js_typed_array_copy_semantics_proven"], false);
        assert_eq!(row["import_binding_identity_proven"], false);
        assert_eq!(row["module_memory_identity_proven"], false);
        assert_eq!(row["destination_load_interpretation_proven"], false);
        assert_eq!(
            row["module_memory_identity_limitation"],
            "multiple carrier sources prove module-memory identity"
        );
        assert_eq!(row["ambiguity"], "multiple carrier sources prove the same constructor/set import semantics; multiple exact module/import-object binding proofs; multiple module-memory carrier proofs");
        assert_eq!(
            row["module_memory_identity_proofs"][0]["source_path"],
            "src/a.js"
        );
        assert_eq!(
            row["module_memory_identity_proofs"][1]["source_path"],
            "src/b.js"
        );
    }

    #[test]
    fn contextual_handler_evidence_never_migrates_to_other_assignment_or_site() {
        let handler = json!({
            "assignment_start": 10, "assignment_end": 20,
            "initialization_witnesses": [{"site_start": 100, "site_end": 120}]
        });
        let usages = vec![
            json!({"assignment_start":10,"assignment_end":20,"instantiation_sites":[
                {"start":40,"end":60},{"start":100,"end":120},{"start":100,"end":121}
            ]}),
            json!({"assignment_start":11,"assignment_end":20,"instantiation_sites":[
                {"start":100,"end":120}
            ]}),
        ];
        assert_eq!(
            contextual_handler_usages(usages, &handler),
            vec![
                json!({"assignment_start":10,"assignment_end":20,"instantiation_sites":[
                    {"start":100,"end":120}
                ]}),
            ]
        );
    }

    #[test]
    fn copied_source_requires_unique_exact_import_handlers() {
        let module = json!({"sha256":"example"});
        let export = json!({"export":"copy"});
        let null = serde_json::Value::Null;
        let imports = vec![
            json!({"module":"wbg", "name":"set"}),
            json!({"module":"wbg", "name":"ctor"}),
        ];
        let carriers = Vec::new();
        let scope = BoundaryExport {
            module: &module,
            export: &export,
            analysis: &null,
            report: &null,
            function_imports: &imports,
            carrier_candidates: &carriers,
        };
        let candidate = json!({"set_import_function":0,"constructor_import_function":1});
        let names = CopyImportNames::from_candidate(&imports, &candidate);
        assert_eq!(names.set_name, Some("set"));
        assert_eq!(names.constructor_name, Some("ctor"));

        let set = json!({"kind":"typed_array_set","import_module":"wbg","import_name":"set"});
        let ctor = json!({
            "kind":"uint32_array_constructor",
            "import_module":"wbg",
            "import_name":"ctor",
            "element_width_bits":32
        });
        let exact = json!({"handler_semantics":[set,ctor],"import_object_usages":[]});
        let proof = BoundaryCorrelation::match_copied_source(
            &scope,
            &candidate,
            names,
            "src/carrier.js",
            &exact,
        );
        assert!(
            proof.is_some(),
            "unique exact handler pair must yield source-local evidence"
        );
        let Some(proof) = proof else {
            return;
        };
        assert_eq!(proof["source_path"], "src/carrier.js");
        assert_eq!(proof["module_memory_identity_proofs"], json!([]));
        assert_eq!(proof["import_binding_identity_proofs"], json!([]));

        let duplicate = json!({"handler_semantics":[set,set,ctor]});
        assert!(
            BoundaryCorrelation::match_copied_source(
                &scope,
                &candidate,
                names,
                "src/carrier.js",
                &duplicate,
            )
            .is_none(),
            "duplicate handler matches must not be silently accepted"
        );
        let wrong_module = json!({"handler_semantics":[
            {"kind":"typed_array_set","import_module":"foreign","import_name":"set"},
            ctor
        ]});
        assert!(BoundaryCorrelation::match_copied_source(
            &scope,
            &candidate,
            names,
            "src/carrier.js",
            &wrong_module
        )
        .is_none());
        let invalid_width = json!({"handler_semantics":[
            set,
            {"kind":"uint32_array_constructor","import_module":"wbg","import_name":"ctor","element_width_bits":16}
        ]});
        assert!(BoundaryCorrelation::match_copied_source(
            &scope,
            &candidate,
            names,
            "src/carrier.js",
            &invalid_width
        )
        .is_none());
    }

    fn transitive_word_fixture() -> (Value, Vec<Value>) {
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
        (analysis, interpretations)
    }

    #[test]
    fn source_word_overlay_tracks_transitive_runtime_dependencies() {
        let (analysis, interpretations) = transitive_word_fixture();
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
        assert_eq!(bad_bindings.len(), 0);
        assert_eq!(bad_returns.len(), 0);

        let mut normalization_mismatch = analysis.clone();
        normalization_mismatch["returns"][0]["normalized_semantic_ir"] =
            json!({"kind": "runtime", "value": 10, "name": "$runtime0"});
        let (bad_bindings, bad_returns, bad_graph) =
            source_word_semantic_overlay(&normalization_mismatch, &interpretations);
        assert!(!bad_graph);
        assert_eq!(bad_bindings.len(), 0);
        assert_eq!(bad_returns.len(), 0);

        let mut cyclic = analysis;
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
        assert_eq!(bad_bindings.len(), 0);
        assert_eq!(bad_returns.len(), 0);
    }
}
