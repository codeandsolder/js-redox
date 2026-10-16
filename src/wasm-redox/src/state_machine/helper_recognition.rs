use super::{
    ir::{i32_const, operator_family},
    value_flow::{incoming_block_param_values, unique_transparent_origin},
};
use std::collections::{BTreeMap, BTreeSet};
use waffle::{Func, FunctionBody, ImportKind, Module, Operator, Terminator, Type, Value, ValueDef};

#[derive(Default)]
pub(super) struct SemanticCallNames {
    labels: BTreeMap<Func, String>,
    validated_memory_grow_imports: BTreeSet<Func>,
    validated_buffer_imports: BTreeSet<Func>,
    validated_byte_length_imports: BTreeSet<Func>,
    validated_view_new_imports: BTreeSet<Func>,
    validated_get_u32_imports: BTreeSet<Func>,
    validated_memory_get_u32_helpers: BTreeSet<Func>,
    memory_slot_imports: BTreeMap<Func, Func>,
    opaque_host_effect_helpers: BTreeMap<Func, Func>,
}

impl SemanticCallNames {
    pub(super) fn label(&self, function: Func) -> Option<&str> {
        self.labels.get(&function).map(String::as_str)
    }

    pub(super) fn is_memory_grow_import(&self, function: Func) -> bool {
        self.validated_memory_grow_imports.contains(&function)
    }

    pub(super) fn is_memory_get_u32_helper(&self, function: Func) -> bool {
        self.validated_memory_get_u32_helpers.contains(&function)
    }

    pub(super) fn memory_slot_import(&self, function: Func) -> Option<Func> {
        self.memory_slot_imports.get(&function).copied()
    }

    pub(super) fn opaque_host_effect_import(&self, function: Func) -> Option<Func> {
        self.opaque_host_effect_helpers.get(&function).copied()
    }
}

fn strip_wasm_bindgen_hash(name: &str) -> &str {
    let Some((base, suffix)) = name.rsplit_once('_') else {
        return name;
    };
    if suffix.len() == 16 && suffix.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        base
    } else {
        name
    }
}

pub(super) fn normalize_import_name(module: &str, name: &str) -> String {
    let name = strip_wasm_bindgen_hash(name);
    if let Some(name) = name.strip_prefix("__wbg_") {
        format!("{module}.{name}")
    } else if let Some(name) = name.strip_prefix("__wbindgen_") {
        format!("wbindgen.{name}")
    } else {
        format!("{module}.{name}")
    }
}

fn direct_called_functions(body: &FunctionBody) -> BTreeSet<Func> {
    body.values
        .entries()
        .filter_map(|(_, value)| match value {
            ValueDef::Operator(Operator::Call { function_index }, _, _) => Some(*function_index),
            _ => None,
        })
        .collect()
}

fn unique_return_value(body: &FunctionBody) -> Option<Value> {
    let mut values = BTreeSet::new();
    for (_, block) in body.blocks.entries() {
        let Terminator::Return { values: returned } = &block.terminator else {
            continue;
        };
        if returned.len() != 1 {
            return None;
        }
        values.insert(body.resolve_alias(returned[0]));
    }
    (values.len() == 1)
        .then(|| values.into_iter().next())
        .flatten()
}

fn call_target(body: &FunctionBody, value: Value, depth: usize) -> Option<(Func, Vec<Value>)> {
    if depth == 0 {
        return None;
    }
    let value = body.resolve_alias(value);
    match &body.values[value] {
        ValueDef::Operator(Operator::Call { function_index }, args, _) => {
            Some((*function_index, body.arg_pool[*args].to_vec()))
        }
        ValueDef::PickOutput(source, 0, _) => call_target(body, *source, depth - 1),
        ValueDef::BlockParam(block, _, _) => {
            let incoming = incoming_block_param_values(body, *block, value);
            let [incoming] = incoming.as_slice() else {
                return None;
            };
            call_target(body, *incoming, depth - 1)
        }
        _ => None,
    }
}

fn call_label<'a>(
    body: &FunctionBody,
    value: Value,
    names: &'a SemanticCallNames,
) -> Option<(&'a str, Vec<Value>)> {
    let (function, args) = call_target(body, value, 8)?;
    Some((names.labels.get(&function)?.as_str(), args))
}

fn is_entry_parameter(body: &FunctionBody, value: Value) -> bool {
    matches!(
        body.values[body.resolve_alias(value)],
        ValueDef::BlockParam(block, index, _)
            if block == body.entry
                && usize::try_from(index).is_ok_and(|index| index < body.n_params)
    )
}

fn entry_parameter_index(body: &FunctionBody, value: Value) -> Option<usize> {
    match body.values[body.resolve_alias(value)] {
        ValueDef::BlockParam(block, index, _)
            if block == body.entry
                && usize::try_from(index).is_ok_and(|index| index < body.n_params) =>
        {
            usize::try_from(index).ok()
        }
        _ => None,
    }
}

fn table_get_slot(body: &FunctionBody, value: Value) -> Option<Value> {
    let value = body.resolve_alias(value);
    let ValueDef::Operator(Operator::TableGet { .. }, args, _) = &body.values[value] else {
        return None;
    };
    let [slot] = &body.arg_pool[*args] else {
        return None;
    };
    Some(*slot)
}

fn is_table_get_of_entry_parameter(body: &FunctionBody, value: Value) -> bool {
    table_get_slot(body, value).is_some_and(|index| is_entry_parameter(body, index))
}

fn helper_returns_import_call(
    body: &FunctionBody,
    names: &SemanticCallNames,
    import_name: &str,
) -> Option<Vec<Value>> {
    let returned = unique_return_value(body)?;
    let (label, args) = call_label(body, returned, names)?;
    (label == import_name).then_some(args)
}

fn memory_slot_import(body: &FunctionBody, names: &SemanticCallNames) -> Option<Func> {
    if body.n_params != 0 {
        return None;
    }
    let returned_slot = unique_transparent_origin(body, unique_return_value(body)?, 8);
    let imports = body
        .values
        .entries()
        .filter_map(|(_, value)| {
            let ValueDef::Operator(Operator::TableSet { .. }, args, _) = value else {
                return None;
            };
            let [slot, stored] = &body.arg_pool[*args] else {
                return None;
            };
            if unique_transparent_origin(body, *slot, 8) != returned_slot {
                return None;
            }
            let (function, _) = call_target(body, *stored, 8)?;
            (names.label(function) == Some("wbindgen.memory")).then_some(function)
        })
        .collect::<BTreeSet<_>>();
    (imports.len() == 1)
        .then(|| imports.into_iter().next())
        .flatten()
}

fn helper_is_memory_slot(body: &FunctionBody, names: &SemanticCallNames) -> bool {
    memory_slot_import(body, names).is_some()
}

pub(super) fn memory_slot_from_table_get(
    body: &FunctionBody,
    value: Value,
    names: &SemanticCallNames,
) -> Option<Value> {
    let slot = table_get_slot(body, value)?;
    let (label, call_args) = call_label(body, slot, names)?;
    (label == "wbindgen.memory_slot" && call_args.is_empty()).then_some(slot)
}

fn helper_is_buffer_slot(body: &FunctionBody, names: &SemanticCallNames) -> bool {
    if body.n_params != 1 {
        return false;
    }
    let Some(returned_slot) = unique_return_value(body) else {
        return false;
    };
    let returned_slot = unique_transparent_origin(body, returned_slot, 8);
    body.values.entries().any(|(_, value)| {
        let ValueDef::Operator(Operator::TableSet { .. }, args, _) = value else {
            return false;
        };
        let [slot, stored] = &body.arg_pool[*args] else {
            return false;
        };
        if unique_transparent_origin(body, *slot, 8) != returned_slot {
            return false;
        }
        let Some((function, call_args)) = call_target(body, *stored, 8) else {
            return false;
        };
        names.validated_buffer_imports.contains(&function)
            && matches!(call_args.as_slice(), [receiver]
                if is_table_get_of_entry_parameter(body, *receiver))
    })
}

fn helper_is_memory_get_u32(body: &FunctionBody, names: &SemanticCallNames) -> bool {
    if body.n_params != 1 {
        return false;
    }
    let Some(returned) = unique_return_value(body) else {
        return false;
    };
    let Some((get_function, get_args)) = call_target(body, returned, 8) else {
        return false;
    };
    if !names.validated_get_u32_imports.contains(&get_function) {
        return false;
    }
    let [receiver, offset] = get_args.as_slice() else {
        return false;
    };
    if !is_entry_parameter(body, *offset) {
        return false;
    }
    let Some(view_slot) = table_get_slot(body, *receiver) else {
        return false;
    };
    let view_slot_origin = unique_transparent_origin(body, view_slot, 8);

    body.values.entries().any(|(_, value)| {
        let ValueDef::Operator(Operator::TableSet { .. }, args, _) = value else {
            return false;
        };
        let [slot, stored] = &body.arg_pool[*args] else {
            return false;
        };
        if unique_transparent_origin(body, *slot, 8) != view_slot_origin {
            return false;
        }
        let Some((view_function, view_args)) = call_target(body, *stored, 8) else {
            return false;
        };
        if !names.validated_view_new_imports.contains(&view_function) {
            return false;
        }
        let [buffer_ref, start, length] = view_args.as_slice() else {
            return false;
        };
        if i32_const(body, *start) != Some(0) {
            return false;
        }
        let Some(buffer_slot) = table_get_slot(body, *buffer_ref) else {
            return false;
        };
        let buffer_slot_origin = unique_transparent_origin(body, buffer_slot, 8);
        let Some((buffer_label, buffer_args)) = call_label(body, buffer_slot, names) else {
            return false;
        };
        let [memory_slot] = buffer_args.as_slice() else {
            return false;
        };
        if buffer_label != "wbindgen.buffer_slot" {
            return false;
        }
        let Some((memory_label, memory_args)) = call_label(body, *memory_slot, names) else {
            return false;
        };
        if memory_label != "wbindgen.memory_slot" || !memory_args.is_empty() {
            return false;
        }
        let Some((length_function, length_args)) = call_target(body, *length, 8) else {
            return false;
        };
        if !names
            .validated_byte_length_imports
            .contains(&length_function)
        {
            return false;
        }
        let [length_receiver] = length_args.as_slice() else {
            return false;
        };
        table_get_slot(body, *length_receiver).is_some_and(|length_slot| {
            unique_transparent_origin(body, length_slot, 8) == buffer_slot_origin
        })
    })
}

fn helper_is_loose_get_u32(body: &FunctionBody, names: &SemanticCallNames) -> bool {
    helper_returns_import_call(body, names, "wbg.getUint32").is_some_and(|args| {
        args.into_iter()
            .any(|value| is_entry_parameter(body, value))
    })
}

fn is_straight_line_void_body(body: &FunctionBody) -> bool {
    let mut seen = BTreeSet::new();
    let mut block = body.entry;
    loop {
        if !seen.insert(block) {
            return false;
        }
        match &body.blocks[block].terminator {
            Terminator::Br { target } if target.args.is_empty() => block = target.block,
            Terminator::Return { values } if values.is_empty() => {
                return seen.len() == body.blocks.entries().count();
            }
            _ => return false,
        }
    }
}

fn opaque_host_effect_target(
    body: &FunctionBody,
    imported_functions: &BTreeSet<Func>,
) -> Option<Func> {
    if body.n_params != 3 || !is_straight_line_void_body(body) {
        return None;
    }

    if body.values.entries().any(|(_, value)| {
        matches!(
            value,
            ValueDef::Operator(operator, _, _)
                if !matches!(operator, Operator::Call { .. } | Operator::TableGet { .. })
        )
    }) {
        return None;
    }

    let mut calls = body.values.entries().filter_map(|(_, value)| {
        let ValueDef::Operator(Operator::Call { function_index }, args, _) = value else {
            return None;
        };
        Some((*function_index, body.arg_pool[*args].to_vec()))
    });
    let (imported, args) = calls.next()?;
    if calls.next().is_some() || !imported_functions.contains(&imported) {
        return None;
    }
    let [receiver, base, offset] = args.as_slice() else {
        return None;
    };
    if table_get_slot(body, *receiver).and_then(|slot| entry_parameter_index(body, slot)) != Some(0)
        || entry_parameter_index(body, *base) != Some(1)
        || entry_parameter_index(body, *offset) != Some(2)
    {
        return None;
    }
    Some(imported)
}

pub(super) fn memory_grow_base_slot(
    body: &FunctionBody,
    base: Value,
    names: &SemanticCallNames,
) -> Option<Value> {
    let base = body.resolve_alias(base);
    let ValueDef::Operator(Operator::I32Shl, args, _) = &body.values[base] else {
        return None;
    };
    let [grow_result, shift] = &body.arg_pool[*args] else {
        return None;
    };
    if i32_const(body, *shift) != Some(16) {
        return None;
    }
    let (grow_function, grow_args) = call_target(body, *grow_result, 8)?;
    if !names.validated_memory_grow_imports.contains(&grow_function) {
        return None;
    }
    let [receiver, _delta] = grow_args.as_slice() else {
        return None;
    };
    let memory_slot = memory_slot_from_table_get(body, *receiver, names)?;
    Some(unique_transparent_origin(body, memory_slot, 8))
}

fn classify_base_wasm_bindgen_helper(
    body: &FunctionBody,
    names: &SemanticCallNames,
) -> Option<&'static str> {
    if helper_returns_import_call(body, names, "wbg.length").is_some_and(
        |args| matches!(args.as_slice(), [value] if is_table_get_of_entry_parameter(body, *value)),
    ) {
        Some("wbindgen.externref_length")
    } else if helper_is_memory_slot(body, names) {
        Some("wbindgen.memory_slot")
    } else if helper_is_buffer_slot(body, names) {
        Some("wbindgen.buffer_slot")
    } else {
        None
    }
}

fn helper_is_heap_allocator(
    module: &Module<'_>,
    function: Func,
    body: &FunctionBody,
    imported_functions: &BTreeSet<Func>,
) -> bool {
    let signature = &module.signatures[module.funcs[function].sig()];
    if signature.params.as_slice() != [Type::I32]
        || signature.returns.as_slice() != [Type::I32]
        || direct_called_functions(body)
            .iter()
            .any(|callee| imported_functions.contains(callee))
    {
        return false;
    }

    let mut memory_grows = 0usize;
    let mut loads = 0usize;
    let mut stores = 0usize;
    for (_, value) in body.values.entries() {
        let ValueDef::Operator(operator, _, _) = value else {
            continue;
        };
        let family = operator_family(operator);
        if matches!(operator, Operator::MemoryGrow { .. }) {
            memory_grows += 1;
        } else if family.contains("load") {
            loads += 1;
        } else if family.contains("store") {
            stores += 1;
        }
    }

    let mut zero_return = false;
    let mut nonzero_return = false;
    for (_, block) in body.blocks.entries() {
        let Terminator::Return { values } = &block.terminator else {
            continue;
        };
        let [value] = values.as_slice() else {
            continue;
        };
        match i32_const(body, *value) {
            Some(0) => zero_return = true,
            _ => nonzero_return = true,
        }
    }

    memory_grows > 0 && loads >= 4 && stores >= 8 && zero_return && nonzero_return
}

pub(super) fn build_semantic_call_names(module: &mut Module<'_>, root: Func) -> SemanticCallNames {
    let mut names = SemanticCallNames::default();
    for import in &module.imports {
        if let ImportKind::Func(function) = import.kind {
            names.labels.insert(
                function,
                normalize_import_name(&import.module, &import.name),
            );
            if import.module == "wbg" {
                match import.name.as_str() {
                    "__wbg_grow_43d369088a370694" => {
                        names.validated_memory_grow_imports.insert(function);
                    }
                    "__wbg_buffer_609cc3eee51ed158" => {
                        names.validated_buffer_imports.insert(function);
                    }
                    "__wbg_byteLength_ea52ac3de882b483" => {
                        names.validated_byte_length_imports.insert(function);
                    }
                    "__wbg_new_7e079fa25e135eb1" => {
                        names.validated_view_new_imports.insert(function);
                    }
                    "__wbg_getUint32_9c3cc8fde7919ed4" => {
                        names.validated_get_u32_imports.insert(function);
                    }
                    _ => {}
                }
            }
        }
    }

    let imported_functions = module
        .imports
        .iter()
        .filter_map(|import| match import.kind {
            ImportKind::Func(function) => Some(function),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let direct_callees = module.funcs[root]
        .body()
        .map(direct_called_functions)
        .unwrap_or_default();
    let mut candidates = direct_callees
        .iter()
        .copied()
        .filter(|callee| !imported_functions.contains(callee))
        .collect::<BTreeSet<_>>();

    // Inspect exactly one nested helper layer. This is enough for wasm-bindgen
    // wrappers such as memory -> buffer -> DataView without turning semantic
    // naming into an unbounded whole-module expansion.
    for callee in direct_callees {
        if imported_functions.contains(&callee) || module.expand_func(callee).is_err() {
            continue;
        }
        let nested = module.funcs[callee]
            .body()
            .map(direct_called_functions)
            .unwrap_or_default();
        candidates.extend(
            nested
                .into_iter()
                .filter(|nested| !imported_functions.contains(nested)),
        );
    }
    for callee in candidates.iter().copied() {
        let _ = module.expand_func(callee);
    }

    // Helper labels depend on one another (memory_slot -> buffer_slot), so use
    // a tiny bounded fixed point over only the candidate set above.
    for _ in 0..3 {
        let mut changed = false;
        for callee in candidates.iter().copied() {
            if names.labels.contains_key(&callee) {
                continue;
            }
            let Some(body) = module.funcs[callee].body() else {
                continue;
            };
            let label = classify_base_wasm_bindgen_helper(body, &names)
                .map(str::to_owned)
                .or_else(|| {
                    helper_is_heap_allocator(module, callee, body, &imported_functions)
                        .then(|| "wasm.heap_alloc".to_owned())
                });
            if let Some(label) = label {
                names.labels.insert(callee, label);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    for callee in candidates.iter().copied() {
        let Some(body) = module.funcs[callee].body() else {
            continue;
        };
        if let Some(imported) = memory_slot_import(body, &names) {
            names.memory_slot_imports.insert(callee, imported);
        }
    }

    // Record tiny wrappers that unconditionally forward
    // (externref slot, base, offset) to one imported host function. The import
    // remains opaque: this proves an effect boundary, not that the host function
    // writes memory. Call-site analysis below separately proves the slot is the
    // wasm Memory slot that produced the base through Memory.grow.
    for callee in candidates.iter().copied() {
        let Some(body) = module.funcs[callee].body() else {
            continue;
        };
        if let Some(imported) = opaque_host_effect_target(body, &imported_functions) {
            names.opaque_host_effect_helpers.insert(callee, imported);
        }
    }

    // The strong memory-read proof needs the nested buffer/memory helper labels
    // established above. Fall back to the older loose bridge name when only
    // the imported getUint32 call and offset parameter can be proven.
    for callee in candidates {
        if names.labels.contains_key(&callee) {
            continue;
        }
        let Some(body) = module.funcs[callee].body() else {
            continue;
        };
        if helper_is_memory_get_u32(body, &names) {
            names
                .labels
                .insert(callee, "wbindgen.memory_get_u32".to_owned());
            names.validated_memory_get_u32_helpers.insert(callee);
        } else if helper_is_loose_get_u32(body, &names) {
            names
                .labels
                .insert(callee, "wbindgen.getUint32_bridge".to_owned());
        }
    }
    names
}
