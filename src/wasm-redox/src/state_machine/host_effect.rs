use super::{
    helper_recognition::{memory_grow_base_slot, SemanticCallNames},
    ir::i32_const,
    value_flow::unique_transparent_origin,
};
use serde::Serialize;
use std::collections::BTreeMap;
use waffle::{entity::EntityRef, Func, FunctionBody, Operator, Value, ValueDef};

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct OpaqueHostEffectMemoryReadReport {
    /// WAFFLE basic block containing both operations. The host effect call is
    /// earlier than the validated memory read in this same block.
    pub block: usize,
    pub host_effect_value: usize,
    pub host_wrapper_function: usize,
    pub host_import_function: usize,
    /// Normalized imported host function reached through the proven wrapper.
    /// The import remains semantically opaque; this does not claim a write.
    pub host_import: String,
    pub memory_read_value: usize,
    pub memory_read_helper: usize,
    pub base_value: usize,
    pub offset: u32,
    pub runtime_binding: Option<String>,
}

fn base_and_constant_offset(body: &FunctionBody, address: Value) -> Option<(Value, u32)> {
    let address = body.resolve_alias(address);
    let ValueDef::Operator(Operator::I32Or, args, _) = &body.values[address] else {
        return None;
    };
    let [left, right] = &body.arg_pool[*args] else {
        return None;
    };
    if let Some(offset) = i32_const(body, *left) {
        return Some((unique_transparent_origin(body, *right, 8), offset));
    }
    i32_const(body, *right).map(|offset| (unique_transparent_origin(body, *left, 8), offset))
}

pub(super) fn opaque_host_effect_memory_reads(
    body: &FunctionBody,
    names: &SemanticCallNames,
    runtime_names: &BTreeMap<Value, String>,
) -> Vec<OpaqueHostEffectMemoryReadReport> {
    let mut reports = Vec::new();
    for (block, block_def) in body.blocks.entries() {
        let mut earlier_host_effects: BTreeMap<(Value, u32), (Value, Func, Func)> = BTreeMap::new();
        for inst in &block_def.insts {
            let value = body.resolve_alias(*inst);
            let ValueDef::Operator(Operator::Call { function_index }, args, _) =
                &body.values[value]
            else {
                continue;
            };
            let call_args = &body.arg_pool[*args];
            if let Some(imported) = names.opaque_host_effect_import(*function_index) {
                if let [slot, base, offset] = call_args {
                    let slot = unique_transparent_origin(body, *slot, 8);
                    if memory_grow_base_slot(body, *base, names) == Some(slot) {
                        if let Some(offset) = i32_const(body, *offset) {
                            earlier_host_effects.insert(
                                (unique_transparent_origin(body, *base, 8), offset),
                                (value, *function_index, imported),
                            );
                        }
                    }
                }
                continue;
            }
            if !names.is_memory_get_u32_helper(*function_index) {
                continue;
            }
            let [address] = call_args else {
                continue;
            };
            let Some((base, offset)) = base_and_constant_offset(body, *address) else {
                continue;
            };
            let Some((host_effect_value, host_wrapper, host_import)) =
                earlier_host_effects.get(&(base, offset)).copied()
            else {
                continue;
            };
            let report = OpaqueHostEffectMemoryReadReport {
                block: block.index(),
                host_effect_value: host_effect_value.index(),
                host_wrapper_function: host_wrapper.index(),
                host_import_function: host_import.index(),
                host_import: names
                    .label(host_import)
                    .map(str::to_owned)
                    .unwrap_or_else(|| format!("func{}", host_import.index())),
                memory_read_value: value.index(),
                memory_read_helper: function_index.index(),
                base_value: base.index(),
                offset,
                runtime_binding: runtime_names.get(&value).cloned(),
            };
            if !reports.contains(&report) {
                reports.push(report);
            }
        }
    }
    reports
}
