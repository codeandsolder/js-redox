use super::{ir::i32_const, value_flow::unique_transparent_origin};
use serde::Serialize;
use std::collections::BTreeSet;
use waffle::{
    cfg::CFGInfo, entity::EntityRef, Block, Func, FunctionBody, ImportKind, Module, Operator,
    Value, ValueDef,
};

#[derive(Clone, Debug, Serialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct StructuralInputCopyLoadReport {
    pub value: usize,
    pub memory: usize,
    pub byte_offset: u32,
    pub align: u32,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExternrefBulkCopyCandidateReport {
    /// Basic block and instruction position containing the set-like imported call.
    pub block: usize,
    pub set_instruction_index: usize,
    pub set_call_value: usize,
    /// Imported function receiving `(receiver, source, element_offset)`.
    pub set_import_function: usize,
    /// Imported one-argument function whose result becomes `receiver`.
    pub constructor_import_function: usize,
    /// Root export parameter stored in the table and later passed as `source`.
    pub source_entry_parameter: usize,
    pub source_slot_value: usize,
    pub source_store_block: usize,
    pub source_store_instruction_index: usize,
    pub source_store_value: usize,
    pub receiver_slot_value: usize,
    pub receiver_store_block: usize,
    pub receiver_store_instruction_index: usize,
    pub receiver_store_value: usize,
    /// Byte-address value shifted right before it is passed as the element offset.
    pub destination_base_value: usize,
    pub destination_element_index_shift: u32,
    /// Table slot from which the constructor input is loaded.
    pub constructor_input_slot_value: usize,
    /// Optional structural helper chain producing the constructor-input slot.
    pub constructor_input_slot_provider_function: Option<usize>,
    pub constructor_input_provider_argument_function: Option<usize>,
    /// Native WASM loads dominated by the set-like call and reusing the same destination-base SSA value.
    /// This does not prove the copied bytes remain unmodified before each load.
    pub destination_loads: Vec<StructuralInputCopyLoadReport>,
}

fn direct_call(body: &FunctionBody, value: Value, depth: usize) -> Option<(Func, Vec<Value>)> {
    if depth == 0 {
        return None;
    }
    let value = body.resolve_alias(value);
    match &body.values[value] {
        ValueDef::Operator(Operator::Call { function_index }, args, _) => {
            Some((*function_index, body.arg_pool[*args].to_vec()))
        }
        ValueDef::PickOutput(source, 0, _) => direct_call(body, *source, depth - 1),
        _ => None,
    }
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
    Some(unique_transparent_origin(body, *slot, 8))
}

fn same_origin(body: &FunctionBody, left: Value, right: Value) -> bool {
    unique_transparent_origin(body, left, 8) == unique_transparent_origin(body, right, 8)
}

fn same_table_slot(body: &FunctionBody, left: Value, right: Value) -> bool {
    same_origin(body, left, right)
        || matches!((i32_const(body, left), i32_const(body, right)), (Some(a), Some(b)) if a == b)
}

#[derive(Clone, Copy, Debug)]
struct TableStoreSite {
    block: Block,
    position: usize,
    value: Value,
    stored: Value,
}

fn table_store_for_slot(
    body: &FunctionBody,
    instruction: Value,
    wanted_slot: Value,
) -> Option<(Value, Value)> {
    let value = body.resolve_alias(instruction);
    let ValueDef::Operator(Operator::TableSet { .. }, args, _) = &body.values[value] else {
        return None;
    };
    let [slot, stored] = &body.arg_pool[*args] else {
        return None;
    };
    same_table_slot(body, *slot, wanted_slot).then_some((value, *stored))
}

fn no_slot_overwrite_between(
    body: &FunctionBody,
    cfg: &CFGInfo,
    store: TableStoreSite,
    target_block: Block,
    target_position: usize,
    wanted_slot: Value,
) -> bool {
    if store.block == target_block {
        return store.position < target_position
            && !body.blocks[target_block].insts[store.position + 1..target_position]
                .iter()
                .any(|instruction| {
                    table_store_for_slot(body, *instruction, wanted_slot).is_some()
                });
    }
    if cfg.rpo_pos[store.block].is_none()
        || cfg.rpo_pos[target_block].is_none()
        || !cfg.dominates(store.block, target_block)
    {
        return false;
    }
    if body.blocks[store.block].insts[store.position + 1..]
        .iter()
        .any(|instruction| table_store_for_slot(body, *instruction, wanted_slot).is_some())
    {
        return false;
    }

    let mut stack = vec![target_block];
    let mut visited = BTreeSet::new();
    while let Some(block) = stack.pop() {
        if block == store.block || !visited.insert(block) {
            continue;
        }
        let end = if block == target_block {
            target_position
        } else {
            body.blocks[block].insts.len()
        };
        if body.blocks[block].insts[..end]
            .iter()
            .any(|instruction| table_store_for_slot(body, *instruction, wanted_slot).is_some())
        {
            return false;
        }
        for predecessor in cfg.preds[block].iter().copied() {
            if cfg.rpo_pos[predecessor].is_none() {
                continue;
            }
            if predecessor != store.block && !cfg.dominates(store.block, predecessor) {
                return false;
            }
            stack.push(predecessor);
        }
    }
    true
}

fn safe_store_before(
    body: &FunctionBody,
    cfg: &CFGInfo,
    target_block: Block,
    target_position: usize,
    wanted_slot: Value,
) -> Option<TableStoreSite> {
    let mut candidates = Vec::new();
    for (block, block_definition) in body.blocks.entries() {
        for (position, instruction) in block_definition.insts.iter().copied().enumerate() {
            let Some((value, stored)) = table_store_for_slot(body, instruction, wanted_slot) else {
                continue;
            };
            let site = TableStoreSite {
                block,
                position,
                value,
                stored,
            };
            if no_slot_overwrite_between(
                body,
                cfg,
                site,
                target_block,
                target_position,
                wanted_slot,
            ) {
                candidates.push(site);
            }
        }
    }
    (candidates.len() == 1)
        .then(|| candidates.into_iter().next())
        .flatten()
}

fn base_shifted_right_by_two(body: &FunctionBody, value: Value) -> Option<Value> {
    let value = body.resolve_alias(value);
    let ValueDef::Operator(Operator::I32ShrU, args, _) = &body.values[value] else {
        return None;
    };
    let [base, shift] = &body.arg_pool[*args] else {
        return None;
    };
    (i32_const(body, *shift) == Some(2)).then(|| unique_transparent_origin(body, *base, 8))
}

fn provider_chain(body: &FunctionBody, input_slot: Value) -> (Option<usize>, Option<usize>) {
    let Some((provider, args)) = direct_call(body, input_slot, 4) else {
        return (None, None);
    };
    let nested = match args.as_slice() {
        [argument] => direct_call(body, *argument, 4).map(|(function, _)| function.index()),
        _ => None,
    };
    (Some(provider.index()), nested)
}

fn destination_loads_dominated_by_set(
    body: &FunctionBody,
    cfg: &CFGInfo,
    set_block: Block,
    set_position: usize,
    destination_base: Value,
) -> Vec<StructuralInputCopyLoadReport> {
    let mut loads = Vec::new();
    for (block, block_definition) in body.blocks.entries() {
        if !cfg.dominates(set_block, block) {
            continue;
        }
        let start = if block == set_block {
            set_position + 1
        } else {
            0
        };
        for instruction in &block_definition.insts[start..] {
            let value = body.resolve_alias(*instruction);
            let ValueDef::Operator(Operator::I32Load { memory }, args, _) = &body.values[value]
            else {
                continue;
            };
            let [address] = &body.arg_pool[*args] else {
                continue;
            };
            if !same_origin(body, *address, destination_base) {
                continue;
            }
            loads.push(StructuralInputCopyLoadReport {
                value: value.index(),
                memory: memory.memory.index(),
                byte_offset: memory.offset,
                align: memory.align,
            });
        }
    }
    loads.sort_by(|left, right| {
        left.byte_offset
            .cmp(&right.byte_offset)
            .then_with(|| left.memory.cmp(&right.memory))
            .then_with(|| left.value.cmp(&right.value))
    });
    loads.dedup();
    loads
}

pub(super) fn externref_bulk_copy_candidates(
    module: &Module<'_>,
    body: &FunctionBody,
) -> Vec<ExternrefBulkCopyCandidateReport> {
    let cfg = CFGInfo::new(body);
    let imported = module
        .imports
        .iter()
        .filter_map(|import| match import.kind {
            ImportKind::Func(function) => Some(function),
            _ => None,
        })
        .collect::<BTreeSet<_>>();

    let mut reports = Vec::new();
    for (block, block_definition) in body.blocks.entries() {
        for (position, instruction) in block_definition.insts.iter().enumerate() {
            let call_value = body.resolve_alias(*instruction);
            let ValueDef::Operator(Operator::Call { function_index }, args, _) =
                &body.values[call_value]
            else {
                continue;
            };
            if !imported.contains(function_index) {
                continue;
            }
            let [receiver, source, element_offset] = &body.arg_pool[*args] else {
                continue;
            };
            let Some(receiver_slot) = table_get_slot(body, *receiver) else {
                continue;
            };
            let Some(source_slot) = table_get_slot(body, *source) else {
                continue;
            };
            let Some(source_store) = safe_store_before(body, &cfg, block, position, source_slot)
            else {
                continue;
            };
            let Some(source_entry_parameter) = entry_parameter_index(body, source_store.stored)
            else {
                continue;
            };
            let Some(destination_base) = base_shifted_right_by_two(body, *element_offset) else {
                continue;
            };
            let Some(receiver_store) =
                safe_store_before(body, &cfg, block, position, receiver_slot)
            else {
                continue;
            };
            let Some((constructor_import, constructor_args)) =
                direct_call(body, receiver_store.stored, 4)
            else {
                continue;
            };
            let [constructor_input] = constructor_args.as_slice() else {
                continue;
            };
            if !imported.contains(&constructor_import) || constructor_import == *function_index {
                continue;
            }
            let Some(constructor_input_slot) = table_get_slot(body, *constructor_input) else {
                continue;
            };
            let (slot_provider, provider_argument) = provider_chain(body, constructor_input_slot);
            reports.push(ExternrefBulkCopyCandidateReport {
                block: block.index(),
                set_instruction_index: position,
                set_call_value: call_value.index(),
                set_import_function: function_index.index(),
                constructor_import_function: constructor_import.index(),
                source_entry_parameter,
                source_slot_value: source_slot.index(),
                source_store_block: source_store.block.index(),
                source_store_instruction_index: source_store.position,
                source_store_value: source_store.value.index(),
                receiver_slot_value: receiver_slot.index(),
                receiver_store_block: receiver_store.block.index(),
                receiver_store_instruction_index: receiver_store.position,
                receiver_store_value: receiver_store.value.index(),
                destination_base_value: destination_base.index(),
                destination_element_index_shift: 2,
                constructor_input_slot_value: constructor_input_slot.index(),
                constructor_input_slot_provider_function: slot_provider,
                constructor_input_provider_argument_function: provider_argument,
                destination_loads: destination_loads_dominated_by_set(
                    body,
                    &cfg,
                    block,
                    position,
                    destination_base,
                ),
            });
        }
    }
    reports.sort();
    reports.dedup();
    reports
}
