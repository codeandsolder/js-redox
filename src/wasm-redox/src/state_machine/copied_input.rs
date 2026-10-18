use super::{
    helper_recognition::SemanticCallNames,
    ir::i32_const,
    value_flow::{incoming_block_param_values, unique_transparent_origin},
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use waffle::{
    cfg::CFGInfo, entity::EntityRef, Block, Func, FunctionBody, ImportKind, Module, Operator,
    SideEffect, Value, ValueDef,
};

#[derive(Clone, Debug, Serialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct StructuralInputCopyLoadReport {
    pub value: usize,
    pub block: usize,
    pub instruction_index: usize,
    pub memory: usize,
    pub byte_offset: u32,
    pub align: u32,
    /// Imported source-length property getters reached through the structural
    /// wasm-bindgen helper on paths from the proven set-like call to this load.
    /// Cross-language correlation may discharge these only with an exact pure
    /// `length` handler proof for the same module/import object and a proven
    /// Uint32Array source.
    pub source_length_import_barriers: Vec<usize>,
    /// Other imported calls reachable before this load. These remain opaque
    /// memory barriers and prevent byte-integrity claims.
    pub other_import_call_barriers: Vec<usize>,
    /// True when a same-memory write, indirect call, recursive unknown, or other
    /// unresolved side effect can occur before this static load execution.
    pub unresolved_intervening_memory_mutation: bool,
    /// Standalone WASM-only integrity proof. Cross-language correlation may be
    /// stronger by discharging `source_length_import_barriers` semantically.
    pub copied_bytes_unmodified_since_set: bool,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct FreshDestinationBaseRecipeReport {
    /// Internal single-i32 producer whose result can become the destination base.
    pub function: usize,
    /// Structural wasm-bindgen source-length helper feeding the byte-count expression.
    pub source_length_helper_function: usize,
    /// Imported property getter called by that helper.
    pub source_length_import_function: usize,
    /// Exact left shift converting source element count to producer byte count.
    pub source_length_byte_shift: u32,
    /// Other destination-base origins, all proven constants aligned to the element width.
    pub alternate_constant_bases: Vec<u32>,
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
    /// Minimum number of low zero bits proven for every possible value of the
    /// destination base. A value >= `destination_element_index_shift` proves
    /// that the JS typed-array element offset and WASM byte base coincide.
    pub destination_base_guaranteed_trailing_zero_bits: u32,
    /// Optional exact recipe for evaluating the non-constant destination-base producer
    /// on fresh module state once the JS-side source length is known.
    pub fresh_destination_base_recipe: Option<FreshDestinationBaseRecipeReport>,
    /// Table slot from which the constructor input is loaded.
    pub constructor_input_slot_value: usize,
    /// Optional structural helper chain producing the constructor-input slot.
    pub constructor_input_slot_provider_function: Option<usize>,
    pub constructor_input_provider_argument_function: Option<usize>,
    /// Imported function proven to provide the module Memory object to that helper chain.
    pub constructor_input_memory_import_function: Option<usize>,
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

fn collect_origin_values(
    body: &FunctionBody,
    value: Value,
    depth: usize,
    visiting: &mut BTreeSet<Value>,
    origins: &mut BTreeSet<Value>,
) -> bool {
    if depth == 0 {
        return false;
    }
    let value = body.resolve_alias(value);
    if !visiting.insert(value) {
        return false;
    }
    let complete = match &body.values[value] {
        ValueDef::Alias(alias) | ValueDef::PickOutput(alias, 0, _) => {
            collect_origin_values(body, *alias, depth - 1, visiting, origins)
        }
        ValueDef::BlockParam(block, _, _) if *block != body.entry => {
            let incoming = incoming_block_param_values(body, *block, value);
            !incoming.is_empty()
                && incoming.into_iter().all(|incoming| {
                    collect_origin_values(body, incoming, depth - 1, visiting, origins)
                })
        }
        _ => {
            origins.insert(value);
            true
        }
    };
    visiting.remove(&value);
    complete
}

fn fresh_destination_base_recipe(
    module: &Module<'_>,
    body: &FunctionBody,
    destination_base: Value,
    source_slot: Value,
    names: &SemanticCallNames,
) -> Option<FreshDestinationBaseRecipeReport> {
    let mut origins = BTreeSet::new();
    if !collect_origin_values(
        body,
        destination_base,
        16,
        &mut BTreeSet::new(),
        &mut origins,
    ) {
        return None;
    }

    let mut recipe: Option<(Func, Func, Func, u32)> = None;
    let mut alternate_constant_bases = Vec::new();
    for origin in origins {
        if let Some(value) = i32_const(body, origin) {
            if value.trailing_zeros() < 2 {
                return None;
            }
            alternate_constant_bases.push(value);
            continue;
        }

        let (function, args) = direct_call(body, origin, 4)?;
        module.funcs[function].body()?;
        let [byte_count] = args.as_slice() else {
            return None;
        };
        let byte_count = body.resolve_alias(*byte_count);
        let ValueDef::Operator(Operator::I32Shl, shift_args, _) = &body.values[byte_count] else {
            return None;
        };
        let [source_length, shift] = &body.arg_pool[*shift_args] else {
            return None;
        };
        let shift = i32_const(body, *shift)?;
        if shift >= 32 {
            return None;
        }
        let (length_helper, length_args) = direct_call(body, *source_length, 4)?;
        let [length_source_slot] = length_args.as_slice() else {
            return None;
        };
        if !same_table_slot(body, *length_source_slot, source_slot) {
            return None;
        }
        let length_import = names.externref_length_import(length_helper)?;
        let candidate = (function, length_helper, length_import, shift);
        if recipe.is_some_and(|existing| existing != candidate) {
            return None;
        }
        recipe = Some(candidate);
    }
    let (function, length_helper, length_import, shift) = recipe?;
    alternate_constant_bases.sort_unstable();
    alternate_constant_bases.dedup();
    Some(FreshDestinationBaseRecipeReport {
        function: function.index(),
        source_length_helper_function: length_helper.index(),
        source_length_import_function: length_import.index(),
        source_length_byte_shift: shift,
        alternate_constant_bases,
    })
}

fn provider_chain(
    body: &FunctionBody,
    input_slot: Value,
    names: &SemanticCallNames,
) -> (Option<usize>, Option<usize>, Option<usize>) {
    let Some((provider, args)) = direct_call(body, input_slot, 4) else {
        return (None, None, None);
    };
    let nested = match args.as_slice() {
        [argument] => direct_call(body, *argument, 4).map(|(function, _)| function),
        _ => None,
    };
    let memory_import = nested
        .and_then(|function| names.memory_slot_import(function))
        .map(|function| function.index());
    (
        Some(provider.index()),
        nested.map(|function| function.index()),
        memory_import,
    )
}

fn function_return_trailing_zero_bits(
    module: &Module<'_>,
    function: Func,
    function_cache: &mut BTreeMap<Func, u32>,
    visiting_functions: &mut BTreeSet<Func>,
) -> u32 {
    if let Some(bits) = function_cache.get(&function) {
        return *bits;
    }
    if !visiting_functions.insert(function) {
        return 0;
    }
    let bits = module.funcs[function].body().map_or(0, |body| {
        let mut value_cache = BTreeMap::new();
        let mut visiting_values = BTreeSet::new();
        let mut found = false;
        let mut result = 32;
        for (_, block) in body.blocks.entries() {
            let waffle::Terminator::Return { values } = &block.terminator else {
                continue;
            };
            let [value] = values.as_slice() else {
                return 0;
            };
            found = true;
            result = result.min(value_trailing_zero_bits(
                module,
                body,
                *value,
                function_cache,
                visiting_functions,
                &mut value_cache,
                &mut visiting_values,
            ));
        }
        if found {
            result
        } else {
            0
        }
    });
    visiting_functions.remove(&function);
    function_cache.insert(function, bits);
    bits
}

fn binary_argument_bits(
    module: &Module<'_>,
    body: &FunctionBody,
    args: &[Value],
    function_cache: &mut BTreeMap<Func, u32>,
    visiting_functions: &mut BTreeSet<Func>,
    value_cache: &mut BTreeMap<Value, u32>,
    visiting_values: &mut BTreeSet<Value>,
) -> Option<(u32, u32)> {
    let [left, right] = args else {
        return None;
    };
    Some((
        value_trailing_zero_bits(
            module,
            body,
            *left,
            function_cache,
            visiting_functions,
            value_cache,
            visiting_values,
        ),
        value_trailing_zero_bits(
            module,
            body,
            *right,
            function_cache,
            visiting_functions,
            value_cache,
            visiting_values,
        ),
    ))
}

fn value_trailing_zero_bits(
    module: &Module<'_>,
    body: &FunctionBody,
    value: Value,
    function_cache: &mut BTreeMap<Func, u32>,
    visiting_functions: &mut BTreeSet<Func>,
    value_cache: &mut BTreeMap<Value, u32>,
    visiting_values: &mut BTreeSet<Value>,
) -> u32 {
    let value = body.resolve_alias(value);
    if let Some(bits) = value_cache.get(&value) {
        return *bits;
    }
    if !visiting_values.insert(value) {
        // A cyclic value may progressively destroy alignment (for example a
        // loop-carried right shift). Solving that fixed point is deliberately out
        // of scope here; fail closed rather than treating the backedge as an
        // identity-preserving path.
        return 0;
    }
    let bits = match &body.values[value] {
        ValueDef::Alias(alias) => value_trailing_zero_bits(
            module,
            body,
            *alias,
            function_cache,
            visiting_functions,
            value_cache,
            visiting_values,
        ),
        ValueDef::BlockParam(block, _, _) if *block != body.entry => {
            let incoming = incoming_block_param_values(body, *block, value);
            if incoming.is_empty() {
                0
            } else {
                incoming.into_iter().fold(32, |known, argument| {
                    known.min(value_trailing_zero_bits(
                        module,
                        body,
                        argument,
                        function_cache,
                        visiting_functions,
                        value_cache,
                        visiting_values,
                    ))
                })
            }
        }
        ValueDef::BlockParam(..) => 0,
        ValueDef::Operator(Operator::I32Const { value }, _, _) => value.trailing_zeros(),
        ValueDef::Operator(operator, args, _) => {
            let args = &body.arg_pool[*args];
            match operator {
                Operator::I32Add | Operator::I32Sub | Operator::I32Or | Operator::I32Xor => {
                    binary_argument_bits(
                        module,
                        body,
                        args,
                        function_cache,
                        visiting_functions,
                        value_cache,
                        visiting_values,
                    )
                    .map_or(0, |(left, right)| left.min(right))
                }
                Operator::I32Mul => binary_argument_bits(
                    module,
                    body,
                    args,
                    function_cache,
                    visiting_functions,
                    value_cache,
                    visiting_values,
                )
                .map_or(0, |(left, right)| left.saturating_add(right).min(32)),
                Operator::I32And => binary_argument_bits(
                    module,
                    body,
                    args,
                    function_cache,
                    visiting_functions,
                    value_cache,
                    visiting_values,
                )
                .map_or(0, |(left, right)| left.max(right)),
                Operator::I32Shl => match args {
                    [input, shift] => i32_const(body, *shift).map_or(0, |shift| {
                        let input_bits = value_trailing_zero_bits(
                            module,
                            body,
                            *input,
                            function_cache,
                            visiting_functions,
                            value_cache,
                            visiting_values,
                        );
                        input_bits.saturating_add(shift & 31).min(32)
                    }),
                    _ => 0,
                },
                Operator::I32ShrS | Operator::I32ShrU => match args {
                    [input, shift] => i32_const(body, *shift).map_or(0, |shift| {
                        value_trailing_zero_bits(
                            module,
                            body,
                            *input,
                            function_cache,
                            visiting_functions,
                            value_cache,
                            visiting_values,
                        )
                        .saturating_sub(shift & 31)
                    }),
                    _ => 0,
                },
                Operator::Call { function_index } => function_return_trailing_zero_bits(
                    module,
                    *function_index,
                    function_cache,
                    visiting_functions,
                ),
                _ => 0,
            }
        }
        ValueDef::PickOutput(source, index, _) if *index == 0 => {
            let source = body.resolve_alias(*source);
            match &body.values[source] {
                ValueDef::Operator(Operator::Call { function_index }, _, _) => {
                    function_return_trailing_zero_bits(
                        module,
                        *function_index,
                        function_cache,
                        visiting_functions,
                    )
                }
                _ => 0,
            }
        }
        ValueDef::PickOutput(..) | ValueDef::Placeholder(_) | ValueDef::None => 0,
    };
    visiting_values.remove(&value);
    value_cache.insert(value, bits);
    bits
}

fn guaranteed_trailing_zero_bits(module: &Module<'_>, body: &FunctionBody, value: Value) -> u32 {
    let mut function_cache = BTreeMap::new();
    let mut visiting_functions = BTreeSet::new();
    let mut value_cache = BTreeMap::new();
    let mut visiting_values = BTreeSet::new();
    value_trailing_zero_bits(
        module,
        body,
        value,
        &mut function_cache,
        &mut visiting_functions,
        &mut value_cache,
        &mut visiting_values,
    )
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct MemoryBarrierSummary {
    unresolved: bool,
    source_length_imports: BTreeSet<usize>,
    other_imports: BTreeSet<usize>,
}

impl MemoryBarrierSummary {
    fn merge(&mut self, other: &Self) -> bool {
        let old_unresolved = self.unresolved;
        let old_source_len = self.source_length_imports.len();
        let old_other_len = self.other_imports.len();
        self.unresolved |= other.unresolved;
        self.source_length_imports
            .extend(other.source_length_imports.iter().copied());
        self.other_imports
            .extend(other.other_imports.iter().copied());
        self.unresolved != old_unresolved
            || self.source_length_imports.len() != old_source_len
            || self.other_imports.len() != old_other_len
    }

    fn is_empty(&self) -> bool {
        !self.unresolved && self.source_length_imports.is_empty() && self.other_imports.is_empty()
    }
}

fn operator_direct_memory_mutation(operator: &Operator, target_memory: usize) -> bool {
    match operator {
        Operator::I32Store { memory }
        | Operator::I64Store { memory }
        | Operator::F32Store { memory }
        | Operator::F64Store { memory }
        | Operator::I32Store8 { memory }
        | Operator::I32Store16 { memory }
        | Operator::I64Store8 { memory }
        | Operator::I64Store16 { memory }
        | Operator::I64Store32 { memory }
        | Operator::V128Store { memory }
        | Operator::V128Store8Lane { memory, .. }
        | Operator::V128Store16Lane { memory, .. }
        | Operator::V128Store32Lane { memory, .. }
        | Operator::V128Store64Lane { memory, .. } => memory.memory.index() == target_memory,
        Operator::MemoryCopy { dst_mem, .. } => dst_mem.index() == target_memory,
        Operator::MemoryFill { mem } | Operator::MemoryInit { mem, .. } => {
            mem.index() == target_memory
        }
        // memory.grow preserves every pre-existing byte. The JS copy has already
        // completed at the start of this proof interval, so buffer replacement is
        // not itself a content mutation for subsequent WASM loads.
        Operator::MemoryGrow { .. } => false,
        Operator::Call { .. } | Operator::CallIndirect { .. } => false,
        _ => operator
            .effects()
            .iter()
            .any(|effect| matches!(effect, SideEffect::All | SideEffect::WriteMem)),
    }
}

struct MemoryBarrierAnalyzer<'m, 'n, 'b> {
    module: &'m Module<'m>,
    names: &'n SemanticCallNames,
    body: &'b FunctionBody,
    target_memory: usize,
    source_slot: Value,
    function_cache: BTreeMap<Func, MemoryBarrierSummary>,
    visiting_functions: BTreeSet<Func>,
}

impl MemoryBarrierAnalyzer<'_, '_, '_> {
    fn function(&mut self, function: Func) -> MemoryBarrierSummary {
        if let Some(summary) = self.function_cache.get(&function) {
            return summary.clone();
        }
        if !self.visiting_functions.insert(function) {
            return MemoryBarrierSummary {
                unresolved: true,
                ..MemoryBarrierSummary::default()
            };
        }
        let Some(body) = self.module.funcs[function].body() else {
            self.visiting_functions.remove(&function);
            return MemoryBarrierSummary {
                other_imports: BTreeSet::from([function.index()]),
                ..MemoryBarrierSummary::default()
            };
        };
        let mut summary = MemoryBarrierSummary::default();
        for (_, value) in body.values.entries() {
            let ValueDef::Operator(operator, _, _) = value else {
                continue;
            };
            match operator {
                Operator::Call { function_index } => {
                    summary.merge(&self.function(*function_index));
                }
                Operator::CallIndirect { .. } => summary.unresolved = true,
                _ if operator_direct_memory_mutation(operator, self.target_memory) => {
                    summary.unresolved = true;
                }
                _ => {}
            }
        }
        self.visiting_functions.remove(&function);
        self.function_cache.insert(function, summary.clone());
        summary
    }

    fn instruction(&mut self, instruction: Value) -> MemoryBarrierSummary {
        let value = self.body.resolve_alias(instruction);
        match &self.body.values[value] {
            ValueDef::Operator(Operator::Call { function_index }, args, _) => {
                if let Some(imported) = self.names.externref_length_import(*function_index) {
                    if matches!(&self.body.arg_pool[*args], [slot] if same_origin(self.body, *slot, self.source_slot))
                    {
                        return MemoryBarrierSummary {
                            source_length_imports: BTreeSet::from([imported.index()]),
                            ..MemoryBarrierSummary::default()
                        };
                    }
                }
                self.function(*function_index)
            }
            ValueDef::Operator(Operator::CallIndirect { .. }, _, _) => MemoryBarrierSummary {
                unresolved: true,
                ..MemoryBarrierSummary::default()
            },
            ValueDef::Operator(operator, _, _)
                if operator_direct_memory_mutation(operator, self.target_memory) =>
            {
                MemoryBarrierSummary {
                    unresolved: true,
                    ..MemoryBarrierSummary::default()
                }
            }
            ValueDef::PickOutput(source, _, _) => self.instruction(*source),
            _ => MemoryBarrierSummary::default(),
        }
    }
}

#[derive(Clone, Copy)]
struct CopySite {
    block: Block,
    position: usize,
    destination_base: Value,
    source_slot: Value,
}

#[derive(Clone, Copy)]
struct LoadSite {
    block: Block,
    position: usize,
    memory: usize,
}

fn barriers_before_load(
    module: &Module<'_>,
    names: &SemanticCallNames,
    body: &FunctionBody,
    cfg: &CFGInfo,
    copy: CopySite,
    load: LoadSite,
) -> Option<MemoryBarrierSummary> {
    if (copy.block == load.block && copy.position >= load.position)
        || (copy.block != load.block && !cfg.dominates(copy.block, load.block))
    {
        return None;
    }

    let mut states = BTreeMap::<(usize, usize), MemoryBarrierSummary>::new();
    states.insert(
        (copy.block.index(), copy.position + 1),
        MemoryBarrierSummary::default(),
    );
    let mut queue = VecDeque::from([(copy.block, copy.position + 1)]);
    let mut reached_load = false;
    let mut load_summary = MemoryBarrierSummary::default();
    let mut analyzer = MemoryBarrierAnalyzer {
        module,
        names,
        body,
        target_memory: load.memory,
        source_slot: copy.source_slot,
        function_cache: BTreeMap::new(),
        visiting_functions: BTreeSet::new(),
    };

    while let Some((block, position)) = queue.pop_front() {
        let key = (block.index(), position);
        let Some(state) = states.get(&key).cloned() else {
            continue;
        };
        let block_definition = &body.blocks[block];
        if block == load.block && position == load.position {
            reached_load = true;
            load_summary.merge(&state);
        }
        if position < block_definition.insts.len() {
            let mut next = state;
            let barriers = analyzer.instruction(block_definition.insts[position]);
            next.merge(&barriers);
            let next_key = (block.index(), position + 1);
            let changed = match states.get_mut(&next_key) {
                Some(existing) => existing.merge(&next),
                None => {
                    states.insert(next_key, next);
                    true
                }
            };
            if changed {
                queue.push_back((block, position + 1));
            }
            continue;
        }
        block_definition.terminator.visit_targets(|target| {
            let next_key = (target.block.index(), 0);
            let changed = match states.get_mut(&next_key) {
                Some(existing) => existing.merge(&state),
                None => {
                    states.insert(next_key, state.clone());
                    true
                }
            };
            if changed {
                queue.push_back((target.block, 0));
            }
        });
    }
    reached_load.then_some(load_summary)
}

fn destination_loads_dominated_by_set(
    module: &Module<'_>,
    names: &SemanticCallNames,
    body: &FunctionBody,
    cfg: &CFGInfo,
    copy: CopySite,
) -> Vec<StructuralInputCopyLoadReport> {
    let mut loads = Vec::new();
    for (block, block_definition) in body.blocks.entries() {
        if !cfg.dominates(copy.block, block) {
            continue;
        }
        let start = if block == copy.block {
            copy.position + 1
        } else {
            0
        };
        for (position, instruction) in block_definition
            .insts
            .iter()
            .copied()
            .enumerate()
            .skip(start)
        {
            let value = body.resolve_alias(instruction);
            let ValueDef::Operator(Operator::I32Load { memory }, args, _) = &body.values[value]
            else {
                continue;
            };
            let [address] = &body.arg_pool[*args] else {
                continue;
            };
            if !same_origin(body, *address, copy.destination_base) {
                continue;
            }
            let barriers = barriers_before_load(
                module,
                names,
                body,
                cfg,
                copy,
                LoadSite {
                    block,
                    position,
                    memory: memory.memory.index(),
                },
            )
            .unwrap_or_else(|| MemoryBarrierSummary {
                unresolved: true,
                ..MemoryBarrierSummary::default()
            });
            loads.push(StructuralInputCopyLoadReport {
                value: value.index(),
                block: block.index(),
                instruction_index: position,
                memory: memory.memory.index(),
                byte_offset: memory.offset,
                align: memory.align,
                source_length_import_barriers: barriers
                    .source_length_imports
                    .iter()
                    .copied()
                    .collect(),
                other_import_call_barriers: barriers.other_imports.iter().copied().collect(),
                unresolved_intervening_memory_mutation: barriers.unresolved,
                copied_bytes_unmodified_since_set: barriers.is_empty(),
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
    names: &SemanticCallNames,
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
            let (slot_provider, provider_argument, memory_import) =
                provider_chain(body, constructor_input_slot, names);
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
                destination_base_guaranteed_trailing_zero_bits: guaranteed_trailing_zero_bits(
                    module,
                    body,
                    destination_base,
                ),
                fresh_destination_base_recipe: fresh_destination_base_recipe(
                    module,
                    body,
                    destination_base,
                    source_slot,
                    names,
                ),
                constructor_input_slot_value: constructor_input_slot.index(),
                constructor_input_slot_provider_function: slot_provider,
                constructor_input_provider_argument_function: provider_argument,
                constructor_input_memory_import_function: memory_import,
                destination_loads: destination_loads_dominated_by_set(
                    module,
                    names,
                    body,
                    &cfg,
                    CopySite {
                        block,
                        position,
                        destination_base,
                        source_slot,
                    },
                ),
            });
        }
    }
    reports.sort();
    reports.dedup();
    reports
}
