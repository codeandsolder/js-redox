use anyhow::{anyhow, Context, Result};
use serde::Serialize;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    panic::{catch_unwind, AssertUnwindSafe},
};
use waffle::{
    entity::EntityRef, Block, ExportKind, FrontendOptions, Func, FunctionBody, Module, Operator,
    OptOptions, Value, ValueDef,
};

mod helper_recognition;
mod ir;
mod scalar;
mod semantic_render;
mod transition;
mod value_flow;

#[cfg(test)]
use helper_recognition::normalize_import_name;
use helper_recognition::{build_semantic_call_names, memory_grow_base_slot, SemanticCallNames};
use ir::{i32_const, operator_family};
#[cfg(test)]
use scalar::{fold_closed_i32_expression, render_scalar_family};
use scalar::{render_instruction, render_value, substitute_arguments, try_eval_i32_expression};
use semantic_render::render_return_expressions;
pub use semantic_render::SemanticRuntimeBindingReport;
use transition::{
    eval_next_state, is_state_predicate, state_cmp_count, transitions_for, TransitionTrace,
};
use value_flow::unique_transparent_origin;

fn is_effectful_operator(op: &Operator) -> bool {
    let rendered = op.to_string();
    rendered.starts_with("call")
        || rendered.contains("store")
        || rendered.starts_with("globalset")
        || rendered.starts_with("memory")
        || rendered.starts_with("table")
        || rendered.starts_with("data.drop")
        || rendered.starts_with("elem.drop")
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct StateTransitionReport {
    pub successor: u32,
    pub arguments: Vec<String>,
    pub composed_arguments: Vec<String>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct NestedMachineEntryReport {
    pub machine_index: usize,
    pub arguments: Vec<String>,
    pub composed_arguments: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct StateCaseReport {
    pub state: u32,
    pub blocks: BTreeSet<usize>,
    pub entry_arguments: Vec<String>,
    pub successors: BTreeSet<u32>,
    pub transitions: Vec<StateTransitionReport>,
    pub nested_machines: BTreeSet<usize>,
    pub direct_nested_machines: BTreeSet<usize>,
    pub nested_entries: Vec<NestedMachineEntryReport>,
    pub operator_counts: BTreeMap<String, usize>,
    pub effects: Vec<String>,
    pub instruction_sample: Vec<String>,
}

fn summarize_state_case(
    body: &FunctionBody,
    dispatcher: Block,
    state: Value,
    param_index: usize,
    current: u32,
    trace: &TransitionTrace,
    excluded_blocks: &BTreeSet<Block>,
) -> StateCaseReport {
    const MAX_INSTRUCTIONS: usize = 96;
    const MAX_EFFECTS: usize = 64;

    let mut operator_counts = BTreeMap::new();
    let mut effects = Vec::new();
    let mut instruction_sample = Vec::new();

    for block in &trace.blocks {
        if excluded_blocks.contains(block) {
            continue;
        }
        for inst in &body.blocks[*block].insts {
            let resolved = body.resolve_alias(*inst);
            let ValueDef::Operator(op, _, _) = &body.values[resolved] else {
                continue;
            };
            if matches!(op, Operator::I32Const { .. })
                || is_state_predicate(body, state, resolved)
                || eval_next_state(body, state, resolved, current).is_some()
            {
                continue;
            }
            *operator_counts.entry(operator_family(op)).or_insert(0) += 1;
            if let Some(rendered) = render_instruction(body, dispatcher, state, resolved) {
                if is_effectful_operator(op) && effects.len() < MAX_EFFECTS {
                    effects.push(rendered.clone());
                }
                if instruction_sample.len() < MAX_INSTRUCTIONS {
                    instruction_sample.push(rendered);
                }
            }
        }
    }

    let mut transitions = Vec::new();
    for edge in &trace.transitions {
        let arguments = edge
            .args
            .iter()
            .enumerate()
            .map(|(index, value)| {
                if index == param_index {
                    format!("0x{:08x}", edge.successor)
                } else {
                    render_value(body, dispatcher, state, *value, 20)
                }
            })
            .collect::<Vec<_>>();
        let report = StateTransitionReport {
            successor: edge.successor,
            arguments,
            composed_arguments: Vec::new(),
        };
        if !transitions.contains(&report) {
            transitions.push(report);
        }
    }

    StateCaseReport {
        state: current,
        blocks: trace
            .blocks
            .difference(excluded_blocks)
            .map(|block| block.index())
            .collect(),
        entry_arguments: Vec::new(),
        successors: trace.next.clone(),
        transitions,
        nested_machines: BTreeSet::new(),
        direct_nested_machines: BTreeSet::new(),
        nested_entries: Vec::new(),
        operator_counts,
        effects,
        instruction_sample,
    }
}

fn linearize_state_graph(
    initial: &BTreeSet<u32>,
    graph: &BTreeMap<u32, BTreeSet<u32>>,
) -> Option<Vec<u32>> {
    let mut current = *initial.iter().next()?;
    if initial.len() != 1 {
        return None;
    }

    let mut order = Vec::new();
    let mut seen = BTreeSet::new();
    loop {
        if !seen.insert(current) {
            return None;
        }
        order.push(current);
        let successors = graph.get(&current)?;
        match successors.len() {
            0 => break,
            1 => {
                let &next = successors.iter().next()?;
                current = next;
            }
            _ => return None,
        }
    }

    (seen.len() == graph.len()).then_some(order)
}

#[derive(Clone, Copy)]
struct MachineMeta {
    dispatcher: Block,
    state: Value,
    param_index: usize,
}

fn target_argument_vectors(
    body: &FunctionBody,
    source_blocks: &BTreeSet<Block>,
    target_block: Block,
    target_state_param_index: usize,
    target_initial: &BTreeSet<u32>,
    dispatcher: Block,
    state: Value,
) -> Vec<Vec<String>> {
    let mut result = Vec::new();
    for block in source_blocks {
        body.blocks[*block].terminator.visit_targets(|target| {
            if target.block != target_block {
                return;
            }
            let Some(target_state) = target.args.get(target_state_param_index) else {
                return;
            };
            let Some(target_state) = i32_const(body, *target_state) else {
                return;
            };
            if !target_initial.contains(&target_state) {
                return;
            }
            let arguments = target
                .args
                .iter()
                .map(|value| render_value(body, dispatcher, state, *value, 20))
                .collect::<Vec<_>>();
            if !result.contains(&arguments) {
                result.push(arguments);
            }
        });
    }
    result
}

fn annotate_initial_entries(
    body: &FunctionBody,
    machines: &mut [StateMachineReport],
    metadata: &[MachineMeta],
) {
    let all_blocks = body
        .blocks
        .entries()
        .map(|(block, _)| block)
        .collect::<BTreeSet<_>>();
    let entries = machines
        .iter()
        .zip(metadata)
        .map(|(machine, meta)| {
            target_argument_vectors(
                body,
                &all_blocks,
                meta.dispatcher,
                meta.param_index,
                &machine.initial,
                meta.dispatcher,
                meta.state,
            )
        })
        .collect::<Vec<_>>();
    for (machine, initial_entries) in machines.iter_mut().zip(entries) {
        machine.initial_entries = initial_entries;
    }
}

fn initial_environment(machine: &StateMachineReport) -> Vec<String> {
    if let [entry] = machine.initial_entries.as_slice() {
        if entry.len() == machine.parameter_count {
            return entry.clone();
        }
    }
    let mut environment = (0..machine.parameter_count)
        .map(|index| format!("$p{index}"))
        .collect::<Vec<_>>();
    if machine.initial.len() == 1 {
        if let Some(value) = machine.initial.iter().next() {
            if let Some(state) = environment.get_mut(machine.state_param_index) {
                *state = format!("0x{value:08x}");
            }
        }
    }
    environment
}

fn annotate_composed_machine_flows(machines: &mut [StateMachineReport]) {
    for machine in machines {
        if machine.linearized.is_none() {
            continue;
        }
        let mut environment = initial_environment(machine);
        for case in &mut machine.cases {
            case.entry_arguments = environment.clone();
            for transition in &mut case.transitions {
                transition.composed_arguments =
                    substitute_arguments(&transition.arguments, &environment);
            }
            for entry in &mut case.nested_entries {
                entry.composed_arguments = substitute_arguments(&entry.arguments, &environment);
            }
            match case.transitions.as_slice() {
                [transition] => environment = transition.composed_arguments.clone(),
                [] => {}
                _ => break,
            }
        }
    }
}

#[derive(Debug, Serialize)]
pub struct StateMachinePipelineStageReport {
    pub machine_index: usize,
    pub state_count: usize,
    pub entry_arguments: Vec<String>,
    pub exit_arguments: Vec<String>,
    pub next_machine: Option<usize>,
}

#[derive(Debug, Serialize)]
pub struct StateMachinePipelineReport {
    pub root_machine: usize,
    pub stages: Vec<StateMachinePipelineStageReport>,
}

fn unique_direct_entry(machine: &StateMachineReport) -> Option<&NestedMachineEntryReport> {
    let mut entries = machine
        .cases
        .iter()
        .flat_map(|case| case.nested_entries.iter());
    let first = entries.next()?;
    entries.next().is_none().then_some(first)
}

pub fn compose_machine_pipelines(
    machines: &[StateMachineReport],
) -> Vec<StateMachinePipelineReport> {
    let mut pipelines = Vec::new();
    for root in root_machine_indices(machines) {
        let mut current = root;
        let mut environment = initial_environment(&machines[root]);
        let mut seen = BTreeSet::new();
        let mut stages = Vec::new();

        loop {
            if !seen.insert(current) {
                break;
            }
            let machine = &machines[current];
            let terminal_local = machine
                .cases
                .last()
                .map(|case| case.entry_arguments.as_slice())
                .unwrap_or_default();
            let terminal_absolute = substitute_arguments(terminal_local, &environment);

            let (next_machine, next_environment, exit_arguments) =
                if let Some(entry) = unique_direct_entry(machine) {
                    let absolute = substitute_arguments(&entry.composed_arguments, &environment);
                    if absolute.len() == machines[entry.machine_index].parameter_count {
                        (Some(entry.machine_index), Some(absolute.clone()), absolute)
                    } else {
                        (None, None, terminal_absolute)
                    }
                } else {
                    (None, None, terminal_absolute)
                };

            stages.push(StateMachinePipelineStageReport {
                machine_index: current,
                state_count: machine.cases.len(),
                entry_arguments: environment.clone(),
                exit_arguments,
                next_machine,
            });

            let (Some(next), Some(next_environment)) = (next_machine, next_environment) else {
                break;
            };
            current = next;
            environment = next_environment;
        }

        pipelines.push(StateMachinePipelineReport {
            root_machine: root,
            stages,
        });
    }
    pipelines
}

fn terminal_environment(machine: &StateMachineReport) -> Vec<String> {
    machine
        .cases
        .last()
        .map(|case| case.entry_arguments.clone())
        .unwrap_or_else(|| initial_environment(machine))
}

#[derive(Debug, Serialize)]
pub struct SemanticBindingReport {
    pub machine_index: usize,
    pub parameter_index: usize,
    pub state_parameter: bool,
    pub name: String,
    pub expression: String,
}

fn terminal_bindings(
    body: &FunctionBody,
    machines: &[StateMachineReport],
    metadata: &[MachineMeta],
) -> (BTreeMap<Value, String>, Vec<SemanticBindingReport>) {
    let mut bindings = BTreeMap::new();
    let mut reports = Vec::new();
    for (machine, meta) in machines.iter().zip(metadata) {
        let environment = terminal_environment(machine);
        for (parameter_index, ((_, parameter), expression)) in body.blocks[meta.dispatcher]
            .params
            .iter()
            .zip(environment)
            .enumerate()
        {
            let name = format!("$m{}_p{parameter_index}", machine.machine_index);
            let state_parameter = parameter_index == machine.state_param_index;
            let rendered_binding =
                if !state_parameter && try_eval_i32_expression(&expression).is_some() {
                    expression.clone()
                } else {
                    name.clone()
                };
            bindings.insert(*parameter, rendered_binding);
            reports.push(SemanticBindingReport {
                machine_index: machine.machine_index,
                parameter_index,
                state_parameter,
                name,
                expression,
            });
        }
    }
    (bindings, reports)
}

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

fn opaque_host_effect_memory_reads(
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

fn machine_contains(machines: &[StateMachineReport], outer: usize, inner: usize) -> bool {
    let dispatcher = machines[inner].dispatcher_block;
    machines[outer]
        .cases
        .iter()
        .any(|case| case.blocks.contains(&dispatcher))
}

fn annotate_nested_machines(
    body: &FunctionBody,
    machines: &mut [StateMachineReport],
    metadata: &[MachineMeta],
) {
    let contains = (0..machines.len())
        .map(|outer| {
            (0..machines.len())
                .map(|inner| outer != inner && machine_contains(machines, outer, inner))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let raw_regions = machines
        .iter()
        .map(|machine| {
            machine
                .cases
                .iter()
                .flat_map(|case| case.blocks.iter().copied())
                .map(Block::new)
                .collect::<BTreeSet<_>>()
        })
        .collect::<Vec<_>>();
    let dispatcher_blocks = machines
        .iter()
        .map(|machine| Block::new(machine.dispatcher_block))
        .collect::<Vec<_>>();

    for machine_index in 0..machines.len() {
        let meta = metadata[machine_index];
        let order = machines[machine_index]
            .linearized
            .clone()
            .unwrap_or_else(|| machines[machine_index].graph.keys().copied().collect());

        let mut cases = Vec::with_capacity(order.len());
        for current in order {
            let trace =
                transitions_for(body, meta.dispatcher, meta.state, meta.param_index, current);
            let nested = (0..machines.len())
                .filter(|&inner| {
                    inner != machine_index
                        && trace
                            .blocks
                            .iter()
                            .any(|block| block.index() == machines[inner].dispatcher_block)
                })
                .collect::<BTreeSet<_>>();
            let direct_nested = nested
                .iter()
                .copied()
                .filter(|&inner| {
                    !nested
                        .iter()
                        .copied()
                        .any(|other| other != inner && contains[other][inner])
                })
                .collect::<BTreeSet<_>>();
            let excluded = direct_nested
                .iter()
                .flat_map(|&inner| raw_regions[inner].iter().copied())
                .collect::<BTreeSet<_>>();
            let mut nested_entries = Vec::new();
            for &inner in &direct_nested {
                for arguments in target_argument_vectors(
                    body,
                    &trace.blocks,
                    dispatcher_blocks[inner],
                    machines[inner].state_param_index,
                    &machines[inner].initial,
                    meta.dispatcher,
                    meta.state,
                ) {
                    let entry = NestedMachineEntryReport {
                        machine_index: inner,
                        arguments,
                        composed_arguments: Vec::new(),
                    };
                    if !nested_entries.contains(&entry) {
                        nested_entries.push(entry);
                    }
                }
            }

            let mut case = summarize_state_case(
                body,
                meta.dispatcher,
                meta.state,
                meta.param_index,
                current,
                &trace,
                &excluded,
            );
            case.nested_machines = nested;
            case.direct_nested_machines = direct_nested;
            case.nested_entries = nested_entries;
            cases.push(case);
        }
        machines[machine_index].cases = cases;
    }
}

pub fn root_machine_indices(machines: &[StateMachineReport]) -> Vec<usize> {
    (0..machines.len())
        .filter(|&candidate| {
            !(0..machines.len()).any(|outer| {
                outer != candidate
                    && machines[outer]
                        .cases
                        .iter()
                        .any(|case| case.direct_nested_machines.contains(&candidate))
            })
        })
        .collect()
}

#[derive(Debug, Serialize)]
pub struct StateMachineReport {
    pub machine_index: usize,
    pub state_value: usize,
    pub dispatcher_block: usize,
    pub parameter_count: usize,
    pub state_param_index: usize,
    pub initial_entries: Vec<Vec<String>>,
    pub comparisons: usize,
    pub initial: BTreeSet<u32>,
    pub graph: BTreeMap<u32, BTreeSet<u32>>,
    pub linearized: Option<Vec<u32>>,
    pub cases: Vec<StateCaseReport>,
    pub unresolved_backedges: usize,
    pub data_forks: usize,
}

#[derive(Debug, Serialize)]
pub struct ExportSemanticAnalysis {
    pub state_machine_roots: Vec<usize>,
    pub state_machine_pipelines: Vec<StateMachinePipelineReport>,
    pub state_machines: Vec<StateMachineReport>,
    pub terminal_bindings: Vec<SemanticBindingReport>,
    pub runtime_bindings: Vec<SemanticRuntimeBindingReport>,
    pub opaque_host_effect_memory_reads: Vec<OpaqueHostEffectMemoryReadReport>,
    pub return_expressions: Vec<String>,
}

pub fn analyze_export_semantics(bytes: &[u8], export_name: &str) -> Result<ExportSemanticAnalysis> {
    match catch_unwind(AssertUnwindSafe(|| analyze_inner(bytes, export_name))) {
        Ok(result) => result,
        Err(payload) => {
            let detail = payload
                .downcast_ref::<&str>()
                .map(|value| (*value).to_owned())
                .or_else(|| payload.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "non-string panic payload".to_owned());
            Err(anyhow!("WAFFLE analysis panicked: {detail}"))
        }
    }
}

fn analyze_inner(bytes: &[u8], export_name: &str) -> Result<ExportSemanticAnalysis> {
    let mut module = Module::from_wasm_bytes(bytes, &FrontendOptions::default())?;
    let func = module
        .exports
        .iter()
        .find_map(|e| match e.kind {
            ExportKind::Func(f) if e.name == export_name => Some(f),
            _ => None,
        })
        .context("export")?;
    module.expand_func(func)?;
    module.funcs[func]
        .body_mut()
        .context("body")?
        .optimize(&OptOptions::default());
    let call_names = build_semantic_call_names(&mut module, func);
    let body = module.funcs[func].body().context("body")?;

    let mut candidates = Vec::new();
    for (block, def) in body.blocks.entries() {
        for (param_index, (_, param)) in def.params.iter().enumerate() {
            let n = state_cmp_count(body, *param);
            if n >= 5 {
                candidates.push((n, block, param_index, *param));
            }
        }
    }
    candidates.sort_by_key(|(n, _, _, _)| std::cmp::Reverse(*n));

    let mut machines = Vec::new();
    let mut metadata = Vec::new();
    for (cmp_count, dispatcher, param_index, state) in candidates {
        let mut initial = BTreeSet::new();
        for (_, pred) in body.blocks.entries() {
            pred.terminator.visit_targets(|target| {
                if target.block == dispatcher {
                    if let Some(arg) = target.args.get(param_index) {
                        if let Some(c) = i32_const(body, *arg) {
                            initial.insert(c);
                        }
                    }
                }
            });
        }
        if initial.is_empty() {
            continue;
        }
        let mut states = initial.iter().copied().collect::<VecDeque<_>>();
        let mut seen = BTreeSet::new();
        let mut graph: BTreeMap<u32, BTreeSet<u32>> = BTreeMap::new();
        let mut unresolved = 0usize;
        let mut forks = 0usize;
        while let Some(current) = states.pop_front() {
            if !seen.insert(current) || seen.len() > 256 {
                continue;
            }
            let trace = transitions_for(body, dispatcher, state, param_index, current);
            unresolved = unresolved.saturating_add(trace.unresolved_backedges);
            forks = forks.saturating_add(trace.data_forks);
            for n in &trace.next {
                if !seen.contains(n) {
                    states.push_back(*n);
                }
            }
            graph.insert(current, trace.next);
        }

        let incoming = graph
            .values()
            .flat_map(|successors| successors.iter().copied())
            .collect::<BTreeSet<_>>();
        let graph_roots = graph
            .keys()
            .copied()
            .filter(|state| !incoming.contains(state))
            .collect::<BTreeSet<_>>();
        if !graph_roots.is_empty() {
            initial = graph_roots;
        }

        let linearized = linearize_state_graph(&initial, &graph);
        let order = linearized
            .clone()
            .unwrap_or_else(|| graph.keys().copied().collect());
        let cases = order
            .into_iter()
            .map(|current| {
                let trace = transitions_for(body, dispatcher, state, param_index, current);
                summarize_state_case(
                    body,
                    dispatcher,
                    state,
                    param_index,
                    current,
                    &trace,
                    &BTreeSet::new(),
                )
            })
            .collect();

        let machine_index = machines.len();
        machines.push(StateMachineReport {
            machine_index,
            state_value: state.index(),
            dispatcher_block: dispatcher.index(),
            parameter_count: body.blocks[dispatcher].params.len(),
            state_param_index: param_index,
            initial_entries: Vec::new(),
            comparisons: cmp_count,
            initial,
            graph,
            linearized,
            cases,
            unresolved_backedges: unresolved,
            data_forks: forks,
        });
        metadata.push(MachineMeta {
            dispatcher,
            state,
            param_index,
        });
    }
    annotate_initial_entries(body, &mut machines, &metadata);
    annotate_nested_machines(body, &mut machines, &metadata);
    annotate_composed_machine_flows(&mut machines);
    let state_machine_roots = root_machine_indices(&machines);
    let state_machine_pipelines = compose_machine_pipelines(&machines);
    let (bindings, terminal_bindings) = terminal_bindings(body, &machines, &metadata);
    let (return_expressions, runtime_bindings, runtime_names) =
        render_return_expressions(body, &bindings, &call_names);
    let opaque_host_effect_memory_reads =
        opaque_host_effect_memory_reads(body, &call_names, &runtime_names);
    Ok(ExportSemanticAnalysis {
        state_machine_roots,
        state_machine_pipelines,
        state_machines: machines,
        terminal_bindings,
        runtime_bindings,
        opaque_host_effect_memory_reads,
        return_expressions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recovers_xor_encoded_state_chain() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (result i32)
                    (local $state i32)
                    i32.const 10
                    local.set $state
                    loop $dispatch
                        local.get $state i32.const 10 i32.eq
                        if
                            local.get $state i32.const 30 i32.xor local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 20 i32.eq
                        if
                            local.get $state i32.const 10 i32.xor local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 30 i32.eq
                        if
                            local.get $state i32.const 54 i32.xor local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 40 i32.eq
                        if
                            local.get $state i32.const 26 i32.xor local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 50 i32.eq
                        if i32.const 7 return end
                        unreachable
                    end
                    unreachable))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        let machines = &analysis.state_machines;
        assert_eq!(machines.len(), 1);
        let machine = &machines[0];
        assert_eq!(machine.initial, BTreeSet::from([10]));
        assert_eq!(machine.graph.len(), 5);
        assert_eq!(machine.unresolved_backedges, 0);
        assert_eq!(machine.graph[&10], BTreeSet::from([20]));
        assert_eq!(machine.graph[&20], BTreeSet::from([30]));
        assert_eq!(machine.graph[&30], BTreeSet::from([40]));
        assert_eq!(machine.graph[&40], BTreeSet::from([50]));
        assert!(machine.graph[&50].is_empty());
        assert_eq!(machine.linearized, Some(vec![10, 20, 30, 40, 50]));
        assert_eq!(machine.cases.len(), 5);
        assert_eq!(machine.cases[0].state, 10);
        assert_eq!(machine.cases[0].successors, BTreeSet::from([20]));
        assert_eq!(machine.cases[0].transitions.len(), 1);
        assert_eq!(machine.cases[0].transitions[0].successor, 20);
        assert!(!machine.cases[0].transitions[0]
            .composed_arguments
            .is_empty());
        assert!(machine.cases[0].nested_machines.is_empty());
        assert!(machine.cases[0].direct_nested_machines.is_empty());
        assert_eq!(root_machine_indices(machines), vec![0]);
        Ok(())
    }

    #[test]
    fn folds_closed_i32_expression_language() {
        assert_eq!(
            try_eval_i32_expression(
                "wrapping_add(reverse_bits32(0x00000001), rotl(0x00000001, 0x00000008))"
            ),
            Some(0x8000_0100)
        );
        assert_eq!(
            fold_closed_i32_expression("((0x000000f0 >> 0x00000004) | 0x00000010)".to_owned()),
            "0x0000001f"
        );
        assert_eq!(try_eval_i32_expression("$p1"), None);
        assert_eq!(
            render_scalar_family("i32mul", &["$x".into(), "0x00000000".into()]),
            Some("0x00000000".into())
        );
        assert_eq!(
            render_scalar_family("i32or", &["$x".into(), "0x00000000".into()]),
            Some("$x".into())
        );
        assert_eq!(
            render_scalar_family("i32add", &["0x00000002".into(), "0x00000003".into()]),
            Some("0x00000005".into())
        );
    }

    #[test]
    fn folds_carried_value_across_linear_state_chain() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (result i32)
                    (local $state i32)
                    (local $value i32)
                    i32.const 10
                    local.set $state
                    i32.const 1
                    local.set $value
                    loop $dispatch
                        local.get $state i32.const 10 i32.eq
                        if
                            local.get $value i32.const 3 i32.add local.set $value
                            i32.const 20 local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 20 i32.eq
                        if
                            local.get $value i32.const 1 i32.rotl local.set $value
                            i32.const 30 local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 30 i32.eq
                        if
                            local.get $value i32.const 5 i32.xor local.set $value
                            i32.const 40 local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 40 i32.eq
                        if
                            local.get $value i32.const 7 i32.mul local.set $value
                            i32.const 50 local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 50 i32.eq
                        if local.get $value return end
                        unreachable
                    end
                    unreachable))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.state_machines.len(), 1);
        assert_eq!(analysis.state_machine_pipelines.len(), 1);
        assert!(analysis
            .terminal_bindings
            .iter()
            .filter(|binding| !binding.state_parameter)
            .any(|binding| binding.expression == "0x0000005b"));
        Ok(())
    }

    #[test]
    fn renders_canonical_i32_bit_reverse() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "reverse") (param $input i32) (result i32)
                    (local $value i32)
                    local.get $input
                    i32.const 1
                    i32.shr_u
                    i32.const 0x55555555
                    i32.and
                    local.get $input
                    i32.const 0x55555555
                    i32.and
                    i32.const 1
                    i32.shl
                    i32.or
                    local.set $value

                    local.get $value
                    i32.const 2
                    i32.shr_u
                    i32.const 0x33333333
                    i32.and
                    local.get $value
                    i32.const 0x33333333
                    i32.and
                    i32.const 2
                    i32.shl
                    i32.or
                    local.set $value

                    local.get $value
                    i32.const 4
                    i32.shr_u
                    i32.const 0x0f0f0f0f
                    i32.and
                    local.get $value
                    i32.const 0x0f0f0f0f
                    i32.and
                    i32.const 4
                    i32.shl
                    i32.or
                    local.set $value

                    local.get $value
                    i32.const 24
                    i32.shr_u
                    local.get $value
                    i32.const 8
                    i32.shr_u
                    i32.const 0x0000ff00
                    i32.and
                    i32.or
                    local.get $value
                    i32.const 8
                    i32.shl
                    i32.const 0x00ff0000
                    i32.and
                    i32.or
                    local.get $value
                    i32.const 24
                    i32.shl
                    i32.or))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "reverse")?;
        assert_eq!(analysis.return_expressions, ["reverse_bits32($arg0)"]);
        assert!(analysis.state_machines.is_empty());
        Ok(())
    }

    #[test]
    fn recovers_nested_linear_state_machines() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (result i32)
                    (local $outer i32)
                    (local $inner i32)
                    i32.const 10
                    local.set $outer
                    block $after_outer
                        loop $outer_dispatch
                            local.get $outer i32.const 10 i32.eq
                            if i32.const 20 local.set $outer br $outer_dispatch end
                            local.get $outer i32.const 20 i32.eq
                            if i32.const 30 local.set $outer br $outer_dispatch end
                            local.get $outer i32.const 30 i32.eq
                            if i32.const 40 local.set $outer br $outer_dispatch end
                            local.get $outer i32.const 40 i32.eq
                            if i32.const 50 local.set $outer br $outer_dispatch end
                            local.get $outer i32.const 50 i32.eq
                            if br $after_outer end
                            unreachable
                        end
                    end
                    i32.const 100
                    local.set $inner
                    loop $inner_dispatch
                        local.get $inner i32.const 100 i32.eq
                        if i32.const 110 local.set $inner br $inner_dispatch end
                        local.get $inner i32.const 110 i32.eq
                        if i32.const 120 local.set $inner br $inner_dispatch end
                        local.get $inner i32.const 120 i32.eq
                        if i32.const 130 local.set $inner br $inner_dispatch end
                        local.get $inner i32.const 130 i32.eq
                        if i32.const 140 local.set $inner br $inner_dispatch end
                        local.get $inner i32.const 140 i32.eq
                        if i32.const 7 return end
                        unreachable
                    end
                    unreachable))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        let machines = &analysis.state_machines;
        assert_eq!(machines.len(), 2);
        let roots = &analysis.state_machine_roots;
        assert_eq!(roots.len(), 1);
        let root = roots[0];
        let children = machines[root]
            .cases
            .iter()
            .flat_map(|case| case.direct_nested_machines.iter().copied())
            .collect::<BTreeSet<_>>();
        assert_eq!(children.len(), 1);
        let child = *children.iter().next().context("nested child")?;
        assert!(machines[child]
            .cases
            .iter()
            .all(|case| case.direct_nested_machines.is_empty()));
        assert!(machines[root].graph.len() >= 5);
        assert!(machines[child].graph.len() >= 5);
        let pipelines = compose_machine_pipelines(machines);
        assert_eq!(pipelines.len(), 1);
        assert_eq!(pipelines[0].stages.len(), 2);
        assert_eq!(pipelines[0].stages[0].next_machine, Some(child));
        Ok(())
    }

    #[test]
    fn names_proven_wasm_bindgen_length_wrapper() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbg_length_6ca527665d89694d"
                    (func $length (param externref) (result i32)))
                (table 1 externref)
                (func $length_slot (param $slot i32) (result i32)
                    local.get $slot
                    table.get 0
                    call $length)
                (func (export "run") (result i32)
                    i32.const 0
                    call $length_slot))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.return_expressions, ["$runtime0"]);
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(analysis.runtime_bindings[0].name, "$runtime0");
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.externref_length(0x00000000)"
        );
        assert_eq!(
            normalize_import_name("wbg", "__wbg_length_6ca527665d89694d"),
            "wbg.length"
        );
        Ok(())
    }

    #[test]
    fn does_not_name_transformed_length_helper_as_plain_length() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbg_length_6ca527665d89694d"
                    (func $length (param externref) (result i32)))
                (table 1 externref)
                (func $length_plus_one (param $slot i32) (result i32)
                    local.get $slot
                    table.get 0
                    call $length
                    i32.const 1
                    i32.add)
                (func (export "run") (result i32)
                    i32.const 0
                    call $length_plus_one))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.return_expressions.len(), 1);
        assert!(analysis
            .runtime_bindings
            .iter()
            .all(|binding| !binding.expression.contains("wbindgen.externref_length")));
        Ok(())
    }

    #[test]
    fn names_proven_wasm_bindgen_memory_slot_wrapper() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "host" "alloc" (func $alloc (result i32)))
                (table 2 externref)
                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $alloc
                    local.tee $slot
                    call $memory
                    table.set 0
                    local.get $slot)
                (func (export "run") (result externref)
                    call $memory_slot
                    table.get 0))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(
            analysis.return_expressions,
            ["table_get<table0>($runtime0)"]
        );
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.memory_slot()"
        );
        Ok(())
    }

    #[test]
    fn names_proven_wasm_bindgen_get_u32_bridge() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbg_getUint32_9c3cc8fde7919ed4"
                    (func $get (param externref i32) (result i32)))
                (func $bridge (param $offset i32) (result i32)
                    ref.null extern
                    local.get $offset
                    call $get)
                (func (export "run") (result i32)
                    i32.const 7
                    call $bridge))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.return_expressions, ["$runtime0"]);
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.getUint32_bridge(0x00000007)"
        );
        Ok(())
    }

    #[test]
    fn runtime_dag_reuses_one_ssa_call_value() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "host" "read" (func $read (param i32) (result i32)))
                (func (export "run") (result i32)
                    (local $value i32)
                    i32.const 3
                    call $read
                    local.set $value
                    local.get $value
                    local.get $value
                    i32.add))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "host.read(0x00000003)"
        );
        assert_eq!(
            analysis.return_expressions,
            ["wrapping_add($runtime0, $runtime0)"]
        );
        Ok(())
    }

    #[test]
    fn follows_surviving_block_params_after_redundant_param_removal() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (param $cond i32) (result i32)
                    (local $a i32)
                    (local $b i32)
                    (local $c i32)
                    (local $d i32)
                    i32.const 10
                    local.set $a
                    i32.const 20
                    local.set $b
                    i32.const 30
                    local.set $c
                    i32.const 40
                    local.set $d

                    local.get $cond
                    if
                        i32.const 21
                        local.set $b
                        i32.const 41
                        local.set $d
                    end

                    local.get $a
                    local.get $b
                    i32.add
                    local.get $c
                    i32.add
                    local.get $d
                    i32.add))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        let expression = analysis
            .return_expressions
            .first()
            .context("return expression")?;
        assert!(expression.contains("phi(0x00000014, 0x00000015)"));
        assert!(expression.contains("phi(0x00000028, 0x00000029)"));
        Ok(())
    }

    #[test]
    fn names_structurally_proven_heap_allocator() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (memory 1)
                (func $alloc (param $bytes i32) (result i32)
                    (local $ptr i32)
                    local.get $bytes
                    i32.const 65535
                    i32.add
                    i32.const 16
                    i32.shr_u
                    memory.grow
                    local.tee $ptr
                    i32.const -1
                    i32.eq
                    if
                        i32.const 0
                        return
                    end
                    local.get $ptr
                    i32.const 16
                    i32.shl
                    local.set $ptr

                    local.get $ptr
                    i32.load
                    drop
                    local.get $ptr
                    i32.load offset=4
                    drop
                    local.get $ptr
                    i32.load offset=8
                    drop
                    local.get $ptr
                    i32.load offset=12
                    drop

                    local.get $ptr
                    i32.const 1
                    i32.store
                    local.get $ptr
                    i32.const 2
                    i32.store offset=4
                    local.get $ptr
                    i32.const 3
                    i32.store offset=8
                    local.get $ptr
                    i32.const 4
                    i32.store offset=12
                    local.get $ptr
                    i32.const 5
                    i32.store offset=16
                    local.get $ptr
                    i32.const 6
                    i32.store offset=20
                    local.get $ptr
                    i32.const 7
                    i32.store offset=24
                    local.get $ptr
                    i32.const 8
                    i32.store offset=28

                    local.get $ptr
                    i32.const 8
                    i32.add)
                (func (export "run") (param $bytes i32) (result i32)
                    local.get $bytes
                    call $alloc))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.return_expressions, ["$runtime0"]);
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wasm.heap_alloc($arg0)"
        );
        Ok(())
    }

    #[test]
    fn does_not_name_plain_memory_grow_as_heap_allocator() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (memory 1)
                (func $grow (param $pages i32) (result i32)
                    local.get $pages
                    memory.grow)
                (func (export "run") (param $pages i32) (result i32)
                    local.get $pages
                    call $grow))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.return_expressions, ["$runtime0"]);
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert!(!analysis.runtime_bindings[0]
            .expression
            .contains("wasm.heap_alloc"));
        Ok(())
    }

    #[test]
    fn renders_direct_conditional_phi_with_its_guard() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (param $cond i32) (result i32)
                    (local $value i32)
                    i32.const 10
                    local.set $value
                    local.get $cond
                    if
                        i32.const 20
                        local.set $value
                    else
                        i32.const 30
                        local.set $value
                    end
                    local.get $value))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        let expression = analysis
            .return_expressions
            .first()
            .context("return expression")?;
        assert_eq!(expression, "phi_if($arg0, 0x00000014, 0x0000001e)");
        Ok(())
    }
    #[test]
    fn names_captured_memory_grow_only_with_proven_memory_receiver() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "__wbg_grow_43d369088a370694"
                    (func $grow (param externref i32) (result i32)))
                (import "host" "alloc" (func $alloc (result i32)))
                (table 2 externref)
                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $alloc
                    local.tee $slot
                    call $memory
                    table.set 0
                    local.get $slot)
                (func (export "run") (result i32)
                    call $memory_slot
                    table.get 0
                    i32.const 1
                    call $grow))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.runtime_bindings.len(), 2);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.memory_slot()"
        );
        assert_eq!(
            analysis.runtime_bindings[1].expression,
            "wasm.memory_grow(0x00000001, externref_slot=$runtime0)"
        );
        Ok(())
    }
    fn host_effect_memory_fixture(host_effect_body: &str, run_body: &str) -> Result<Vec<u8>> {
        wat::parse_str(format!(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "__wbg_grow_43d369088a370694"
                    (func $grow (param externref i32) (result i32)))
                (import "wbg" "__wbg_buffer_609cc3eee51ed158"
                    (func $buffer (param externref) (result externref)))
                (import "wbg" "__wbg_byteLength_ea52ac3de882b483"
                    (func $byte_length (param externref) (result i32)))
                (import "wbg" "__wbg_new_7e079fa25e135eb1"
                    (func $view_new (param externref i32 i32) (result externref)))
                (import "wbg" "__wbg_getUint32_9c3cc8fde7919ed4"
                    (func $get_u32 (param externref i32) (result i32)))
                (import "host" "opaque_signal"
                    (func $opaque_signal (param externref i32 i32)))
                (import "host" "alloc" (func $alloc (result i32)))
                (table 16 externref)

                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $alloc
                    local.tee $slot
                    call $memory
                    table.set 0
                    local.get $slot)

                (func $buffer_slot (param $memory_slot i32) (result i32)
                    (local $buffer externref)
                    (local $slot i32)
                    local.get $memory_slot
                    table.get 0
                    call $buffer
                    local.set $buffer
                    call $alloc
                    local.tee $slot
                    local.get $buffer
                    table.set 0
                    local.get $slot)

                (func $memory_get (param $offset i32) (result i32)
                    (local $buffer_slot i32)
                    (local $length i32)
                    (local $view externref)
                    (local $view_slot i32)
                    call $memory_slot
                    call $buffer_slot
                    local.tee $buffer_slot
                    table.get 0
                    call $byte_length
                    local.set $length
                    local.get $buffer_slot
                    table.get 0
                    i32.const 0
                    local.get $length
                    call $view_new
                    local.set $view
                    call $alloc
                    local.tee $view_slot
                    local.get $view
                    table.set 0
                    local.get $view_slot
                    table.get 0
                    local.get $offset
                    call $get_u32)

                (func $host_effect (param $slot i32) (param $base i32) (param $offset i32)
                    {host_effect_body})

                (func (export "run") (result i32)
                    (local $slot i32)
                    (local $base i32)
                    call $memory_slot
                    local.tee $slot
                    table.get 0
                    i32.const 1
                    call $grow
                    i32.const 16
                    i32.shl
                    local.set $base
                    {run_body}))"#
        ))
        .map_err(Into::into)
    }

    const STRAIGHT_HOST_EFFECT: &str = r#"
        local.get $slot
        table.get 0
        local.get $base
        local.get $offset
        call $opaque_signal
    "#;

    #[test]
    fn reports_same_block_opaque_host_effect_before_memory_read() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            STRAIGHT_HOST_EFFECT,
            r#"
                local.get $slot
                local.get $base
                i32.const 3536
                call $host_effect
                local.get $base
                i32.const 3536
                i32.or
                call $memory_get
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.opaque_host_effect_memory_reads.len(), 1);
        let relation = &analysis.opaque_host_effect_memory_reads[0];
        assert_eq!(relation.offset, 3536);
        assert_eq!(relation.host_import, "host.opaque_signal");
        assert!(relation
            .runtime_binding
            .as_deref()
            .is_some_and(|name| name.starts_with("$runtime")));
        Ok(())
    }

    #[test]
    fn rejects_host_effect_memory_read_with_different_offset() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            STRAIGHT_HOST_EFFECT,
            r#"
                local.get $slot
                local.get $base
                i32.const 3536
                call $host_effect
                local.get $base
                i32.const 3540
                i32.or
                call $memory_get
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert!(analysis.opaque_host_effect_memory_reads.is_empty());
        Ok(())
    }

    #[test]
    fn rejects_host_effect_with_different_memory_slot() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            STRAIGHT_HOST_EFFECT,
            r#"
                i32.const 3
                local.get $base
                i32.const 3536
                call $host_effect
                local.get $base
                i32.const 3536
                i32.or
                call $memory_get
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert!(analysis.opaque_host_effect_memory_reads.is_empty());
        Ok(())
    }

    #[test]
    fn rejects_memory_read_before_host_effect() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            STRAIGHT_HOST_EFFECT,
            r#"
                local.get $base
                i32.const 3536
                i32.or
                call $memory_get
                drop
                local.get $slot
                local.get $base
                i32.const 3536
                call $host_effect
                i32.const 0
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert!(analysis.opaque_host_effect_memory_reads.is_empty());
        Ok(())
    }

    #[test]
    fn rejects_conditional_opaque_host_effect_wrapper() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            r#"
                local.get $offset
                if
                    local.get $slot
                    table.get 0
                    local.get $base
                    local.get $offset
                    call $opaque_signal
                end
            "#,
            r#"
                local.get $slot
                local.get $base
                i32.const 3536
                call $host_effect
                local.get $base
                i32.const 3536
                i32.or
                call $memory_get
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert!(analysis.opaque_host_effect_memory_reads.is_empty());
        Ok(())
    }

    #[test]
    fn names_only_proven_module_memory_get_u32_bridge_strongly() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "__wbg_buffer_609cc3eee51ed158"
                    (func $buffer (param externref) (result externref)))
                (import "wbg" "__wbg_byteLength_ea52ac3de882b483"
                    (func $byte_length (param externref) (result i32)))
                (import "wbg" "__wbg_new_7e079fa25e135eb1"
                    (func $view_new (param externref i32 i32) (result externref)))
                (import "wbg" "__wbg_getUint32_9c3cc8fde7919ed4"
                    (func $get_u32 (param externref i32) (result i32)))
                (import "host" "alloc" (func $alloc (result i32)))
                (table 16 externref)

                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $alloc
                    local.tee $slot
                    call $memory
                    table.set 0
                    local.get $slot)

                (func $buffer_slot (param $memory_slot i32) (result i32)
                    (local $buffer externref)
                    (local $slot i32)
                    local.get $memory_slot
                    table.get 0
                    call $buffer
                    local.set $buffer
                    call $alloc
                    local.tee $slot
                    local.get $buffer
                    table.set 0
                    local.get $slot)

                (func $memory_get (param $offset i32) (result i32)
                    (local $memory_slot i32)
                    (local $buffer_slot i32)
                    (local $length i32)
                    (local $view externref)
                    (local $view_slot i32)
                    call $memory_slot
                    local.tee $memory_slot
                    call $buffer_slot
                    local.tee $buffer_slot
                    table.get 0
                    call $byte_length
                    local.set $length
                    local.get $buffer_slot
                    table.get 0
                    i32.const 0
                    local.get $length
                    call $view_new
                    local.set $view
                    call $alloc
                    local.tee $view_slot
                    local.get $view
                    table.set 0
                    local.get $view_slot
                    table.get 0
                    local.get $offset
                    call $get_u32)

                (func (export "run") (result i32)
                    i32.const 7
                    call $memory_get))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.memory_get_u32(0x00000007)"
        );
        Ok(())
    }
}
