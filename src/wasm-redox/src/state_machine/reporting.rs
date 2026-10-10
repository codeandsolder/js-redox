use super::{
    ir::{i32_const, operator_family},
    scalar::{render_instruction, render_value, substitute_arguments, try_eval_i32_expression},
    transition::{eval_next_state, is_state_predicate, TransitionTrace},
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use waffle::{entity::EntityRef, Block, FunctionBody, Operator, Value, ValueDef};

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

pub(super) fn summarize_state_case(
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

pub(super) fn linearize_state_graph(
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
pub(super) struct MachineMeta {
    pub(super) dispatcher: Block,
    pub(super) state: Value,
    pub(super) param_index: usize,
}

pub(super) fn target_argument_vectors(
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

pub(super) fn annotate_initial_entries(
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

pub(super) fn annotate_composed_machine_flows(machines: &mut [StateMachineReport]) {
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

pub(super) fn terminal_bindings(
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
