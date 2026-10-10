use super::{
    reporting::{
        summarize_state_case, target_argument_vectors, MachineMeta, NestedMachineEntryReport,
        StateMachineReport,
    },
    transition::transitions_for,
};
use std::collections::BTreeSet;
use waffle::{entity::EntityRef, Block, FunctionBody};

fn machine_contains(machines: &[StateMachineReport], outer: usize, inner: usize) -> bool {
    let dispatcher = machines[inner].dispatcher_block;
    machines[outer]
        .cases
        .iter()
        .any(|case| case.blocks.contains(&dispatcher))
}

pub(super) fn annotate_nested_machines(
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
