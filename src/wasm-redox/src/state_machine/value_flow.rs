use std::collections::{BTreeSet, VecDeque};
use waffle::{entity::EntityRef, Block, FunctionBody, Terminator, Value};

pub(super) fn incoming_block_param_edges(
    body: &FunctionBody,
    block: Block,
    parameter: Value,
) -> Vec<(Block, Value)> {
    let parameter = body.resolve_alias(parameter);
    let Some(index) = body.blocks[block]
        .params
        .iter()
        .position(|(_, candidate)| body.resolve_alias(*candidate) == parameter)
    else {
        return Vec::new();
    };
    let mut incoming = Vec::new();

    for (predecessor_block, predecessor) in body.blocks.entries() {
        predecessor.terminator.visit_targets(|target| {
            if target.block != block {
                return;
            }
            let Some(value) = target.args.get(index) else {
                return;
            };
            let value = body.resolve_alias(*value);
            if value != parameter {
                incoming.push((predecessor_block, value));
            }
        });
    }
    incoming.sort_unstable_by_key(|(block, value)| (block.index(), value.index()));
    incoming.dedup();
    incoming
}

pub(super) fn incoming_block_param_values(
    body: &FunctionBody,
    block: Block,
    parameter: Value,
) -> Vec<Value> {
    incoming_block_param_edges(body, block, parameter)
        .into_iter()
        .map(|(_, value)| value)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn reachable_blocks(body: &FunctionBody) -> BTreeSet<Block> {
    let mut reachable = BTreeSet::new();
    let mut queue = VecDeque::from([body.entry]);
    while let Some(block) = queue.pop_front() {
        if !reachable.insert(block) {
            continue;
        }
        body.blocks[block]
            .terminator
            .visit_targets(|target| queue.push_back(target.block));
    }
    reachable
}

fn reachable_predecessors(
    body: &FunctionBody,
    target_block: Block,
    reachable: &BTreeSet<Block>,
) -> BTreeSet<Block> {
    body.blocks
        .entries()
        .filter_map(|(block, definition)| {
            if !reachable.contains(&block) {
                return None;
            }
            let mut reaches_target = false;
            definition.terminator.visit_targets(|target| {
                reaches_target |= target.block == target_block;
            });
            reaches_target.then_some(block)
        })
        .collect()
}

pub(super) fn conditional_phi_inputs(
    body: &FunctionBody,
    incoming: &[(Block, Value)],
) -> Option<(Value, Value, Value)> {
    if incoming.len() != 2 {
        return None;
    }
    let reachable = reachable_blocks(body);
    let mut candidates = Vec::new();
    for (branch_block, block) in body.blocks.entries() {
        if !reachable.contains(&branch_block) {
            continue;
        }
        let Terminator::CondBr {
            cond,
            if_true,
            if_false,
        } = &block.terminator
        else {
            continue;
        };
        if if_true.block == if_false.block
            || reachable_predecessors(body, if_true.block, &reachable)
                != BTreeSet::from([branch_block])
            || reachable_predecessors(body, if_false.block, &reachable)
                != BTreeSet::from([branch_block])
        {
            continue;
        }
        let Some((_, true_value)) = incoming
            .iter()
            .find(|(predecessor, _)| *predecessor == if_true.block)
        else {
            continue;
        };
        let Some((_, false_value)) = incoming
            .iter()
            .find(|(predecessor, _)| *predecessor == if_false.block)
        else {
            continue;
        };
        candidates.push((
            body.resolve_alias(*cond),
            body.resolve_alias(*true_value),
            body.resolve_alias(*false_value),
        ));
    }
    candidates.sort_unstable_by_key(|(cond, if_true, if_false)| {
        (cond.index(), if_true.index(), if_false.index())
    });
    candidates.dedup();
    (candidates.len() == 1).then(|| candidates[0])
}
