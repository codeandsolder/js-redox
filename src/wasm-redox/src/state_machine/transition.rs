use super::ir::i32_const;
use std::collections::{BTreeSet, VecDeque};
use waffle::{Block, BlockTarget, FunctionBody, Operator, Terminator, Value, ValueDef};

pub(super) fn state_cmp_count(body: &FunctionBody, state: Value) -> usize {
    let state = body.resolve_alias(state);
    body.blocks
        .entries()
        .filter(|(_, block)| {
            let Terminator::CondBr { cond, .. } = &block.terminator else {
                return false;
            };
            eval_state_cond(body, state, *cond, 0).is_some()
        })
        .count()
}

fn eval_state_cond(
    body: &FunctionBody,
    state: Value,
    cond: Value,
    state_value: u32,
) -> Option<bool> {
    let cond = body.resolve_alias(cond);
    let ValueDef::Operator(op, args, _) = &body.values[cond] else {
        return None;
    };
    let args = &body.arg_pool[*args];
    if args.len() != 2 {
        return None;
    }
    let a = body.resolve_alias(args[0]);
    let b = body.resolve_alias(args[1]);
    let (lhs, rhs) = if a == state {
        (state_value, i32_const(body, b)?)
    } else if b == state {
        (i32_const(body, a)?, state_value)
    } else {
        return None;
    };
    Some(match op {
        Operator::I32Eq => lhs == rhs,
        Operator::I32Ne => lhs != rhs,
        Operator::I32LtU => lhs < rhs,
        Operator::I32LeU => lhs <= rhs,
        Operator::I32GtU => lhs > rhs,
        Operator::I32GeU => lhs >= rhs,
        Operator::I32LtS => (lhs.cast_signed()) < (rhs.cast_signed()),
        Operator::I32LeS => (lhs.cast_signed()) <= (rhs.cast_signed()),
        Operator::I32GtS => (lhs.cast_signed()) > (rhs.cast_signed()),
        Operator::I32GeS => (lhs.cast_signed()) >= (rhs.cast_signed()),
        _ => return None,
    })
}

pub(super) fn eval_next_state(
    body: &FunctionBody,
    state: Value,
    expr: Value,
    current: u32,
) -> Option<u32> {
    let expr = body.resolve_alias(expr);
    if expr == state {
        return Some(current);
    }
    if let Some(c) = i32_const(body, expr) {
        return Some(c);
    }
    let ValueDef::Operator(Operator::I32Xor, args, _) = &body.values[expr] else {
        return None;
    };
    let args = &body.arg_pool[*args];
    if args.len() != 2 {
        return None;
    }
    let a = body.resolve_alias(args[0]);
    let b = body.resolve_alias(args[1]);
    if a == state {
        Some(current ^ i32_const(body, b)?)
    } else if b == state {
        Some(i32_const(body, a)? ^ current)
    } else {
        None
    }
}

fn push_target(queue: &mut VecDeque<Block>, seen: &BTreeSet<Block>, target: &BlockTarget) {
    if !seen.contains(&target.block) {
        queue.push_back(target.block);
    }
}

#[derive(Debug)]
pub(super) struct TransitionEdge {
    pub(super) successor: u32,
    pub(super) args: Vec<Value>,
}

#[derive(Debug)]
pub(super) struct TransitionTrace {
    pub(super) next: BTreeSet<u32>,
    pub(super) transitions: Vec<TransitionEdge>,
    pub(super) unresolved_backedges: usize,
    pub(super) data_forks: usize,
    pub(super) blocks: BTreeSet<Block>,
}

fn record_backedge(
    body: &FunctionBody,
    state: Value,
    param_index: usize,
    current: u32,
    target: &BlockTarget,
    next: &mut BTreeSet<u32>,
    transitions: &mut Vec<TransitionEdge>,
) -> bool {
    let Some(successor) = target
        .args
        .get(param_index)
        .and_then(|value| eval_next_state(body, state, *value, current))
    else {
        return false;
    };
    next.insert(successor);
    transitions.push(TransitionEdge {
        successor,
        args: target.args.clone(),
    });
    true
}

pub(super) fn transitions_for(
    body: &FunctionBody,
    dispatcher: Block,
    state: Value,
    param_index: usize,
    current: u32,
) -> TransitionTrace {
    let mut queue = VecDeque::from([dispatcher]);
    let mut seen = BTreeSet::new();
    let mut next = BTreeSet::new();
    let mut transitions = Vec::new();
    let mut unresolved_backedges = 0;
    let mut data_forks = 0;
    while let Some(block) = queue.pop_front() {
        if !seen.insert(block) {
            continue;
        }
        let term = &body.blocks[block].terminator;
        match term {
            Terminator::Br { target } => {
                if target.block == dispatcher {
                    if !record_backedge(
                        body,
                        state,
                        param_index,
                        current,
                        target,
                        &mut next,
                        &mut transitions,
                    ) {
                        unresolved_backedges += 1;
                    }
                } else {
                    push_target(&mut queue, &seen, target);
                }
            }
            Terminator::CondBr {
                cond,
                if_true,
                if_false,
            } => {
                if let Some(take_true) = eval_state_cond(body, state, *cond, current) {
                    let target = if take_true { if_true } else { if_false };
                    if target.block == dispatcher {
                        if !record_backedge(
                            body,
                            state,
                            param_index,
                            current,
                            target,
                            &mut next,
                            &mut transitions,
                        ) {
                            unresolved_backedges += 1;
                        }
                    } else {
                        push_target(&mut queue, &seen, target);
                    }
                } else {
                    data_forks += 1;
                    for target in [if_true, if_false] {
                        if target.block == dispatcher {
                            if !record_backedge(
                                body,
                                state,
                                param_index,
                                current,
                                target,
                                &mut next,
                                &mut transitions,
                            ) {
                                unresolved_backedges += 1;
                            }
                        } else {
                            push_target(&mut queue, &seen, target);
                        }
                    }
                }
            }
            Terminator::Select {
                targets, default, ..
            } => {
                data_forks += 1;
                for target in targets.iter().chain(std::iter::once(default)) {
                    if target.block == dispatcher {
                        if !record_backedge(
                            body,
                            state,
                            param_index,
                            current,
                            target,
                            &mut next,
                            &mut transitions,
                        ) {
                            unresolved_backedges += 1;
                        }
                    } else {
                        push_target(&mut queue, &seen, target);
                    }
                }
            }
            Terminator::Return { .. } | Terminator::Unreachable | Terminator::None => {}
        }
    }
    TransitionTrace {
        next,
        transitions,
        unresolved_backedges,
        data_forks,
        blocks: seen,
    }
}

pub(super) fn is_state_predicate(body: &FunctionBody, state: Value, value: Value) -> bool {
    let value = body.resolve_alias(value);
    let ValueDef::Operator(op, args, _) = &body.values[value] else {
        return false;
    };
    if !matches!(
        op,
        Operator::I32Eq
            | Operator::I32Ne
            | Operator::I32LtU
            | Operator::I32LeU
            | Operator::I32GtU
            | Operator::I32GeU
            | Operator::I32LtS
            | Operator::I32LeS
            | Operator::I32GtS
            | Operator::I32GeS
    ) {
        return false;
    }
    let args = &body.arg_pool[*args];
    if args.len() != 2 {
        return false;
    }
    let a = body.resolve_alias(args[0]);
    let b = body.resolve_alias(args[1]);
    (a == body.resolve_alias(state) && i32_const(body, b).is_some())
        || (b == body.resolve_alias(state) && i32_const(body, a).is_some())
}
