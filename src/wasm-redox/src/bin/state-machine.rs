use anyhow::{anyhow, Context, Result};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    env, fs,
    panic::{catch_unwind, AssertUnwindSafe},
};
use waffle::{
    entity::EntityRef, Block, BlockTarget, ExportKind, FrontendOptions, FunctionBody, Module,
    Operator, OptOptions, Terminator, Value, ValueDef,
};

fn i32_const(body: &FunctionBody, value: Value) -> Option<u32> {
    let value = body.resolve_alias(value);
    match body.values[value] {
        ValueDef::Operator(Operator::I32Const { value }, _, _) => Some(value),
        _ => None,
    }
}

fn state_cmp_count(body: &FunctionBody, state: Value) -> usize {
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

fn eval_next_state(body: &FunctionBody, state: Value, expr: Value, current: u32) -> Option<u32> {
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

fn transitions_for(
    body: &FunctionBody,
    dispatcher: Block,
    state: Value,
    param_index: usize,
    current: u32,
) -> (BTreeSet<u32>, usize, usize) {
    let mut queue = VecDeque::from([dispatcher]);
    let mut seen = BTreeSet::new();
    let mut next = BTreeSet::new();
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
                    if let Some(value) = target
                        .args
                        .get(param_index)
                        .and_then(|v| eval_next_state(body, state, *v, current))
                    {
                        next.insert(value);
                    } else {
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
                        if let Some(value) = target
                            .args
                            .get(param_index)
                            .and_then(|v| eval_next_state(body, state, *v, current))
                        {
                            next.insert(value);
                        } else {
                            unresolved_backedges += 1;
                        }
                    } else {
                        push_target(&mut queue, &seen, target);
                    }
                } else {
                    data_forks += 1;
                    for target in [if_true, if_false] {
                        if target.block == dispatcher {
                            if let Some(value) = target
                                .args
                                .get(param_index)
                                .and_then(|v| eval_next_state(body, state, *v, current))
                            {
                                next.insert(value);
                            } else {
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
                        if let Some(value) = target
                            .args
                            .get(param_index)
                            .and_then(|v| eval_next_state(body, state, *v, current))
                        {
                            next.insert(value);
                        } else {
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
    (next, unresolved_backedges, data_forks)
}

#[derive(Debug)]
struct Machine {
    state: Value,
    dispatcher: Block,
    comparisons: usize,
    initial: BTreeSet<u32>,
    graph: BTreeMap<u32, BTreeSet<u32>>,
    unresolved: usize,
    forks: usize,
}

fn analyze(bytes: &[u8], export_name: &str) -> Result<Vec<Machine>> {
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

fn analyze_inner(bytes: &[u8], export_name: &str) -> Result<Vec<Machine>> {
    let mut module = Module::from_wasm_bytes(bytes, &FrontendOptions::default())?;
    module.expand_all_funcs()?;
    module.per_func_body(|f| f.optimize(&OptOptions::default()));
    let func = module
        .exports
        .iter()
        .find_map(|e| match e.kind {
            ExportKind::Func(f) if e.name == export_name => Some(f),
            _ => None,
        })
        .context("export")?;
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
            let (next, u, f) = transitions_for(body, dispatcher, state, param_index, current);
            unresolved = unresolved.saturating_add(u);
            forks = forks.saturating_add(f);
            for n in &next {
                if !seen.contains(n) {
                    states.push_back(*n);
                }
            }
            graph.insert(current, next);
        }
        machines.push(Machine {
            state,
            dispatcher,
            comparisons: cmp_count,
            initial,
            graph,
            unresolved,
            forks,
        });
    }
    Ok(machines)
}

fn main() -> Result<()> {
    let path = env::args().nth(1).context("wasm")?;
    let export_name = env::args().nth(2).context("export")?;
    let bytes = fs::read(path)?;
    for machine in analyze(&bytes, &export_name)? {
        println!(
            "MACHINE state=v{} dispatcher={} comparisons={} initial={:?}",
            machine.state.index(),
            machine.dispatcher,
            machine.comparisons,
            machine.initial
        );
        println!(
            "  recovered_states={} unresolved_backedges={} data_forks={}",
            machine.graph.len(),
            machine.unresolved,
            machine.forks
        );
        for (from, to) in machine.graph.iter().take(64) {
            println!("  {from:10} -> {:?}", to);
        }
    }
    Ok(())
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
                        local.get $state
                        i32.const 10
                        i32.eq
                        if
                            local.get $state
                            i32.const 30
                            i32.xor
                            local.set $state
                            br $dispatch
                        end
                        local.get $state
                        i32.const 20
                        i32.eq
                        if
                            local.get $state
                            i32.const 10
                            i32.xor
                            local.set $state
                            br $dispatch
                        end
                        local.get $state
                        i32.const 30
                        i32.eq
                        if
                            local.get $state
                            i32.const 54
                            i32.xor
                            local.set $state
                            br $dispatch
                        end
                        local.get $state
                        i32.const 40
                        i32.eq
                        if
                            local.get $state
                            i32.const 26
                            i32.xor
                            local.set $state
                            br $dispatch
                        end
                        local.get $state
                        i32.const 50
                        i32.eq
                        if
                            i32.const 7
                            return
                        end
                        unreachable
                    end
                    unreachable)
            )"#,
        )?;
        let machines = analyze(&bytes, "run")?;
        assert_eq!(machines.len(), 1);
        let machine = &machines[0];
        assert_eq!(machine.initial, BTreeSet::from([10]));
        assert_eq!(machine.graph.len(), 5);
        assert_eq!(machine.unresolved, 0);
        assert_eq!(machine.graph[&10], BTreeSet::from([20]));
        assert_eq!(machine.graph[&20], BTreeSet::from([30]));
        assert_eq!(machine.graph[&30], BTreeSet::from([40]));
        assert_eq!(machine.graph[&40], BTreeSet::from([50]));
        assert!(machine.graph[&50].is_empty());
        Ok(())
    }
}
