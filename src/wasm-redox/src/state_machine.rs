use anyhow::{anyhow, Context, Result};
use serde::Serialize;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
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

#[derive(Debug)]
struct TransitionEdge {
    successor: u32,
    args: Vec<Value>,
}

#[derive(Debug)]
struct TransitionTrace {
    next: BTreeSet<u32>,
    transitions: Vec<TransitionEdge>,
    unresolved_backedges: usize,
    data_forks: usize,
    blocks: BTreeSet<Block>,
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

fn transitions_for(
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

fn is_state_predicate(body: &FunctionBody, state: Value, value: Value) -> bool {
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

fn is_inlineable_scalar(op: &Operator) -> bool {
    matches!(
        operator_family(op).as_str(),
        "i32add"
            | "i32sub"
            | "i32mul"
            | "i32and"
            | "i32or"
            | "i32xor"
            | "i32shl"
            | "i32shrs"
            | "i32shru"
            | "i32rotl"
            | "i32rotr"
            | "i32eq"
            | "i32ne"
            | "i32ltu"
            | "i32leu"
            | "i32gtu"
            | "i32geu"
            | "i32lts"
            | "i32les"
            | "i32gts"
            | "i32ges"
    )
}

fn render_value(
    body: &FunctionBody,
    dispatcher: Block,
    state: Value,
    value: Value,
    depth: usize,
) -> String {
    let value = body.resolve_alias(value);
    if value == body.resolve_alias(state) {
        return "$state".to_owned();
    }
    for (index, (_, param)) in body.blocks[dispatcher].params.iter().enumerate() {
        if value == body.resolve_alias(*param) {
            return format!("$p{index}");
        }
    }
    if let Some(value) = i32_const(body, value) {
        return format!("0x{value:08x}");
    }
    if depth > 0 {
        if let Some(expression) = render_scalar_expression(body, dispatcher, state, value, depth) {
            return expression;
        }
    }
    format!("v{}", value.index())
}

fn render_scalar_expression(
    body: &FunctionBody,
    dispatcher: Block,
    state: Value,
    value: Value,
    depth: usize,
) -> Option<String> {
    let value = body.resolve_alias(value);
    let ValueDef::Operator(op, args, _) = &body.values[value] else {
        return None;
    };
    if !is_inlineable_scalar(op) {
        return None;
    }
    let family = operator_family(op);
    let args = body.arg_pool[*args]
        .iter()
        .map(|arg| render_value(body, dispatcher, state, *arg, depth.saturating_sub(1)))
        .collect::<Vec<_>>();
    if args.len() != 2 {
        return Some(format!("{family}({})", args.join(", ")));
    }
    let a = &args[0];
    let b = &args[1];
    let rendered = match family.as_str() {
        "i32add" => format!("wrapping_add({a}, {b})"),
        "i32sub" => format!("wrapping_sub({a}, {b})"),
        "i32mul" => format!("wrapping_mul({a}, {b})"),
        "i32and" => format!("({a} & {b})"),
        "i32or" => format!("({a} | {b})"),
        "i32xor" => format!("({a} ^ {b})"),
        "i32shl" => format!("({a} << {b})"),
        "i32shrs" => format!("ashr({a}, {b})"),
        "i32shru" => format!("({a} >> {b})"),
        "i32rotl" => format!("rotl({a}, {b})"),
        "i32rotr" => format!("rotr({a}, {b})"),
        "i32eq" => format!("({a} == {b})"),
        "i32ne" => format!("({a} != {b})"),
        "i32ltu" => format!("ult({a}, {b})"),
        "i32leu" => format!("ule({a}, {b})"),
        "i32gtu" => format!("ugt({a}, {b})"),
        "i32geu" => format!("uge({a}, {b})"),
        "i32lts" => format!("slt({a}, {b})"),
        "i32les" => format!("sle({a}, {b})"),
        "i32gts" => format!("sgt({a}, {b})"),
        "i32ges" => format!("sge({a}, {b})"),
        _ => format!("{family}({a}, {b})"),
    };
    Some(rendered)
}

fn render_instruction(
    body: &FunctionBody,
    dispatcher: Block,
    state: Value,
    value: Value,
) -> Option<String> {
    let value = body.resolve_alias(value);
    let ValueDef::Operator(op, args, _) = &body.values[value] else {
        return None;
    };
    if matches!(op, Operator::I32Const { .. }) || is_state_predicate(body, state, value) {
        return None;
    }
    if let Some(expression) = render_scalar_expression(body, dispatcher, state, value, 5) {
        return Some(format!("v{} = {expression}", value.index()));
    }
    let args = body.arg_pool[*args]
        .iter()
        .map(|arg| render_value(body, dispatcher, state, *arg, 4))
        .collect::<Vec<_>>();
    Some(format!("v{} = {}({})", value.index(), op, args.join(", ")))
}

fn operator_family(op: &Operator) -> String {
    let rendered = op.to_string();
    rendered
        .split_once('<')
        .map_or(rendered.as_str(), |(family, _)| family)
        .to_owned()
}

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

#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct StateTransitionReport {
    pub successor: u32,
    pub arguments: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct StateCaseReport {
    pub state: u32,
    pub blocks: BTreeSet<usize>,
    pub successors: BTreeSet<u32>,
    pub transitions: Vec<StateTransitionReport>,
    pub nested_machines: BTreeSet<usize>,
    pub direct_nested_machines: BTreeSet<usize>,
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
                    render_value(body, dispatcher, state, *value, 6)
                }
            })
            .collect::<Vec<_>>();
        let report = StateTransitionReport {
            successor: edge.successor,
            arguments,
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
        successors: trace.next.clone(),
        transitions,
        nested_machines: BTreeSet::new(),
        direct_nested_machines: BTreeSet::new(),
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
    pub comparisons: usize,
    pub initial: BTreeSet<u32>,
    pub graph: BTreeMap<u32, BTreeSet<u32>>,
    pub linearized: Option<Vec<u32>>,
    pub cases: Vec<StateCaseReport>,
    pub unresolved_backedges: usize,
    pub data_forks: usize,
}

pub fn analyze_export_state_machines(
    bytes: &[u8],
    export_name: &str,
) -> Result<Vec<StateMachineReport>> {
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

fn analyze_inner(bytes: &[u8], export_name: &str) -> Result<Vec<StateMachineReport>> {
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
    annotate_nested_machines(body, &mut machines, &metadata);
    Ok(machines)
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
        let machines = analyze_export_state_machines(&bytes, "run")?;
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
        assert!(machine.cases[0].nested_machines.is_empty());
        assert!(machine.cases[0].direct_nested_machines.is_empty());
        assert_eq!(root_machine_indices(&machines), vec![0]);
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

        let machines = analyze_export_state_machines(&bytes, "run")?;
        assert_eq!(machines.len(), 2);
        let roots = root_machine_indices(&machines);
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
        Ok(())
    }
}
