use anyhow::{anyhow, Context, Result};
use serde::Serialize;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    panic::{catch_unwind, AssertUnwindSafe},
};
use waffle::{
    entity::EntityRef, Block, BlockTarget, ExportKind, FrontendOptions, Func, FunctionBody,
    ImportKind, Module, Operator, OptOptions, Terminator, Type, Value, ValueDef,
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

fn render_scalar_family(family: &str, args: &[String]) -> Option<String> {
    let [a, b] = args else {
        return None;
    };
    Some(match family {
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
        _ => return None,
    })
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
    if let ValueDef::BlockParam(block, index, _) = body.values[value] {
        if block == body.entry && usize::try_from(index).is_ok_and(|index| index < body.n_params) {
            return format!("$arg{index}");
        }
    }
    if let Some(value) = i32_const(body, value) {
        return format!("0x{value:08x}");
    }
    if depth > 0 {
        if let Some(source) = reverse_bits_source(body, value) {
            if source != value {
                return format!(
                    "reverse_bits32({})",
                    render_value(body, dispatcher, state, source, depth.saturating_sub(1))
                );
            }
        }
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
    render_scalar_family(&family, &args).or_else(|| Some(format!("{family}({})", args.join(", "))))
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

fn substitute_params(expression: &str, environment: &[String]) -> String {
    let bytes = expression.as_bytes();
    let mut output = String::with_capacity(expression.len());
    let mut index = 0usize;
    while index < bytes.len() {
        if bytes[index] == b'$'
            && index + 2 < bytes.len()
            && bytes[index + 1] == b'p'
            && bytes[index + 2].is_ascii_digit()
        {
            let mut end = index + 2;
            while end < bytes.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if let Ok(parameter) = expression[index + 2..end].parse::<usize>() {
                if let Some(replacement) = environment.get(parameter) {
                    output.push('(');
                    output.push_str(replacement);
                    output.push(')');
                    index = end;
                    continue;
                }
            }
        }
        output.push(char::from(bytes[index]));
        index += 1;
    }
    output
}

fn strip_outer_parentheses(mut expression: &str) -> &str {
    loop {
        let bytes = expression.as_bytes();
        if bytes.first() != Some(&b'(') || bytes.last() != Some(&b')') {
            return expression;
        }
        let mut depth = 0usize;
        let mut closes_before_end = false;
        for (index, byte) in bytes.iter().enumerate() {
            match byte {
                b'(' => depth = depth.saturating_add(1),
                b')' => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 && index + 1 != bytes.len() {
                        closes_before_end = true;
                        break;
                    }
                }
                _ => {}
            }
        }
        if closes_before_end || depth != 0 {
            return expression;
        }
        expression = &expression[1..expression.len() - 1];
    }
}

fn split_top_level_binary<'a>(expression: &'a str, operator: &str) -> Option<(&'a str, &'a str)> {
    let bytes = expression.as_bytes();
    let operator = operator.as_bytes();
    let mut depth = 0usize;
    let mut index = 0usize;
    while index + operator.len() <= bytes.len() {
        match bytes[index] {
            b'(' => depth = depth.saturating_add(1),
            b')' => depth = depth.saturating_sub(1),
            _ if depth == 0 && &bytes[index..index + operator.len()] == operator => {
                return Some((&expression[..index], &expression[index + operator.len()..]));
            }
            _ => {}
        }
        index = index.saturating_add(1);
    }
    None
}

fn split_top_level_arguments(expression: &str) -> Vec<&str> {
    let bytes = expression.as_bytes();
    let mut depth = 0usize;
    let mut start = 0usize;
    let mut arguments = Vec::new();
    for (index, byte) in bytes.iter().enumerate() {
        match byte {
            b'(' => depth = depth.saturating_add(1),
            b')' => depth = depth.saturating_sub(1),
            b',' if depth == 0 => {
                arguments.push(expression[start..index].trim());
                start = index.saturating_add(1);
            }
            _ => {}
        }
    }
    arguments.push(expression[start..].trim());
    arguments
}

fn eval_i32_function(name: &str, arguments: &[&str]) -> Option<u32> {
    match (name, arguments) {
        ("reverse_bits32", [value]) => Some(try_eval_i32_expression(value)?.reverse_bits()),
        ("wrapping_add", [left, right]) => {
            Some(try_eval_i32_expression(left)?.wrapping_add(try_eval_i32_expression(right)?))
        }
        ("wrapping_sub", [left, right]) => {
            Some(try_eval_i32_expression(left)?.wrapping_sub(try_eval_i32_expression(right)?))
        }
        ("wrapping_mul", [left, right]) => {
            Some(try_eval_i32_expression(left)?.wrapping_mul(try_eval_i32_expression(right)?))
        }
        ("rotl", [value, amount]) => {
            Some(try_eval_i32_expression(value)?.rotate_left(try_eval_i32_expression(amount)? & 31))
        }
        ("rotr", [value, amount]) => Some(
            try_eval_i32_expression(value)?.rotate_right(try_eval_i32_expression(amount)? & 31),
        ),
        ("ashr", [value, amount]) => Some(
            (try_eval_i32_expression(value)?.cast_signed()
                >> (try_eval_i32_expression(amount)? & 31))
                .cast_unsigned(),
        ),
        ("ult", [left, right]) => Some(u32::from(
            try_eval_i32_expression(left)? < try_eval_i32_expression(right)?,
        )),
        ("ule", [left, right]) => Some(u32::from(
            try_eval_i32_expression(left)? <= try_eval_i32_expression(right)?,
        )),
        ("ugt", [left, right]) => Some(u32::from(
            try_eval_i32_expression(left)? > try_eval_i32_expression(right)?,
        )),
        ("uge", [left, right]) => Some(u32::from(
            try_eval_i32_expression(left)? >= try_eval_i32_expression(right)?,
        )),
        ("slt", [left, right]) => Some(u32::from(
            try_eval_i32_expression(left)?.cast_signed()
                < try_eval_i32_expression(right)?.cast_signed(),
        )),
        ("sle", [left, right]) => Some(u32::from(
            try_eval_i32_expression(left)?.cast_signed()
                <= try_eval_i32_expression(right)?.cast_signed(),
        )),
        ("sgt", [left, right]) => Some(u32::from(
            try_eval_i32_expression(left)?.cast_signed()
                > try_eval_i32_expression(right)?.cast_signed(),
        )),
        ("sge", [left, right]) => Some(u32::from(
            try_eval_i32_expression(left)?.cast_signed()
                >= try_eval_i32_expression(right)?.cast_signed(),
        )),
        _ => None,
    }
}

fn try_eval_i32_expression(expression: &str) -> Option<u32> {
    let expression = strip_outer_parentheses(expression.trim());
    if let Some(hex) = expression.strip_prefix("0x") {
        if let Ok(value) = u32::from_str_radix(hex, 16) {
            return Some(value);
        }
    }

    if let Some(open) = expression.find('(') {
        if expression.ends_with(')') {
            let name = &expression[..open];
            if !name.is_empty()
                && name
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            {
                let arguments =
                    split_top_level_arguments(&expression[open + 1..expression.len() - 1]);
                if let Some(value) = eval_i32_function(name, &arguments) {
                    return Some(value);
                }
            }
        }
    }

    for operator in ["==", "!=", "|", "^", "&", "<<", ">>"] {
        if let Some((left, right)) = split_top_level_binary(expression, operator) {
            let left = try_eval_i32_expression(left)?;
            let right = try_eval_i32_expression(right)?;
            return Some(match operator {
                "==" => u32::from(left == right),
                "!=" => u32::from(left != right),
                "|" => left | right,
                "^" => left ^ right,
                "&" => left & right,
                "<<" => left.wrapping_shl(right & 31),
                ">>" => left.wrapping_shr(right & 31),
                _ => return None,
            });
        }
    }
    None
}

fn fold_closed_i32_expression(expression: String) -> String {
    try_eval_i32_expression(&expression).map_or(expression, |value| format!("0x{value:08x}"))
}

fn substitute_arguments(arguments: &[String], environment: &[String]) -> Vec<String> {
    arguments
        .iter()
        .map(|argument| fold_closed_i32_expression(substitute_params(argument, environment)))
        .collect()
}

#[derive(Clone)]
struct BitPermutation {
    base: Value,
    bits: [Option<u8>; 32],
}

fn identity_bit_permutation(base: Value) -> BitPermutation {
    BitPermutation {
        base,
        bits: std::array::from_fn(|index| u8::try_from(index).ok()),
    }
}

fn zero_bit_permutation(base: Value) -> BitPermutation {
    BitPermutation {
        base,
        bits: [None; 32],
    }
}

fn bit_permutation(
    body: &FunctionBody,
    value: Value,
    depth: usize,
    visiting: &mut BTreeSet<Value>,
) -> Option<BitPermutation> {
    let value = body.resolve_alias(value);
    if depth == 0 || !visiting.insert(value) {
        return Some(identity_bit_permutation(value));
    }

    let result = match &body.values[value] {
        ValueDef::Operator(Operator::I32Const { value: 0 }, _, _) => {
            Some(zero_bit_permutation(value))
        }
        ValueDef::Operator(op, args, _) => {
            let args = &body.arg_pool[*args];
            let family = operator_family(op);
            match (family.as_str(), args) {
                ("i32and", [left, right]) => {
                    let (source, mask) = if let Some(mask) = i32_const(body, *right) {
                        (*left, mask)
                    } else if let Some(mask) = i32_const(body, *left) {
                        (*right, mask)
                    } else {
                        visiting.remove(&value);
                        return Some(identity_bit_permutation(value));
                    };
                    let mut permutation =
                        bit_permutation(body, source, depth.saturating_sub(1), visiting)?;
                    for bit in 0..32 {
                        if mask & (1u32 << bit) == 0 {
                            permutation.bits[bit] = None;
                        }
                    }
                    Some(permutation)
                }
                ("i32or", [left, right]) => {
                    let left = bit_permutation(body, *left, depth.saturating_sub(1), visiting)?;
                    let right = bit_permutation(body, *right, depth.saturating_sub(1), visiting)?;
                    if left.base != right.base {
                        None
                    } else {
                        let mut bits = [None; 32];
                        for (bit, merged) in bits.iter_mut().enumerate() {
                            *merged = match (left.bits[bit], right.bits[bit]) {
                                (Some(a), Some(b)) if a != b => {
                                    visiting.remove(&value);
                                    return None;
                                }
                                (Some(a), _) => Some(a),
                                (_, Some(b)) => Some(b),
                                (None, None) => None,
                            };
                        }
                        Some(BitPermutation {
                            base: left.base,
                            bits,
                        })
                    }
                }
                ("i32shl", [source, amount])
                | ("i32shru", [source, amount])
                | ("i32rotl", [source, amount])
                | ("i32rotr", [source, amount]) => {
                    let amount = i32_const(body, *amount)? & 31;
                    let source = bit_permutation(body, *source, depth.saturating_sub(1), visiting)?;
                    let mut bits = [None; 32];
                    for output in 0..32u32 {
                        let input = match family.as_str() {
                            "i32shl" => output.checked_sub(amount),
                            "i32shru" => output.checked_add(amount).filter(|input| *input < 32),
                            "i32rotl" => Some((output + 32 - amount) & 31),
                            "i32rotr" => Some((output + amount) & 31),
                            _ => None,
                        };
                        if let Some(input) = input {
                            bits[usize::try_from(output).ok()?] =
                                source.bits[usize::try_from(input).ok()?];
                        }
                    }
                    Some(BitPermutation {
                        base: source.base,
                        bits,
                    })
                }
                _ => Some(identity_bit_permutation(value)),
            }
        }
        ValueDef::Alias(source) => {
            bit_permutation(body, *source, depth.saturating_sub(1), visiting)
        }
        _ => Some(identity_bit_permutation(value)),
    };
    visiting.remove(&value);
    result
}

fn reverse_bits_source(body: &FunctionBody, value: Value) -> Option<Value> {
    let mut visiting = BTreeSet::new();
    let permutation = bit_permutation(body, value, 24, &mut visiting)?;
    permutation
        .bits
        .iter()
        .enumerate()
        .all(|(output, source)| *source == u8::try_from(31usize.saturating_sub(output)).ok())
        .then_some(permutation.base)
}

fn incoming_block_param_values(body: &FunctionBody, block: Block, parameter: Value) -> Vec<Value> {
    let parameter = body.resolve_alias(parameter);
    let Some(index) = body.blocks[block]
        .params
        .iter()
        .position(|(_, candidate)| body.resolve_alias(*candidate) == parameter)
    else {
        return Vec::new();
    };
    let mut incoming = BTreeSet::new();

    for (_, predecessor) in body.blocks.entries() {
        predecessor.terminator.visit_targets(|target| {
            if target.block != block {
                return;
            }
            let Some(value) = target.args.get(index) else {
                return;
            };
            let value = body.resolve_alias(*value);
            if value != parameter {
                incoming.insert(value);
            }
        });
    }

    incoming.into_iter().collect()
}

#[derive(Default)]
struct SemanticCallNames {
    labels: BTreeMap<Func, String>,
}

fn strip_wasm_bindgen_hash(name: &str) -> &str {
    let Some((base, suffix)) = name.rsplit_once('_') else {
        return name;
    };
    if suffix.len() == 16 && suffix.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        base
    } else {
        name
    }
}

fn normalize_import_name(module: &str, name: &str) -> String {
    let name = strip_wasm_bindgen_hash(name);
    if let Some(name) = name.strip_prefix("__wbg_") {
        format!("{module}.{name}")
    } else if let Some(name) = name.strip_prefix("__wbindgen_") {
        format!("wbindgen.{name}")
    } else {
        format!("{module}.{name}")
    }
}

fn direct_called_functions(body: &FunctionBody) -> BTreeSet<Func> {
    body.values
        .entries()
        .filter_map(|(_, value)| match value {
            ValueDef::Operator(Operator::Call { function_index }, _, _) => Some(*function_index),
            _ => None,
        })
        .collect()
}

fn unique_return_value(body: &FunctionBody) -> Option<Value> {
    let mut values = BTreeSet::new();
    for (_, block) in body.blocks.entries() {
        let Terminator::Return { values: returned } = &block.terminator else {
            continue;
        };
        if returned.len() != 1 {
            return None;
        }
        values.insert(body.resolve_alias(returned[0]));
    }
    (values.len() == 1)
        .then(|| values.into_iter().next())
        .flatten()
}

fn call_label<'a>(
    body: &FunctionBody,
    value: Value,
    names: &'a SemanticCallNames,
) -> Option<(&'a str, Vec<Value>)> {
    fn inner<'a>(
        body: &FunctionBody,
        value: Value,
        names: &'a SemanticCallNames,
        depth: usize,
    ) -> Option<(&'a str, Vec<Value>)> {
        if depth == 0 {
            return None;
        }
        let value = body.resolve_alias(value);
        match &body.values[value] {
            ValueDef::Operator(Operator::Call { function_index }, args, _) => Some((
                names.labels.get(function_index)?.as_str(),
                body.arg_pool[*args].to_vec(),
            )),
            ValueDef::PickOutput(source, 0, _) => inner(body, *source, names, depth - 1),
            ValueDef::BlockParam(block, _, _) => {
                let incoming = incoming_block_param_values(body, *block, value);
                let [incoming] = incoming.as_slice() else {
                    return None;
                };
                inner(body, *incoming, names, depth - 1)
            }
            _ => None,
        }
    }
    inner(body, value, names, 8)
}

fn is_entry_parameter(body: &FunctionBody, value: Value) -> bool {
    matches!(
        body.values[body.resolve_alias(value)],
        ValueDef::BlockParam(block, index, _)
            if block == body.entry
                && usize::try_from(index).is_ok_and(|index| index < body.n_params)
    )
}

fn is_table_get_of_entry_parameter(body: &FunctionBody, value: Value) -> bool {
    let value = body.resolve_alias(value);
    let ValueDef::Operator(Operator::TableGet { .. }, args, _) = &body.values[value] else {
        return false;
    };
    matches!(&body.arg_pool[*args], [index] if is_entry_parameter(body, *index))
}

fn helper_returns_import_call(
    body: &FunctionBody,
    names: &SemanticCallNames,
    import_name: &str,
) -> Option<Vec<Value>> {
    let returned = unique_return_value(body)?;
    let (label, args) = call_label(body, returned, names)?;
    (label == import_name).then_some(args)
}

fn unique_transparent_origin(body: &FunctionBody, value: Value, depth: usize) -> Value {
    if depth == 0 {
        return body.resolve_alias(value);
    }
    let value = body.resolve_alias(value);
    match &body.values[value] {
        ValueDef::PickOutput(source, 0, _) => unique_transparent_origin(body, *source, depth - 1),
        ValueDef::BlockParam(block, _, _) => {
            let incoming = incoming_block_param_values(body, *block, value);
            let [incoming] = incoming.as_slice() else {
                return value;
            };
            unique_transparent_origin(body, *incoming, depth - 1)
        }
        _ => value,
    }
}

fn helper_is_memory_slot(body: &FunctionBody, names: &SemanticCallNames) -> bool {
    if body.n_params != 0 {
        return false;
    }
    let Some(returned_slot) = unique_return_value(body) else {
        return false;
    };
    let returned_slot = unique_transparent_origin(body, returned_slot, 8);
    body.values.entries().any(|(_, value)| {
        let ValueDef::Operator(Operator::TableSet { .. }, args, _) = value else {
            return false;
        };
        let [slot, stored] = &body.arg_pool[*args] else {
            return false;
        };
        unique_transparent_origin(body, *slot, 8) == returned_slot
            && call_label(body, *stored, names).is_some_and(|(label, _)| label == "wbindgen.memory")
    })
}

fn classify_wasm_bindgen_helper(
    body: &FunctionBody,
    names: &SemanticCallNames,
) -> Option<&'static str> {
    if helper_returns_import_call(body, names, "wbg.length").is_some_and(
        |args| matches!(args.as_slice(), [value] if is_table_get_of_entry_parameter(body, *value)),
    ) {
        Some("wbindgen.externref_length")
    } else if helper_returns_import_call(body, names, "wbg.getUint32").is_some_and(|args| {
        args.into_iter()
            .any(|value| is_entry_parameter(body, value))
    }) {
        Some("wbindgen.getUint32_bridge")
    } else if helper_is_memory_slot(body, names) {
        Some("wbindgen.memory_slot")
    } else {
        None
    }
}

fn helper_is_heap_allocator(
    module: &Module<'_>,
    function: Func,
    body: &FunctionBody,
    imported_functions: &BTreeSet<Func>,
) -> bool {
    let signature = &module.signatures[module.funcs[function].sig()];
    if signature.params.as_slice() != [Type::I32]
        || signature.returns.as_slice() != [Type::I32]
        || direct_called_functions(body)
            .iter()
            .any(|callee| imported_functions.contains(callee))
    {
        return false;
    }

    let mut memory_grows = 0usize;
    let mut loads = 0usize;
    let mut stores = 0usize;
    for (_, value) in body.values.entries() {
        let ValueDef::Operator(operator, _, _) = value else {
            continue;
        };
        let family = operator_family(operator);
        if matches!(operator, Operator::MemoryGrow { .. }) {
            memory_grows += 1;
        } else if family.contains("load") {
            loads += 1;
        } else if family.contains("store") {
            stores += 1;
        }
    }

    let mut zero_return = false;
    let mut nonzero_return = false;
    for (_, block) in body.blocks.entries() {
        let Terminator::Return { values } = &block.terminator else {
            continue;
        };
        let [value] = values.as_slice() else {
            continue;
        };
        match i32_const(body, *value) {
            Some(0) => zero_return = true,
            _ => nonzero_return = true,
        }
    }

    memory_grows > 0 && loads >= 4 && stores >= 8 && zero_return && nonzero_return
}

fn build_semantic_call_names(module: &mut Module<'_>, root: Func) -> SemanticCallNames {
    let mut names = SemanticCallNames::default();
    for import in &module.imports {
        if let ImportKind::Func(function) = import.kind {
            names.labels.insert(
                function,
                normalize_import_name(&import.module, &import.name),
            );
        }
    }

    let imported_functions = module
        .imports
        .iter()
        .filter_map(|import| match import.kind {
            ImportKind::Func(function) => Some(function),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let direct_callees = module.funcs[root]
        .body()
        .map(direct_called_functions)
        .unwrap_or_default();
    for callee in direct_callees {
        if names.labels.contains_key(&callee) || module.expand_func(callee).is_err() {
            continue;
        }
        let Some(body) = module.funcs[callee].body() else {
            continue;
        };
        if let Some(label) = classify_wasm_bindgen_helper(body, &names) {
            names.labels.insert(callee, label.to_owned());
        } else if helper_is_heap_allocator(module, callee, body, &imported_functions) {
            names.labels.insert(callee, "wasm.heap_alloc".to_owned());
        }
    }
    names
}

#[derive(Debug, Serialize)]
pub struct SemanticRuntimeBindingReport {
    pub name: String,
    pub expression: String,
}

fn is_runtime_boundary(op: &Operator) -> bool {
    let family = operator_family(op);
    matches!(op, Operator::Call { .. })
        || family.starts_with("i32load")
        || family.starts_with("i64load")
        || family.starts_with("f32load")
        || family.starts_with("f64load")
        || family.starts_with("globalget")
        || family.starts_with("global_get")
}

struct SemanticRenderContext<'a> {
    bindings: &'a BTreeMap<Value, String>,
    call_names: &'a SemanticCallNames,
    runtime_names: BTreeMap<Value, String>,
    runtime_bindings: Vec<SemanticRuntimeBindingReport>,
}

fn render_semantic_value(
    body: &FunctionBody,
    value: Value,
    context: &mut SemanticRenderContext<'_>,
    depth: usize,
    visiting: &mut BTreeSet<Value>,
) -> String {
    let value = body.resolve_alias(value);
    if let Some(binding) = context.bindings.get(&value) {
        return binding.clone();
    }
    if let Some(binding) = context.runtime_names.get(&value) {
        return binding.clone();
    }
    if let Some(constant) = i32_const(body, value) {
        return format!("0x{constant:08x}");
    }
    if let Some(source) = reverse_bits_source(body, value) {
        if source != value {
            return format!(
                "reverse_bits32({})",
                render_semantic_value(body, source, context, depth.saturating_sub(1), visiting)
            );
        }
    }
    if depth == 0 || !visiting.insert(value) {
        return format!("v{}", value.index());
    }

    let (rendered, runtime_boundary) = match &body.values[value] {
        ValueDef::BlockParam(block, index, _) => {
            let rendered = if *block == body.entry
                && usize::try_from(*index).is_ok_and(|index| index < body.n_params)
            {
                format!("$arg{index}")
            } else {
                let incoming = incoming_block_param_values(body, *block, value)
                    .into_iter()
                    .map(|incoming| {
                        render_semantic_value(
                            body,
                            incoming,
                            context,
                            depth.saturating_sub(1),
                            visiting,
                        )
                    })
                    .collect::<BTreeSet<_>>();
                match incoming.len() {
                    0 => format!("$block{}p{index}", block.index()),
                    1 => incoming
                        .into_iter()
                        .next()
                        .unwrap_or_else(|| format!("$block{}p{index}", block.index())),
                    _ => format!(
                        "phi({})",
                        incoming.into_iter().collect::<Vec<_>>().join(", ")
                    ),
                }
            };
            (rendered, false)
        }
        ValueDef::Operator(op, arg_ref, _) => {
            let raw_args = &body.arg_pool[*arg_ref];
            {
                let args = raw_args
                    .iter()
                    .map(|arg| {
                        render_semantic_value(
                            body,
                            *arg,
                            context,
                            depth.saturating_sub(1),
                            visiting,
                        )
                    })
                    .collect::<Vec<_>>();
                let family = operator_family(op);
                let rendered = if let Operator::Call { function_index } = op {
                    context.call_names.labels.get(function_index).map_or_else(
                        || format!("{op}({})", args.join(", ")),
                        |name| format!("{name}({})", args.join(", ")),
                    )
                } else if is_inlineable_scalar(op) {
                    render_scalar_family(&family, &args)
                        .unwrap_or_else(|| format!("{family}({})", args.join(", ")))
                } else {
                    format!("{op}({})", args.join(", "))
                };
                (rendered, is_runtime_boundary(op))
            }
        }
        ValueDef::PickOutput(source, index, _) => (
            format!(
                "pick{index}({})",
                render_semantic_value(body, *source, context, depth.saturating_sub(1), visiting,)
            ),
            false,
        ),
        ValueDef::Alias(source) => (
            render_semantic_value(body, *source, context, depth.saturating_sub(1), visiting),
            false,
        ),
        ValueDef::Placeholder(_) | ValueDef::None => (format!("v{}", value.index()), false),
    };
    visiting.remove(&value);
    if runtime_boundary {
        let name = format!("$runtime{}", context.runtime_bindings.len());
        context.runtime_names.insert(value, name.clone());
        context.runtime_bindings.push(SemanticRuntimeBindingReport {
            name: name.clone(),
            expression: rendered,
        });
        name
    } else {
        rendered
    }
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

fn render_return_expressions(
    body: &FunctionBody,
    bindings: &BTreeMap<Value, String>,
    call_names: &SemanticCallNames,
) -> (Vec<String>, Vec<SemanticRuntimeBindingReport>) {
    let mut expressions = Vec::new();
    let mut context = SemanticRenderContext {
        bindings,
        call_names,
        runtime_names: BTreeMap::new(),
        runtime_bindings: Vec::new(),
    };
    for (_, block) in body.blocks.entries() {
        let Terminator::Return { values } = &block.terminator else {
            continue;
        };
        for value in values {
            let mut visiting = BTreeSet::new();
            let expression = render_semantic_value(body, *value, &mut context, 48, &mut visiting);
            if !expressions.contains(&expression) {
                expressions.push(expression);
            }
        }
    }
    (expressions, context.runtime_bindings)
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
    let (return_expressions, runtime_bindings) =
        render_return_expressions(body, &bindings, &call_names);
    Ok(ExportSemanticAnalysis {
        state_machine_roots,
        state_machine_pipelines,
        state_machines: machines,
        terminal_bindings,
        runtime_bindings,
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
}
