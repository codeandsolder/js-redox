use super::{i32_const, is_state_predicate, operator_family};
use std::collections::BTreeSet;
use waffle::{entity::EntityRef, Block, FunctionBody, Operator, Value, ValueDef};

pub(super) fn is_inlineable_scalar(op: &Operator) -> bool {
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
            | "i32eqz"
    )
}

pub(super) fn render_scalar_family(family: &str, args: &[String]) -> Option<String> {
    const ZERO: &str = "0x00000000";
    const ONE: &str = "0x00000001";
    const ALL_ONES: &str = "0xffffffff";

    if let [a] = args {
        let expression = match family {
            "i32eqz" => format!("is_zero({a})"),
            _ => return None,
        };
        return Some(fold_closed_i32_expression(expression));
    }
    let [a, b] = args else {
        return None;
    };
    let expression = match family {
        "i32add" if a == ZERO => b.clone(),
        "i32add" if b == ZERO => a.clone(),
        "i32sub" if b == ZERO => a.clone(),
        "i32mul" if a == ZERO || b == ZERO => ZERO.to_owned(),
        "i32mul" if a == ONE => b.clone(),
        "i32mul" if b == ONE => a.clone(),
        "i32and" if a == ZERO || b == ZERO => ZERO.to_owned(),
        "i32and" if a == ALL_ONES => b.clone(),
        "i32and" if b == ALL_ONES => a.clone(),
        "i32or" | "i32xor" if a == ZERO => b.clone(),
        "i32or" | "i32xor" if b == ZERO => a.clone(),
        "i32shl" | "i32shrs" | "i32shru" | "i32rotl" | "i32rotr" if a == ZERO => ZERO.to_owned(),
        "i32shl" | "i32shrs" | "i32shru" | "i32rotl" | "i32rotr" if b == ZERO => a.clone(),
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
    };
    Some(fold_closed_i32_expression(expression))
}

pub(super) fn render_value(
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

pub(super) fn render_instruction(
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

pub(super) fn try_eval_i32_expression(expression: &str) -> Option<u32> {
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

pub(super) fn fold_closed_i32_expression(expression: String) -> String {
    try_eval_i32_expression(&expression).map_or(expression, |value| format!("0x{value:08x}"))
}

pub(super) fn substitute_arguments(arguments: &[String], environment: &[String]) -> Vec<String> {
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

pub(super) fn reverse_bits_source(body: &FunctionBody, value: Value) -> Option<Value> {
    let mut visiting = BTreeSet::new();
    let permutation = bit_permutation(body, value, 24, &mut visiting)?;
    permutation
        .bits
        .iter()
        .enumerate()
        .all(|(output, source)| *source == u8::try_from(31usize.saturating_sub(output)).ok())
        .then_some(permutation.base)
}
