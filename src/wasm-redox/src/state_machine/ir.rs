use waffle::{FunctionBody, Operator, Value, ValueDef};

pub(super) fn i32_const(body: &FunctionBody, value: Value) -> Option<u32> {
    let value = body.resolve_alias(value);
    match body.values[value] {
        ValueDef::Operator(Operator::I32Const { value }, _, _) => Some(value),
        _ => None,
    }
}

pub(super) fn operator_family(op: &Operator) -> String {
    let rendered = op.to_string();
    rendered
        .split_once('<')
        .map_or(rendered.as_str(), |(family, _)| family)
        .to_owned()
}
