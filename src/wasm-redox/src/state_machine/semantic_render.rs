use super::{
    helper_recognition::{memory_slot_from_table_get, SemanticCallNames},
    ir::{i32_const, operator_family},
    scalar::{is_inlineable_scalar, render_scalar_family, reverse_bits_source},
    semantic_normalize::normalize_semantic_expression,
    value_flow::{conditional_phi_inputs, incoming_block_param_edges},
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use waffle::{entity::EntityRef, FunctionBody, Operator, Terminator, Value, ValueDef};

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SemanticExpression {
    I32Const {
        value: u32,
    },
    Argument {
        index: usize,
    },
    Runtime {
        value: usize,
        name: String,
    },
    Symbol {
        name: String,
    },
    SsaValue {
        value: usize,
    },
    Opaque {
        expression: String,
    },
    Operation {
        value: usize,
        operator: String,
        arguments: Vec<SemanticExpression>,
    },
}

#[derive(Debug, Serialize)]
pub struct SemanticRuntimeBindingReport {
    pub value: usize,
    pub name: String,
    pub expression: String,
    pub semantic_ir: SemanticExpression,
    pub normalized_semantic_ir: SemanticExpression,
    pub runtime_dependencies: Vec<usize>,
}

#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct SemanticReturnReport {
    pub value: usize,
    pub expression: String,
    pub semantic_ir: SemanticExpression,
    pub normalized_semantic_ir: SemanticExpression,
    pub runtime_dependencies: Vec<usize>,
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

struct SemanticExpressionContext<'a> {
    bindings: &'a BTreeMap<Value, String>,
    call_names: &'a SemanticCallNames,
    runtime_names: &'a BTreeMap<Value, String>,
    expanded_runtime: Option<Value>,
    visiting: BTreeSet<Value>,
    expanded: BTreeSet<Value>,
}

fn semantic_binding_leaf(binding: &str) -> SemanticExpression {
    if let Some(hex) = binding.strip_prefix("0x") {
        if hex.len() == 8 {
            if let Ok(value) = u32::from_str_radix(hex, 16) {
                return SemanticExpression::I32Const { value };
            }
        }
    }
    if let Some(index) = binding
        .strip_prefix("$arg")
        .and_then(|index| index.parse::<usize>().ok())
    {
        return SemanticExpression::Argument { index };
    }
    if binding.starts_with('$') {
        return SemanticExpression::Symbol {
            name: binding.to_owned(),
        };
    }
    SemanticExpression::Opaque {
        expression: binding.to_owned(),
    }
}

fn build_semantic_expression(
    body: &FunctionBody,
    value: Value,
    depth: usize,
    context: &mut SemanticExpressionContext<'_>,
) -> SemanticExpression {
    let value = body.resolve_alias(value);
    if let Some(binding) = context.bindings.get(&value) {
        return semantic_binding_leaf(binding);
    }
    if Some(value) != context.expanded_runtime {
        if let Some(name) = context.runtime_names.get(&value) {
            return SemanticExpression::Runtime {
                value: value.index(),
                name: name.clone(),
            };
        }
    }
    if let Some(constant) = i32_const(body, value) {
        return SemanticExpression::I32Const { value: constant };
    }
    if depth == 0 {
        return SemanticExpression::SsaValue {
            value: value.index(),
        };
    }

    match &body.values[value] {
        ValueDef::BlockParam(block, index, _) => {
            if *block == body.entry
                && usize::try_from(*index).is_ok_and(|index| index < body.n_params)
            {
                return SemanticExpression::Argument {
                    index: usize::try_from(*index).unwrap_or_default(),
                };
            }
            let incoming_edges = incoming_block_param_edges(body, *block, value);
            let incoming_values = incoming_edges
                .iter()
                .map(|(_, incoming)| *incoming)
                .collect::<BTreeSet<_>>();
            match incoming_values.len() {
                0 => SemanticExpression::Symbol {
                    name: format!("$block{}p{index}", block.index()),
                },
                1 => {
                    let incoming = incoming_values.into_iter().next().unwrap_or(value);
                    build_semantic_expression(body, incoming, depth.saturating_sub(1), context)
                }
                _ => {
                    if !context.expanded.insert(value) || !context.visiting.insert(value) {
                        return SemanticExpression::SsaValue {
                            value: value.index(),
                        };
                    }
                    let conditional = conditional_phi_inputs(body, &incoming_edges);
                    let arguments = if let Some((condition, if_true, if_false)) = conditional {
                        [condition, if_true, if_false]
                            .into_iter()
                            .map(|input| {
                                build_semantic_expression(
                                    body,
                                    input,
                                    depth.saturating_sub(1),
                                    context,
                                )
                            })
                            .collect()
                    } else {
                        incoming_values
                            .into_iter()
                            .map(|incoming| {
                                build_semantic_expression(
                                    body,
                                    incoming,
                                    depth.saturating_sub(1),
                                    context,
                                )
                            })
                            .collect()
                    };
                    context.visiting.remove(&value);
                    SemanticExpression::Operation {
                        value: value.index(),
                        operator: if conditional.is_some() {
                            "phi_if"
                        } else {
                            "phi"
                        }
                        .to_owned(),
                        arguments,
                    }
                }
            }
        }
        ValueDef::Operator(op, arg_ref, _) => {
            if !context.expanded.insert(value) || !context.visiting.insert(value) {
                return SemanticExpression::SsaValue {
                    value: value.index(),
                };
            }
            let expression = if let Some(source) = reverse_bits_source(body, value) {
                if source != value {
                    SemanticExpression::Operation {
                        value: value.index(),
                        operator: "reverse_bits32".to_owned(),
                        arguments: vec![build_semantic_expression(
                            body,
                            source,
                            depth.saturating_sub(1),
                            context,
                        )],
                    }
                } else {
                    semantic_operator_expression(body, value, op, *arg_ref, depth, context)
                }
            } else {
                semantic_operator_expression(body, value, op, *arg_ref, depth, context)
            };
            context.visiting.remove(&value);
            expression
        }
        ValueDef::PickOutput(source, index, _) => {
            if !context.expanded.insert(value) || !context.visiting.insert(value) {
                return SemanticExpression::SsaValue {
                    value: value.index(),
                };
            }
            let expression = SemanticExpression::Operation {
                value: value.index(),
                operator: format!("pick{index}"),
                arguments: vec![build_semantic_expression(
                    body,
                    *source,
                    depth.saturating_sub(1),
                    context,
                )],
            };
            context.visiting.remove(&value);
            expression
        }
        ValueDef::Alias(source) => {
            build_semantic_expression(body, *source, depth.saturating_sub(1), context)
        }
        ValueDef::Placeholder(_) | ValueDef::None => SemanticExpression::SsaValue {
            value: value.index(),
        },
    }
}

fn semantic_operator_expression(
    body: &FunctionBody,
    value: Value,
    op: &Operator,
    arg_ref: waffle::pool::ListRef<Value>,
    depth: usize,
    context: &mut SemanticExpressionContext<'_>,
) -> SemanticExpression {
    let raw_args = &body.arg_pool[arg_ref];
    SemanticExpression::Operation {
        value: value.index(),
        operator: if let Operator::Call { function_index } = op {
            context
                .call_names
                .label(*function_index)
                .map_or_else(|| op.to_string(), str::to_owned)
        } else if is_inlineable_scalar(op) {
            operator_family(op)
        } else {
            op.to_string()
        },
        arguments: raw_args
            .iter()
            .map(|argument| {
                build_semantic_expression(body, *argument, depth.saturating_sub(1), context)
            })
            .collect(),
    }
}

fn render_semantic_value(
    body: &FunctionBody,
    value: Value,
    context: &mut SemanticRenderContext<'_>,
    depth: usize,
    visiting: &mut BTreeSet<Value>,
    runtime_dependencies: &mut BTreeSet<Value>,
) -> String {
    let value = body.resolve_alias(value);
    if let Some(binding) = context.bindings.get(&value) {
        return binding.clone();
    }
    if let Some(binding) = context.runtime_names.get(&value) {
        runtime_dependencies.insert(value);
        return binding.clone();
    }
    if let Some(constant) = i32_const(body, value) {
        return format!("0x{constant:08x}");
    }
    if let Some(source) = reverse_bits_source(body, value) {
        if source != value {
            return format!(
                "reverse_bits32({})",
                render_semantic_value(
                    body,
                    source,
                    context,
                    depth.saturating_sub(1),
                    visiting,
                    runtime_dependencies,
                )
            );
        }
    }
    if depth == 0 || !visiting.insert(value) {
        return format!("v{}", value.index());
    }

    let rendered = match &body.values[value] {
        ValueDef::BlockParam(block, index, _) => {
            if *block == body.entry
                && usize::try_from(*index).is_ok_and(|index| index < body.n_params)
            {
                format!("$arg{index}")
            } else {
                let incoming_edges = incoming_block_param_edges(body, *block, value);
                let incoming_values = incoming_edges
                    .iter()
                    .map(|(_, incoming)| *incoming)
                    .collect::<BTreeSet<_>>();
                match incoming_values.len() {
                    0 => format!("$block{}p{index}", block.index()),
                    1 => {
                        let incoming = incoming_values.into_iter().next().unwrap_or(value);
                        render_semantic_value(
                            body,
                            incoming,
                            context,
                            depth.saturating_sub(1),
                            visiting,
                            runtime_dependencies,
                        )
                    }
                    _ => {
                        if let Some((condition, if_true, if_false)) =
                            conditional_phi_inputs(body, &incoming_edges)
                        {
                            let condition = render_semantic_value(
                                body,
                                condition,
                                context,
                                depth.saturating_sub(1),
                                visiting,
                                runtime_dependencies,
                            );
                            let if_true = render_semantic_value(
                                body,
                                if_true,
                                context,
                                depth.saturating_sub(1),
                                visiting,
                                runtime_dependencies,
                            );
                            let if_false = render_semantic_value(
                                body,
                                if_false,
                                context,
                                depth.saturating_sub(1),
                                visiting,
                                runtime_dependencies,
                            );
                            format!("phi_if({condition}, {if_true}, {if_false})")
                        } else {
                            let incoming = incoming_values
                                .into_iter()
                                .map(|incoming| {
                                    render_semantic_value(
                                        body,
                                        incoming,
                                        context,
                                        depth.saturating_sub(1),
                                        visiting,
                                        runtime_dependencies,
                                    )
                                })
                                .collect::<BTreeSet<_>>();
                            format!(
                                "phi({})",
                                incoming.into_iter().collect::<Vec<_>>().join(", ")
                            )
                        }
                    }
                }
            }
        }
        ValueDef::Operator(op, arg_ref, _) => {
            let raw_args = &body.arg_pool[*arg_ref];
            let mut operator_runtime_dependencies = BTreeSet::new();
            let args = raw_args
                .iter()
                .map(|arg| {
                    render_semantic_value(
                        body,
                        *arg,
                        context,
                        depth.saturating_sub(1),
                        visiting,
                        &mut operator_runtime_dependencies,
                    )
                })
                .collect::<Vec<_>>();
            let family = operator_family(op);
            let rendered = if let Operator::Call { function_index } = op {
                if context.call_names.is_memory_grow_import(*function_index) {
                    let [receiver, delta] = raw_args else {
                        visiting.remove(&value);
                        runtime_dependencies.extend(operator_runtime_dependencies);
                        return format!("{op}({})", args.join(", "));
                    };
                    if let Some(slot) =
                        memory_slot_from_table_get(body, *receiver, context.call_names)
                    {
                        let slot = render_semantic_value(
                            body,
                            slot,
                            context,
                            depth.saturating_sub(1),
                            visiting,
                            &mut operator_runtime_dependencies,
                        );
                        let delta = render_semantic_value(
                            body,
                            *delta,
                            context,
                            depth.saturating_sub(1),
                            visiting,
                            &mut operator_runtime_dependencies,
                        );
                        format!("wasm.memory_grow({delta}, externref_slot={slot})")
                    } else {
                        context.call_names.label(*function_index).map_or_else(
                            || format!("{op}({})", args.join(", ")),
                            |name| format!("{name}({})", args.join(", ")),
                        )
                    }
                } else {
                    context.call_names.label(*function_index).map_or_else(
                        || format!("{op}({})", args.join(", ")),
                        |name| format!("{name}({})", args.join(", ")),
                    )
                }
            } else if is_inlineable_scalar(op) {
                render_scalar_family(&family, &args)
                    .unwrap_or_else(|| format!("{family}({})", args.join(", ")))
            } else {
                format!("{op}({})", args.join(", "))
            };

            if is_runtime_boundary(op) {
                visiting.remove(&value);
                let name = format!("$runtime{}", context.runtime_bindings.len());
                context.runtime_names.insert(value, name.clone());
                let mut semantic_context = SemanticExpressionContext {
                    bindings: context.bindings,
                    call_names: context.call_names,
                    runtime_names: &context.runtime_names,
                    expanded_runtime: Some(value),
                    visiting: BTreeSet::new(),
                    expanded: BTreeSet::new(),
                };
                let semantic_ir = build_semantic_expression(body, value, 48, &mut semantic_context);
                let normalized_semantic_ir = normalize_semantic_expression(&semantic_ir);
                context.runtime_bindings.push(SemanticRuntimeBindingReport {
                    value: value.index(),
                    name: name.clone(),
                    expression: rendered,
                    semantic_ir,
                    normalized_semantic_ir,
                    runtime_dependencies: operator_runtime_dependencies
                        .iter()
                        .map(|value| value.index())
                        .collect(),
                });
                runtime_dependencies.insert(value);
                return name;
            }
            runtime_dependencies.extend(operator_runtime_dependencies);
            rendered
        }
        ValueDef::PickOutput(source, index, _) => format!(
            "pick{index}({})",
            render_semantic_value(
                body,
                *source,
                context,
                depth.saturating_sub(1),
                visiting,
                runtime_dependencies,
            )
        ),
        ValueDef::Alias(source) => render_semantic_value(
            body,
            *source,
            context,
            depth.saturating_sub(1),
            visiting,
            runtime_dependencies,
        ),
        ValueDef::Placeholder(_) | ValueDef::None => format!("v{}", value.index()),
    };
    visiting.remove(&value);
    rendered
}

pub(super) fn render_return_semantics(
    body: &FunctionBody,
    bindings: &BTreeMap<Value, String>,
    call_names: &SemanticCallNames,
) -> (
    Vec<SemanticReturnReport>,
    Vec<SemanticRuntimeBindingReport>,
    BTreeMap<Value, String>,
) {
    let mut returns = Vec::new();
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
            let mut runtime_dependencies = BTreeSet::new();
            let resolved = body.resolve_alias(*value);
            let expression = render_semantic_value(
                body,
                resolved,
                &mut context,
                48,
                &mut visiting,
                &mut runtime_dependencies,
            );
            let mut semantic_context = SemanticExpressionContext {
                bindings: context.bindings,
                call_names: context.call_names,
                runtime_names: &context.runtime_names,
                expanded_runtime: None,
                visiting: BTreeSet::new(),
                expanded: BTreeSet::new(),
            };
            let semantic_ir = build_semantic_expression(body, resolved, 48, &mut semantic_context);
            let normalized_semantic_ir = normalize_semantic_expression(&semantic_ir);
            let report = SemanticReturnReport {
                value: resolved.index(),
                expression,
                semantic_ir,
                normalized_semantic_ir,
                runtime_dependencies: runtime_dependencies
                    .iter()
                    .map(|value| value.index())
                    .collect(),
            };
            if !returns.contains(&report) {
                returns.push(report);
            }
        }
    }
    (returns, context.runtime_bindings, context.runtime_names)
}
