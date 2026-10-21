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

#[derive(Default)]
struct RuntimeDiscovery {
    names: BTreeMap<Value, String>,
    ordered: Vec<Value>,
    dependencies: BTreeMap<Value, BTreeSet<Value>>,
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
    let (operator, arguments) = if let Operator::Call { function_index } = op {
        if context.call_names.is_memory_grow_import(*function_index) {
            if let [receiver, delta] = raw_args {
                if let Some(slot) = memory_slot_from_table_get(body, *receiver, context.call_names)
                {
                    ("wasm.memory_grow".to_owned(), vec![*delta, slot])
                } else {
                    (
                        context
                            .call_names
                            .label(*function_index)
                            .map_or_else(|| op.to_string(), str::to_owned),
                        raw_args.to_vec(),
                    )
                }
            } else {
                (
                    context
                        .call_names
                        .label(*function_index)
                        .map_or_else(|| op.to_string(), str::to_owned),
                    raw_args.to_vec(),
                )
            }
        } else {
            (
                context
                    .call_names
                    .label(*function_index)
                    .map_or_else(|| op.to_string(), str::to_owned),
                raw_args.to_vec(),
            )
        }
    } else {
        (
            if is_inlineable_scalar(op) {
                operator_family(op)
            } else {
                op.to_string()
            },
            raw_args.to_vec(),
        )
    };
    SemanticExpression::Operation {
        value: value.index(),
        operator,
        arguments: arguments
            .into_iter()
            .map(|argument| {
                build_semantic_expression(body, argument, depth.saturating_sub(1), context)
            })
            .collect(),
    }
}

fn render_semantic_expression(expression: &SemanticExpression) -> String {
    match expression {
        SemanticExpression::I32Const { value } => format!("0x{value:08x}"),
        SemanticExpression::Argument { index } => format!("$arg{index}"),
        SemanticExpression::Runtime { name, .. } | SemanticExpression::Symbol { name } => {
            name.clone()
        }
        SemanticExpression::SsaValue { value } => format!("v{value}"),
        SemanticExpression::Opaque { expression } => expression.clone(),
        SemanticExpression::Operation {
            operator,
            arguments,
            ..
        } => {
            let arguments = arguments
                .iter()
                .map(render_semantic_expression)
                .collect::<Vec<_>>();
            if operator == "wasm.memory_grow" && arguments.len() == 2 {
                format!(
                    "wasm.memory_grow({}, externref_slot={})",
                    arguments[0], arguments[1]
                )
            } else {
                render_scalar_family(operator, &arguments)
                    .unwrap_or_else(|| format!("{operator}({})", arguments.join(", ")))
            }
        }
    }
}

fn discover_runtime_roots(
    body: &FunctionBody,
    value: Value,
    bindings: &BTreeMap<Value, String>,
    discovery: &mut RuntimeDiscovery,
    depth: usize,
    visiting: &mut BTreeSet<Value>,
) -> BTreeSet<Value> {
    let value = body.resolve_alias(value);
    if bindings.contains_key(&value) || i32_const(body, value).is_some() {
        return BTreeSet::new();
    }
    if discovery.names.contains_key(&value) {
        return [value].into_iter().collect();
    }
    if let Some(source) = reverse_bits_source(body, value) {
        if source != value {
            return discover_runtime_roots(
                body,
                source,
                bindings,
                discovery,
                depth.saturating_sub(1),
                visiting,
            );
        }
    }
    if depth == 0 || !visiting.insert(value) {
        return BTreeSet::new();
    }

    let roots = match &body.values[value] {
        ValueDef::BlockParam(block, index, _) => {
            if *block == body.entry
                && usize::try_from(*index).is_ok_and(|index| index < body.n_params)
            {
                BTreeSet::new()
            } else {
                let incoming_edges = incoming_block_param_edges(body, *block, value);
                let incoming_values = incoming_edges
                    .iter()
                    .map(|(_, incoming)| *incoming)
                    .collect::<BTreeSet<_>>();
                match incoming_values.len() {
                    0 => BTreeSet::new(),
                    1 => discover_runtime_roots(
                        body,
                        incoming_values.into_iter().next().unwrap_or(value),
                        bindings,
                        discovery,
                        depth.saturating_sub(1),
                        visiting,
                    ),
                    _ => {
                        let ordered = conditional_phi_inputs(body, &incoming_edges).map_or_else(
                            || incoming_values.into_iter().collect::<Vec<_>>(),
                            |(condition, if_true, if_false)| vec![condition, if_true, if_false],
                        );
                        let mut roots = BTreeSet::new();
                        for incoming in ordered {
                            roots.extend(discover_runtime_roots(
                                body,
                                incoming,
                                bindings,
                                discovery,
                                depth.saturating_sub(1),
                                visiting,
                            ));
                        }
                        roots
                    }
                }
            }
        }
        ValueDef::Operator(op, arg_ref, _) => {
            let mut dependencies = BTreeSet::new();
            for argument in &body.arg_pool[*arg_ref] {
                dependencies.extend(discover_runtime_roots(
                    body,
                    *argument,
                    bindings,
                    discovery,
                    depth.saturating_sub(1),
                    visiting,
                ));
            }
            if is_runtime_boundary(op) {
                let name = format!("$runtime{}", discovery.ordered.len());
                discovery.names.insert(value, name);
                discovery.ordered.push(value);
                discovery.dependencies.insert(value, dependencies);
                [value].into_iter().collect()
            } else {
                dependencies
            }
        }
        ValueDef::PickOutput(source, _, _) | ValueDef::Alias(source) => discover_runtime_roots(
            body,
            *source,
            bindings,
            discovery,
            depth.saturating_sub(1),
            visiting,
        ),
        ValueDef::Placeholder(_) | ValueDef::None => BTreeSet::new(),
    };
    visiting.remove(&value);
    roots
}

fn semantic_expression_for(
    body: &FunctionBody,
    value: Value,
    bindings: &BTreeMap<Value, String>,
    call_names: &SemanticCallNames,
    runtime_names: &BTreeMap<Value, String>,
    expanded_runtime: Option<Value>,
) -> SemanticExpression {
    let mut context = SemanticExpressionContext {
        bindings,
        call_names,
        runtime_names,
        expanded_runtime,
        visiting: BTreeSet::new(),
        expanded: BTreeSet::new(),
    };
    build_semantic_expression(body, value, 48, &mut context)
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
    let mut discovery = RuntimeDiscovery::default();
    let mut discovered_returns = Vec::new();
    for (_, block) in body.blocks.entries() {
        let Terminator::Return { values } = &block.terminator else {
            continue;
        };
        for value in values {
            let resolved = body.resolve_alias(*value);
            let dependencies = discover_runtime_roots(
                body,
                resolved,
                bindings,
                &mut discovery,
                48,
                &mut BTreeSet::new(),
            );
            discovered_returns.push((resolved, dependencies));
        }
    }

    let mut runtime_bindings = Vec::new();
    for value in &discovery.ordered {
        let semantic_ir = semantic_expression_for(
            body,
            *value,
            bindings,
            call_names,
            &discovery.names,
            Some(*value),
        );
        let normalized_semantic_ir = normalize_semantic_expression(&semantic_ir);
        runtime_bindings.push(SemanticRuntimeBindingReport {
            value: value.index(),
            name: discovery.names[value].clone(),
            expression: render_semantic_expression(&semantic_ir),
            semantic_ir,
            normalized_semantic_ir,
            runtime_dependencies: discovery
                .dependencies
                .get(value)
                .into_iter()
                .flatten()
                .map(|dependency| dependency.index())
                .collect(),
        });
    }

    let mut returns = Vec::new();
    for (resolved, dependencies) in discovered_returns {
        let semantic_ir =
            semantic_expression_for(body, resolved, bindings, call_names, &discovery.names, None);
        let normalized_semantic_ir = normalize_semantic_expression(&semantic_ir);
        let report = SemanticReturnReport {
            value: resolved.index(),
            expression: render_semantic_expression(&semantic_ir),
            semantic_ir,
            normalized_semantic_ir,
            runtime_dependencies: dependencies
                .iter()
                .map(|dependency| dependency.index())
                .collect(),
        };
        if !returns.contains(&report) {
            returns.push(report);
        }
    }
    (returns, runtime_bindings, discovery.names)
}
