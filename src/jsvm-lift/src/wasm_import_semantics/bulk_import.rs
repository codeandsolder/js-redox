use super::{
    exact_zero, expression_is_symbol, expression_property_name, global_constructor,
    parameter_symbols, static_member_of_symbol, symbol_binding_is_stable, unparenthesized,
};
use oxc_ast::ast::{Argument, Expression, Function, Statement};
use oxc_semantic::Scoping;
use oxc_syntax::symbol::SymbolId;
use serde::Serialize;
use std::collections::HashMap;

/// Proven syntax-level semantics for a simple WebAssembly import handler.
///
/// These proofs deliberately describe only the JavaScript handler body. They do not prove
/// that the handler belongs to a particular recovered module; cross-stage correlation owns that join.
#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum WasmImportHandlerSemantic {
    PropertyGetter {
        receiver_param: usize,
        property: &'static str,
        standard_builtin_semantics_required: bool,
    },
    Uint32ArrayConstructor {
        source_param: usize,
        element_width_bits: u8,
        global_object: String,
        standard_builtin_semantics_required: bool,
    },
    TypedArraySet {
        receiver_param: usize,
        source_param: usize,
        offset_param: usize,
        offset_to_u32_proven: bool,
        normal_return_set_call_proven: bool,
        standard_builtin_semantics_required: bool,
    },
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmImportHandlerShape {
    pub import_module: Option<String>,
    pub import_name: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
    #[serde(flatten)]
    pub semantic: WasmImportHandlerSemantic,
}

fn stable_parameters(function: &Function<'_>, scoping: &Scoping) -> Option<Vec<SymbolId>> {
    if function.r#async || function.generator {
        return None;
    }
    let params = parameter_symbols(function)?;
    params
        .iter()
        .all(|symbol| symbol_binding_is_stable(scoping, *symbol))
        .then_some(params)
}

fn single_return_expression<'a>(function: &'a Function<'a>) -> Option<&'a Expression<'a>> {
    let body = function.body.as_ref()?;
    let [Statement::ReturnStatement(statement)] = body.statements.as_slice() else {
        return None;
    };
    statement.argument.as_ref()
}

fn single_expression<'a>(function: &'a Function<'a>) -> Option<&'a Expression<'a>> {
    let body = function.body.as_ref()?;
    let [Statement::ExpressionStatement(statement)] = body.statements.as_slice() else {
        return None;
    };
    Some(&statement.expression)
}

fn property_getter(
    function: &Function<'_>,
    scoping: &Scoping,
) -> Option<WasmImportHandlerSemantic> {
    let params = stable_parameters(function, scoping)?;
    let [receiver] = params.as_slice() else {
        return None;
    };
    let expression = single_return_expression(function)?;
    for property in ["buffer", "length"] {
        if static_member_of_symbol(scoping, expression, *receiver, property) {
            return Some(WasmImportHandlerSemantic::PropertyGetter {
                receiver_param: 0,
                property,
                standard_builtin_semantics_required: true,
            });
        }
    }
    None
}

fn uint32_array_constructor(
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
) -> Option<WasmImportHandlerSemantic> {
    let params = stable_parameters(function, scoping)?;
    let [source] = params.as_slice() else {
        return None;
    };
    let Expression::NewExpression(new_expression) =
        unparenthesized(single_return_expression(function)?)
    else {
        return None;
    };
    let global = global_constructor(
        scoping,
        global_aliases,
        &new_expression.callee,
        "Uint32Array",
    )?;
    let [argument] = new_expression.arguments.as_slice() else {
        return None;
    };
    let source_expression = argument.as_expression()?;
    expression_is_symbol(scoping, source_expression, *source).then_some(
        WasmImportHandlerSemantic::Uint32ArrayConstructor {
            source_param: 0,
            element_width_bits: 32,
            global_object: global,
            standard_builtin_semantics_required: true,
        },
    )
}

fn u32_coerced_symbol(scoping: &Scoping, argument: &Argument<'_>, symbol: SymbolId) -> bool {
    let Some(expression) = argument.as_expression() else {
        return false;
    };
    let Expression::BinaryExpression(binary) = unparenthesized(expression) else {
        return false;
    };
    binary.operator.as_str() == ">>>"
        && expression_is_symbol(scoping, &binary.left, symbol)
        && exact_zero(&binary.right)
}

fn typed_array_set(
    function: &Function<'_>,
    scoping: &Scoping,
) -> Option<WasmImportHandlerSemantic> {
    let params = stable_parameters(function, scoping)?;
    let [receiver, source, offset] = params.as_slice() else {
        return None;
    };
    let Expression::CallExpression(call) = unparenthesized(single_expression(function)?) else {
        return None;
    };
    if call.optional || call.arguments.len() != 2 || call.arguments.iter().any(Argument::is_spread)
    {
        return None;
    }
    if expression_property_name(&call.callee) != Some("set") {
        return None;
    }
    let call_receiver = match unparenthesized(&call.callee) {
        Expression::StaticMemberExpression(member) if !member.optional => &member.object,
        Expression::ComputedMemberExpression(member) if !member.optional => &member.object,
        _ => return None,
    };
    let source_argument = call.arguments[0].as_expression()?;
    if !expression_is_symbol(scoping, call_receiver, *receiver)
        || !expression_is_symbol(scoping, source_argument, *source)
        || !u32_coerced_symbol(scoping, &call.arguments[1], *offset)
    {
        return None;
    }
    Some(WasmImportHandlerSemantic::TypedArraySet {
        receiver_param: 0,
        source_param: 1,
        offset_param: 2,
        offset_to_u32_proven: true,
        normal_return_set_call_proven: true,
        standard_builtin_semantics_required: true,
    })
}

pub(super) fn analyze_import_handler(
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
) -> Option<WasmImportHandlerSemantic> {
    uint32_array_constructor(function, scoping, global_aliases)
        .or_else(|| typed_array_set(function, scoping))
        .or_else(|| property_getter(function, scoping))
}
