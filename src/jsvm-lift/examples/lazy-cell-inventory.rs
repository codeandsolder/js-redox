use anyhow::{Context, Result};
use jsvm_lift::{
    lazy_cell::{
        proven_slow_lazy_cell_factory_call, proven_slow_lazy_cell_update_state,
        structurally_proven_slow_lazy_cell_factory_shapes,
    },
    receiver_identity::structurally_proven_origin_flow,
};
use oxc_allocator::Allocator;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde_json::json;
use std::{env, fs, path::PathBuf};

fn snippet(source: &str, start: u32, end: u32) -> String {
    source
        .get(start as usize..(end as usize).min(source.len()))
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn main() -> Result<()> {
    let path = env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .context("usage: cargo run -p jsvm-lift --example lazy-cell-inventory -- <file.js>")?;
    let source =
        fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &source, SourceType::cjs());
    anyhow::ensure!(parsed.is_clean(), "parse diagnostics");
    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .with_check_syntax_error(true)
        .build(&parsed.program);
    anyhow::ensure!(semantic.diagnostics.is_empty(), "semantic diagnostics");
    let scoping = semantic.semantic.scoping();

    let shapes = structurally_proven_slow_lazy_cell_factory_shapes(&parsed.program, scoping);
    let shape_json = shapes
        .iter()
        .map(|shape| {
            let phase = scoping.symbol_span(shape.phase_binding_symbol);
            let phase_local = scoping.symbol_span(shape.phase_local_symbol);
            let index_state = scoping.symbol_span(shape.index_state_symbol);
            json!({
                "function": [shape.function_start, shape.function_end],
                "guard": [shape.guard_start, shape.guard_end],
                "guard_source": snippet(&source, shape.guard_start, shape.guard_end),
                "slow_sequence": [shape.slow_sequence_start, shape.slow_sequence_end],
                "state_parameter_index": shape.state_parameter_index,
                "handler_parameter_index": shape.handler_parameter_index,
                "handler_slot": shape.handler_slot,
                "handler_capture": [shape.handler_capture_start, shape.handler_capture_end],
                "handler_capture_source": snippet(&source, shape.handler_capture_start, shape.handler_capture_end),
                "index_state_declaration": [index_state.start, index_state.end],
                "index_state_initialization": [shape.index_state_initialization_start, shape.index_state_initialization_end],
                "index_state_initialization_source": snippet(&source, shape.index_state_initialization_start, shape.index_state_initialization_end),
                "prototype_field": shape.prototype_field,
                "method_key_field": shape.method_key_field,
                "phase_local_declaration": [phase_local.start, phase_local.end],
                "phase_binding_declaration": [phase.start, phase.end],
                "phase_capture": [shape.phase_capture_start, shape.phase_capture_end],
                "phase_capture_source": snippet(&source, shape.phase_capture_start, shape.phase_capture_end),
                "cell_construction": [shape.cell_construction_start, shape.cell_construction_end],
                "cell_construction_source": snippet(&source, shape.cell_construction_start, shape.cell_construction_end),
                "update_function": [shape.update_function_start, shape.update_function_end],
                "resolver_property": shape.resolver_property,
                "resolver_function": [shape.resolver_function_start, shape.resolver_function_end],
            })
        })
        .collect::<Vec<_>>();

    let flow = structurally_proven_origin_flow(&parsed.program, scoping);
    let candidate_calls = flow
        .direct_calls
        .iter()
        .filter(|call| {
            shapes.iter().any(|shape| {
                shape.function_start == call.callee.function_start
                    && shape.function_end == call.callee.function_end
            })
        })
        .map(|call| {
            let specialized = proven_slow_lazy_cell_factory_call(
                &source,
                &parsed.program,
                &semantic.semantic,
                call,
            );
            let update = specialized.as_ref().and_then(|factory| {
                proven_slow_lazy_cell_update_state(&parsed.program, &semantic.semantic, factory)
            });
            json!({
                "call": [call.call_start, call.call_end],
                "call_source": snippet(&source, call.call_start, call.call_end),
                "caller": [call.caller.function_start, call.caller.function_end],
                "callee": [call.callee.function_start, call.callee.function_end],
                "allocation": [call.callee.allocation_start, call.callee.allocation_end],
                "constructor": [call.callee.constructor_start, call.callee.constructor_end],
                "origin_parameter_indices": call.callee.parameter_indices,
                "exact_integer_arguments": call.exact_integer_arguments,
                "specialized": specialized.is_some(),
                "update": update.as_ref().map(|update| json!({
                    "initial_state_value": update.initial_state_value,
                    "post_update_state_value": update.post_update_state_value,
                    "selector_capture": scoping.symbol_name(update.selector_capture_symbol),
                    "update_parameter": scoping.symbol_name(update.update_parameter_symbol),
                })),
            })
        })
        .collect::<Vec<_>>();
    let specialized_calls = candidate_calls
        .iter()
        .filter(|call| call["specialized"] == true)
        .cloned()
        .collect::<Vec<_>>();

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "shapes": shape_json,
            "candidate_calls": candidate_calls,
            "specialized_calls": specialized_calls,
        }))?
    );
    Ok(())
}
