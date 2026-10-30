use anyhow::{Context, Result};
use jsvm_lift::{
    forwarding_semantics::structurally_proven_lazy_registry_read_calls,
    lazy_cell::{
        proven_slow_lazy_cell_captured_handler_install,
        proven_slow_lazy_cell_exact_registry_assignments, proven_slow_lazy_cell_factory_call,
        proven_slow_lazy_cell_prototype_carrier, proven_slow_lazy_cell_registry_assignment,
        proven_slow_lazy_cell_resolved_handler, proven_slow_lazy_cell_resolver_index,
        proven_slow_lazy_cell_state_fields,
        proven_slow_lazy_cell_state_fields_for_exact_assignment,
        proven_slow_lazy_cell_update_state, structurally_proven_slow_lazy_cell_factory_shapes,
    },
    receiver_identity::structurally_proven_origin_flow,
    registry_identity::proven_origin_registry_handler_installs,
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
    let mut args = env::args_os();
    let _program = args.next();
    let path = args.next().map(PathBuf::from).context(
        "usage: cargo run -p jsvm-lift --example lazy-cell-inventory -- <file.js> [--phase-value=N]",
    )?;
    let mut phase_value = None;
    for argument in args {
        let argument = argument.to_string_lossy();
        if let Some(value) = argument.strip_prefix("--phase-value=") {
            phase_value = Some(value.parse::<i64>().context("invalid phase value")?);
        } else {
            anyhow::bail!("unknown argument: {argument}");
        }
    }
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

    let lazy_reads = structurally_proven_lazy_registry_read_calls(&parsed.program, scoping);
    let accessor = lazy_reads.first().filter(|first| {
        lazy_reads.iter().all(|read| {
            read.accessor_function_start == first.accessor_function_start
                && read.accessor_function_end == first.accessor_function_end
                && read.read.registry_path.as_slice() == first.read.registry_path.as_slice()
                && read.update_property == first.update_property
                && read.projection_property == first.projection_property
                && read.selector_key_symbol == first.selector_key_symbol
                && read.selector_polynomial == first.selector_polynomial
        })
    });

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
    let origin_installs = proven_origin_registry_handler_installs(&parsed.program, scoping, &flow);
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
            let state_fields = specialized.as_ref().and_then(|factory| {
                proven_slow_lazy_cell_state_fields(
                    &source,
                    &parsed.program,
                    &semantic.semantic,
                    factory,
                )
            });
            let registry = specialized.as_ref().and_then(|factory| {
                proven_slow_lazy_cell_registry_assignment(
                    &parsed.program,
                    &semantic.semantic,
                    factory,
                )
            });
            let exact_assignments = registry
                .as_ref()
                .map(|registry| {
                    proven_slow_lazy_cell_exact_registry_assignments(
                        &source,
                        &parsed.program,
                        &semantic.semantic,
                        &flow,
                        registry,
                    )
                })
                .unwrap_or_default();
            let path_state_fields = exact_assignments
                .iter()
                .filter_map(|exact_assignment| {
                    proven_slow_lazy_cell_state_fields_for_exact_assignment(
                        &source,
                        &parsed.program,
                        &semantic.semantic,
                        exact_assignment,
                    )
                    .map(|fields| (exact_assignment.exact_key_value, fields))
                })
                .collect::<Vec<_>>();
            let carrier_proofs = accessor
                .map(|accessor| {
                    path_state_fields
                        .iter()
                        .filter_map(|(key, fields)| {
                            proven_slow_lazy_cell_prototype_carrier(
                                &source,
                                &parsed.program,
                                &semantic.semantic,
                                fields,
                                accessor,
                            )
                            .map(|proof| (*key, proof))
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            let mut captured_handlers = Vec::new();
            for exact_assignment in &exact_assignments {
                for install in &origin_installs {
                    if let Some(proof) = proven_slow_lazy_cell_captured_handler_install(
                        &source,
                        &parsed.program,
                        &semantic.semantic,
                        exact_assignment,
                        install,
                    ) {
                        captured_handlers.push(proof);
                    }
                }
            }
            let resolver_proofs = match (&update, accessor, phase_value) {
                (Some(update), Some(accessor), Some(phase_value)) => exact_assignments
                    .iter()
                    .filter_map(|exact_assignment| {
                        proven_slow_lazy_cell_resolver_index(
                            &source,
                            &parsed.program,
                            &semantic.semantic,
                            update,
                            accessor.selector_start,
                            accessor.selector_end,
                            accessor.selector_key_symbol,
                            exact_assignment,
                            phase_value,
                        )
                    })
                    .collect::<Vec<_>>(),
                _ => Vec::new(),
            };
            let mut resolved_handlers = Vec::new();
            for resolver in &resolver_proofs {
                for captured in &captured_handlers {
                    if let Some(proof) = proven_slow_lazy_cell_resolved_handler(resolver, captured) {
                        resolved_handlers.push(proof);
                    }
                }
            }
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
                "state_fields": state_fields.as_ref().map(|fields| json!({
                    "prototype_field": fields.prototype_field.initialization.property,
                    "prototype_write": [
                        fields.prototype_field.initialization.write_start,
                        fields.prototype_field.initialization.write_end,
                    ],
                    "method_key_field": fields.method_key.string.assignment.property,
                    "method_key_value": fields.method_key.string.assignment.value,
                })),
                "update": update.as_ref().map(|update| json!({
                    "initial_state_value": update.initial_state_value,
                    "post_update_state_value": update.post_update_state_value,
                    "selector_capture": scoping.symbol_name(update.selector_capture_symbol),
                    "update_parameter": scoping.symbol_name(update.update_parameter_symbol),
                })),
                "registry_assignment": registry.as_ref().map(|registry| json!({
                    "path": registry.registry_path,
                    "receiver": [registry.receiver_start, registry.receiver_end],
                    "key": [registry.key_start, registry.key_end],
                    "key_source": snippet(&source, registry.key_start, registry.key_end),
                    "registry_key_symbol": scoping.symbol_name(registry.registry_key_symbol),
                    "factory_key_parameter_index": registry.factory_key_parameter_index,
                    "factory_key_symbol": scoping.symbol_name(registry.factory_key_symbol),
                })),
                "exact_registry_assignments": exact_assignments.iter().map(|proof| json!({
                    "caller": [proof.caller.call_start, proof.caller.call_end],
                    "provenance": proof.provenance_calls.iter().map(|call| {
                        [call.call_start, call.call_end]
                    }).collect::<Vec<_>>(),
                    "exact_key_value": proof.exact_key_value,
                })).collect::<Vec<_>>(),
                "path_state_fields": path_state_fields.iter().map(|(key, fields)| json!({
                    "exact_key_value": key,
                    "prototype_field": fields.prototype_field.initialization.property,
                    "method_key_value": fields.method_key.string.assignment.value,
                })).collect::<Vec<_>>(),
                "carrier_proofs": carrier_proofs.iter().map(|(key, proof)| json!({
                    "exact_key_value": key,
                    "method_name": proof.method_name,
                    "projection_property": proof.projection_property,
                    "resolver_property": proof.resolver_property,
                    "helper_call": [proof.helper_call_start, proof.helper_call_end],
                    "helper_create": [proof.helper_create_start, proof.helper_create_end],
                    "getter": [proof.getter_function_start, proof.getter_function_end],
                    "standard_object_prototype_semantics_required": proof.standard_object_prototype_semantics_required,
                })).collect::<Vec<_>>(),
                "captured_handlers": captured_handlers.iter().map(|proof| json!({
                    "exact_key_value": proof.exact_assignment.exact_key_value,
                    "logical_install": [proof.install.install.call_start, proof.install.install.call_end],
                    "handler": [proof.install.install.handler_start, proof.install.install.handler_end],
                    "handler_source": snippet(
                        &source,
                        proof.install.install.handler_start,
                        proof.install.install.handler_end,
                    ),
                    "caller_handler_parameter_index": proof.caller_handler_parameter_index,
                    "caller_handler_symbol": scoping.symbol_name(proof.caller_handler_symbol),
                })).collect::<Vec<_>>(),
                "resolver_proofs": resolver_proofs.iter().map(|resolver| json!({
                    "phase_value": resolver.phase_value,
                    "exact_key_value": resolver.exact_key_value,
                    "handler_slot": resolver.handler_slot,
                    "index_assignment": [resolver.index_assignment_start, resolver.index_assignment_end],
                    "index_assignment_source": snippet(
                        &source,
                        resolver.index_assignment_start,
                        resolver.index_assignment_end,
                    ),
                })).collect::<Vec<_>>(),
                "resolved_handlers": resolved_handlers.iter().map(|proof| json!({
                    "exact_key_value": proof.resolver.exact_key_value,
                    "handler_slot": proof.resolver.handler_slot,
                    "logical_handler": [
                        proof.captured_handler.install.install.handler_start,
                        proof.captured_handler.install.install.handler_end,
                    ],
                })).collect::<Vec<_>>(),
            })
        })
        .collect::<Vec<_>>();
    let specialized_calls = candidate_calls
        .iter()
        .filter(|call| call["specialized"] == true)
        .cloned()
        .collect::<Vec<_>>();
    let state_field_proven_calls = candidate_calls
        .iter()
        .filter(|call| !call["state_fields"].is_null())
        .count();
    let resolver_proven_calls = candidate_calls
        .iter()
        .map(|call| call["resolver_proofs"].as_array().map_or(0, Vec::len))
        .sum::<usize>();
    let resolved_handler_proofs = candidate_calls
        .iter()
        .map(|call| call["resolved_handlers"].as_array().map_or(0, Vec::len))
        .sum::<usize>();
    let accessor_json = accessor.map(|accessor| {
        json!({
            "call_count": lazy_reads.len(),
            "function": [accessor.accessor_function_start, accessor.accessor_function_end],
            "registry_path": accessor.read.registry_path,
            "update_property": accessor.update_property,
            "projection_property": accessor.projection_property,
            "selector": [accessor.selector_start, accessor.selector_end],
            "selector_source": snippet(&source, accessor.selector_start, accessor.selector_end),
            "selector_key_symbol": scoping.symbol_name(accessor.selector_key_symbol),
        })
    });

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "phase_value": phase_value,
            "lazy_accessor": accessor_json,
            "shapes": shape_json,
            "candidate_calls": candidate_calls,
            "specialized_calls": specialized_calls,
            "origin_handler_installs": origin_installs.len(),
            "state_field_proven_calls": state_field_proven_calls,
            "resolver_proven_calls": resolver_proven_calls,
            "resolved_handler_proofs": resolved_handler_proofs,
        }))?
    );
    Ok(())
}
