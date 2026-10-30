use anyhow::{Context, Result};
use jsvm_lift::cfg_order::prove_event_before_barriers;
use jsvm_lift::{
    cfg_order::prove_events_before_event,
    receiver_identity::{
        propagate_matched_prototype_method_call_origins,
        propagate_proven_prototype_method_call_origins,
        proven_origin_direct_call_event_unreachable, proven_own_data_field_at_runtime_method_call,
        proven_prototype_method_receiver_preservation_summary,
        proven_prototype_string_at_allocation, proven_prototype_string_at_direct_calls,
        proven_receiver_preserving_prototype_method_call,
        structurally_matched_prototype_method_calls, structurally_proven_origin_flow,
        structurally_proven_own_data_field_initializations,
        structurally_proven_own_data_fields_at_member_calls,
        structurally_proven_prototype_method_calls_at_runtime,
        structurally_proven_prototype_method_lookup_targets,
        structurally_proven_prototype_method_receiver_effects,
        structurally_proven_prototype_string_assignments,
        structurally_proven_receiver_preserving_prototype_method_calls,
    },
    registry_identity::{
        proven_origin_registry_handler_installs, proven_origin_registry_read_calls,
    },
    table_vm,
};
use oxc_allocator::Allocator;
use oxc_semantic::SemanticBuilder;
use oxc_span::{SourceType, Span};
use rolldown_redox::ecmascript::parse_program;
use serde_json::{json, Value};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

fn snippet(source: &str, start: u32, end: u32) -> String {
    source
        .get(start as usize..(end as usize).min(source.len()))
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn main() -> Result<()> {
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    let summary = args.iter().any(|arg| arg == "--summary");
    let runtime_only = args.iter().any(|arg| arg == "--runtime-only");
    let prototype_strings_only = args.iter().any(|arg| arg == "--prototype-strings");
    let preserve_call_start = args.iter().find_map(|arg| {
        arg.to_str()?
            .strip_prefix("--preserve-call-start=")?
            .parse::<u32>()
            .ok()
    });
    let fully_preserve_call_start = args.iter().find_map(|arg| {
        arg.to_str()?
            .strip_prefix("--fully-preserve-call-start=")?
            .parse::<u32>()
            .ok()
    });
    let field_runtime_call_start = args.iter().find_map(|arg| {
        arg.to_str()?
            .strip_prefix("--field-runtime-call-start=")?
            .parse::<u32>()
            .ok()
    });
    let registry_origin_call_start = args.iter().find_map(|arg| {
        arg.to_str()?
            .strip_prefix("--registry-origin-call-start=")?
            .parse::<u32>()
            .ok()
    });
    let field_property = args
        .iter()
        .find_map(|arg| arg.to_str()?.strip_prefix("--field=").map(str::to_owned));
    let path = args
        .iter()
        .find(|arg| !arg.to_string_lossy().starts_with("--"))
        .map(PathBuf::from)
        .context(
            "usage: cargo run -p jsvm-lift --example receiver-proof-inventory -- <file.js> [--summary] [--runtime-only] [--preserve-call-start=N] [--fully-preserve-call-start=N] [--field-runtime-call-start=N --field=NAME] [--registry-origin-call-start=N]",
        )?;
    let source =
        fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &source, SourceType::cjs());
    anyhow::ensure!(
        parsed.diagnostics == 0 && !parsed.fatal_error,
        "parse diagnostics"
    );
    let semantic = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .with_check_syntax_error(true)
        .build(&parsed.program);
    anyhow::ensure!(semantic.diagnostics.is_empty(), "semantic diagnostics");
    let scoping = semantic.semantic.scoping();
    if prototype_strings_only {
        let strings = structurally_proven_prototype_string_assignments(&parsed.program, scoping)
            .into_iter()
            .map(|assignment| {
                json!({
                    "constructor": [assignment.constructor_start, assignment.constructor_end],
                    "property": assignment.property,
                    "value": assignment.value,
                    "assignment": [assignment.assignment_start, assignment.assignment_end],
                })
            })
            .collect::<Vec<_>>();
        println!("{}", serde_json::to_string_pretty(&strings)?);
        return Ok(());
    }
    if let Some(call_start) = registry_origin_call_start {
        let mut targets = structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        )
        .into_iter()
        .filter(|proof| proof.candidate.call.call_start == call_start);
        let target = targets
            .next()
            .context("no runtime-proven method call at requested start")?;
        anyhow::ensure!(
            targets.next().is_none(),
            "ambiguous runtime method call start"
        );
        let seeded =
            propagate_proven_prototype_method_call_origins(&parsed.program, scoping, &target);
        let base = structurally_proven_origin_flow(&parsed.program, scoping);
        let target_origin = (
            target.candidate.call.allocation_start,
            target.candidate.call.allocation_end,
            target.candidate.call.constructor_start,
            target.candidate.call.constructor_end,
        );
        let prototype_strings_at_allocation = structurally_proven_prototype_string_assignments(
            &parsed.program,
            scoping,
        )
        .into_iter()
        .filter(|assignment| {
            assignment.constructor_start == target_origin.2
                && assignment.constructor_end == target_origin.3
        })
        .filter_map(|assignment| {
            proven_prototype_string_at_allocation(
                &parsed.program,
                &semantic.semantic,
                target_origin.2,
                target_origin.3,
                Span::new(target_origin.0, target_origin.1),
                &assignment.property,
            )
        })
        .map(|proof| {
            json!({
                "property": proof.assignment.property,
                "value": proof.assignment.value,
                "assignment": [proof.assignment.assignment_start, proof.assignment.assignment_end],
            })
        })
        .collect::<Vec<_>>();
        let prototype_string_direct_calls =
            structurally_proven_prototype_string_assignments(&parsed.program, scoping)
                .into_iter()
                .filter(|assignment| {
                    assignment.constructor_start == target_origin.2
                        && assignment.constructor_end == target_origin.3
                })
                .filter_map(|assignment| {
                    proven_prototype_string_at_allocation(
                        &parsed.program,
                        &semantic.semantic,
                        target_origin.2,
                        target_origin.3,
                        Span::new(target_origin.0, target_origin.1),
                        &assignment.property,
                    )
                })
                .flat_map(|string| {
                    proven_prototype_string_at_direct_calls(
                &source,
                &parsed.program,
                &semantic.semantic,
                &string,
            )
            .into_iter()
            .map(move |proof| {
                json!({
                    "property": proof.string.assignment.property,
                    "value": proof.string.assignment.value,
                    "call": [proof.call.call_start, proof.call.call_end],
                    "caller": [proof.call.caller.function_start, proof.call.caller.function_end],
                    "callee": [proof.call.callee.function_start, proof.call.callee.function_end],
                    "exact_integer_arguments": proof.call.exact_integer_arguments,
                })
            })
                })
                .collect::<Vec<_>>();
        let reads = proven_origin_registry_read_calls(&parsed.program, scoping, &seeded)
            .into_iter()
            .filter(|proof| {
                (
                    proof.origin.allocation_start,
                    proof.origin.allocation_end,
                    proof.origin.constructor_start,
                    proof.origin.constructor_end,
                ) == target_origin
            })
            .map(|proof| {
                json!({
                    "call": [proof.read.call_start, proof.read.call_end],
                    "receiver": [proof.read.receiver_start, proof.read.receiver_end],
                    "key_span": [proof.read.key_start, proof.read.key_end],
                    "exact_key": proof.exact_key,
                    "registry_path": proof.read.registry_path,
                })
            })
            .collect::<Vec<_>>();
        let table_analysis =
            table_vm::analyze_with_registry_origins(&source, &parsed.program, &base, &seeded);
        let origin_prefix = format!(
            "origin@{}-{}:{}-{}",
            target_origin.0, target_origin.1, target_origin.2, target_origin.3
        );
        let origin_tables = table_analysis
            .handler_function_tables
            .iter()
            .filter(|table| table.binding.starts_with(&origin_prefix))
            .map(|table| {
                json!({
                    "binding": table.binding,
                    "entries": table.entries,
                    "function_values": table.function_values,
                    "read_sites": table.read_sites,
                    "dynamic_read_sites": table.dynamic_read_sites,
                    "dynamic_call_sites": table.dynamic_call_sites,
                    "looped_dynamic_call_sites": table.looped_dynamic_call_sites,
                })
            })
            .collect::<Vec<_>>();
        let installs = proven_origin_registry_handler_installs(&parsed.program, scoping, &base)
            .into_iter()
            .filter(|proof| {
                (
                    proof.origin.allocation_start,
                    proof.origin.allocation_end,
                    proof.origin.constructor_start,
                    proof.origin.constructor_end,
                ) == target_origin
            })
            .map(|proof| {
                json!({
                    "call": [proof.install.call_start, proof.install.call_end],
                    "receiver": [proof.install.receiver_start, proof.install.receiver_end],
                    "key_span": [proof.install.key_start, proof.install.key_end],
                    "exact_key": proof.exact_key,
                    "registry_path": proof.install.registry_path,
                    "handler": [proof.install.handler_start, proof.install.handler_end],
                    "handler_params": proof.install.handler_params,
                    "handler_async": proof.install.handler_async,
                })
            })
            .collect::<Vec<_>>();
        println!(
            "{}",
            serde_json::to_string_pretty(&json!({
                "call": [target.candidate.call.call_start, target.candidate.call.call_end],
                "property": target.candidate.call.property,
                "allocation": [target.candidate.call.allocation_start, target.candidate.call.allocation_end],
                "registry_reads": reads,
                "registry_installs": installs,
                "origin_tables": origin_tables,
                "table_vms": table_analysis.table_vms,
                "prototype_strings_at_allocation": prototype_strings_at_allocation,
                "prototype_string_direct_calls": prototype_string_direct_calls,
            }))?
        );
        return Ok(());
    }
    if let Some(call_start) = fully_preserve_call_start {
        let mut targets = structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        )
        .into_iter()
        .filter(|proof| proof.candidate.call.call_start == call_start);
        let target = targets
            .next()
            .context("no runtime-proven method call at requested start")?;
        anyhow::ensure!(
            targets.next().is_none(),
            "ambiguous runtime method call start"
        );
        let proof = proven_receiver_preserving_prototype_method_call(
            &source,
            &parsed.program,
            &semantic.semantic,
            &target,
        )
        .map(|proof| {
            json!({
                "call": [proof.candidate.call.call_start, proof.candidate.call.call_end],
                "property": proof.candidate.call.property,
                "allocation": [proof.candidate.call.allocation_start, proof.candidate.call.allocation_end],
                "own_data_reads": proof.own_data_reads.iter().map(|field| json!({
                    "field": field.initialization.property,
                    "initialization": [field.initialization.write_start, field.initialization.write_end],
                    "direct_call_path": field.direct_call_path.iter().map(|edge| [edge.call_start, edge.call_end]).collect::<Vec<_>>(),
                    "discharged_preserving_method_calls": field.discharged_preserving_method_calls.iter().map(|call| json!({
                        "call": [call.call_start, call.call_end],
                        "property": call.property,
                    })).collect::<Vec<_>>(),
                })).collect::<Vec<_>>(),
            })
        });
        println!("{}", serde_json::to_string_pretty(&proof)?);
        return Ok(());
    }
    if let Some(call_start) = field_runtime_call_start {
        let property = field_property
            .as_deref()
            .context("--field-runtime-call-start requires --field=NAME")?;
        let mut targets = structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        )
        .into_iter()
        .filter(|proof| proof.candidate.call.call_start == call_start);
        let target = targets
            .next()
            .context("no runtime-proven method call at requested start")?;
        anyhow::ensure!(
            targets.next().is_none(),
            "ambiguous runtime method call start"
        );
        let proof = proven_own_data_field_at_runtime_method_call(
            &source,
            &parsed.program,
            &semantic.semantic,
            &target,
            property,
        )
        .map(|proof| {
            let call = &proof.call_target.candidate.call;
            json!({
                "field": proof.initialization.property,
                "initialization": [proof.initialization.write_start, proof.initialization.write_end],
                "call": [call.call_start, call.call_end],
                "property": call.property,
                "allocation": [call.allocation_start, call.allocation_end],
                "direct_call_path": proof.direct_call_path.iter().map(|edge| json!({
                    "call": [edge.call_start, edge.call_end],
                    "caller": [edge.caller.function_start, edge.caller.function_end],
                    "callee": [edge.callee.function_start, edge.callee.function_end],
                    "standard_function_call_semantics_required": edge.standard_function_call_semantics_required,
                })).collect::<Vec<_>>(),
                "discharged_preserving_method_calls": proof.discharged_preserving_method_calls.iter().map(|crossed| json!({
                    "call": [crossed.call_start, crossed.call_end],
                    "property": crossed.property,
                    "function": [crossed.context.function_start, crossed.context.function_end],
                })).collect::<Vec<_>>(),
                "standard_function_call_semantics_required": proof.standard_function_call_semantics_required,
            })
        });
        println!("{}", serde_json::to_string_pretty(&proof)?);
        return Ok(());
    }
    if let Some(call_start) = preserve_call_start {
        let mut matches = structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        )
        .into_iter()
        .filter(|proof| proof.candidate.call.call_start == call_start);
        let target = matches
            .next()
            .context("no runtime-proven method call at requested start")?;
        anyhow::ensure!(
            matches.next().is_none(),
            "ambiguous runtime method call start"
        );
        let summary = proven_prototype_method_receiver_preservation_summary(
            &source,
            &parsed.program,
            &semantic.semantic,
            &target,
        )
        .map(|summary| {
            let candidate = &summary.call_target.candidate;
            json!({
                "call": [candidate.call.call_start, candidate.call.call_end],
                "property": candidate.call.property,
                "allocation": [candidate.call.allocation_start, candidate.call.allocation_end],
                "assignment": [candidate.lookup_target.assignment_start, candidate.lookup_target.assignment_end],
                "required_own_data_fields": summary.required_own_data_fields,
                "standard_function_call_semantics_required": summary.standard_function_call_semantics_required,
                "standard_prototype_semantics_required": summary.call_target.standard_prototype_semantics_required,
            })
        });
        println!("{}", serde_json::to_string_pretty(&summary)?);
        return Ok(());
    }
    if runtime_only {
        let runtime_method_calls = structurally_proven_prototype_method_calls_at_runtime(
            &parsed.program,
            &semantic.semantic,
        )
        .into_iter()
        .map(|proof| {
            let candidate = proof.candidate;
            json!({
                "call": [candidate.call.call_start, candidate.call.call_end],
                "property": candidate.call.property,
                "allocation": [candidate.call.allocation_start, candidate.call.allocation_end],
                "constructor": [candidate.call.constructor_start, candidate.call.constructor_end],
                "assignment": [candidate.lookup_target.assignment_start, candidate.lookup_target.assignment_end],
                "method_functions": candidate.lookup_target.possible_functions.iter().map(|f| [f.function_start, f.function_end]).collect::<Vec<_>>(),
                "standard_prototype_semantics_required": proof.standard_prototype_semantics_required,
            })
        })
        .collect::<Vec<_>>();
        println!(
            "{}",
            serde_json::to_string_pretty(&json!({
                "file": path,
                "runtime_prototype_method_calls": runtime_method_calls,
            }))?
        );
        return Ok(());
    }
    let flow = structurally_proven_origin_flow(&parsed.program, scoping);
    let matched = structurally_matched_prototype_method_calls(&parsed.program, scoping);
    let lookup_targets =
        structurally_proven_prototype_method_lookup_targets(&parsed.program, scoping);
    let runtime_method_calls =
        structurally_proven_prototype_method_calls_at_runtime(&parsed.program, &semantic.semantic);
    let receiver_effects =
        structurally_proven_prototype_method_receiver_effects(&parsed.program, scoping);
    let own_data_fields =
        structurally_proven_own_data_field_initializations(&parsed.program, scoping);
    let own_data_fields_at_member_calls = structurally_proven_own_data_fields_at_member_calls(
        &source,
        &parsed.program,
        &semantic.semantic,
    );
    let receiver_preserving_method_calls =
        structurally_proven_receiver_preserving_prototype_method_calls(
            &source,
            &parsed.program,
            &semantic.semantic,
        );
    let runtime_method_calls = runtime_method_calls
        .iter()
        .map(|proof| {
            let candidate = &proof.candidate;
            json!({
                "call": [candidate.call.call_start, candidate.call.call_end],
                "property": candidate.call.property,
                "allocation": [candidate.call.allocation_start, candidate.call.allocation_end],
                "assignment": [candidate.lookup_target.assignment_start, candidate.lookup_target.assignment_end],
                "method_functions": candidate.lookup_target.possible_functions.iter().map(|f| [f.function_start, f.function_end]).collect::<Vec<_>>(),
                "standard_prototype_semantics_required": proof.standard_prototype_semantics_required,
            })
        })
        .collect::<Vec<_>>();

    let matched_method_origin_flows = if summary {
        Vec::new()
    } else {
        matched
        .iter()
        .map(|candidate| {
            let seeded = propagate_matched_prototype_method_call_origins(
                &parsed.program,
                scoping,
                candidate,
            );
            let direct_call_effect_checks = seeded
                .direct_calls
                .iter()
                .map(|call| {
                    let event_check = |start: u32, end: u32| {
                        proven_origin_direct_call_event_unreachable(
                            &source,
                            &parsed.program,
                            scoping,
                            call,
                            Span::new(start, end),
                        )
                    };
                    json!({
                        "call": [call.call_start, call.call_end],
                        "callee_function": [call.callee.function_start, call.callee.function_end],
                        "exact_integer_arguments": call.exact_integer_arguments,
                        "member_calls": seeded.member_calls.iter().filter(|event| event.context == call.callee).map(|event| json!({
                            "span": [event.call_start, event.call_end],
                            "property": event.property,
                            "unreachable": event_check(event.call_start, event.call_end),
                        })).collect::<Vec<_>>(),
                        "member_reads": seeded.member_reads.iter().filter(|event| event.context == call.callee).map(|event| json!({
                            "span": [event.read_start, event.read_end],
                            "property": event.property,
                            "unreachable": event_check(event.read_start, event.read_end),
                        })).collect::<Vec<_>>(),
                        "member_writes": seeded.member_writes.iter().filter(|event| event.context == call.callee).map(|event| json!({
                            "span": [event.write_start, event.write_end],
                            "property": event.property,
                            "operation": event.operation,
                            "unreachable": event_check(event.write_start, event.write_end),
                        })).collect::<Vec<_>>(),
                        "exposures": seeded.exposures.iter().filter(|event| event.context == call.callee).map(|event| json!({
                            "span": [event.exposure_start, event.exposure_end],
                            "kind": event.kind,
                            "unreachable": event_check(event.exposure_start, event.exposure_end),
                        })).collect::<Vec<_>>(),
                        "nested_direct_calls": seeded.direct_calls.iter().filter(|event| event.caller == call.callee).map(|event| json!({
                            "span": [event.call_start, event.call_end],
                            "callee_function": [event.callee.function_start, event.callee.function_end],
                            "unreachable": event_check(event.call_start, event.call_end),
                        })).collect::<Vec<_>>(),
                    })
                })
                .collect::<Vec<_>>();
            json!({
                "call": [candidate.call.call_start, candidate.call.call_end],
                "property": candidate.call.property,
                "direct_call_effect_checks": direct_call_effect_checks,
                "direct_calls": seeded.direct_calls.iter().map(|call| json!({
                    "call": [call.call_start, call.call_end],
                    "caller_function": [call.caller.function_start, call.caller.function_end],
                    "caller_context": {"this_origin": call.caller.this_origin, "parameter_indices": call.caller.parameter_indices},
                    "callee_function": [call.callee.function_start, call.callee.function_end],
                    "callee_context": {"this_origin": call.callee.this_origin, "parameter_indices": call.callee.parameter_indices},
                    "standard_function_call_semantics_required": call.standard_function_call_semantics_required,
                    "exact_integer_arguments": call.exact_integer_arguments,
                })).collect::<Vec<_>>(),
                "member_calls": seeded.member_calls.iter().map(|call| json!({
                    "call": [call.call_start, call.call_end],
                    "function": [call.context.function_start, call.context.function_end],
                    "context": {"this_origin": call.context.this_origin, "parameter_indices": call.context.parameter_indices},
                    "property": call.property,
                })).collect::<Vec<_>>(),
                "member_reads": seeded.member_reads.iter().map(|read| json!({
                    "read": [read.read_start, read.read_end],
                    "function": [read.context.function_start, read.context.function_end],
                    "context": {"this_origin": read.context.this_origin, "parameter_indices": read.context.parameter_indices},
                    "property": read.property,
                })).collect::<Vec<_>>(),
                "member_writes": seeded.member_writes.iter().map(|write| json!({
                    "write": [write.write_start, write.write_end],
                    "function": [write.context.function_start, write.context.function_end],
                    "context": {"this_origin": write.context.this_origin, "parameter_indices": write.context.parameter_indices},
                    "property": write.property,
                    "operation": write.operation,
                })).collect::<Vec<_>>(),
                "exposures": seeded.exposures.iter().map(|exposure| json!({
                    "span": [exposure.exposure_start, exposure.exposure_end],
                    "function": [exposure.context.function_start, exposure.context.function_end],
                    "context": {"this_origin": exposure.context.this_origin, "parameter_indices": exposure.context.parameter_indices},
                    "kind": exposure.kind,
                })).collect::<Vec<_>>(),
            })
        })
        .collect::<Vec<_>>()
    };

    let mut own_data_field_entry_dominance = Vec::new();
    for field in &own_data_fields {
        for call in flow
            .direct_calls
            .iter()
            .filter(|call| call.caller == field.context)
        {
            own_data_field_entry_dominance.push(json!({
                "field": field.property,
                "initialization": [field.write_start, field.write_end],
                "entry_call": [call.call_start, call.call_end],
                "caller_function": [call.caller.function_start, call.caller.function_end],
                "dominates": prove_events_before_event(
                    &semantic.semantic,
                    &[Span::new(field.write_start, field.write_end)],
                    Span::new(call.call_start, call.call_end),
                ),
            }));
        }
    }
    let direct_calls = flow
        .direct_calls
        .iter()
        .map(|call| {
            json!({
                "call_start": call.call_start,
                "call_end": call.call_end,
                "evaluation_order": call.evaluation_order,
                "call": snippet(&source, call.call_start, call.call_end),
                "caller_function": [call.caller.function_start, call.caller.function_end],
                "caller_context": {"this_origin": call.caller.this_origin, "parameter_indices": call.caller.parameter_indices},
                "callee_function": [call.callee.function_start, call.callee.function_end],
                "callee_context": {"this_origin": call.callee.this_origin, "parameter_indices": call.callee.parameter_indices},
                "standard_function_call_semantics_required": call.standard_function_call_semantics_required,
                "arguments": call.argument_spans.iter().zip(&call.exact_integer_arguments).map(|((start, end), exact_integer)| json!({"start": start, "end": end, "source": snippet(&source, *start, *end), "exact_integer": exact_integer})).collect::<Vec<_>>(),
                "allocation": [call.caller.allocation_start, call.caller.allocation_end],
            })
        })
        .collect::<Vec<_>>();
    let member_reads = flow
        .member_reads
        .iter()
        .map(|read| {
            json!({
                "read_start": read.read_start,
                "read_end": read.read_end,
                "evaluation_order": read.evaluation_order,
                "read": snippet(&source, read.read_start, read.read_end),
                "function": [read.context.function_start, read.context.function_end],
                "context": {"this_origin": read.context.this_origin, "parameter_indices": read.context.parameter_indices},
                "property": read.property,
                "allocation": [read.allocation_start, read.allocation_end],
                "constructor": [read.constructor_start, read.constructor_end],
            })
        })
        .collect::<Vec<_>>();
    let member_calls = flow
        .member_calls
        .iter()
        .map(|call| {
            json!({
                "call_start": call.call_start,
                "call_end": call.call_end,
                "evaluation_order": call.evaluation_order,
                "call": snippet(&source, call.call_start, call.call_end),
                "function": [call.context.function_start, call.context.function_end],
                "context": {"this_origin": call.context.this_origin, "parameter_indices": call.context.parameter_indices},
                "property": call.property,
                "allocation": [call.allocation_start, call.allocation_end],
                "constructor": [call.constructor_start, call.constructor_end],
            })
        })
        .collect::<Vec<_>>();
    let member_writes = flow
        .member_writes
        .iter()
        .map(|write| {
            json!({
                "write_start": write.write_start,
                "write_end": write.write_end,
                "evaluation_order": write.evaluation_order,
                "write": snippet(&source, write.write_start, write.write_end),
                "function": [write.context.function_start, write.context.function_end],
                "context": {"this_origin": write.context.this_origin, "parameter_indices": write.context.parameter_indices},
                "property": write.property,
                "operation": write.operation,
                "allocation": [write.allocation_start, write.allocation_end],
            })
        })
        .collect::<Vec<_>>();
    let exposures = flow
        .exposures
        .iter()
        .map(|exposure| {
            json!({
                "start": exposure.exposure_start,
                "end": exposure.exposure_end,
                "evaluation_order": exposure.evaluation_order,
                "expression": snippet(&source, exposure.exposure_start, exposure.exposure_end),
                "function": [exposure.context.function_start, exposure.context.function_end],
                "context": {"this_origin": exposure.context.this_origin, "parameter_indices": exposure.context.parameter_indices},
                "kind": exposure.kind,
                "allocation": [exposure.allocation_start, exposure.allocation_end],
            })
        })
        .collect::<Vec<_>>();
    let lookup_targets = lookup_targets
        .iter()
        .map(|target| {
            json!({
                "constructor": [target.constructor_start, target.constructor_end],
                "property": target.property,
                "assignment": [target.assignment_start, target.assignment_end],
                "method_functions": target.possible_functions.iter().map(|f| Value::Array(vec![Value::from(f.function_start), Value::from(f.function_end)])).collect::<Vec<_>>(),
                "standard_prototype_semantics_required": target.standard_prototype_semantics_required,
            })
        })
        .collect::<Vec<_>>();
    let own_data_fields = own_data_fields
        .iter()
        .map(|field| {
            json!({
                "function": [field.context.function_start, field.context.function_end],
                "context": {"this_origin": field.context.this_origin, "parameter_indices": field.context.parameter_indices},
                "property": field.property,
                "write": [field.write_start, field.write_end],
                "evaluation_order": field.evaluation_order,
                "allocation": [field.allocation_start, field.allocation_end],
                "constructor": [field.constructor_start, field.constructor_end],
                "standard_prototype_semantics_required": field.standard_prototype_semantics_required,
            })
        })
        .collect::<Vec<_>>();
    let own_data_fields_at_member_calls = own_data_fields_at_member_calls
        .iter()
        .map(|proof| {
            json!({
                "field": proof.initialization.property,
                "initialization": [proof.initialization.write_start, proof.initialization.write_end],
                "entry_call": [proof.entry_call.call_start, proof.entry_call.call_end],
                "member_call": [proof.member_call.call_start, proof.member_call.call_end],
                "member_property": proof.member_call.property,
                "allocation": [proof.initialization.allocation_start, proof.initialization.allocation_end],
            })
        })
        .collect::<Vec<_>>();
    let receiver_preserving_method_calls = receiver_preserving_method_calls
        .iter()
        .map(|proof| {
            json!({
                "call": [proof.candidate.call.call_start, proof.candidate.call.call_end],
                "property": proof.candidate.call.property,
                "allocation": [proof.candidate.call.allocation_start, proof.candidate.call.allocation_end],
                "own_data_reads": proof.own_data_reads.iter().map(|field| field.initialization.property.clone()).collect::<Vec<_>>(),
            })
        })
        .collect::<Vec<_>>();
    let receiver_effects = receiver_effects
        .iter()
        .map(|effect| {
            json!({
                "constructor": [effect.constructor_start, effect.constructor_end],
                "property": effect.property,
                "assignment": [effect.assignment_start, effect.assignment_end],
                "method_functions": effect.possible_functions.iter().map(|f| Value::Array(vec![Value::from(f.function_start), Value::from(f.function_end)])).collect::<Vec<_>>(),
                "receiver_reads": effect.receiver_reads,
                "receiver_calls": effect.receiver_calls,
                "mutates_receiver": effect.mutates_receiver,
                "exposes_receiver": effect.exposes_receiver,
                "dynamic_receiver_access": effect.dynamic_receiver_access,
            })
        })
        .collect::<Vec<_>>();

    let mut direct_call_exposure_checks = Vec::new();
    for call in &flow.direct_calls {
        let bindings = call
            .exact_integer_arguments
            .iter()
            .enumerate()
            .filter_map(|(index, value)| value.map(|value| (index, value)))
            .collect::<BTreeMap<_, _>>();
        for exposure in &flow.exposures {
            if exposure.context != call.callee {
                continue;
            }
            let event = oxc_span::Span::new(exposure.exposure_start, exposure.exposure_end);
            direct_call_exposure_checks.push(json!({
                "call_start": call.call_start,
                "callee_function": [call.callee.function_start, call.callee.function_end],
                "exposure_start": exposure.exposure_start,
                "exposure_kind": exposure.kind,
                "exact_integer_bindings": bindings,
                "unreachable_under_exact_integer_bindings":
                    proven_origin_direct_call_event_unreachable(
                        &source,
                        &parsed.program,
                        scoping,
                        call,
                        event,
                    ),
            }));
        }
    }

    let mut direct_call_nested_call_checks = Vec::new();
    for parent in &flow.direct_calls {
        let bindings = parent
            .exact_integer_arguments
            .iter()
            .enumerate()
            .filter_map(|(index, value)| value.map(|value| (index, value)))
            .collect::<BTreeMap<_, _>>();
        if bindings.is_empty() {
            continue;
        }
        for nested in &flow.direct_calls {
            if nested.caller != parent.callee {
                continue;
            }
            let event = oxc_span::Span::new(nested.call_start, nested.call_end);
            let unreachable = proven_origin_direct_call_event_unreachable(
                &source,
                &parsed.program,
                scoping,
                parent,
                event,
            );
            direct_call_nested_call_checks.push(json!({
                "parent_call_start": parent.call_start,
                "parent_callee_function": [parent.callee.function_start, parent.callee.function_end],
                "nested_call_start": nested.call_start,
                "nested_callee_function": [nested.callee.function_start, nested.callee.function_end],
                "exact_integer_bindings": bindings,
                "unreachable_under_exact_integer_bindings": unreachable,
            }));
        }
    }

    let candidates = matched
        .iter()
        .map(|candidate| {
            let function = (
                candidate.call.context.function_start,
                candidate.call.context.function_end,
            );
            let allocation = (
                candidate.call.allocation_start,
                candidate.call.allocation_end,
            );
            let mut barriers = flow
                .exposures
                .iter()
                .filter(|exposure| {
                    (exposure.context.function_start, exposure.context.function_end) == function
                        && (exposure.allocation_start, exposure.allocation_end) == allocation
                })
                .map(|exposure| Span::new(exposure.exposure_start, exposure.exposure_end))
                .chain(
                    flow.member_writes
                        .iter()
                        .filter(|write| {
                            (write.context.function_start, write.context.function_end) == function
                                && (write.allocation_start, write.allocation_end) == allocation
                                && write.property.as_deref().is_none_or(|property| {
                                    property == candidate.call.property.as_str()
                                })
                        })
                        .map(|write| Span::new(write.write_start, write.write_end)),
                )
                .chain(
                    flow.member_calls
                        .iter()
                        .filter(|call| {
                            (call.context.function_start, call.context.function_end) == function
                                && (call.allocation_start, call.allocation_end) == allocation
                                && (call.call_start, call.call_end)
                                    != (candidate.call.call_start, candidate.call.call_end)
                        })
                        .map(|call| Span::new(call.call_start, call.call_end)),
                )
                .collect::<Vec<_>>();
            barriers.sort_by_key(|span| (span.start, span.end));
            barriers.dedup();
            let local_prefix_clean = prove_event_before_barriers(
                &semantic.semantic,
                Span::new(candidate.call.call_start, candidate.call.call_end),
                &barriers,
            );
            let local_barriers = barriers
                .iter()
                .map(|span| {
                    json!({
                        "start": span.start,
                        "end": span.end,
                        "source": snippet(&source, span.start, span.end),
                    })
                })
                .collect::<Vec<_>>();
            json!({
                "call_start": candidate.call.call_start,
                "call_end": candidate.call.call_end,
                "call": snippet(&source, candidate.call.call_start, candidate.call.call_end),
                "function": [candidate.call.context.function_start, candidate.call.context.function_end],
                "property": candidate.call.property,
                "allocation": [candidate.call.allocation_start, candidate.call.allocation_end],
                "constructor": [candidate.call.constructor_start, candidate.call.constructor_end],
                "method_functions": candidate.lookup_target.possible_functions.iter().map(|f| Value::Array(vec![Value::from(f.function_start), Value::from(f.function_end)])).collect::<Vec<_>>(),
                "receiver_reads": candidate.receiver_effects.receiver_reads,
                "receiver_calls": candidate.receiver_effects.receiver_calls,
                "mutates_receiver": candidate.receiver_effects.mutates_receiver,
                "exposes_receiver": candidate.receiver_effects.exposes_receiver,
                "dynamic_receiver_access": candidate.receiver_effects.dynamic_receiver_access,
                "local_prefix_clean": local_prefix_clean,
                "local_barriers": local_barriers,
            })
        })
        .collect::<Vec<_>>();

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "file": path,
            "direct_calls": direct_calls,
            "member_calls": member_calls,
            "member_reads": member_reads,
            "member_writes": member_writes,
            "exposures": exposures,
            "direct_call_exposure_checks": direct_call_exposure_checks,
            "direct_call_nested_call_checks": direct_call_nested_call_checks,
            "prototype_lookup_targets": lookup_targets,
        "own_data_field_initializations": own_data_fields,
        "own_data_field_entry_dominance": own_data_field_entry_dominance,
        "own_data_fields_at_member_calls": own_data_fields_at_member_calls,
        "receiver_preserving_method_calls": receiver_preserving_method_calls,
        "runtime_prototype_method_calls": runtime_method_calls,
        "matched_method_origin_flows": matched_method_origin_flows,
        "prototype_receiver_effects": receiver_effects,
        "prototype_method_call_candidates": candidates,
        }))?
    );
    Ok(())
}
