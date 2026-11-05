use anyhow::{Context, Result};
use jsvm_lift::cfg_order::prove_event_before_barriers;
use jsvm_lift::{
    cfg_order::prove_events_before_event,
    forwarding_semantics::{
        structurally_proven_lazy_registry_read_calls,
        structurally_proven_registry_forwarding_calls, structurally_proven_registry_read_calls,
    },
    lexical_mutation::audit_lexical_binding_mutation,
    receiver_identity::{
        propagate_matched_prototype_method_call_origins,
        propagate_proven_prototype_method_call_origins, proven_exact_own_data_field_at_direct_call,
        proven_origin_direct_call_event_unreachable, proven_own_data_field_at_runtime_method_call,
        proven_prototype_method_phase_at_event,
        proven_prototype_method_receiver_preservation_summary,
        proven_prototype_string_at_allocation, proven_prototype_string_at_direct_calls,
        proven_receiver_preserving_prototype_method_call,
        structurally_matched_prototype_method_calls, structurally_proven_origin_flow,
        structurally_proven_own_data_field_initializations,
        structurally_proven_own_data_fields_at_member_calls,
        structurally_proven_prototype_method_calls_at_runtime,
        structurally_proven_prototype_method_lookup_targets,
        structurally_proven_prototype_method_phase_closures,
        structurally_proven_prototype_method_receiver_effects,
        structurally_proven_prototype_string_assignments,
        structurally_proven_receiver_preserving_prototype_method_calls,
        structurally_proven_runtime_origin_flow,
    },
    registry_identity::{
        proven_origin_registry_handler_installs, proven_origin_registry_read_calls,
    },
    table_vm,
};
use oxc_allocator::Allocator;
use oxc_semantic::SemanticBuilder;
use oxc_span::{GetSpan, SourceType, Span};
use rolldown_redox::ecmascript::parse_program;
use serde_json::{json, Value};
use std::{collections::BTreeMap, env, fs, path::PathBuf, time::Duration};
use work_budget::{BudgetLimits, WorkBudget};

fn snippet(source: &str, start: u32, end: u32) -> String {
    source
        .get(start as usize..(end as usize).min(source.len()))
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn compact_snippet(source: &str, start: u32, end: u32) -> String {
    snippet(source, start, end).chars().take(160).collect()
}

fn main() -> Result<()> {
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    let origin_only = args.iter().any(|arg| arg == "--origin-only");
    let origin_work = args
        .iter()
        .find_map(|arg| arg.to_str()?.strip_prefix("--origin-work="));
    let origin_secs = args
        .iter()
        .find_map(|arg| arg.to_str()?.strip_prefix("--origin-secs="));
    let budget = if origin_only {
        let work = origin_work
            .unwrap_or("20000000")
            .parse::<u64>()
            .context("invalid --origin-work")?;
        let seconds = origin_secs
            .unwrap_or("90")
            .parse::<u64>()
            .context("invalid --origin-secs")?;
        WorkBudget::new(
            "receiver-origin-inventory",
            BudgetLimits::wall_time(Duration::from_secs(seconds)).with_work(work),
        )
    } else {
        anyhow::ensure!(
            origin_work.is_none() && origin_secs.is_none(),
            "--origin-work and --origin-secs require --origin-only"
        );
        WorkBudget::unlimited("receiver-proof-inventory")
    };
    let summary = args.iter().any(|arg| arg == "--summary");
    let runtime_only = args.iter().any(|arg| arg == "--runtime-only");
    let prototype_strings_only = args.iter().any(|arg| arg == "--prototype-strings");
    let phase_closures_only = args.iter().any(|arg| arg == "--phase-closures");
    let phase_event_start = args.iter().find_map(|arg| {
        arg.to_str()?
            .strip_prefix("--phase-event-start=")?
            .parse::<u32>()
            .ok()
    });
    let phase_event_end = args.iter().find_map(|arg| {
        arg.to_str()?
            .strip_prefix("--phase-event-end=")?
            .parse::<u32>()
            .ok()
    });
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
    let exact_field_call_start = args.iter().find_map(|arg| {
        arg.to_str()?
            .strip_prefix("--exact-field-call-start=")?
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
            "usage: cargo run -p jsvm-lift --example receiver-proof-inventory -- <file.js> [--summary] [--origin-only [--origin-work=N] [--origin-secs=N]] [--runtime-only] [--phase-closures [--phase-event-start=N --phase-event-end=N]] [--preserve-call-start=N] [--fully-preserve-call-start=N] [--field-runtime-call-start=N --field=NAME] [--exact-field-call-start=N --field=NAME] [--registry-origin-call-start=N]",
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
    if origin_only {
        let timer = std::time::Instant::now();
        let base = structurally_proven_origin_flow(&parsed.program, scoping, &budget)?;
        let base_elapsed_ms = timer.elapsed().as_millis();
        eprintln!(
            "base exact-origin flow: {} calls, {} reads, {} ms",
            base.direct_calls.len(),
            base.member_reads.len(),
            base_elapsed_ms
        );
        let runtime =
            structurally_proven_runtime_origin_flow(&parsed.program, &semantic.semantic, &budget)?;
        let runtime_elapsed_ms = timer.elapsed().as_millis();
        eprintln!(
            "runtime exact-origin flow: {} calls, {} reads, {} ms",
            runtime.direct_calls.len(),
            runtime.member_reads.len(),
            runtime_elapsed_ms
        );
        let structural_installs =
            structurally_proven_registry_forwarding_calls(&parsed.program, scoping, &budget)?;
        let structural_reads =
            structurally_proven_registry_read_calls(&parsed.program, scoping, &budget)?;
        let accessor_result_calls = jsvm_lift::registry_call_value::analyze(
            &semantic.semantic,
            &structural_reads,
            &budget,
        )?;
        let lazy_reads =
            structurally_proven_lazy_registry_read_calls(&parsed.program, scoping, &budget)?;
        let lazy_result_calls = jsvm_lift::registry_call_value::join_lazy_accessor_results(
            &accessor_result_calls,
            &lazy_reads,
            &budget,
        )?;
        let origin_installs =
            proven_origin_registry_handler_installs(&parsed.program, scoping, &runtime, &budget)?;
        let origin_reads =
            proven_origin_registry_read_calls(&parsed.program, scoping, &runtime, &budget)?;
        let exact_origin_lazy_results =
            jsvm_lift::registry_call_value::join_exact_origin_lazy_accessor_results(
                &lazy_result_calls,
                &origin_reads,
                &budget,
            )?;
        let table_analysis = table_vm::analyze(&source, &parsed.program, &budget)?;
        println!(
            "{}",
            serde_json::to_string_pretty(&json!({
                "file": path,
                "source_bytes": source.len(),
                "elapsed_ms": timer.elapsed().as_millis(),
                "base": {
                    "direct_calls": base.direct_calls.len(),
                    "member_calls": base.member_calls.len(),
                    "member_reads": base.member_reads.len(),
                    "member_writes": base.member_writes.len(),
                    "exposures": base.exposures.len(),
                },
                "runtime": {
                    "direct_calls": runtime.direct_calls.len(),
                    "member_calls": runtime.member_calls.len(),
                    "member_reads": runtime.member_reads.len(),
                    "member_writes": runtime.member_writes.len(),
                    "exposures": runtime.exposures.len(),
                },
                "tables": table_analysis.handler_function_tables.iter().map(|table| json!({
                "binding": table.binding,
                "kind": table.container_kind,
                "entries": table.entries,
                "function_values": table.function_values,
                "read_sites": table.read_sites,
                "dynamic_read_sites": table.dynamic_read_sites,
                "looped_dynamic_read_sites": table.looped_dynamic_read_sites,
                "dynamic_call_sites": table.dynamic_call_sites,
                "looped_dynamic_call_sites": table.looped_dynamic_call_sites,
            })).collect::<Vec<_>>(),
            "table_vm_candidates": table_analysis.table_vms.len(),
            "structural_lazy_registry_reads": lazy_reads.len(),
            "exact_origin_lazy_accessor_result_indirect_call_candidates": exact_origin_lazy_results.len(),
            "exact_origin_lazy_accessor_result_indirect_call_examples": exact_origin_lazy_results.iter().take(48).map(|proof| json!({
                "binding": proof.lazy.result.binding,
                "accessor_call": [proof.lazy.result.accessor_call_start, proof.lazy.result.accessor_call_end],
                "indirect_call": [proof.lazy.result.indirect_call_start, proof.lazy.result.indirect_call_end],
                "definite_accessor_result": proof.lazy.result.definite_accessor_result,
                "cfg_write_free_path": proof.lazy.result.cfg_write_free_path,
                "origin_allocation": [proof.origin_allocation_start, proof.origin_allocation_end],
                "origin_constructor": [proof.origin_constructor_start, proof.origin_constructor_end],
                "exact_key": proof.exact_key,
                "registry_path": proof.lazy.registry_path,
            })).collect::<Vec<_>>(),
            "lazy_accessor_result_indirect_call_candidates": lazy_result_calls.len(),
            "lazy_accessor_result_indirect_call_definite": lazy_result_calls.iter()
                .filter(|edge| edge.result.definite_accessor_result).count(),
            "lazy_accessor_result_indirect_call_cfg_write_free_paths": lazy_result_calls.iter()
                .filter(|edge| edge.result.cfg_write_free_path).count(),
            "lazy_accessor_result_indirect_call_examples": lazy_result_calls.iter().take(48).map(|edge| json!({
                "binding": edge.result.binding,
                "accessor_call": [edge.result.accessor_call_start, edge.result.accessor_call_end],
                "assignment": [edge.result.assignment_start, edge.result.assignment_end],
                "indirect_call": [edge.result.indirect_call_start, edge.result.indirect_call_end],
                "definite_accessor_result": edge.result.definite_accessor_result,
                "cfg_write_free_path": edge.result.cfg_write_free_path,
                "registry_receiver": [edge.registry_receiver_start, edge.registry_receiver_end],
                "registry_key": [edge.registry_key_start, edge.registry_key_end],
                "registry_path": edge.registry_path,
                "fast_probe_property": edge.fast_probe_property,
                "update_method": edge.update_method,
                "slow_projection_property": edge.slow_projection_property,
                "slow_selector": [edge.slow_selector_start, edge.slow_selector_end],
            })).collect::<Vec<_>>(),
            "accessor_result_indirect_call_candidates": accessor_result_calls.len(),
            "accessor_result_indirect_call_definite": accessor_result_calls.iter()
                .filter(|edge| edge.definite_accessor_result).count(),
            "accessor_result_indirect_call_cfg_write_free_paths": accessor_result_calls.iter()
                .filter(|edge| edge.cfg_write_free_path).count(),
            "accessor_result_indirect_call_examples": accessor_result_calls.iter().take(48).map(|edge| json!({
                "binding": edge.binding,
                "assignment": [edge.assignment_start, edge.assignment_end],
                "accessor_call": [edge.accessor_call_start, edge.accessor_call_end],
                "indirect_call": [edge.indirect_call_start, edge.indirect_call_end],
                "definite_accessor_result": edge.definite_accessor_result,
                "cfg_write_free_path": edge.cfg_write_free_path,
            })).collect::<Vec<_>>(),
            "structural_registry_handler_installs": structural_installs.len(),
                "structural_registry_reads": structural_reads.len(),
                "exact_origin_handler_installs": origin_installs.iter().map(|proof| json!({
                    "call": [proof.install.call_start, proof.install.call_end],
                    "call_source": compact_snippet(&source, proof.install.call_start, proof.install.call_end),
                    "origin": {
                    "allocation": [proof.origin.allocation_start, proof.origin.allocation_end],
                    "constructor": [proof.origin.constructor_start, proof.origin.constructor_end],
                },
                    "key": proof.exact_key,
                    "path": proof.install.registry_path,
                    "handler": [proof.install.handler_start, proof.install.handler_end],
                })).collect::<Vec<_>>(),
                "exact_origin_registry_reads": origin_reads.iter().map(|proof| json!({
                    "call": [proof.read.call_start, proof.read.call_end],
                    "call_source": compact_snippet(&source, proof.read.call_start, proof.read.call_end),
                    "origin": {
                    "allocation": [proof.origin.allocation_start, proof.origin.allocation_end],
                    "constructor": [proof.origin.constructor_start, proof.origin.constructor_end],
                },
                    "key": proof.exact_key,
                    "path": proof.read.registry_path,
                })).collect::<Vec<_>>(),
                "structural_registry_reads_examples": structural_reads.iter().take(32).map(|proof| json!({
                    "call": [proof.call_start,proof.call_end],
                    "source": compact_snippet(&source,proof.call_start,proof.call_end),
                    "path": proof.registry_path,
                })).collect::<Vec<_>>(),
                "runtime_direct_calls_examples": runtime.direct_calls.iter().take(64).map(|proof| json!({
                    "call": [proof.call_start,proof.call_end],
                    "source": compact_snippet(&source,proof.call_start,proof.call_end),
                    "allocation": [proof.callee.allocation_start,proof.callee.allocation_end],
                    "caller": [proof.caller.function_start,proof.caller.function_end],
                    "callee": [proof.callee.function_start,proof.callee.function_end],
                })).collect::<Vec<_>>(),
            }))?
        );
        return Ok(());
    }
    if phase_closures_only {
        anyhow::ensure!(
            phase_event_start.is_some() == phase_event_end.is_some(),
            "phase event requires both --phase-event-start and --phase-event-end"
        );
        let event = phase_event_start
            .zip(phase_event_end)
            .map(|(start, end)| Span::new(start, end));
        let closures = structurally_proven_prototype_method_phase_closures(&parsed.program, scoping, &budget)?
            .into_iter()
            .map(|closure| -> Result<Value> {
                let hazard = audit_lexical_binding_mutation(
                    &semantic.semantic,
                    closure.phase_binding_symbol,
                    Span::new(closure.phase_assignment_start, closure.phase_assignment_end),
                    &budget,
                )?;
                let phase = event.as_ref().and_then(|event| {
                    proven_prototype_method_phase_at_event(
                        &source,
                        &parsed.program,
                        &semantic.semantic,
                        &closure,
                        *event,
                    )
                });
                let phase_binding = scoping.symbol_span(closure.phase_binding_symbol);
                let left = scoping.symbol_span(closure.left_symbol);
                let right = scoping.symbol_span(closure.right_symbol);
                let phase_binding_writes = scoping
                    .get_resolved_reference_ids(closure.phase_binding_symbol)
                    .iter()
                    .filter_map(|reference_id| {
                        let reference = scoping.get_reference(*reference_id);
                        reference.is_write().then(|| {
                            let span = semantic
                                .semantic
                                .nodes()
                                .get_node(reference.node_id())
                                .kind()
                                .span();
                            [span.start, span.end]
                        })
                    })
                    .collect::<Vec<_>>();
                Ok(json!({
                    "constructor": [closure.constructor_start, closure.constructor_end],
                    "property": closure.property,
                    "method_assignment": [closure.method_assignment_start, closure.method_assignment_end],
                    "factory": [closure.factory_start, closure.factory_end],
                    "method_function": [closure.method_function_start, closure.method_function_end],
                    "phase_assignment": [closure.phase_assignment_start, closure.phase_assignment_end],
                    "phase_function": [closure.phase_function_start, closure.phase_function_end],
                    "phase_binding_declaration": [phase_binding.start, phase_binding.end],
                    "phase_binding_writes": phase_binding_writes,
                    "binding_mutation_audit": {
                        "unique_expected_write": hazard.unique_expected_write,
                        "lexical_direct_eval_calls": hazard.lexical_direct_eval_calls.iter()
                            .map(|site| json!({
                                "span": [site.span.start,site.span.end],
                                "enclosing_function": site.enclosing_function.map(|s| [s.start,s.end]),
                            })).collect::<Vec<_>>(),
                        "lexical_with_statements": hazard.lexical_with_statements.iter()
                            .map(|site| json!({
                                "span": [site.span.start,site.span.end],
                                "enclosing_function": site.enclosing_function.map(|s| [s.start,s.end]),
                            })).collect::<Vec<_>>(),
                        "root_scope_binding": hazard.root_scope_binding,
                        "source_mutation_isolated": hazard.source_mutation_isolated,
                        "runtime_ordering_proven": false,
                    },
                    "left_declaration": [left.start, left.end],
                    "right_declaration": [right.start, right.end],
                    "equal_value": closure.equal_value,
                    "unequal_value": closure.unequal_value,
                    "event_phase": phase.map(|phase| json!({
                        "value": phase.value,
                        "state": phase.equality.state,
                        "assignment": [phase.equality.assignment_start, phase.equality.assignment_end],
                    })),
                }))
            })
            .collect::<Result<Vec<_>>>()?;
        println!("{}", serde_json::to_string_pretty(&closures)?);
        return Ok(());
    }
    if let Some(call_start) = exact_field_call_start {
        let property = field_property
            .as_deref()
            .context("--exact-field-call-start requires --field=NAME")?;
        let flow = structurally_proven_origin_flow(&parsed.program, scoping, &budget)?;
        let mut targets = flow
            .direct_calls
            .iter()
            .filter(|call| call.call_start == call_start);
        let target = targets
            .next()
            .context("no exact-origin direct call at requested start")?;
        anyhow::ensure!(targets.next().is_none(), "ambiguous direct call start");
        let proofs = proven_exact_own_data_field_at_direct_call(
            &source,
            &parsed.program,
            &semantic.semantic,
            property,
            target,
            &budget,
        )?
        .into_iter()
        .map(|proof| {
            json!({
                "field": proof.initialization.property,
                "initialization": [proof.initialization.write_start, proof.initialization.write_end],
                "entry_call": [proof.entry_call.call_start, proof.entry_call.call_end],
                "entry_callee_function": [proof.entry_call.callee.function_start, proof.entry_call.callee.function_end],
                "direct_call": [proof.direct_call.call_start, proof.direct_call.call_end],
                "direct_call_source": snippet(&source, proof.direct_call.call_start, proof.direct_call.call_end),
                "direct_callee_function": [proof.direct_call.callee.function_start, proof.direct_call.callee.function_end],
                "allocation": [proof.initialization.allocation_start, proof.initialization.allocation_end],
            })
        })
        .collect::<Vec<_>>();
        println!("{}", serde_json::to_string_pretty(&proofs)?);
        return Ok(());
    }
    if prototype_strings_only {
        let strings =
            structurally_proven_prototype_string_assignments(&parsed.program, scoping, &budget)?
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
            &budget,
        )?
        .into_iter()
        .filter(|proof| proof.candidate.call.call_start == call_start);
        let target = targets
            .next()
            .context("no runtime-proven method call at requested start")?;
        anyhow::ensure!(
            targets.next().is_none(),
            "ambiguous runtime method call start"
        );
        let seeded = propagate_proven_prototype_method_call_origins(
            &parsed.program,
            scoping,
            &target,
            &budget,
        )?;
        let base = structurally_proven_origin_flow(&parsed.program, scoping, &budget)?;
        let target_origin = (
            target.candidate.call.allocation_start,
            target.candidate.call.allocation_end,
            target.candidate.call.constructor_start,
            target.candidate.call.constructor_end,
        );
        let prototype_string_assignments =
            structurally_proven_prototype_string_assignments(&parsed.program, scoping, &budget)?;
        let mut prototype_strings_at_allocation = Vec::new();
        let mut prototype_string_direct_calls = Vec::new();
        for assignment in prototype_string_assignments.iter().filter(|assignment| {
            assignment.constructor_start == target_origin.2
                && assignment.constructor_end == target_origin.3
        }) {
            let Some(string) = proven_prototype_string_at_allocation(
                &parsed.program,
                &semantic.semantic,
                target_origin.2,
                target_origin.3,
                Span::new(target_origin.0, target_origin.1),
                &assignment.property,
                &budget,
            )?
            else {
                continue;
            };
            prototype_strings_at_allocation.push(json!({
                "property": string.assignment.property,
                "value": string.assignment.value,
                "assignment": [string.assignment.assignment_start, string.assignment.assignment_end],
            }));
            for proof in proven_prototype_string_at_direct_calls(
                &source,
                &parsed.program,
                &semantic.semantic,
                &string,
                &budget,
            )? {
                prototype_string_direct_calls.push(json!({
                    "property": proof.string.assignment.property,
                    "value": proof.string.assignment.value,
                    "call": [proof.call.call_start, proof.call.call_end],
                    "caller": [proof.call.caller.function_start, proof.call.caller.function_end],
                    "callee": [proof.call.callee.function_start, proof.call.callee.function_end],
                    "exact_integer_arguments": proof.call.exact_integer_arguments,
                }));
            }
        }
        let reads = proven_origin_registry_read_calls(&parsed.program, scoping, &seeded, &budget)?
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
        let table_analysis = table_vm::analyze_with_registry_origins(
            &source,
            &parsed.program,
            &base,
            &seeded,
            &budget,
        )?;
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
        let seeded_installs =
            proven_origin_registry_handler_installs(&parsed.program, scoping, &seeded, &budget)?
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
                        "exact_key": proof.exact_key,
                        "registry_path": proof.install.registry_path,
                        "handler": [proof.install.handler_start, proof.install.handler_end],
                    })
                })
                .collect::<Vec<_>>();
        let installs =
            proven_origin_registry_handler_installs(&parsed.program, scoping, &base, &budget)?
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
                "seeded_registry_installs": seeded_installs,
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
            &budget,
        )?
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
            &budget,
        )?
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
            &budget,
        )?
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
            &budget,
        )?
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
            &budget,
        )?
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
            &budget,
        )?
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
            &budget,
        )?
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
    let flow = structurally_proven_origin_flow(&parsed.program, scoping, &budget)?;
    let matched = structurally_matched_prototype_method_calls(&parsed.program, scoping, &budget)?;
    let lookup_targets =
        structurally_proven_prototype_method_lookup_targets(&parsed.program, scoping, &budget)?;
    let runtime_method_calls = structurally_proven_prototype_method_calls_at_runtime(
        &parsed.program,
        &semantic.semantic,
        &budget,
    )?;
    let receiver_effects =
        structurally_proven_prototype_method_receiver_effects(&parsed.program, scoping, &budget)?;
    let own_data_fields =
        structurally_proven_own_data_field_initializations(&parsed.program, scoping, &budget)?;
    let own_data_fields_at_member_calls = structurally_proven_own_data_fields_at_member_calls(
        &source,
        &parsed.program,
        &semantic.semantic,
        &budget,
    )?;
    let receiver_preserving_method_calls =
        structurally_proven_receiver_preserving_prototype_method_calls(
            &source,
            &parsed.program,
            &semantic.semantic,
            &budget,
        )?;
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
        .map(|candidate| -> Result<Value> {
            let seeded = propagate_matched_prototype_method_call_origins(
                &parsed.program,
                scoping,
                candidate,
                &budget,
            )?;
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
            Ok(json!({
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
            }))
        })
        .collect::<Result<Vec<_>>>()?
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
