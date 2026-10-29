use anyhow::{Context, Result};
use jsvm_lift::cfg_order::prove_event_before_barriers;
use jsvm_lift::receiver_identity::{
    structurally_matched_prototype_method_calls, structurally_proven_origin_flow,
    structurally_proven_prototype_method_lookup_targets,
    structurally_proven_prototype_method_receiver_effects,
};
use oxc_allocator::Allocator;
use oxc_semantic::SemanticBuilder;
use oxc_span::{SourceType, Span};
use rolldown_redox::ecmascript::parse_program;
use serde_json::{json, Value};
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
        .context("usage: cargo run -p jsvm-lift --example receiver-proof-inventory -- <file.js>")?;
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
    let flow = structurally_proven_origin_flow(&parsed.program, scoping);
    let matched = structurally_matched_prototype_method_calls(&parsed.program, scoping);
    let lookup_targets =
        structurally_proven_prototype_method_lookup_targets(&parsed.program, scoping);
    let receiver_effects =
        structurally_proven_prototype_method_receiver_effects(&parsed.program, scoping);

    let direct_calls = flow
        .direct_calls
        .iter()
        .map(|call| {
            json!({
                "call_start": call.call_start,
                "call_end": call.call_end,
                "call": snippet(&source, call.call_start, call.call_end),
                "caller_function": [call.caller.function_start, call.caller.function_end],
                "caller_context": {"this_origin": call.caller.this_origin, "parameter_indices": call.caller.parameter_indices},
                "callee_function": [call.callee.function_start, call.callee.function_end],
                "callee_context": {"this_origin": call.callee.this_origin, "parameter_indices": call.callee.parameter_indices},
                "allocation": [call.caller.allocation_start, call.caller.allocation_end],
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
            "member_writes": member_writes,
            "exposures": exposures,
            "prototype_lookup_targets": lookup_targets,
        "prototype_receiver_effects": receiver_effects,
        "prototype_method_call_candidates": candidates,
        }))?
    );
    Ok(())
}
