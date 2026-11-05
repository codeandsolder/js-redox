use anyhow::{Context, Result};
use jsvm_lift::{
    forwarding_semantics::structurally_proven_lazy_registry_read_calls,
    lazy_cell::{
        proven_slow_lazy_cell_captured_handler_install,
        proven_slow_lazy_cell_exact_registry_assignments, proven_slow_lazy_cell_factory_call,
        proven_slow_lazy_cell_prototype_carrier, proven_slow_lazy_cell_registry_assignment,
        proven_slow_lazy_cell_resolved_handler, proven_slow_lazy_cell_resolver_index,
        proven_slow_lazy_cell_state_fields_for_exact_assignment,
        proven_slow_lazy_cell_update_state, structurally_compatible_slow_lazy_cell_read,
        structurally_proven_slow_lazy_cell_factory_shapes, SlowLazyCellResolverIndexFacts,
    },
    lexical_mutation::audit_lexical_binding_mutation,
    receiver_identity::{
        structurally_proven_prototype_method_phase_closures,
        structurally_proven_runtime_origin_flow,
    },
    registry_identity::proven_origin_registry_handler_installs,
};
use oxc_allocator::Allocator;
use oxc_semantic::SemanticBuilder;
use oxc_span::{SourceType, Span};
use rolldown_redox::ecmascript::parse_program;
use serde_json::{json, Value};
use std::{
    collections::{HashMap, HashSet},
    env, fs,
    time::Duration,
};
use work_budget::{BudgetLimits, WorkBudget};

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    let input = args
        .next()
        .context("usage: lazy-resolver-probe <input.js> [key_limit]")?;
    let limit: usize = args.next().map_or(Ok(usize::MAX), |s| s.parse())?;
    let source = fs::read_to_string(input)?;
    let alloc = Allocator::default();
    let parsed = parse_program(&alloc, &source, SourceType::cjs());
    anyhow::ensure!(parsed.is_clean(), "parse refused");
    let semantic_ret = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .with_check_syntax_error(true)
        .build(&parsed.program);
    anyhow::ensure!(semantic_ret.diagnostics.is_empty(), "semantic refused");
    let semantic = &semantic_ret.semantic;
    let scoping = semantic.scoping();
    let budget = WorkBudget::new(
        "lazy-resolver-probe",
        BudgetLimits::wall_time(Duration::from_secs(240)),
    );
    let flow = structurally_proven_runtime_origin_flow(&parsed.program, semantic, &budget)?;
    let shapes = structurally_proven_slow_lazy_cell_factory_shapes(&parsed.program, scoping);
    let phase_closures =
        structurally_proven_prototype_method_phase_closures(&parsed.program, scoping, &budget)?;
    let mut phase_binding_mutation_audits = Vec::new();
    for closure in &phase_closures {
        let audit = audit_lexical_binding_mutation(
            semantic,
            closure.phase_binding_symbol,
            Span::new(closure.phase_assignment_start, closure.phase_assignment_end),
            &budget,
        )?;
        phase_binding_mutation_audits.push(json!({
            "phase_assignment":[closure.phase_assignment_start,closure.phase_assignment_end],
            "unique_expected_write":audit.unique_expected_write,
            "lexical_direct_eval_calls":audit.lexical_direct_eval_calls.iter()
                .map(|site|json!({
                    "span":[site.span.start,site.span.end],
                    "enclosing_function":site.enclosing_function.map(|span|[span.start,span.end])
                })).collect::<Vec<_>>(),
            "lexical_with_statements":audit.lexical_with_statements.iter()
                .map(|site|json!({
                    "span":[site.span.start,site.span.end],
                    "enclosing_function":site.enclosing_function.map(|span|[span.start,span.end])
                })).collect::<Vec<_>>(),
            "root_scope_binding":audit.root_scope_binding,
            "source_mutation_isolated":audit.source_mutation_isolated,
        }));
    }
    let reads = structurally_proven_lazy_registry_read_calls(&parsed.program, scoping, &budget)?;
    let installs =
        proven_origin_registry_handler_installs(&parsed.program, scoping, &flow, &budget)?;
    let mut seen_accessors = HashSet::new();
    let unique_reads = reads
        .iter()
        .filter(|read| {
            seen_accessors.insert((
                read.accessor_function_start,
                read.accessor_function_end,
                read.selector_start,
                read.selector_end,
            ))
        })
        .collect::<Vec<_>>();
    eprintln!("origin calls={} shape={} phase-closures={} reads={} distinct_accessor_shapes={} installs={}",
        flow.direct_calls.len(),shapes.len(),phase_closures.len(),reads.len(),unique_reads.len(),installs.len());

    let mut seen = HashSet::new();
    let mut reports: Vec<Value> = Vec::new();
    let mut key_reports: HashMap<i64, Vec<Value>> = HashMap::new();
    let mut captured_count = 0usize;
    'calls: for call in &flow.direct_calls {
        budget.consume(1)?;
        let Some(shape) = shapes.iter().find(|s| {
            s.function_start == call.callee.function_start
                && s.function_end == call.callee.function_end
        }) else {
            continue;
        };
        let Some(factory) =
            proven_slow_lazy_cell_factory_call(&source, &parsed.program, semantic, call)
        else {
            continue;
        };
        let Some(registry) =
            proven_slow_lazy_cell_registry_assignment(&parsed.program, semantic, &factory)
        else {
            continue;
        };
        let update = proven_slow_lazy_cell_update_state(&parsed.program, semantic, &factory);
        let possible_phase_closures = phase_closures
            .iter()
            .filter(|c| c.phase_binding_symbol == shape.phase_binding_symbol)
            .collect::<Vec<_>>();
        let mut phase_values = possible_phase_closures
            .iter()
            .flat_map(|p| [p.equal_value, p.unequal_value])
            .collect::<Vec<_>>();
        phase_values.sort_unstable();
        phase_values.dedup();
        let phase_evidence = possible_phase_closures
            .iter()
            .map(|p| {
                json!({
                  "function":[p.phase_function_start,p.phase_function_end],
                  "equal":p.equal_value,"unequal":p.unequal_value,
                  "phase_assignment":[p.phase_assignment_start,p.phase_assignment_end],
                  "method":[p.method_function_start,p.method_function_end]
                })
            })
            .collect::<Vec<_>>();
        for exact in proven_slow_lazy_cell_exact_registry_assignments(
            &source,
            &parsed.program,
            semantic,
            &flow,
            &registry,
        ) {
            budget.consume(1)?;
            for install in installs.iter().filter(|install| {
                install.exact_key == exact.exact_key_value
                    && install.origin.allocation_start == factory.call.callee.allocation_start
                    && install.origin.allocation_end == factory.call.callee.allocation_end
                    && install.origin.constructor_start == factory.call.callee.constructor_start
                    && install.origin.constructor_end == factory.call.callee.constructor_end
                    && install.install.registry_path == registry.registry_path
            }) {
                budget.consume(1)?;
                let Some(captured) = proven_slow_lazy_cell_captured_handler_install(
                    &source,
                    &parsed.program,
                    semantic,
                    &exact,
                    install,
                ) else {
                    continue;
                };
                let key = exact.exact_key_value;
                if !seen.insert((
                    key,
                    install.install.handler_start,
                    install.install.handler_end,
                )) {
                    continue;
                }
                captured_count += 1;
                eprintln!("captured key={key} ({captured_count}/{limit}): evaluating carrier and {} structural phase candidates",phase_values.len());
                let fields = proven_slow_lazy_cell_state_fields_for_exact_assignment(
                    &source,
                    &parsed.program,
                    semantic,
                    &exact,
                    &budget,
                )?;
                let mut per_phase = Vec::new();
                for read in unique_reads
                    .iter()
                    .filter(|r| r.read.registry_path == registry.registry_path)
                {
                    budget.consume(1)?;
                    let carrier = if let Some(fields) = fields.as_ref() {
                        proven_slow_lazy_cell_prototype_carrier(
                            &source,
                            &parsed.program,
                            semantic,
                            fields,
                            read,
                            &budget,
                        )?
                    } else {
                        None
                    };
                    for phase_value in &phase_values {
                        let resolver = update.as_ref().and_then(|u| {
                            proven_slow_lazy_cell_resolver_index(
                                &source,
                                &parsed.program,
                                semantic,
                                u,
                                SlowLazyCellResolverIndexFacts {
                                    selector: Span::new(read.selector_start, read.selector_end),
                                    selector_key_symbol: read.selector_key_symbol,
                                    exact_assignment: &exact,
                                    phase_value: *phase_value,
                                },
                            )
                        });
                        let resolved = resolver
                            .as_ref()
                            .and_then(|r| proven_slow_lazy_cell_resolved_handler(r, &captured));
                        let compatible = carrier
                            .as_ref()
                            .zip(resolved.as_ref())
                            .and_then(|(c, r)| structurally_compatible_slow_lazy_cell_read(r, c))
                            .is_some();
                        per_phase.push(json!({
                          "phase_value_assumed":phase_value,"resolver_index_proven":resolver.is_some(),
                          "compatible_return_structure":compatible,
                          "accessor":[read.accessor_function_start,read.accessor_function_end],
                          "selector":[read.selector_start,read.selector_end],
                          "carrier_proven":carrier.is_some(),
                        }));
                    }
                }
                let report = json!({
                    "key":key,"function":[captured.install.install.handler_start,captured.install.install.handler_end],
                    "factory_call":[factory.call.call_start,factory.call.call_end],
                    "state_fields_proven":fields.is_some(),"phase_closure_evidence":phase_evidence,
                    "conditional_phases":per_phase,
                    "limitations":["phase return at runtime not established","registry slot stability not proved","branch execution not observed"]
                });
                key_reports.entry(key).or_default().push(report.clone());
                reports.push(report);
                if captured_count >= limit {
                    break 'calls;
                }
            }
        }
    }
    let successes = reports
        .iter()
        .flat_map(|r| r["conditional_phases"].as_array().into_iter().flatten())
        .filter(|p| p["compatible_return_structure"] == true)
        .count();
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "captured_count":captured_count,"conditional_compatible_count":successes,
            "distinct_keys":key_reports.len(),"phase_closure_count":phase_closures.len(),
            "phase_binding_mutation_audits":phase_binding_mutation_audits,
            "distinct_accessor_shapes":unique_reads.len(),
            "reports":reports,
            "interpretation":"Each phase-value condition is a theorem premise, NOT evidence that the captured phase function returned that value at the actual call."
        }))?
    );
    Ok(())
}
