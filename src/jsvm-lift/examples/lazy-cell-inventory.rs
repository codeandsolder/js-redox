use anyhow::{Context, Result};
use jsvm_lift::{
    forwarding_semantics::{
        structurally_proven_lazy_registry_read_calls, ProvenLazyRegistryReadCall,
    },
    lazy_cell::{
        proven_fast_lazy_cell_factory_call, proven_slow_lazy_cell_captured_handler_from_value,
        proven_slow_lazy_cell_captured_value_install,
        proven_slow_lazy_cell_exact_registry_assignments, proven_slow_lazy_cell_factory_call,
        proven_slow_lazy_cell_prototype_carrier, proven_slow_lazy_cell_registry_assignment,
        proven_slow_lazy_cell_resolved_handler, proven_slow_lazy_cell_resolver_index,
        proven_slow_lazy_cell_state_fields,
        proven_slow_lazy_cell_state_fields_for_exact_assignment,
        proven_slow_lazy_cell_update_state, structurally_compatible_slow_lazy_cell_read,
        structurally_proven_fast_lazy_cell_factory_shapes,
        structurally_proven_slow_lazy_cell_factory_shapes, FastLazyCellFactoryShape,
        ProvenSlowLazyCellCapturedHandlerInstall, ProvenSlowLazyCellCapturedValueInstall,
        ProvenSlowLazyCellExactRegistryAssignment, ProvenSlowLazyCellExactStateFields,
        ProvenSlowLazyCellPrototypeCarrier, ProvenSlowLazyCellRegistryAssignment,
        ProvenSlowLazyCellResolvedHandler, ProvenSlowLazyCellResolverIndex,
        ProvenSlowLazyCellStateFields, ProvenSlowLazyCellUpdateState, SlowLazyCellFactoryShape,
        SlowLazyCellReadCompatibility, SlowLazyCellResolverIndexFacts,
    },
    receiver_identity::{
        structurally_proven_origin_flow, ProvenOriginDirectCall, ProvenOriginFlow,
    },
    registry_identity::{
        proven_origin_registry_handler_installs, proven_origin_registry_value_installs,
        ProvenOriginRegistryHandlerInstall, ProvenOriginRegistryValueInstall,
    },
};
use oxc_allocator::Allocator;
use oxc_ast::ast::Program;
use oxc_semantic::{Scoping, Semantic, SemanticBuilder};
use oxc_span::{SourceType, Span};
use rolldown_redox::ecmascript::parse_program;
use serde_json::{json, Value};
use std::{env, fs, path::PathBuf};
use work_budget::{BudgetExceeded, WorkBudget};

fn snippet(source: &str, start: u32, end: u32) -> String {
    source
        .get(start as usize..(end as usize).min(source.len()))
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

/// Group a source file's lazy registry reads by their independently proven
/// accessor shape, rather than requiring every call to use one accessor.
fn distinct_lazy_accessor_families<'a>(
    reads: &'a [ProvenLazyRegistryReadCall],
    budget: &WorkBudget,
) -> Result<Vec<&'a ProvenLazyRegistryReadCall>, BudgetExceeded> {
    let mut families: Vec<&ProvenLazyRegistryReadCall> = Vec::new();
    for read in reads {
        budget.consume(1)?;
        let mut already_seen = false;
        for prior in &families {
            budget.consume(1)?;
            if prior.accessor_function_start == read.accessor_function_start
                && prior.accessor_function_end == read.accessor_function_end
                && prior.cell_assignment_start == read.cell_assignment_start
                && prior.cell_assignment_end == read.cell_assignment_end
                && prior.read.registry_path == read.read.registry_path
                && prior.probe_property == read.probe_property
                && prior.update_property == read.update_property
                && prior.projection_property == read.projection_property
                && prior.selector_start == read.selector_start
                && prior.selector_end == read.selector_end
                && prior.selector_key_symbol == read.selector_key_symbol
                && prior.selector_polynomial == read.selector_polynomial
            {
                already_seen = true;
                break;
            }
        }
        if already_seen {
            continue;
        }
        families.push(read);
    }
    Ok(families)
}

fn slow_shapes_json(
    shapes: &[SlowLazyCellFactoryShape],
    source: &str,
    scoping: &Scoping,
) -> Vec<Value> {
    shapes
        .iter()
        .map(|shape| {
            let phase = scoping.symbol_span(shape.phase_binding_symbol);
            let phase_local = scoping.symbol_span(shape.phase_local_symbol);
            let index_state = scoping.symbol_span(shape.index_state_symbol);
            json!({
                "function": [shape.function_start, shape.function_end],
                "guard": [shape.guard_start, shape.guard_end],
                "guard_source": snippet(source, shape.guard_start, shape.guard_end),
                "slow_sequence": [shape.slow_sequence_start, shape.slow_sequence_end],
                "state_parameter_index": shape.state_parameter_index,
                "handler_parameter_index": shape.handler_parameter_index,
                "handler_slot": shape.handler_slot,
                "handler_capture": [shape.handler_capture_start, shape.handler_capture_end],
                "handler_capture_source": snippet(source, shape.handler_capture_start, shape.handler_capture_end),
                "index_state_declaration": [index_state.start, index_state.end],
                "index_state_initialization": [shape.index_state_initialization_start, shape.index_state_initialization_end],
                "index_state_initialization_source": snippet(source, shape.index_state_initialization_start, shape.index_state_initialization_end),
                "prototype_field": shape.prototype_field,
                "method_key_field": shape.method_key_field,
                "phase_local_declaration": [phase_local.start, phase_local.end],
                "phase_binding_declaration": [phase.start, phase.end],
                "phase_capture": [shape.phase_capture_start, shape.phase_capture_end],
                "phase_capture_source": snippet(source, shape.phase_capture_start, shape.phase_capture_end),
                "cell_construction": [shape.cell_construction_start, shape.cell_construction_end],
                "cell_construction_source": snippet(source, shape.cell_construction_start, shape.cell_construction_end),
                "update_function": [shape.update_function_start, shape.update_function_end],
                "resolver_property": shape.resolver_property,
                "resolver_function": [shape.resolver_function_start, shape.resolver_function_end],
            })
        })
        .collect::<Vec<_>>()
}

fn fast_shapes_json(fast_shapes: &[FastLazyCellFactoryShape], source: &str) -> Vec<Value> {
    fast_shapes
        .iter()
        .map(|shape| json!({
            "function": [shape.function_start, shape.function_end],
            "guard": [shape.guard_start, shape.guard_end],
            "guard_source": snippet(source, shape.guard_start, shape.guard_end),
            "mode_parameter_index": shape.mode_parameter_index,
            "value_parameter_index": shape.value_parameter_index,
            "state_parameter_index": shape.state_parameter_index,
            "prototype_field": shape.prototype_field,
            "method_key_field": shape.method_key_field,
            "updater_property": shape.updater_property,
            "cell_construction": [shape.cell_construction_start, shape.cell_construction_end],
            "getter_function": [shape.getter_function_start, shape.getter_function_end],
            "updater_function": [shape.updater_function_start, shape.updater_function_end],
            "post_construction_cell_reference_barriers": shape
                .post_construction_cell_reference_barriers
                .iter()
                .map(|span| json!({
                    "span": [span.start, span.end],
                    "source": snippet(source, span.start, span.end),
                }))
                .collect::<Vec<_>>(),
            "standard_object_create_semantics_required": shape.standard_object_create_semantics_required,
        }))
        .collect::<Vec<_>>()
}

fn fast_calls_json(
    flow: &ProvenOriginFlow,
    fast_shapes: &[FastLazyCellFactoryShape],
    source: &str,
    program: &Program<'_>,
    semantic: &Semantic<'_>,
) -> Vec<Value> {
    flow.direct_calls
        .iter()
        .filter(|call| {
            fast_shapes.iter().any(|shape| {
                (shape.function_start, shape.function_end)
                    == (call.callee.function_start, call.callee.function_end)
            })
        })
        .map(|call| {
            let proven = proven_fast_lazy_cell_factory_call(source, program, semantic, call);
            json!({
                "call": [call.call_start, call.call_end],
                "call_source": snippet(source, call.call_start, call.call_end),
                "caller": [call.caller.function_start, call.caller.function_end],
                "origin_parameter_indices": call.callee.parameter_indices,
                "exact_integer_arguments": call.exact_integer_arguments,
                "proven": proven.is_some(),
                "exact_mode_value": proven.as_ref().map(|proof| proof.exact_mode_value),
            })
        })
        .collect::<Vec<_>>()
}

struct SlowCallProof {
    specialized: bool,
    state_fields: Option<ProvenSlowLazyCellStateFields>,
    update: Option<ProvenSlowLazyCellUpdateState>,
    registry: Option<ProvenSlowLazyCellRegistryAssignment>,
    exact_assignments: Vec<ProvenSlowLazyCellExactRegistryAssignment>,
    path_state_fields: Vec<ProvenSlowLazyCellExactStateFields>,
    carrier_proofs: Vec<ProvenSlowLazyCellPrototypeCarrier>,
    captured_handlers: Vec<ProvenSlowLazyCellCapturedHandlerInstall>,
    captured_values: Vec<ProvenSlowLazyCellCapturedValueInstall>,
    resolver_proofs: Vec<ProvenSlowLazyCellResolverIndex>,
    resolved_handlers: Vec<ProvenSlowLazyCellResolvedHandler>,
    read_compatibilities: Vec<SlowLazyCellReadCompatibility>,
}

fn captured_handlers_json(
    proof: &ProvenSlowLazyCellCapturedHandlerInstall,
    source: &str,
    scoping: &Scoping,
) -> Value {
    json!({
        "exact_key_value": proof.exact_assignment.exact_key_value,
        "logical_install": [proof.install.install.call_start, proof.install.install.call_end],
        "handler": [proof.install.install.handler_start, proof.install.install.handler_end],
        "handler_source": snippet(
            source,
            proof.install.install.handler_start,
            proof.install.install.handler_end,
        ),
        "caller_handler_parameter_index": proof.caller_handler_parameter_index,
        "caller_handler_symbol": scoping.symbol_name(proof.caller_handler_symbol),
    })
}

fn captured_values_json(
    proof: &ProvenSlowLazyCellCapturedValueInstall,
    source: &str,
    scoping: &Scoping,
) -> Value {
    json!({
        "exact_key_value": proof.exact_assignment.exact_key_value,
        "logical_install": [proof.install.install.call_start, proof.install.install.call_end],
        "value": [proof.install.install.value_start, proof.install.install.value_end],
        "value_source": snippet(
            source,
            proof.install.install.value_start,
            proof.install.install.value_end,
        ),
        "caller_value_parameter_index": proof.caller_value_parameter_index,
        "caller_value_symbol": scoping.symbol_name(proof.caller_value_symbol),
    })
}

impl SlowCallProof {
    fn report(&self, call: &ProvenOriginDirectCall, source: &str, scoping: &Scoping) -> Value {
        let Self {
            specialized,
            state_fields,
            update,
            registry,
            exact_assignments,
            path_state_fields,
            carrier_proofs,
            captured_handlers,
            captured_values,
            resolver_proofs,
            resolved_handlers,
            read_compatibilities,
        } = self;
        json!({
            "call": [call.call_start, call.call_end],
            "call_source": snippet(source, call.call_start, call.call_end),
            "caller": [call.caller.function_start, call.caller.function_end],
            "callee": [call.callee.function_start, call.callee.function_end],
            "allocation": [call.callee.allocation_start, call.callee.allocation_end],
            "constructor": [call.callee.constructor_start, call.callee.constructor_end],
            "origin_parameter_indices": call.callee.parameter_indices,
            "exact_integer_arguments": call.exact_integer_arguments,
            "specialized": specialized,
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
                "key_source": snippet(source, registry.key_start, registry.key_end),
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
            "path_state_fields": path_state_fields.iter().map(|proof| json!({
                "exact_key_value": proof.exact_assignment.exact_key_value,
                "prototype_field": proof.fields.prototype_field.initialization.property,
                "method_key_value": proof.fields.method_key.string.assignment.value,
            })).collect::<Vec<_>>(),
            "carrier_proofs": carrier_proofs.iter().map(|proof| json!({
                "exact_key_value": proof.state_fields.exact_assignment.exact_key_value,
                "method_name": proof.method_name,
                "projection_property": proof.projection_property,
                "resolver_property": proof.resolver_property,
                "helper_call": [proof.helper_call_start, proof.helper_call_end],
                "helper_create": [proof.helper_create_start, proof.helper_create_end],
                "getter": [proof.getter_function_start, proof.getter_function_end],
                "standard_object_prototype_semantics_required": proof.standard_object_prototype_semantics_required,
            })).collect::<Vec<_>>(),
            "captured_handlers": captured_handlers.iter().map(|proof| captured_handlers_json(proof, source, scoping)).collect::<Vec<_>>(),
            "captured_values": captured_values.iter().map(|proof| captured_values_json(proof, source, scoping)).collect::<Vec<_>>(),
            "resolver_proofs": resolver_proofs.iter().map(|resolver| json!({
                "phase_value": resolver.phase_value,
                "exact_key_value": resolver.exact_key_value,
                "handler_slot": resolver.handler_slot,
                "index_assignment": [resolver.index_assignment_start, resolver.index_assignment_end],
                "index_assignment_source": snippet(
                    source,
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
            "read_compatibilities": read_compatibilities.iter().map(|proof| json!({
                "exact_key_value": proof.resolved_handler.resolver.exact_key_value,
                "handler_slot": proof.resolved_handler.resolver.handler_slot,
                "logical_handler": [
                    proof.resolved_handler.captured_handler.install.install.handler_start,
                    proof.resolved_handler.captured_handler.install.install.handler_end,
                ],
            })).collect::<Vec<_>>(),
        })
    }
}

struct SlowCallAnalyzer<'a, 'ast> {
    source: &'a str,
    program: &'a Program<'ast>,
    semantic: &'a Semantic<'ast>,
    flow: &'a ProvenOriginFlow,
    budget: &'a WorkBudget,
    accessors: &'a [&'a ProvenLazyRegistryReadCall],
    origin_installs: &'a [ProvenOriginRegistryHandlerInstall],
    origin_value_installs: &'a [ProvenOriginRegistryValueInstall],
    phase_value: Option<i64>,
}

impl SlowCallAnalyzer<'_, '_> {
    fn carriers(
        &self,
        exact_assignments: &[ProvenSlowLazyCellExactRegistryAssignment],
    ) -> Result<(
        Vec<ProvenSlowLazyCellExactStateFields>,
        Vec<ProvenSlowLazyCellPrototypeCarrier>,
    )> {
        let mut path_state_fields = Vec::new();
        for exact_assignment in exact_assignments {
            if let Some(fields) = proven_slow_lazy_cell_state_fields_for_exact_assignment(
                self.source,
                self.program,
                self.semantic,
                exact_assignment,
                self.budget,
            )? {
                path_state_fields.push(fields);
            }
        }
        let mut carrier_proofs = Vec::new();
        for accessor in self.accessors {
            for fields in &path_state_fields {
                if let Some(proof) = proven_slow_lazy_cell_prototype_carrier(
                    self.source,
                    self.program,
                    self.semantic,
                    fields,
                    accessor,
                    self.budget,
                )? {
                    carrier_proofs.push(proof);
                }
            }
        }
        Ok((path_state_fields, carrier_proofs))
    }
    fn captures(
        &self,
        exact_assignments: &[ProvenSlowLazyCellExactRegistryAssignment],
    ) -> (
        Vec<ProvenSlowLazyCellCapturedValueInstall>,
        Vec<ProvenSlowLazyCellCapturedHandlerInstall>,
    ) {
        let mut captured_values = Vec::new();
        for exact_assignment in exact_assignments {
            for install in self.origin_value_installs {
                if let Some(proof) = proven_slow_lazy_cell_captured_value_install(
                    self.source,
                    self.program,
                    self.semantic,
                    exact_assignment,
                    install,
                ) {
                    captured_values.push(proof);
                }
            }
        }
        let captured_handlers = captured_values
            .iter()
            .flat_map(|captured| {
                self.origin_installs.iter().filter_map(|install| {
                    proven_slow_lazy_cell_captured_handler_from_value(captured, install)
                })
            })
            .collect::<Vec<_>>();
        (captured_values, captured_handlers)
    }
    fn resolvers(
        &self,
        update: Option<&ProvenSlowLazyCellUpdateState>,
        exact_assignments: &[ProvenSlowLazyCellExactRegistryAssignment],
    ) -> Vec<ProvenSlowLazyCellResolverIndex> {
        let mut resolver_proofs = Vec::new();
        if let (Some(update), Some(phase_value)) = (update, self.phase_value) {
            for accessor in self.accessors {
                for exact_assignment in exact_assignments {
                    if let Some(proof) = proven_slow_lazy_cell_resolver_index(
                        self.source,
                        self.program,
                        self.semantic,
                        update,
                        SlowLazyCellResolverIndexFacts {
                            selector: Span::new(accessor.selector_start, accessor.selector_end),
                            selector_key_symbol: accessor.selector_key_symbol,
                            exact_assignment,
                            phase_value,
                        },
                    ) {
                        resolver_proofs.push(proof);
                    }
                }
            }
        }
        resolver_proofs
    }
    fn prove_call(&self, call: &ProvenOriginDirectCall) -> Result<SlowCallProof> {
        let specialized =
            proven_slow_lazy_cell_factory_call(self.source, self.program, self.semantic, call);
        let update = specialized.as_ref().and_then(|factory| {
            proven_slow_lazy_cell_update_state(self.program, self.semantic, factory)
        });
        let state_fields = if let Some(factory) = specialized.as_ref() {
            proven_slow_lazy_cell_state_fields(
                self.source,
                self.program,
                self.semantic,
                factory,
                self.budget,
            )?
        } else {
            None
        };
        let registry = specialized.as_ref().and_then(|factory| {
            proven_slow_lazy_cell_registry_assignment(self.program, self.semantic, factory)
        });
        let exact_assignments = registry.as_ref().map_or_default(|registry| {
            proven_slow_lazy_cell_exact_registry_assignments(
                self.source,
                self.program,
                self.semantic,
                self.flow,
                registry,
            )
        });
        let (path_state_fields, carrier_proofs) = self.carriers(&exact_assignments)?;
        let (captured_values, captured_handlers) = self.captures(&exact_assignments);
        let resolver_proofs = self.resolvers(update.as_ref(), &exact_assignments);
        let mut resolved_handlers = Vec::new();
        for resolver in &resolver_proofs {
            for captured in &captured_handlers {
                if let Some(proof) = proven_slow_lazy_cell_resolved_handler(resolver, captured) {
                    resolved_handlers.push(proof);
                }
            }
        }
        let mut read_compatibilities = Vec::new();
        for resolved in &resolved_handlers {
            for carrier in &carrier_proofs {
                if let Some(proof) = structurally_compatible_slow_lazy_cell_read(resolved, carrier)
                {
                    read_compatibilities.push(proof);
                }
            }
        }
        Ok(SlowCallProof {
            specialized: specialized.is_some(),
            state_fields,
            update,
            registry,
            exact_assignments,
            path_state_fields,
            carrier_proofs,
            captured_handlers,
            captured_values,
            resolver_proofs,
            resolved_handlers,
            read_compatibilities,
        })
    }
}

fn accessor_families_json(
    accessors: &[&ProvenLazyRegistryReadCall],
    lazy_reads: &[ProvenLazyRegistryReadCall],
    source: &str,
    scoping: &Scoping,
) -> Vec<Value> {
    accessors
        .iter()
        .map(|accessor| {
            json!({
                "call_count": lazy_reads.iter().filter(|read| {
                    read.accessor_function_start == accessor.accessor_function_start
                        && read.accessor_function_end == accessor.accessor_function_end
                }).count(),
                "function": [accessor.accessor_function_start, accessor.accessor_function_end],
                "registry_path": accessor.read.registry_path,
                "fast_probe_property": accessor.probe_property,
                "update_property": accessor.update_property,
                "projection_property": accessor.projection_property,
                "selector": [accessor.selector_start, accessor.selector_end],
                "selector_source": snippet(source, accessor.selector_start, accessor.selector_end),
                "selector_key_symbol": scoping.symbol_name(accessor.selector_key_symbol),
            })
        })
        .collect::<Vec<_>>()
}

struct Inventory {
    phase_value: Option<i64>,
    accessor_families_json: Vec<Value>,
    shape_json: Vec<Value>,
    fast_shape_json: Vec<Value>,
    fast_calls: Vec<Value>,
    candidate_calls: Vec<Value>,
    handler_installs: usize,
    value_installs: usize,
}

impl Inventory {
    fn report(&self) -> Value {
        let Self {
            phase_value,
            accessor_families_json,
            shape_json,
            fast_shape_json,
            fast_calls,
            candidate_calls,
            handler_installs,
            value_installs,
        } = self;
        let specialized_calls = candidate_calls
            .iter()
            .filter(|call| call["specialized"] == true)
            .cloned()
            .collect::<Vec<_>>();
        let state_field_proven_calls = candidate_calls
            .iter()
            .filter(|call| !call["state_fields"].is_null())
            .count();
        let captured_value_proofs = candidate_calls
            .iter()
            .map(|call| call["captured_values"].as_array().map_or(0, Vec::len))
            .sum::<usize>();
        let resolver_proven_calls = candidate_calls
            .iter()
            .map(|call| call["resolver_proofs"].as_array().map_or(0, Vec::len))
            .sum::<usize>();
        let resolved_handler_proofs = candidate_calls
            .iter()
            .map(|call| call["resolved_handlers"].as_array().map_or(0, Vec::len))
            .sum::<usize>();
        let read_compatibility_count = candidate_calls
            .iter()
            .map(|call| call["read_compatibilities"].as_array().map_or(0, Vec::len))
            .sum::<usize>();
        json!({
            "phase_value": phase_value,
            "lazy_accessor_families": accessor_families_json,
            "shapes": shape_json,
            "fast_shapes": fast_shape_json,
            "fast_calls": fast_calls,
            "candidate_calls": candidate_calls,
            "specialized_calls": specialized_calls,
            "origin_handler_installs": handler_installs,
            "origin_value_installs": value_installs,
            "captured_value_proofs": captured_value_proofs,
            "state_field_proven_calls": state_field_proven_calls,
            "resolver_proven_calls": resolver_proven_calls,
            "resolved_handler_proofs": resolved_handler_proofs,
            "read_compatibility_count": read_compatibility_count,
        })
    }
}

fn main() -> Result<()> {
    let budget = WorkBudget::unlimited("lazy-cell-inventory");
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

    let lazy_reads =
        structurally_proven_lazy_registry_read_calls(&parsed.program, scoping, &budget)?;
    let accessors = distinct_lazy_accessor_families(&lazy_reads, &budget)?;

    let shapes = structurally_proven_slow_lazy_cell_factory_shapes(&parsed.program, scoping);
    let shape_json = slow_shapes_json(&shapes, &source, scoping);
    let fast_shapes = structurally_proven_fast_lazy_cell_factory_shapes(&parsed.program, scoping);
    let fast_shape_json = fast_shapes_json(&fast_shapes, &source);
    let flow = structurally_proven_origin_flow(&parsed.program, scoping, &budget)?;
    let fast_calls = fast_calls_json(
        &flow,
        &fast_shapes,
        &source,
        &parsed.program,
        &semantic.semantic,
    );
    let origin_installs =
        proven_origin_registry_handler_installs(&parsed.program, scoping, &flow, &budget)?;
    let origin_value_installs =
        proven_origin_registry_value_installs(&parsed.program, scoping, &flow, &budget)?;
    let analyzer = SlowCallAnalyzer {
        source: &source,
        program: &parsed.program,
        semantic: &semantic.semantic,
        flow: &flow,
        budget: &budget,
        accessors: &accessors,
        origin_installs: &origin_installs,
        origin_value_installs: &origin_value_installs,
        phase_value,
    };
    let candidate_calls = flow
        .direct_calls
        .iter()
        .filter(|call| {
            shapes.iter().any(|shape| {
                shape.function_start == call.callee.function_start
                    && shape.function_end == call.callee.function_end
            })
        })
        .map(|call| -> Result<_> {
            let proof = analyzer.prove_call(call)?;
            Ok(proof.report(call, &source, scoping))
        })
        .collect::<Result<Vec<_>>>()?;
    let accessor_families_json = accessor_families_json(&accessors, &lazy_reads, &source, scoping);
    let inventory = Inventory {
        phase_value,
        accessor_families_json,
        shape_json,
        fast_shape_json,
        fast_calls,
        candidate_calls,
        handler_installs: origin_installs.len(),
        value_installs: origin_value_installs.len(),
    };
    println!("{}", serde_json::to_string_pretty(&inventory.report())?);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::distinct_lazy_accessor_families;
    use jsvm_lift::forwarding_semantics::structurally_proven_lazy_registry_read_calls;
    use oxc_allocator::Allocator;
    use oxc_ast::ast::Program;
    use oxc_semantic::{Scoping, Semantic, SemanticBuilder};
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;
    use work_budget::{BudgetLimits, WorkBudget};

    #[test]
    fn distinct_lazy_accessor_families_preserve_two_shapes_and_deduplicate_calls() {
        let source = r#"
            function first(s,k,v) {
                v=s.T[k];
                if(v.ready) return v.refresh();
                return (v.refresh(k*2+1),v).current;
            }
            function second(s,k,v) {
                v=s.T[k];
                switch(!v.ready) {
                    case false: return v.refresh();
                }
                return (v.refresh(k*3+1),v).current;
            }
            first(state,12);
            second(state,20);
            first(state,30);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let budget = WorkBudget::unlimited("lazy families");
        let reads = structurally_proven_lazy_registry_read_calls(
            &parsed.program,
            semantic.semantic.scoping(),
            &budget,
        )
        .expect("lazy registry reads");
        assert_eq!(reads.len(), 3);
        let families =
            distinct_lazy_accessor_families(&reads, &budget).expect("distinct accessor families");
        assert_eq!(families.len(), 2);
        assert_ne!(
            families[0].accessor_function_start,
            families[1].accessor_function_start
        );
        assert_eq!(families[0].read.registry_path, ["T"]);
        assert_eq!(families[1].read.registry_path, ["T"]);

        let exhausted = WorkBudget::new("exhausted families", BudgetLimits::work(0));
        assert!(distinct_lazy_accessor_families(&reads, &exhausted).is_err());
    }
}
