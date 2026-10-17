use super::{
    copied_input::{externref_bulk_copy_candidates, ExternrefBulkCopyCandidateReport},
    helper_recognition::build_semantic_call_names,
    host_effect::{opaque_host_effect_memory_reads, OpaqueHostEffectMemoryReadReport},
    ir::i32_const,
    nesting::annotate_nested_machines,
    reporting::{
        annotate_composed_machine_flows, annotate_initial_entries, compose_machine_pipelines,
        linearize_state_graph, root_machine_indices, summarize_state_case, terminal_bindings,
        MachineMeta, SemanticBindingReport, StateMachinePipelineReport, StateMachineReport,
    },
    semantic_render::{render_return_expressions, SemanticRuntimeBindingReport},
    transition::{state_cmp_count, transitions_for},
};
use anyhow::{anyhow, Context, Result};
use serde::Serialize;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    panic::{catch_unwind, AssertUnwindSafe},
};
use waffle::{entity::EntityRef, ExportKind, FrontendOptions, Module, OptOptions};

#[derive(Debug, Serialize)]
pub struct ExportSemanticAnalysis {
    pub state_machine_roots: Vec<usize>,
    pub state_machine_pipelines: Vec<StateMachinePipelineReport>,
    pub state_machines: Vec<StateMachineReport>,
    pub terminal_bindings: Vec<SemanticBindingReport>,
    pub runtime_bindings: Vec<SemanticRuntimeBindingReport>,
    pub externref_bulk_copy_candidates: Vec<ExternrefBulkCopyCandidateReport>,
    pub opaque_host_effect_memory_reads: Vec<OpaqueHostEffectMemoryReadReport>,
    pub return_expressions: Vec<String>,
}

pub fn analyze_export_semantics(bytes: &[u8], export_name: &str) -> Result<ExportSemanticAnalysis> {
    match catch_unwind(AssertUnwindSafe(|| analyze_inner(bytes, export_name))) {
        Ok(result) => result,
        Err(payload) => {
            let detail = payload
                .downcast_ref::<&str>()
                .map(|value| (*value).to_owned())
                .or_else(|| payload.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "non-string panic payload".to_owned());
            Err(anyhow!("WAFFLE analysis panicked: {detail}"))
        }
    }
}

fn analyze_inner(bytes: &[u8], export_name: &str) -> Result<ExportSemanticAnalysis> {
    let mut module = Module::from_wasm_bytes(bytes, &FrontendOptions::default())?;
    let func = module
        .exports
        .iter()
        .find_map(|e| match e.kind {
            ExportKind::Func(f) if e.name == export_name => Some(f),
            _ => None,
        })
        .context("export")?;
    // Copied-input byte-integrity proofs summarize side effects through the
    // reachable internal call graph. Expand lazy defined bodies up front so an
    // unparsed internal helper is never mistaken for an opaque host import.
    module.expand_all_funcs()?;
    module.funcs[func]
        .body_mut()
        .context("body")?
        .optimize(&OptOptions::default());
    let call_names = build_semantic_call_names(&mut module, func);
    let body = module.funcs[func].body().context("body")?;
    let externref_bulk_copy_candidates = externref_bulk_copy_candidates(&module, body, &call_names);

    let mut candidates = Vec::new();
    for (block, def) in body.blocks.entries() {
        for (param_index, (_, param)) in def.params.iter().enumerate() {
            let n = state_cmp_count(body, *param);
            if n >= 5 {
                candidates.push((n, block, param_index, *param));
            }
        }
    }
    candidates.sort_by_key(|(n, _, _, _)| std::cmp::Reverse(*n));

    let mut machines = Vec::new();
    let mut metadata = Vec::new();
    for (cmp_count, dispatcher, param_index, state) in candidates {
        let mut initial = BTreeSet::new();
        for (_, pred) in body.blocks.entries() {
            pred.terminator.visit_targets(|target| {
                if target.block == dispatcher {
                    if let Some(arg) = target.args.get(param_index) {
                        if let Some(c) = i32_const(body, *arg) {
                            initial.insert(c);
                        }
                    }
                }
            });
        }
        if initial.is_empty() {
            continue;
        }
        let mut states = initial.iter().copied().collect::<VecDeque<_>>();
        let mut seen = BTreeSet::new();
        let mut graph: BTreeMap<u32, BTreeSet<u32>> = BTreeMap::new();
        let mut unresolved = 0usize;
        let mut forks = 0usize;
        while let Some(current) = states.pop_front() {
            if !seen.insert(current) || seen.len() > 256 {
                continue;
            }
            let trace = transitions_for(body, dispatcher, state, param_index, current);
            unresolved = unresolved.saturating_add(trace.unresolved_backedges);
            forks = forks.saturating_add(trace.data_forks);
            for n in &trace.next {
                if !seen.contains(n) {
                    states.push_back(*n);
                }
            }
            graph.insert(current, trace.next);
        }

        let incoming = graph
            .values()
            .flat_map(|successors| successors.iter().copied())
            .collect::<BTreeSet<_>>();
        let graph_roots = graph
            .keys()
            .copied()
            .filter(|state| !incoming.contains(state))
            .collect::<BTreeSet<_>>();
        if !graph_roots.is_empty() {
            initial = graph_roots;
        }

        let linearized = linearize_state_graph(&initial, &graph);
        let order = linearized
            .clone()
            .unwrap_or_else(|| graph.keys().copied().collect());
        let cases = order
            .into_iter()
            .map(|current| {
                let trace = transitions_for(body, dispatcher, state, param_index, current);
                summarize_state_case(
                    body,
                    dispatcher,
                    state,
                    param_index,
                    current,
                    &trace,
                    &BTreeSet::new(),
                )
            })
            .collect();

        let machine_index = machines.len();
        machines.push(StateMachineReport {
            machine_index,
            state_value: state.index(),
            dispatcher_block: dispatcher.index(),
            parameter_count: body.blocks[dispatcher].params.len(),
            state_param_index: param_index,
            initial_entries: Vec::new(),
            comparisons: cmp_count,
            initial,
            graph,
            linearized,
            cases,
            unresolved_backedges: unresolved,
            data_forks: forks,
        });
        metadata.push(MachineMeta {
            dispatcher,
            state,
            param_index,
        });
    }
    annotate_initial_entries(body, &mut machines, &metadata);
    annotate_nested_machines(body, &mut machines, &metadata);
    annotate_composed_machine_flows(&mut machines);
    let state_machine_roots = root_machine_indices(&machines);
    let state_machine_pipelines = compose_machine_pipelines(&machines);
    let (bindings, terminal_bindings) = terminal_bindings(body, &machines, &metadata);
    let (return_expressions, runtime_bindings, runtime_names) =
        render_return_expressions(body, &bindings, &call_names);
    let opaque_host_effect_memory_reads =
        opaque_host_effect_memory_reads(body, &call_names, &runtime_names);
    Ok(ExportSemanticAnalysis {
        state_machine_roots,
        state_machine_pipelines,
        state_machines: machines,
        terminal_bindings,
        runtime_bindings,
        externref_bulk_copy_candidates,
        opaque_host_effect_memory_reads,
        return_expressions,
    })
}
