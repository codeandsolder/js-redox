use crate::{
    bytecode::{ArrayCandidate, PushBuilderCandidate},
    decoder::DecoderCandidate,
    dispatch::{DirectSwitchMapCandidate, HandlerTableCandidate},
    embedded::EmbeddedCodeCandidate,
    function_analysis::FunctionMetrics,
    safe_deob::SourceMode,
    scanner::scan_source_core,
    state_flatten::{IfLadderStateMachineCandidate, OpcodeMapCandidate, StateMachineCandidate},
    table_vm,
};
use anyhow::{Context, Result};
use serde::Serialize;
use std::{fs, path::Path};
use work_budget::WorkBudget;

#[derive(Debug, Clone, Serialize)]
pub struct EmbeddedScanReport {
    pub outer_start: u32,
    pub outer_end: u32,
    pub kind: String,
    pub body_bytes: usize,
    pub dump_path: Option<String>,
    pub diagnostics: usize,
    pub fatal_error: bool,
    pub arrays: Vec<ArrayCandidate>,
    pub push_builders: Vec<PushBuilderCandidate>,
    pub decoder_candidates: Vec<DecoderCandidate>,
    pub state_machines: Vec<StateMachineCandidate>,
    pub if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    pub opcode_maps: Vec<OpcodeMapCandidate>,
    pub direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    pub handler_tables: Vec<HandlerTableCandidate>,
    pub handler_function_tables: Vec<table_vm::DetailedHandlerTableCandidate>,
    pub byte_transducers: Vec<table_vm::ByteTransducerCandidate>,
    pub table_vms: Vec<table_vm::TableVmCandidate>,
    pub lazy_registry_indirect_calls: Vec<table_vm::LazyRegistryIndirectCallCandidate>,
    pub functions: Vec<FunctionMetrics>,
    pub embedded: Vec<Self>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ScanReport {
    pub file: String,
    pub bytes: usize,
    pub diagnostics: usize,
    pub fatal_error: bool,
    pub arrays: Vec<ArrayCandidate>,
    pub push_builders: Vec<PushBuilderCandidate>,
    pub decoder_candidates: Vec<DecoderCandidate>,
    pub state_machines: Vec<StateMachineCandidate>,
    pub if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    pub opcode_maps: Vec<OpcodeMapCandidate>,
    pub direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    pub handler_tables: Vec<HandlerTableCandidate>,
    pub handler_function_tables: Vec<table_vm::DetailedHandlerTableCandidate>,
    pub byte_transducers: Vec<table_vm::ByteTransducerCandidate>,
    pub table_vms: Vec<table_vm::TableVmCandidate>,
    pub lazy_registry_indirect_calls: Vec<table_vm::LazyRegistryIndirectCallCandidate>,
    pub functions: Vec<FunctionMetrics>,
    pub embedded: Vec<EmbeddedScanReport>,
}

fn scan_embedded_candidate(
    candidate: EmbeddedCodeCandidate,
    depth: usize,
    dump_dir: Option<&Path>,
    budget: &WorkBudget,
) -> Result<EmbeddedScanReport> {
    let wrapper = format!(
        "function __embedded({}) {{\n{}\n}}\n",
        candidate.params.join(","),
        candidate.body
    );

    let dump_path = dump_dir.and_then(|dir| {
        if fs::create_dir_all(dir).is_err() {
            return None;
        }
        let digest = crate::fnv1a64(wrapper.as_bytes());
        let path = dir.join(format!("embedded-{digest:016x}.js"));
        if !path.exists() && fs::write(&path, &wrapper).is_err() {
            return None;
        }
        Some(path.display().to_string())
    });

    let core = scan_source_core(&wrapper, SourceMode::CommonJs, budget)?;
    let embedded = if depth < 3 {
        core.embedded_code
            .into_iter()
            .map(|child| scan_embedded_candidate(child, depth + 1, dump_dir, budget))
            .collect::<Result<Vec<_>>>()?
    } else {
        Vec::new()
    };

    Ok(EmbeddedScanReport {
        outer_start: candidate.outer_start,
        outer_end: candidate.outer_end,
        kind: candidate.kind,
        body_bytes: candidate.body.len(),
        dump_path,
        diagnostics: core.diagnostics,
        fatal_error: core.fatal_error,
        arrays: core.arrays,
        push_builders: core.push_builders,
        decoder_candidates: core.decoder_candidates,
        state_machines: core.state_machines,
        if_ladder_state_machines: core.if_ladder_state_machines,
        opcode_maps: core.opcode_maps,
        direct_switch_maps: core.direct_switch_maps,
        handler_tables: core.handler_tables,
        handler_function_tables: core.handler_function_tables,
        byte_transducers: core.byte_transducers,
        table_vms: core.table_vms,
        lazy_registry_indirect_calls: core.lazy_registry_indirect_calls,
        functions: core.functions,
        embedded,
    })
}

pub fn scan_source(
    source: &str,
    input_label: impl Into<String>,
    dump_dir: Option<&Path>,
    source_mode: SourceMode,
    budget: &WorkBudget,
) -> Result<ScanReport> {
    let core = scan_source_core(source, source_mode, budget)?;
    let embedded = core
        .embedded_code
        .into_iter()
        .map(|candidate| scan_embedded_candidate(candidate, 1, dump_dir, budget))
        .collect::<Result<Vec<_>>>()?;

    Ok(ScanReport {
        file: input_label.into(),
        bytes: source.len(),
        diagnostics: core.diagnostics,
        fatal_error: core.fatal_error,
        arrays: core.arrays,
        push_builders: core.push_builders,
        decoder_candidates: core.decoder_candidates,
        state_machines: core.state_machines,
        if_ladder_state_machines: core.if_ladder_state_machines,
        opcode_maps: core.opcode_maps,
        direct_switch_maps: core.direct_switch_maps,
        handler_tables: core.handler_tables,
        handler_function_tables: core.handler_function_tables,
        byte_transducers: core.byte_transducers,
        table_vms: core.table_vms,
        lazy_registry_indirect_calls: core.lazy_registry_indirect_calls,
        functions: core.functions,
        embedded,
    })
}

pub fn scan_file(path: &Path, dump_dir: Option<&Path>, budget: &WorkBudget) -> Result<ScanReport> {
    let source = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    scan_source(
        &source,
        path.display().to_string(),
        dump_dir,
        SourceMode::for_path(path),
        budget,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn report_surface_preserves_scanner_inventory() -> Result<()> {
        let source = "function f(){ const code=[0,1,2,3]; return code[0]; }";
        let budget = WorkBudget::unlimited("scan-report-test");
        let report = scan_source(source, "fixture.js", None, SourceMode::Auto, &budget)?;
        assert_eq!(report.file, "fixture.js");
        assert_eq!(report.bytes, source.len());
        assert!(!report.fatal_error);
        Ok(())
    }

    #[test]
    fn scanner_respects_module_source_mode() -> Result<()> {
        let source = "export const value = 1;";
        let budget = WorkBudget::unlimited("scan-report-module-test");
        let report = scan_source(source, "fixture.mjs", None, SourceMode::Module, &budget)?;
        assert!(!report.fatal_error);
        assert_eq!(report.diagnostics, 0);
        Ok(())
    }
}
