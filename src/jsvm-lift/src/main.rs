mod ast_utils;
mod bytecode;
mod decoder;
mod dispatch;
mod embedded;
mod function_analysis;
mod scanner;
mod source_text;
mod state_flatten;
mod table_vm;

use anyhow::{Context, Result};
use bytecode::{ArrayCandidate, PushBuilderCandidate};
use clap::Parser as ClapParser;
use decoder::DecoderCandidate;
use dispatch::{DirectSwitchMapCandidate, HandlerTableCandidate};
use embedded::EmbeddedCodeCandidate;
use function_analysis::FunctionMetrics;
use scanner::scan_source_core;
use serde::Serialize;
use state_flatten::{IfLadderStateMachineCandidate, OpcodeMapCandidate, StateMachineCandidate};
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Detect and inventory JavaScript VM-obfuscation structures")]
struct Args {
    #[arg(required = true)]
    files: Vec<PathBuf>,

    /// Emit one JSON object per file.
    #[arg(long)]
    json: bool,

    /// Minimum VM-likelihood score for text output.
    #[arg(long, default_value_t = 8)]
    min_score: u32,

    /// Materialize statically recovered Function(...) bodies as synthetic JS files.
    #[arg(long)]
    dump_embedded: Option<PathBuf>,
}

#[derive(Debug, Serialize)]
struct EmbeddedScanReport {
    outer_start: u32,
    outer_end: u32,
    kind: String,
    body_bytes: usize,
    dump_path: Option<String>,
    diagnostics: usize,
    panicked: bool,
    arrays: Vec<ArrayCandidate>,
    push_builders: Vec<PushBuilderCandidate>,
    decoder_candidates: Vec<DecoderCandidate>,
    state_machines: Vec<StateMachineCandidate>,
    if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    opcode_maps: Vec<OpcodeMapCandidate>,
    direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    handler_tables: Vec<HandlerTableCandidate>,
    handler_function_tables: Vec<table_vm::DetailedHandlerTableCandidate>,
    byte_transducers: Vec<table_vm::ByteTransducerCandidate>,
    table_vms: Vec<table_vm::TableVmCandidate>,
    functions: Vec<FunctionMetrics>,
    embedded: Vec<Self>,
}

#[derive(Debug, Serialize)]
struct ScanReport {
    file: String,
    bytes: usize,
    diagnostics: usize,
    panicked: bool,
    arrays: Vec<ArrayCandidate>,
    push_builders: Vec<PushBuilderCandidate>,
    decoder_candidates: Vec<DecoderCandidate>,
    state_machines: Vec<StateMachineCandidate>,
    if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    opcode_maps: Vec<OpcodeMapCandidate>,
    direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    handler_tables: Vec<HandlerTableCandidate>,
    handler_function_tables: Vec<table_vm::DetailedHandlerTableCandidate>,
    byte_transducers: Vec<table_vm::ByteTransducerCandidate>,
    table_vms: Vec<table_vm::TableVmCandidate>,
    functions: Vec<FunctionMetrics>,
    embedded: Vec<EmbeddedScanReport>,
}

fn embedded_hash(bytes: &[u8]) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325_u64;
    for byte in bytes {
        h ^= u64::from(*byte);
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    h
}

fn scan_embedded_candidate(
    candidate: EmbeddedCodeCandidate,
    depth: usize,
    dump_dir: Option<&std::path::Path>,
) -> EmbeddedScanReport {
    let wrapper = format!(
        "function __embedded({}) {{\n{}\n}}\n",
        candidate.params.join(","),
        candidate.body
    );

    let dump_path = dump_dir.and_then(|dir| {
        if fs::create_dir_all(dir).is_err() {
            return None;
        }
        let digest = embedded_hash(wrapper.as_bytes());
        let path = dir.join(format!("embedded-{digest:016x}.js"));
        if !path.exists() && fs::write(&path, &wrapper).is_err() {
            return None;
        }
        Some(path.display().to_string())
    });

    let core = scan_source_core(&wrapper);
    let embedded = if depth < 3 {
        core.embedded_code
            .into_iter()
            .map(|c| scan_embedded_candidate(c, depth + 1, dump_dir))
            .collect()
    } else {
        Vec::new()
    };

    EmbeddedScanReport {
        outer_start: candidate.outer_start,
        outer_end: candidate.outer_end,
        kind: candidate.kind,
        body_bytes: candidate.body.len(),
        dump_path,
        diagnostics: core.diagnostics,
        panicked: core.panicked,
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
        functions: core.functions,
        embedded,
    }
}

fn scan_file(path: &PathBuf, dump_dir: Option<&std::path::Path>) -> Result<ScanReport> {
    let source = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    let core = scan_source_core(&source);
    let embedded = core
        .embedded_code
        .into_iter()
        .map(|c| scan_embedded_candidate(c, 1, dump_dir))
        .collect();

    Ok(ScanReport {
        file: path.display().to_string(),
        bytes: source.len(),
        diagnostics: core.diagnostics,
        panicked: core.panicked,
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
        functions: core.functions,
        embedded,
    })
}

fn print_embedded(report: &EmbeddedScanReport, min_score: u32, depth: usize) {
    let indent = "  ".repeat(depth);
    println!(
        "{indent}embedded {} @{:x}-{:x}: {} bytes, {} diagnostics, {} arrays, {} push builders, {} decoders, {} state machines, {} opcode maps, {} handler tables{}",
        report.kind,
        report.outer_start,
        report.outer_end,
        report.body_bytes,
        report.diagnostics,
        report.arrays.len(),
        report.push_builders.len(),
        report.decoder_candidates.len(),
        report.state_machines.len(),
        report.opcode_maps.len(),
        report.handler_tables.len(),
        report
            .dump_path
            .as_ref()
            .map(|p| format!(" -> {p}"))
            .unwrap_or_default()
    );

    for d in report.decoder_candidates.iter().take(12) {
        println!(
            "{indent}  decoder {}: object={} builder={} width={} ip={} base={} offsets={:?} {}",
            d.function_id,
            d.object,
            d.builder_var.as_deref().unwrap_or("?"),
            d.width,
            d.ip,
            d.base.as_deref().unwrap_or("<inline>"),
            d.operand_offsets,
            d.preview
        );
    }
    for sm in report.state_machines.iter().take(12) {
        println!(
            "{indent}  state-machine {}: state={} init={} mask={} shift={:?} selector={} cases={}",
            sm.function_id,
            sm.state_var,
            sm.init_state,
            sm.mask,
            sm.shift,
            sm.selector_var.as_deref().unwrap_or("?"),
            sm.switch_cases
        );
    }
    for h in report.handler_tables.iter().take(8) {
        println!(
            "{indent}  handler table ({}) @{:x}-{:x}: entries={} functions={} async={}",
            h.container_kind,
            h.start,
            h.end,
            h.properties,
            h.function_values,
            h.async_function_values
        );
    }
    for f in report
        .functions
        .iter()
        .filter(|f| f.score >= min_score)
        .take(20)
    {
        println!(
            "{indent}  {} score={:2} {} {} @{:x}-{:x} bytes={} switch_cases={} loops={} computed={} computed_calls={} :: {}{}",
            if f.confirmed_dispatch { "[CONFIRMED]" } else { "[candidate]" },
            f.score,
            f.kind,
            f.name.as_deref().unwrap_or("<anon>"),
            f.start,
            f.end,
            f.bytes,
            f.switch_cases,
            f.loops,
            f.computed_members,
            f.computed_calls,
            f.reasons.join("; "),
            if f.dispatch_reasons.is_empty() {
                String::new()
            } else {
                format!(" | dispatch: {}", f.dispatch_reasons.join("; "))
            }
        );
    }
    for child in &report.embedded {
        print_embedded(child, min_score, depth + 1);
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    for path in &args.files {
        let report = scan_file(path, args.dump_embedded.as_deref())?;
        if args.json {
            println!("{}", serde_json::to_string(&report)?);
            continue;
        }

        println!(
            "{}: {} bytes, {} parse diagnostics, {} array candidates, {} push-builder candidates, {} decoder candidates, {} state machines, {} opcode maps, {} handler-table candidates",
            report.file,
            report.bytes,
            report.diagnostics,
            report.arrays.len(),
            report.push_builders.len(),
            report.decoder_candidates.len(),
            report.state_machines.len(),
            report.opcode_maps.len(),
            report.handler_tables.len()
        );

        for a in report.arrays.iter().take(8) {
            let hints = a
                .width_hints
                .iter()
                .take(3)
                .map(|h| format!("w{}:{}", h.width, h.score))
                .collect::<Vec<_>>()
                .join(",");
            println!(
                "  array @{:x}-{:x}: n={} numeric={:.0}% bytes={} hints=[{}] {}",
                a.start,
                a.end,
                a.elements,
                a.numeric_ratio * 100.0,
                a.byte_values,
                hints,
                a.preview
            );
        }

        for b in report.push_builders.iter().take(8) {
            println!(
                "  push builder @{:x}-{:x}: recv={} args={} numeric={} bytes={} calls={} other={} widths={:?} {}",
                b.start,
                b.end,
                b.receiver,
                b.arguments,
                b.numeric_literals,
                b.byte_literals,
                b.call_arguments,
                b.other_arguments,
                b.width_hints
                    .iter()
                    .take(4)
                    .map(|h| (h.width, h.score))
                    .collect::<Vec<_>>(),
                b.preview
            );
        }

        for d in report.decoder_candidates.iter().take(16) {
            println!(
                "  decoder {}: object={} builder={} width={} ip={} base={} offsets={:?} {}",
                d.function_id,
                d.object,
                d.builder_var.as_deref().unwrap_or("?"),
                d.width,
                d.ip,
                d.base.as_deref().unwrap_or("<inline>"),
                d.operand_offsets,
                d.preview
            );
        }

        for sm in report.state_machines.iter().take(20) {
            println!(
                "  state-machine {}: state={} init={} mask={} shift={:?} selector={} cases={} @{:x}-{:x}",
                sm.function_id,
                sm.state_var,
                sm.init_state,
                sm.mask,
                sm.shift,
                sm.selector_var.as_deref().unwrap_or("?"),
                sm.switch_cases,
                sm.start,
                sm.end
            );
        }

        for h in report.handler_tables.iter().take(8) {
            println!(
                "  handler table ({}) @{:x}-{:x}: entries={} functions={} async={} {}",
                h.container_kind,
                h.start,
                h.end,
                h.properties,
                h.function_values,
                h.async_function_values,
                h.preview
            );
        }

        println!("  VM-shaped functions:");
        for f in report
            .functions
            .iter()
            .filter(|f| f.score >= args.min_score)
            .take(20)
        {
            println!(
                "    {} score={:2} {} {} @{:x}-{:x} bytes={} switch_cases={} loops={} ternaries={} computed={} computed_calls={} arrays={} :: {}{}",
                if f.confirmed_dispatch { "[CONFIRMED]" } else { "[candidate]" },
                f.score,
                f.kind,
                f.name.as_deref().unwrap_or("<anon>"),
                f.start,
                f.end,
                f.bytes,
                f.switch_cases,
                f.loops,
                f.conditionals,
                f.computed_members,
                f.computed_calls,
                f.large_arrays,
                f.reasons.join("; "),
                if f.dispatch_reasons.is_empty() {
                    String::new()
                } else {
                    format!(" | dispatch: {}", f.dispatch_reasons.join("; "))
                }
            );
        }

        for embedded in &report.embedded {
            print_embedded(embedded, args.min_score, 1);
        }
    }
    Ok(())
}
