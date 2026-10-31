use anyhow::Result;
use clap::Parser as ClapParser;
use jsvm_lift::scan_report::{scan_file, EmbeddedScanReport, ScanReport};
use std::path::PathBuf;

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

fn print_array_candidates(report: &ScanReport) {
    for candidate in report.arrays.iter().take(8) {
        let hints = candidate
            .width_hints
            .iter()
            .take(3)
            .map(|hint| format!("w{}:{}", hint.width, hint.score))
            .collect::<Vec<_>>()
            .join(",");
        println!(
            "  array @{:x}-{:x}: n={} numeric={:.0}% bytes={} hints=[{}] {}",
            candidate.start,
            candidate.end,
            candidate.elements,
            candidate.numeric_ratio * 100.0,
            candidate.byte_values,
            hints,
            candidate.preview
        );
    }
}

fn print_push_builders(report: &ScanReport) {
    for builder in report.push_builders.iter().take(8) {
        println!(
            "  push builder @{:x}-{:x}: recv={} args={} numeric={} bytes={} calls={} other={} widths={:?} {}",
            builder.start,
            builder.end,
            builder.receiver,
            builder.arguments,
            builder.numeric_literals,
            builder.byte_literals,
            builder.call_arguments,
            builder.other_arguments,
            builder
                .width_hints
                .iter()
                .take(4)
                .map(|hint| (hint.width, hint.score))
                .collect::<Vec<_>>(),
            builder.preview
        );
    }
}

fn print_decoders(report: &ScanReport) {
    for decoder in report.decoder_candidates.iter().take(16) {
        println!(
            "  decoder {}: object={} builder={} width={} ip={} base={} offsets={:?} {}",
            decoder.function_id,
            decoder.object,
            decoder.builder_var.as_deref().unwrap_or("?"),
            decoder.width,
            decoder.ip,
            decoder.base.as_deref().unwrap_or("<inline>"),
            decoder.operand_offsets,
            decoder.preview
        );
    }
}

fn print_state_machines(report: &ScanReport) {
    for machine in report.state_machines.iter().take(20) {
        println!(
            "  state-machine {}: state={} init={} mask={} shift={:?} selector={} cases={} @{:x}-{:x}",
            machine.function_id,
            machine.state_var,
            machine.init_state,
            machine.mask,
            machine.shift,
            machine.selector_var.as_deref().unwrap_or("?"),
            machine.switch_cases,
            machine.start,
            machine.end
        );
    }
}

fn print_handler_tables(report: &ScanReport) {
    for table in report.handler_tables.iter().take(8) {
        println!(
            "  handler table ({}) @{:x}-{:x}: entries={} functions={} async={} {}",
            table.container_kind,
            table.start,
            table.end,
            table.properties,
            table.function_values,
            table.async_function_values,
            table.preview
        );
    }
}

fn print_vm_functions(report: &ScanReport, min_score: u32) {
    println!("  VM-shaped functions:");
    for function in report
        .functions
        .iter()
        .filter(|function| function.score >= min_score)
        .take(20)
    {
        println!(
            "    {} score={:2} {} {} @{:x}-{:x} bytes={} switch_cases={} loops={} ternaries={} computed={} computed_calls={} arrays={} :: {}{}",
            if function.confirmed_dispatch { "[CONFIRMED]" } else { "[candidate]" },
            function.score,
            function.kind,
            function.name.as_deref().unwrap_or("<anon>"),
            function.start,
            function.end,
            function.bytes,
            function.switch_cases,
            function.loops,
            function.conditionals,
            function.computed_members,
            function.computed_calls,
            function.large_arrays,
            function.reasons.join("; "),
            if function.dispatch_reasons.is_empty() {
                String::new()
            } else {
                format!(" | dispatch: {}", function.dispatch_reasons.join("; "))
            }
        );
    }
}

fn print_report(report: &ScanReport, min_score: u32) {
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
    print_array_candidates(report);
    print_push_builders(report);
    print_decoders(report);
    print_state_machines(report);
    print_handler_tables(report);
    print_vm_functions(report, min_score);
    for embedded in &report.embedded {
        print_embedded(embedded, min_score, 1);
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

        print_report(&report, args.min_score);
    }
    Ok(())
}
