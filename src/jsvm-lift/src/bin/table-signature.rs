use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::effect_shape::{analyze_program, PropertyMode};
use oxc_allocator::Allocator;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde::{Deserialize, Serialize};
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Emit alpha-normalized signatures for function-table VM handlers")]
struct Args {
    source: PathBuf,
    scan: PathBuf,
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Debug, Deserialize)]
struct ScanReport {
    handler_function_tables: Vec<HandlerTable>,
    table_vms: Vec<TableVm>,
}

#[derive(Debug, Deserialize)]
struct HandlerTable {
    binding: String,
    start: u32,
    end: u32,
    handlers: Vec<HandlerSlot>,
}

#[derive(Debug, Deserialize)]
struct HandlerSlot {
    key: String,
    start: u32,
    end: u32,
}

#[derive(Debug, Deserialize)]
struct TableVm {
    handler_table: String,
}

#[derive(Debug, Serialize)]
struct HandlerSignature {
    table: String,
    table_start: u32,
    table_end: u32,
    key: String,
    start: u32,
    end: u32,
    exact_hash: String,
    coarse_hash: String,
}

#[derive(Debug, Serialize)]
struct Output {
    source: String,
    handlers: Vec<HandlerSignature>,
}

fn shape_hash(source: &str, coarse_properties: bool) -> Result<String> {
    let wrapped = format!("({source})");
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &wrapped, SourceType::cjs());
    anyhow::ensure!(!parsed.panicked, "parser panicked");
    anyhow::ensure!(parsed.diagnostics == 0, "parse diagnostics");
    let property_mode = if coarse_properties {
        PropertyMode::Canonical
    } else {
        PropertyMode::Literal
    };
    Ok(format!(
        "{:016x}",
        analyze_program(&parsed.program, property_mode).hash
    ))
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.source)
        .with_context(|| format!("reading {}", args.source.display()))?;
    let scan_text = fs::read_to_string(&args.scan)
        .with_context(|| format!("reading {}", args.scan.display()))?;
    let report: ScanReport = serde_json::from_str(scan_text.trim())
        .with_context(|| format!("parsing {}", args.scan.display()))?;

    let active: std::collections::HashSet<_> = report
        .table_vms
        .iter()
        .map(|v| v.handler_table.as_str())
        .collect();

    let mut handlers = Vec::new();
    for table in report
        .handler_function_tables
        .iter()
        .filter(|table| active.contains(table.binding.as_str()))
    {
        for slot in &table.handlers {
            let start = slot.start as usize;
            let end = (slot.end as usize).min(source.len());
            let Some(raw) = source.get(start..end) else {
                continue;
            };
            handlers.push(HandlerSignature {
                table: table.binding.clone(),
                table_start: table.start,
                table_end: table.end,
                key: slot.key.clone(),
                start: slot.start,
                end: slot.end,
                exact_hash: shape_hash(raw, false).unwrap_or_else(|_| "PARSEFAIL".into()),
                coarse_hash: shape_hash(raw, true).unwrap_or_else(|_| "PARSEFAIL".into()),
            });
        }
    }

    let output = Output {
        source: args.source.display().to_string(),
        handlers,
    };
    let json = serde_json::to_string_pretty(&output)?;
    if let Some(path) = args.output {
        fs::write(&path, format!("{json}\n"))
            .with_context(|| format!("writing {}", path.display()))?;
    } else {
        println!("{json}");
    }
    Ok(())
}
