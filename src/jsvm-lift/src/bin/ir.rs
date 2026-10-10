use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::pipeline::{BindingInfo, NormalizedVm};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::PathBuf,
};

#[derive(ClapParser, Debug)]
#[command(about = "Lift role-normalized JavaScript VM handler effects into stable semantic IR")]
struct Args {
    normalized: PathBuf,
    #[arg(long)]
    scan: Option<PathBuf>,
    #[arg(long)]
    output: PathBuf,
}

#[derive(Debug, Deserialize)]
struct ScanReport {
    #[serde(default)]
    opcode_maps: Vec<ScanOpcodeMap>,
}

#[derive(Debug, Deserialize)]
struct ScanOpcodeMap {
    decoder_function_id: String,
    #[serde(default)]
    observed_opcodes: Vec<u64>,
    opcode_max: u64,
}

#[derive(Debug, Clone, Default)]
struct OpcodeProvenance {
    observed: BTreeSet<u64>,
    opcode_max: Option<u64>,
}

#[derive(Debug, Serialize)]
struct VmIr {
    schema: &'static str,
    file: String,
    decoder: String,
    parent: String,
    role_bindings: BTreeMap<String, BindingInfo>,
    state_machine: serde_json::Value,
    opcode_domain_max: Option<u64>,
    observed_opcodes: Vec<u64>,
    opcodes: Vec<OpcodeIr>,
}

#[derive(Debug, Serialize)]
struct OpcodeIr {
    opcode: u64,
    observed: Option<bool>,
    derived_env: BTreeMap<String, serde_json::Value>,
    paths: Vec<PathIr>,
}

#[derive(Debug, Serialize)]
struct PathIr {
    guards: Vec<String>,
    states: Vec<u64>,
    ops: Vec<IrOp>,
    terminal: Option<String>,
    classified_ops: usize,
    raw_ops: usize,
}

use jsvm_lift::semantic_ir::{classify_effect, IrOp};

fn read_scan(path: &PathBuf) -> Result<HashMap<String, OpcodeProvenance>> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    let mut by_decoder: HashMap<String, OpcodeProvenance> = HashMap::new();

    for (line_no, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let report: ScanReport = serde_json::from_str(line)
            .with_context(|| format!("parsing scan line {}", line_no + 1))?;
        for map in report.opcode_maps {
            let entry = by_decoder.entry(map.decoder_function_id).or_default();
            entry.observed.extend(map.observed_opcodes);
            entry.opcode_max = Some(
                entry
                    .opcode_max
                    .map_or(map.opcode_max, |old| old.max(map.opcode_max)),
            );
        }
    }
    Ok(by_decoder)
}

fn main() -> Result<()> {
    let args = Args::parse();
    let input: Vec<NormalizedVm> = serde_json::from_str(
        &fs::read_to_string(&args.normalized)
            .with_context(|| format!("reading {}", args.normalized.display()))?,
    )?;

    let provenance = if let Some(scan) = &args.scan {
        read_scan(scan)?
    } else {
        HashMap::new()
    };

    let mut total_ops = 0usize;
    let mut raw_ops = 0usize;
    let mut by_kind: BTreeMap<String, usize> = BTreeMap::new();

    let output: Vec<VmIr> = input
        .into_iter()
        .map(|vm| {
            let prov = provenance.get(&vm.decoder);
            let observed = prov.map(|p| p.observed.clone()).unwrap_or_default();

            let opcodes = vm
                .opcodes
                .into_iter()
                .map(|opcode| {
                    let paths = opcode
                        .paths
                        .into_iter()
                        .map(|path| {
                            let ops: Vec<IrOp> = path
                                .effects
                                .iter()
                                .map(|effect| classify_effect(effect))
                                .collect();
                            for op in &ops {
                                total_ops += 1;
                                *by_kind.entry(op.kind.clone()).or_default() += 1;
                                if op.kind == "raw_js" || op.kind == "raw_expression" {
                                    raw_ops += 1;
                                }
                            }
                            let raw = ops
                                .iter()
                                .filter(|op| op.kind == "raw_js" || op.kind == "raw_expression")
                                .count();
                            PathIr {
                                guards: path.guards,
                                states: path.states,
                                classified_ops: ops.len().saturating_sub(raw),
                                raw_ops: raw,
                                ops,
                                terminal: path.terminal,
                            }
                        })
                        .collect();

                    OpcodeIr {
                        opcode: opcode.opcode,
                        observed: prov.map(|_| observed.contains(&opcode.opcode)),
                        derived_env: opcode.derived_env,
                        paths,
                    }
                })
                .collect();

            VmIr {
                schema: "jsvm-ir/v0",
                file: vm.file,
                decoder: vm.decoder,
                parent: vm.parent,
                role_bindings: vm.role_bindings,
                state_machine: vm.state_machine,
                opcode_domain_max: prov.and_then(|p| p.opcode_max),
                observed_opcodes: observed.into_iter().collect(),
                opcodes,
            }
        })
        .collect();

    fs::write(&args.output, serde_json::to_string_pretty(&output)?)
        .with_context(|| format!("writing {}", args.output.display()))?;

    println!(
        "IR VMs {} ops {} classified {} raw {}",
        output.len(),
        total_ops,
        total_ops.saturating_sub(raw_ops),
        raw_ops
    );
    println!("KINDS");
    for (kind, count) in by_kind {
        println!("{kind}\t{count}");
    }
    println!("wrote {}", args.output.display());
    Ok(())
}
