use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::effect_shape::{analyze_effect, family_name};
use serde::Deserialize;

use std::{
    collections::{BTreeSet, HashMap},
    fs,
    path::PathBuf,
};

#[derive(ClapParser, Debug)]
#[command(about = "Cluster reduced VM effects by alpha-normalized AST shape")]
struct Args {
    input: PathBuf,
    #[arg(long, default_value_t = 2)]
    min_decoders: usize,
    #[arg(long, default_value_t = 35)]
    top: usize,
}

#[derive(Debug, Deserialize)]
struct ReducedVm {
    file: String,
    decoder: String,
    opcodes: Vec<ReducedOpcode>,
}

#[derive(Debug, Deserialize)]
struct ReducedOpcode {
    opcode: u64,
    paths: Vec<ReducedPath>,
}

#[derive(Debug, Deserialize)]
struct ReducedPath {
    effects: Vec<String>,
}

#[derive(Default)]
struct Cluster {
    count: usize,
    decoders: BTreeSet<String>,
    families: BTreeSet<String>,
    samples: Vec<String>,
    shape: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let text = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;

    let mut effects: HashMap<u64, Cluster> = HashMap::new();
    let mut paths: HashMap<String, Cluster> = HashMap::new();
    let mut vm_count = 0usize;

    for (line_no, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let vm: ReducedVm =
            serde_json::from_str(line).with_context(|| format!("parsing line {}", line_no + 1))?;
        vm_count += 1;
        let fam = family_name(&vm.file);

        for op in &vm.opcodes {
            for path in &op.paths {
                let mut hashes = Vec::new();

                for raw in &path.effects {
                    if raw == "[no-state-change]" {
                        continue;
                    }
                    let analyzed = analyze_effect(raw);
                    let hash = analyzed.hash;
                    let shape = analyzed.text;
                    hashes.push(format!("{hash:016x}"));

                    let cluster = effects.entry(hash).or_default();
                    cluster.count += 1;
                    cluster.decoders.insert(vm.decoder.clone());
                    cluster.families.insert(fam.clone());
                    if cluster.shape.is_empty() {
                        cluster.shape = shape;
                    }
                    if cluster.samples.len() < 4 && !cluster.samples.contains(raw) {
                        cluster.samples.push(raw.clone());
                    }
                }

                let signature = hashes.join("|");
                let cluster = paths.entry(signature).or_default();
                cluster.count += 1;
                cluster.decoders.insert(vm.decoder.clone());
                cluster.families.insert(fam.clone());
                if cluster.samples.len() < 4 {
                    cluster.samples.push(format!(
                        "{} op {} :: {}",
                        vm.decoder,
                        op.opcode,
                        path.effects.join(" ; ")
                    ));
                }
            }
        }
    }

    let mut effect_rows: Vec<_> = effects
        .into_iter()
        .filter(|(_, c)| c.decoders.len() >= args.min_decoders)
        .collect();
    effect_rows.sort_by(|a, b| {
        b.1.decoders
            .len()
            .cmp(&a.1.decoders.len())
            .then_with(|| b.1.count.cmp(&a.1.count))
    });

    let mut path_rows: Vec<_> = paths
        .into_iter()
        .filter(|(_, c)| c.decoders.len() >= args.min_decoders)
        .collect();
    path_rows.sort_by(|a, b| {
        b.1.decoders
            .len()
            .cmp(&a.1.decoders.len())
            .then_with(|| b.1.count.cmp(&a.1.count))
    });

    println!(
        "VMs {vm_count} shared_effect_shapes {} shared_path_signatures {}",
        effect_rows.len(),
        path_rows.len()
    );
    println!(
        "
TOP EFFECT SHAPES"
    );
    for (hash, c) in effect_rows.into_iter().take(args.top) {
        println!(
            "
{hash:016x} uses {} decoders {} families {}",
            c.count,
            c.decoders.len(),
            c.families.iter().cloned().collect::<Vec<_>>().join(",")
        );
        for sample in c.samples.iter().take(3) {
            let clipped: String = sample.chars().take(240).collect();
            println!("  {clipped}");
        }
    }

    println!(
        "
SHARED FULL PATH SIGNATURES"
    );
    for (sig, c) in path_rows.into_iter().take(args.top) {
        let effects = if sig.is_empty() {
            0
        } else {
            sig.split('|').count()
        };
        println!(
            "
uses {} decoders {} families {} effects {}",
            c.count,
            c.decoders.len(),
            c.families.iter().cloned().collect::<Vec<_>>().join(","),
            effects
        );
        for sample in c.samples.iter().take(2) {
            let clipped: String = sample.chars().take(420).collect();
            println!("  {clipped}");
        }
    }

    Ok(())
}
