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

struct SignatureClusters {
    vm_count: usize,
    effects: HashMap<u64, Cluster>,
    paths: HashMap<String, Cluster>,
}

fn collect_clusters(text: &str) -> Result<SignatureClusters> {
    let mut effects = HashMap::new();
    let mut paths = HashMap::new();
    let mut vm_count = 0;
    for (line_no, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let vm: ReducedVm =
            serde_json::from_str(line).with_context(|| format!("parsing line {}", line_no + 1))?;
        vm_count += 1;
        let family = family_name(&vm.file);
        for op in &vm.opcodes {
            for path in &op.paths {
                record_path(&mut effects, &mut paths, &vm, op, path, &family);
            }
        }
    }
    Ok(SignatureClusters {
        vm_count,
        effects,
        paths,
    })
}

fn record_path(
    effects: &mut HashMap<u64, Cluster>,
    paths: &mut HashMap<String, Cluster>,
    vm: &ReducedVm,
    op: &ReducedOpcode,
    path: &ReducedPath,
    family: &str,
) {
    let mut hashes = Vec::new();
    for raw in &path.effects {
        if raw == "[no-state-change]" {
            continue;
        }
        let analyzed = analyze_effect(raw);
        let hash = analyzed.hash;
        hashes.push(format!("{hash:016x}"));
        let cluster = effects.entry(hash).or_default();
        cluster.count += 1;
        cluster.decoders.insert(vm.decoder.clone());
        cluster.families.insert(family.to_string());
        if cluster.shape.is_empty() {
            cluster.shape = analyzed.text;
        }
        if cluster.samples.len() < 4 && !cluster.samples.contains(raw) {
            cluster.samples.push(raw.clone());
        }
    }

    let signature = hashes.join("|");
    let cluster = paths.entry(signature).or_default();
    cluster.count += 1;
    cluster.decoders.insert(vm.decoder.clone());
    cluster.families.insert(family.to_string());
    if cluster.samples.len() < 4 {
        cluster.samples.push(format!(
            "{} op {} :: {}",
            vm.decoder,
            op.opcode,
            path.effects.join(" ; ")
        ));
    }
}

fn ranked_effects(effects: HashMap<u64, Cluster>, min_decoders: usize) -> Vec<(u64, Cluster)> {
    let mut rows: Vec<_> = effects
        .into_iter()
        .filter(|(_, cluster)| cluster.decoders.len() >= min_decoders)
        .collect();
    rows.sort_by(|a, b| {
        b.1.decoders
            .len()
            .cmp(&a.1.decoders.len())
            .then_with(|| b.1.count.cmp(&a.1.count))
            .then_with(|| a.0.cmp(&b.0))
    });
    rows
}

fn ranked_paths(paths: HashMap<String, Cluster>, min_decoders: usize) -> Vec<(String, Cluster)> {
    let mut rows: Vec<_> = paths
        .into_iter()
        .filter(|(_, cluster)| cluster.decoders.len() >= min_decoders)
        .collect();
    rows.sort_by(|a, b| {
        b.1.decoders
            .len()
            .cmp(&a.1.decoders.len())
            .then_with(|| b.1.count.cmp(&a.1.count))
            .then_with(|| a.0.cmp(&b.0))
    });
    rows
}

fn print_effects(rows: impl IntoIterator<Item = (u64, Cluster)>, top: usize) {
    println!("\nTOP EFFECT SHAPES");
    for (hash, cluster) in rows.into_iter().take(top) {
        println!(
            "\n{hash:016x} uses {} decoders {} families {}",
            cluster.count,
            cluster.decoders.len(),
            cluster
                .families
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join(",")
        );
        for sample in cluster.samples.iter().take(3) {
            let clipped: String = sample.chars().take(240).collect();
            println!("  {clipped}");
        }
    }
}

fn print_paths(rows: impl IntoIterator<Item = (String, Cluster)>, top: usize) {
    println!("\nSHARED FULL PATH SIGNATURES");
    for (signature, cluster) in rows.into_iter().take(top) {
        let effects = if signature.is_empty() {
            0
        } else {
            signature.split('|').count()
        };
        println!(
            "\nuses {} decoders {} families {} effects {}",
            cluster.count,
            cluster.decoders.len(),
            cluster
                .families
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join(","),
            effects
        );
        for sample in cluster.samples.iter().take(2) {
            let clipped: String = sample.chars().take(420).collect();
            println!("  {clipped}");
        }
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    let text = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let clusters = collect_clusters(&text)?;
    let effect_rows = ranked_effects(clusters.effects, args.min_decoders);
    let path_rows = ranked_paths(clusters.paths, args.min_decoders);

    println!(
        "VMs {} shared_effect_shapes {} shared_path_signatures {}",
        clusters.vm_count,
        effect_rows.len(),
        path_rows.len()
    );
    print_effects(effect_rows, args.top);
    print_paths(path_rows, args.top);
    Ok(())
}
