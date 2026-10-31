use anyhow::Result;
use clap::Parser;
use jsvm_lift::source_graph::build_source_graph;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(version, about = "Build the capture-project provenance/source graph")]
struct Args {
    project: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let summary = build_source_graph(&args.project)?;
    println!(
        "source graph: {} nodes / {} edges / {} external URLs",
        summary.nodes, summary.edges, summary.external_urls
    );
    Ok(())
}
