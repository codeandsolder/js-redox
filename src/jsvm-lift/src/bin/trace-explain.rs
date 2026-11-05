//! Rebuild derived execution explanations without expensive project reanalysis.
use anyhow::Result;
use clap::Parser;
use jsvm_lift::{
    analysis_budget::AnalysisBudgets, invocation_views::materialize_invocation_views,
    source_graph::build_source_graph,
};
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[command(
    version,
    about = "Rebuild observed invocation/guard explanations and their source graph without reprocessing a capture"
)]
struct Args {
    /// Existing recovered capture project with a verified selective trace.
    project: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let budgets = AnalysisBudgets::standard("trace-explain");
    let invocations = materialize_invocation_views(&args.project, &budgets)?;
    let graph = build_source_graph(&args.project, &budgets)?;
    println!(
        "Explained {invocations} invocation(s); source graph: {} nodes / {} edges",
        graph.nodes, graph.edges
    );
    Ok(())
}
