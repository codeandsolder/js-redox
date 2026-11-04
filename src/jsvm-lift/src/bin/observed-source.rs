use anyhow::Result;
use clap::Parser;
use jsvm_lift::{
    analysis_budget::AnalysisBudgets, observed_runtime::materialize_observed_runtime_sources,
};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(
    version,
    about = "Regenerate the observed, positively executed JS source tree and its navigation index from a processed browser capture"
)]
struct Args {
    project: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let summary = materialize_observed_runtime_sources(
        &args.project,
        &AnalysisBudgets::standard("observed-source"),
    )?;
    println!(
        "Observed JavaScript: {} witnessed, {} formatted, {} unformatted",
        summary.witnessed_sources, summary.formatted_sources, summary.unformatted_sources
    );
    Ok(())
}
