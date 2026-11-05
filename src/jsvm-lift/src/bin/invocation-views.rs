use anyhow::Result;
use clap::Parser;
use jsvm_lift::{analysis_budget::AnalysisBudgets, invocation_views::materialize_invocation_views};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(
    version,
    about = "Render concrete observed invocation source views from an analyzed capture"
)]
struct Args {
    project: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let count = materialize_invocation_views(
        &args.project,
        &AnalysisBudgets::standard("invocation-views"),
    )?;
    println!("Observed invocation views: {count}");
    Ok(())
}
