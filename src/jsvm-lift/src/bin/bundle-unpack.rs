use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    bundle_unpack::analyze_bundle_source,
};
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Inventory statically explicit Webpack/Next JSONP chunk module tables")]
struct Args {
    input: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let budgets = AnalysisBudgets::standard("bundle-unpack");
    let budget = budgets.operation(
        AnalysisOperation::BundleMaterialization,
        args.input.display().to_string(),
    );
    let report = analyze_bundle_source(&source, args.input.display().to_string(), &budget)?;
    println!("{}", serde_json::to_string(&report)?);
    Ok(())
}
