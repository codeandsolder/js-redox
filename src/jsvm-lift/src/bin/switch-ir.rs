use anyhow::Result;
use clap::Parser;
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    switch_ir::materialize,
};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Infer direct-switch VM roles and lift switch handlers into semantic IR")]
struct Args {
    source: PathBuf,
    scan: PathBuf,
    #[arg(long)]
    output: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let budgets = AnalysisBudgets::standard("switch-ir");
    let budget = budgets.operation(
        AnalysisOperation::IrMaterialization,
        args.source.display().to_string(),
    );
    materialize(&args.source, &args.scan, &args.output, &budget)?;
    println!("wrote {}", args.output.display());
    Ok(())
}
