use anyhow::Result;
use clap::Parser;
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    table_ir::materialize,
};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Infer function-table VM ABI roles and lift handler statements into semantic IR")]
struct Args {
    source: PathBuf,
    scan: PathBuf,
    #[arg(long)]
    output: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let budgets = AnalysisBudgets::standard("table-ir");
    let budget = budgets.operation(
        AnalysisOperation::IrMaterialization,
        args.source.display().to_string(),
    );
    materialize(&args.source, &args.scan, &args.output, &budget)?;
    println!("wrote {}", args.output.display());
    Ok(())
}
