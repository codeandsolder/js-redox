use anyhow::Result;
use clap::{Parser, ValueEnum};
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    switch_ir, table_ir,
};
use std::path::PathBuf;

#[derive(Clone, Copy, Debug, ValueEnum)]
enum VmKind {
    Switch,
    Table,
}

#[derive(Parser, Debug)]
#[command(about = "Infer VM roles and lift handlers into semantic IR")]
struct Args {
    kind: VmKind,
    source: PathBuf,
    scan: PathBuf,
    #[arg(long)]
    output: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let budgets = AnalysisBudgets::standard("vm-ir");
    let budget = budgets.operation(
        AnalysisOperation::IrMaterialization,
        args.source.display().to_string(),
    );
    let materialize = match args.kind {
        VmKind::Switch => switch_ir::materialize,
        VmKind::Table => table_ir::materialize,
    };
    materialize(&args.source, &args.scan, &args.output, None, &budget)?;
    println!("wrote {}", args.output.display());
    Ok(())
}
