use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    js_format::format_source,
};
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Parse JavaScript with Oxc and emit stable readable source")]
struct Args {
    input: PathBuf,
    output: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let budgets = AnalysisBudgets::standard("js-format");
    let budget = budgets.operation(AnalysisOperation::Format, args.input.display().to_string());
    let output = format_source(&source, &budget)?;
    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&args.output, output)
        .with_context(|| format!("writing {}", args.output.display()))?;
    Ok(())
}
