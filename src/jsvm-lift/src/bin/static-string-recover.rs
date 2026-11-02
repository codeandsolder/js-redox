use anyhow::{Context, Result};
use clap::{Parser as ClapParser, ValueEnum};
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    safe_deob::SourceMode,
    string_recovery::recover_static_strings,
};
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(
    version,
    about = "Proof-gated static JavaScript string-decoder recovery"
)]
struct Args {
    input: PathBuf,
    output: PathBuf,
    #[arg(long)]
    report: Option<PathBuf>,
    #[arg(long, default_value_t = 8)]
    max_iterations: usize,
    #[arg(long, value_enum, default_value_t = SourceModeArg::Auto)]
    source_mode: SourceModeArg,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum SourceModeArg {
    Auto,
    Module,
    Commonjs,
}

impl From<SourceModeArg> for SourceMode {
    fn from(value: SourceModeArg) -> Self {
        match value {
            SourceModeArg::Auto => Self::Auto,
            SourceModeArg::Module => Self::Module,
            SourceModeArg::Commonjs => Self::CommonJs,
        }
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    let original = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let budgets = AnalysisBudgets::standard("static-string-recover");
    let budget = budgets.operation(
        AnalysisOperation::StaticStringRecovery,
        args.input.display().to_string(),
    );
    let outcome = recover_static_strings(
        &original,
        args.input.display().to_string(),
        args.source_mode.into(),
        args.max_iterations,
        &budget,
    )?;

    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&args.output, outcome.source.as_bytes())
        .with_context(|| format!("writing {}", args.output.display()))?;

    if let Some(path) = args.report {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let mut encoded = serde_json::to_string_pretty(&outcome.report)?;
        encoded.push('\n');
        fs::write(path, encoded)?;
    }
    println!("{}", serde_json::to_string(&outcome.report)?);
    Ok(())
}
