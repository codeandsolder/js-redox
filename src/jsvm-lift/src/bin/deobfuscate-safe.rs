use anyhow::{Context, Result};
use clap::{Args as ClapArgs, Parser, Subcommand, ValueEnum};
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    project_deob::{materialize_project_deobfuscation, ProjectDeobOptions},
    safe_deob::{deobfuscate_source, SourceMode},
};
use std::{fs, path::PathBuf};

#[derive(Parser, Debug)]
#[command(
    version,
    about = "Proof-oriented static JavaScript deobfuscation; never executes sample code"
)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Deobfuscate one source file and optionally emit a proof report.
    Source(SourceArgs),
    /// Materialize safe source recovery/deobfuscation for a normalized capture project.
    Project(ProjectArgs),
}

#[derive(ClapArgs, Debug)]
struct SourceArgs {
    input: PathBuf,
    output: PathBuf,
    #[arg(long)]
    report: Option<PathBuf>,
    #[arg(long, default_value_t = 16)]
    max_iterations: usize,
    /// Override JavaScript source mode instead of inferring it from the input suffix.
    #[arg(long, value_enum)]
    source_mode: Option<SourceModeArg>,
    /// Pretty-print the final analyst view. This is intentionally opt-in:
    /// Function#toString and related self-defending code can observe formatting.
    #[arg(long)]
    format_output: bool,
}

#[derive(ClapArgs, Debug)]
struct ProjectArgs {
    project: PathBuf,
    #[arg(long)]
    jobs: Option<usize>,
    #[arg(long, default_value_t = 16)]
    max_iterations: usize,
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

fn source_mode(args: &SourceArgs) -> SourceMode {
    args.source_mode
        .map(SourceMode::from)
        .unwrap_or_else(|| SourceMode::for_path(&args.input))
}

fn run_source(args: SourceArgs) -> Result<()> {
    let original = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let budgets = AnalysisBudgets::standard("deobfuscate-safe");
    let budget = budgets.operation(
        AnalysisOperation::SafeDeobfuscation,
        args.input.display().to_string(),
    );
    let outcome = deobfuscate_source(
        &original,
        args.input.display().to_string(),
        source_mode(&args),
        args.max_iterations,
        args.format_output,
        &budget,
    )?;

    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&args.output, outcome.source.as_bytes())
        .with_context(|| format!("writing {}", args.output.display()))?;

    if let Some(path) = &args.report {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let mut encoded = serde_json::to_string_pretty(&outcome.report)?;
        encoded.push('\n');
        fs::write(path, encoded).with_context(|| format!("writing {}", path.display()))?;
    }

    println!(
        "safe deobfuscation changed={} iterations={} transforms={:?}",
        outcome.report.changed, outcome.report.iterations, outcome.report.transforms
    );
    Ok(())
}

fn run_project(args: ProjectArgs) -> Result<()> {
    let project = args
        .project
        .canonicalize()
        .with_context(|| format!("project does not exist: {}", args.project.display()))?;
    let summary = materialize_project_deobfuscation(
        &project,
        &ProjectDeobOptions {
            jobs: args.jobs,
            max_iterations: args.max_iterations,
            budgets: AnalysisBudgets::standard("deobfuscate-safe-project"),
        },
    )?;
    println!(
        "safe source recovery: {} JS occurrences / {} unique raw / {} unique pre-deob / {} unique safe outputs; {} changed, {} deob failures; string recovery={} units/{} replacements",
        summary.javascript_units,
        summary.unique_raw_inputs,
        summary.unique_pre_deob_inputs,
        summary.unique_deob_outputs,
        summary.changed_units,
        summary.failed_units,
        summary.string_recovery_changed_units,
        summary.string_recovery_replacements,
    );
    Ok(())
}

fn main() -> Result<()> {
    match Args::parse().command {
        Command::Source(args) => run_source(args),
        Command::Project(args) => run_project(args),
    }
}
