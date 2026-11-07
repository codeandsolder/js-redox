use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    js_format::format_source,
    readable_aliases::inline_readable_intrinsic_aliases,
    readable_names::recover_readable_names,
};
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Parse JavaScript with Oxc and emit stable readable source")]
struct Args {
    input: PathBuf,
    output: PathBuf,
    /// Restore descriptive names from embedded component metadata in an
    /// analyst-only view (not the semantics-preserving deobfuscated source).
    #[arg(long)]
    semantic_names: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let budgets = AnalysisBudgets::standard("js-format");
    let budget = budgets.operation(AnalysisOperation::Format, args.input.display().to_string());
    let enriched = args
        .semantic_names
        .then(|| recover_readable_names(&source))
        .flatten();
    let named = enriched
        .as_ref()
        .map_or(source.as_str(), |(text, _)| text.as_str());
    let inlined = args
        .semantic_names
        .then(|| inline_readable_intrinsic_aliases(named))
        .flatten();
    let presented = inlined.as_ref().map_or(named, |(text, _)| text.as_str());
    let output = format_source(presented, &budget)?;
    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&args.output, output)
        .with_context(|| format!("writing {}", args.output.display()))?;
    Ok(())
}
