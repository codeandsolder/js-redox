use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::js_refs::extract_js_references;
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Extract JavaScript module/worker execution-boundary references with Oxc")]
struct Args {
    input: Option<PathBuf>,
    #[arg(long)]
    project: Option<PathBuf>,
    #[arg(long)]
    jobs: Option<usize>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    if let Some(project) = args.project {
        let summary = jsvm_lift::project_js_refs::scan_project_references(&project, args.jobs)?;
        println!(
            "JavaScript references: {} units, {} references, {} import-map resolutions, {} unresolved bare, {} ambiguous contexts, {} failures",
            summary.javascript_units,
            summary.references,
            summary.resolved_by_import_map,
            summary.unresolved_bare_specifiers,
            summary.ambiguous_document_contexts,
            summary.failures
        );
        return Ok(());
    }
    let input = args
        .input
        .context("input is required unless --project is used")?;
    let source =
        fs::read_to_string(&input).with_context(|| format!("reading {}", input.display()))?;
    println!(
        "{}",
        serde_json::to_string(&extract_js_references(&source)?)?
    );
    Ok(())
}
