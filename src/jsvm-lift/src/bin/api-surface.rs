use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::api_surface::{analyze_api_surface, ApiCallsite};
use serde::Serialize;
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Extract static browser API request callsites from JavaScript")]
struct Args {
    /// Analyze one JavaScript file.
    #[arg(required_unless_present = "project")]
    input: Option<PathBuf>,
    /// Analyze every selected JavaScript unit in a capture project and write analysis/api-surface.json.
    #[arg(long, conflicts_with = "input")]
    project: Option<PathBuf>,
}

#[derive(Debug, Serialize)]
struct ApiSurfaceFileReport {
    schema: &'static str,
    input: String,
    bytes: usize,
    callsites: Vec<ApiCallsite>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    if let Some(project) = args.project {
        let summary = jsvm_lift::project_api_surface::analyze_project_api_surface(&project)?;
        println!("{}", serde_json::to_string(&summary)?);
        return Ok(());
    }
    let input = args
        .input
        .context("input is required unless --project is used")?;
    let source =
        fs::read_to_string(&input).with_context(|| format!("reading {}", input.display()))?;
    let callsites =
        analyze_api_surface(&source).with_context(|| format!("analyzing {}", input.display()))?;
    let report = ApiSurfaceFileReport {
        schema: "jsvm-api-surface/v2",
        input: input.display().to_string(),
        bytes: source.len(),
        callsites,
    };
    println!("{}", serde_json::to_string(&report)?);
    Ok(())
}
