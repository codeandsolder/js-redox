use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::api_surface::{analyze_api_surface, ApiCallsite};
use serde::Serialize;
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Extract static browser API request callsites from JavaScript")]
struct Args {
    input: PathBuf,
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
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let callsites = analyze_api_surface(&source)
        .with_context(|| format!("analyzing {}", args.input.display()))?;
    let report = ApiSurfaceFileReport {
        schema: "jsvm-api-surface/v1",
        input: args.input.display().to_string(),
        bytes: source.len(),
        callsites,
    };
    println!("{}", serde_json::to_string(&report)?);
    Ok(())
}
