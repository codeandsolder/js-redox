use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::bundle_unpack::analyze_bundle_source;
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Inventory statically explicit Webpack/Next JSONP chunk module tables")]
struct Args {
    input: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let report = analyze_bundle_source(&source, args.input.display().to_string());
    println!("{}", serde_json::to_string(&report)?);
    Ok(())
}
