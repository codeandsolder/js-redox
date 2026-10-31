use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::js_format::format_source;
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
    let output = format_source(&source)?;
    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&args.output, output)
        .with_context(|| format!("writing {}", args.output.display()))?;
    Ok(())
}
