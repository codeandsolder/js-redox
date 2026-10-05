use anyhow::{bail, Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_codegen::Codegen;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Parse JavaScript with Oxc and emit stable readable source")]
struct Args {
    input: PathBuf,
    output: PathBuf,
}

fn generate(source: &str, source_type: SourceType) -> Option<String> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, source_type);
    if !parsed.is_clean() {
        return None;
    }
    Some(Codegen::new().build(&parsed.program).code)
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;

    let output = generate(&source, SourceType::mjs())
        .or_else(|| generate(&source, SourceType::cjs()))
        .ok_or_else(|| anyhow::anyhow!("Oxc could not parse source as module or script"))?;

    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent)?;
    }
    if output.trim().is_empty() && !source.trim().is_empty() {
        bail!("codegen unexpectedly emitted empty source");
    }
    fs::write(&args.output, output)
        .with_context(|| format!("writing {}", args.output.display()))?;
    Ok(())
}
