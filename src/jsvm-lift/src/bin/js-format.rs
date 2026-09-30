use anyhow::{bail, Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_codegen::Codegen;
use oxc_parser::Parser;
use oxc_span::SourceType;
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Parse JavaScript with Oxc and emit stable readable source")]
struct Args {
    input: PathBuf,
    output: PathBuf,
}

fn generate(source: &str, source_type: SourceType) -> Option<String> {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, source_type).parse();
    if parsed.panicked || !parsed.diagnostics.is_empty() {
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
