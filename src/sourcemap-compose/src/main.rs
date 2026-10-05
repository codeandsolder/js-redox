use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use rolldown_redox::sourcemap::{compose_sourcemap_source, OwnedSourceMap};
use std::{fs, path::PathBuf};

#[derive(ClapParser)]
struct Args {
    downstream: PathBuf,
    upstream: PathBuf,
    #[arg(long)]
    source_id: u32,
    #[arg(long)]
    output: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let downstream_json = fs::read_to_string(&args.downstream)
        .with_context(|| format!("reading {}", args.downstream.display()))?;
    let upstream_json = fs::read_to_string(&args.upstream)
        .with_context(|| format!("reading {}", args.upstream.display()))?;
    let downstream = OwnedSourceMap::from_json_string(&downstream_json)
        .with_context(|| format!("parsing {}", args.downstream.display()))?;
    let upstream = OwnedSourceMap::from_json_string(&upstream_json)
        .with_context(|| format!("parsing {}", args.upstream.display()))?;
    let composed = compose_sourcemap_source(
        downstream.as_source_map(),
        args.source_id,
        upstream.as_source_map(),
    );
    fs::write(&args.output, composed.to_json_string())
        .with_context(|| format!("writing {}", args.output.display()))?;
    Ok(())
}
