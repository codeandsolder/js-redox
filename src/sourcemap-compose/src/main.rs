use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use jsvm_lift::project_sourcemaps::{compose_sourcemap_json, recover_project_sourcemaps};
use std::{fs, path::PathBuf};

#[derive(Parser, Debug)]
#[command(about = "Compose source maps or recover source-map chains for a capture project")]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    Compose {
        downstream: PathBuf,
        upstream: PathBuf,
        #[arg(long)]
        source_id: u32,
        #[arg(long)]
        output: PathBuf,
    },
    Project {
        project: PathBuf,
    },
}

fn main() -> Result<()> {
    match Args::parse().command {
        Command::Compose {
            downstream,
            upstream,
            source_id,
            output,
        } => {
            let downstream_json = fs::read_to_string(&downstream)
                .with_context(|| format!("reading {}", downstream.display()))?;
            let upstream_json = fs::read_to_string(&upstream)
                .with_context(|| format!("reading {}", upstream.display()))?;
            let composed = compose_sourcemap_json(&downstream_json, &upstream_json, source_id)?;
            fs::write(&output, composed)
                .with_context(|| format!("writing {}", output.display()))?;
        }
        Command::Project { project } => {
            let summary = recover_project_sourcemaps(&project)?;
            println!(
                "source maps: {} referenced; {} direct source files recovered; {} nested map link(s) composed; {} final source files recovered; {} missing map resources",
                summary.referenced,
                summary.direct_recovered,
                summary.composed_links,
                summary.final_recovered,
                summary.missing_resources,
            );
        }
    }
    Ok(())
}
