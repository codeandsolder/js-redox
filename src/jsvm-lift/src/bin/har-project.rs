use anyhow::Result;
use clap::Parser;
use jsvm_lift::har_project::{import_har_project, HarProjectOptions};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Turn a browser HAR into a provenance-preserving source project")]
struct Args {
    har: PathBuf,
    #[arg(short, long)]
    output: PathBuf,
    #[arg(long)]
    overwrite: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let output = args.output;
    let summary = import_har_project(&HarProjectOptions {
        har: args.har,
        output: output.clone(),
        overwrite: args.overwrite,
    })?;
    println!(
        "HAR project: {} resources, {} script records -> {}",
        summary.resources,
        summary.script_records,
        output.display()
    );
    for (kind, count) in summary.counts {
        println!("{kind}\t{count}");
    }
    Ok(())
}
