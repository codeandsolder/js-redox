use anyhow::Result;
use clap::Parser as ClapParser;
use jsvm_lift::source_materialize::materialize_capture_source;
use std::path::PathBuf;

#[derive(ClapParser, Debug)]
#[command(about = "Materialize captured text/code resources into a readable project source tree")]
struct Args {
    project: PathBuf,
    #[arg(long)]
    jobs: Option<usize>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let summary = materialize_capture_source(&args.project, args.jobs)?;
    println!(
        "materialized {} source unit(s): {} JavaScript / {} unique parsed bodies; {} incomplete; jobs={}",
        summary.units, summary.javascript_units, summary.unique_javascript_inputs, summary.incomplete_units, summary.jobs
    );
    Ok(())
}
