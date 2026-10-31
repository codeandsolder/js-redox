use anyhow::Result;
use clap::Parser as ClapParser;
use jsvm_lift::bundle_materialize::materialize_bundle_modules;
use std::path::PathBuf;

#[derive(ClapParser, Debug)]
#[command(about = "Materialize statically explicit bundle modules into a capture project")]
struct Args {
    project: PathBuf,
    #[arg(long)]
    jobs: Option<usize>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let summary = materialize_bundle_modules(&args.project, args.jobs)?;
    println!(
        "bundle modules: {} bundle payload(s), {} modules, {} unique input body/bodies, {} failed units",
        summary.bundles, summary.modules, summary.unique_input_bodies, summary.failures
    );
    Ok(())
}
