use anyhow::Result;
use clap::Parser as ClapParser;
use jsvm_lift::vm_materialize::materialize_project;
use std::path::PathBuf;

#[derive(ClapParser, Debug)]
#[command(about = "Materialize captured JavaScript VM IR as readable analyst modules")]
struct Args {
    project: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let summary = materialize_project(&args.project)?;
    println!(
        "materialized {} VM module(s): {} direct-switch + {} function-table; human pseudocode under src/_devirtualized/",
        summary.devirtualized_units, summary.switch_vms, summary.table_vms
    );
    Ok(())
}
