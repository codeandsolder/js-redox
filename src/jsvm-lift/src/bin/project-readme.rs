use anyhow::Result;
use clap::Parser;
use jsvm_lift::project_readme::refresh_project_readme;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(
    about = "Refresh the analyst-facing README for a recovered browser-capture source project"
)]
struct Args {
    project: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    refresh_project_readme(&args.project)?;
    println!("refreshed {}/README.md", args.project.display());
    Ok(())
}
