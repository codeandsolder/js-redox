use anyhow::Result;
use clap::Parser;
use jsvm_lift::capture_import::{import_capture_project, CaptureImportOptions};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Normalize HAR, recorder, or saved-page input into a capture project")]
struct Args {
    input: PathBuf,
    #[arg(short, long)]
    output: PathBuf,
    #[arg(long)]
    assets_dir: Option<PathBuf>,
    #[arg(long)]
    overwrite: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let summary = import_capture_project(&CaptureImportOptions {
        input: args.input,
        output: args.output.clone(),
        assets_dir: args.assets_dir,
        overwrite: args.overwrite,
    })?;
    println!(
        "{} capture: {} resources, {} script records -> {}",
        summary.kind.as_str(),
        summary.resources,
        summary.script_records,
        args.output.display()
    );
    Ok(())
}
