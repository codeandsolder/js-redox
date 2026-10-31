use anyhow::Result;
use clap::Parser;
use jsvm_lift::wasm_materialize::materialize_wasm;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Recover captured and statically produced WebAssembly with exact provenance")]
struct Args {
    project: PathBuf,
    /// Optional Wax executable for an additional high-level presentation view.
    #[arg(long)]
    wax: Option<PathBuf>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let summary = materialize_wasm(&args.project, args.wax.as_deref())?;
    println!(
        "WASM: {} unique module(s), {} origin(s), {} failed",
        summary.modules, summary.origins, summary.failed
    );
    Ok(())
}
