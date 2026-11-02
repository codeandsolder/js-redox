use anyhow::Result;
use clap::Parser;
use jsvm_lift::switch_ir::materialize;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Infer direct-switch VM roles and lift switch handlers into semantic IR")]
struct Args {
    source: PathBuf,
    scan: PathBuf,
    #[arg(long)]
    output: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    materialize(&args.source, &args.scan, &args.output)?;
    println!("wrote {}", args.output.display());
    Ok(())
}
