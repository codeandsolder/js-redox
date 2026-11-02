use anyhow::Result;
use clap::Parser;
use jsvm_lift::table_ir::materialize;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Infer function-table VM ABI roles and lift handler statements into semantic IR")]
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
