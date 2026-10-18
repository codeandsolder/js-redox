use anyhow::{Context, Result};
use clap::Parser;
use std::{fs, path::PathBuf};

#[derive(Debug, Parser)]
#[command(
    about = "Fail-closed exact evaluation of an internal i32 WebAssembly call on fresh module state"
)]
struct Args {
    input: PathBuf,

    #[arg(long)]
    function_index: usize,

    #[arg(long = "i32-arg")]
    i32_args: Vec<u32>,

    #[arg(long, default_value_t = 1_000_000)]
    fuel: u64,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let bytes = fs::read(&args.input).with_context(|| format!("read {}", args.input.display()))?;
    let report = wasm_redox::fresh_eval::evaluate_fresh_i32_call(
        &bytes,
        args.function_index,
        &args.i32_args,
        Some(args.fuel),
    );
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}
