use anyhow::{Context, Result};
use clap::Parser;
use std::{
    fs,
    io::ErrorKind,
    path::{Path, PathBuf},
    process::Command,
};

#[derive(Debug, Parser)]
#[command(about = "Recover readable, provenance-friendly views of WebAssembly modules")]
struct Args {
    input: PathBuf,

    #[arg(long)]
    output_dir: PathBuf,

    #[arg(long, default_value = "wax")]
    wax: PathBuf,

    #[arg(long)]
    skip_wax: bool,
}

fn write_wax(input: &Path, output: &Path, wax: &Path) -> Result<()> {
    let result = Command::new(wax).arg(input).output();
    let result = match result {
        Ok(result) => result,
        Err(error) if error.kind() == ErrorKind::NotFound => {
            eprintln!(
                "wasm-redox: Wax not found at {}; skipping high-level view",
                wax.display()
            );
            return Ok(());
        }
        Err(error) => return Err(error).with_context(|| format!("run {}", wax.display())),
    };

    if !result.status.success() {
        eprintln!(
            "wasm-redox: Wax failed for {} ({}); keeping folded WAT fallback\n{}",
            input.display(),
            result.status,
            String::from_utf8_lossy(&result.stderr)
        );
        return Ok(());
    }
    fs::write(output, result.stdout).with_context(|| format!("write {}", output.display()))
}

fn main() -> Result<()> {
    let args = Args::parse();
    let bytes = fs::read(&args.input).with_context(|| format!("read {}", args.input.display()))?;
    let report = wasm_redox::analyze(&bytes)?;
    let wat = wasm_redox::folded_wat(&bytes)?;

    fs::create_dir_all(&args.output_dir)
        .with_context(|| format!("create {}", args.output_dir.display()))?;
    let report_path = args.output_dir.join("module.report.json");
    let wat_path = args.output_dir.join("module.readable.wat");

    fs::write(&report_path, serde_json::to_vec_pretty(&report)?)
        .with_context(|| format!("write {}", report_path.display()))?;
    fs::write(&wat_path, wat).with_context(|| format!("write {}", wat_path.display()))?;

    if !args.skip_wax {
        write_wax(
            &args.input,
            &args.output_dir.join("module.readable.wax"),
            &args.wax,
        )?;
    }

    println!(
        "{}: {} bytes, {} imports, {} exports, {} defined functions",
        report.sha256,
        report.byte_len,
        report.imports.len(),
        report.exports.len(),
        report.sections.defined_functions
    );
    Ok(())
}
