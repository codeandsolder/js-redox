use anyhow::{Context, Result};
use clap::Parser;
use jsvm_lift::corpus_eval::{evaluate_manifest, write_report};
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[command(
    about = "Evaluate pinned real-world JavaScript corpora against manifest-owned acceptance policy"
)]
struct Args {
    /// Public or private corpus manifest describing samples and acceptance policy.
    manifest: PathBuf,
    /// Root containing sample paths from the manifest. Defaults to the manifest directory.
    #[arg(long)]
    corpus_root: Option<PathBuf>,
    /// Optional JSON report destination.
    #[arg(long)]
    report: Option<PathBuf>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let manifest = args
        .manifest
        .canonicalize()
        .with_context(|| format!("manifest does not exist: {}", args.manifest.display()))?;
    let corpus_root = match args.corpus_root {
        Some(path) => path
            .canonicalize()
            .with_context(|| format!("corpus root does not exist: {}", path.display()))?,
        None => manifest
            .parent()
            .context("manifest has no parent directory")?
            .to_path_buf(),
    };
    let report = evaluate_manifest(&manifest, &corpus_root)?;
    if let Some(path) = args.report.as_deref() {
        write_report(&report, path)?;
    }
    println!(
        "PASS: {} samples ({} raw + {} reference), {} proven rewrites, {} confirmed dispatchers",
        report.summary.samples,
        report.summary.raw_samples,
        report.summary.reference_samples,
        report.summary.proven_rewrites,
        report.summary.confirmed_dispatchers,
    );
    if let Some(path) = args.report {
        println!("report: {}", path.display());
    }
    Ok(())
}
