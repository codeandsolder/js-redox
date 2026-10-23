use anyhow::{Context, Result};
use clap::{Parser as ClapParser, ValueEnum};
use serde::Serialize;
use std::{collections::BTreeMap, fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(
    version,
    about = "Proof-gated static JavaScript string-decoder recovery"
)]
struct Args {
    input: PathBuf,
    output: PathBuf,
    #[arg(long)]
    report: Option<PathBuf>,
    #[arg(long, default_value_t = 8)]
    max_iterations: usize,
    #[arg(long, value_enum, default_value_t = SourceModeArg::Auto)]
    source_mode: SourceModeArg,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum SourceModeArg {
    Auto,
    Module,
    Commonjs,
}

impl SourceModeArg {
    const fn safe_mode(self) -> jsvm_safe_core::SafeSourceMode {
        match self {
            Self::Auto => jsvm_safe_core::SafeSourceMode::Auto,
            Self::Module => jsvm_safe_core::SafeSourceMode::Module,
            Self::Commonjs => jsvm_safe_core::SafeSourceMode::CommonJs,
        }
    }

    const fn label(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Module => "module",
            Self::Commonjs => "commonjs",
        }
    }
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    source_mode: &'static str,
    input: String,
    input_sha256: String,
    output_sha256: String,
    changed: bool,
    iterations: usize,
    decoder_candidates: usize,
    replacements: usize,
    transforms: BTreeMap<String, usize>,
    safe_static_only: bool,
    status: &'static str,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let original = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let result = jsvm_safe_core::recover_static_decoders_with_source_mode(
        &original,
        args.max_iterations,
        args.source_mode.safe_mode(),
    );
    let (source, iterations, decoder_candidates, transforms, status) = match result {
        Some(result) => (
            result.source,
            result.iterations,
            result.decoder_candidates,
            result.transforms,
            "proven",
        ),
        None => (
            original.clone(),
            0,
            0,
            BTreeMap::new(),
            "parse_or_semantic_rejected",
        ),
    };

    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&args.output, &source)
        .with_context(|| format!("writing {}", args.output.display()))?;

    let replacements = transforms.values().copied().sum();
    let report = Report {
        schema: "js-static-decoder-recovery/v1",
        source_mode: args.source_mode.label(),
        input: args.input.display().to_string(),
        input_sha256: jsvm_lift::sha256_hex(original.as_bytes()),
        output_sha256: jsvm_lift::sha256_hex(source.as_bytes()),
        changed: source != original,
        iterations,
        decoder_candidates,
        replacements,
        transforms,
        safe_static_only: true,
        status,
    };

    if let Some(path) = args.report {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(
            path,
            format!("{}\n", serde_json::to_string_pretty(&report)?),
        )?;
    }
    println!("{}", serde_json::to_string(&report)?);
    Ok(())
}
