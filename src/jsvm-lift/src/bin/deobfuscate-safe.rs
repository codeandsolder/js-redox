use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_codegen::Codegen;
use oxc_parser::Parser;
use oxc_span::SourceType;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Conservative static JS deobfuscation; never executes sample code")]
struct Args {
    input: PathBuf,
    output: PathBuf,
    #[arg(long)]
    report: Option<PathBuf>,
    #[arg(long, default_value_t = 8)]
    max_iterations: usize,
    /// Pretty-print the final analyst view. This is intentionally opt-in:
    /// Function#toString and related self-defending code can observe formatting.
    #[arg(long)]
    format_output: bool,
}

fn canonicalize(source: &str) -> Option<String> {
    for source_type in [SourceType::mjs(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let parsed = Parser::new(&allocator, source, source_type).parse();
        if parsed.panicked || !parsed.diagnostics.is_empty() {
            continue;
        }
        return Some(Codegen::new().build(&parsed.program).code);
    }
    None
}

fn sha256(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    format!("{:x}", h.finalize())
}

#[derive(Serialize)]
struct ArithmeticStateProofReport {
    iteration: usize,
    input_start: usize,
    input_end: usize,
    state_var: String,
    state_path: Vec<String>,
    termination: String,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    input: String,
    input_sha256: String,
    output_sha256: String,
    changed: bool,
    iterations: usize,
    transforms: BTreeMap<String, usize>,
    arithmetic_state_proofs: Vec<ArithmeticStateProofReport>,
    safe_static_only: bool,
    presentation_formatted: bool,
    runtime_semantics_preserved_by_design: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let original = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;

    // Feed the exact source bytes to the proof-oriented engine. Canonicalizing
    // first is observably unsafe for Function#toString/self-defending code.
    let result = jsvm_safe_core::deobfuscate(&original, args.max_iterations)
        .ok_or_else(|| anyhow::anyhow!("source stopped parsing during safe deobfuscation"))?;

    let arithmetic_state_proofs = result
        .arithmetic_state_proofs
        .iter()
        .map(|proof| ArithmeticStateProofReport {
            iteration: proof.iteration,
            input_start: proof.input_start,
            input_end: proof.input_end,
            state_var: proof.state_var.clone(),
            state_path: proof.state_path.clone(),
            termination: proof.termination.clone(),
        })
        .collect::<Vec<_>>();
    let iterations = result.iterations;

    let mut transforms = result.transforms;
    let source = if args.format_output {
        let formatted = canonicalize(&result.source)
            .ok_or_else(|| anyhow::anyhow!("Oxc could not format transformed source"))?;
        if formatted != result.source {
            *transforms.entry("presentation_codegen".into()).or_default() += 1;
        }
        formatted
    } else {
        result.source
    };

    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&args.output, &source)
        .with_context(|| format!("writing {}", args.output.display()))?;

    let report = Report {
        schema: "js-safe-deobfuscate/v0",
        input: args.input.display().to_string(),
        input_sha256: sha256(original.as_bytes()),
        output_sha256: sha256(source.as_bytes()),
        changed: source != original,
        iterations,
        transforms,
        arithmetic_state_proofs,
        safe_static_only: true,
        presentation_formatted: args.format_output,
        runtime_semantics_preserved_by_design: !args.format_output,
    };

    if let Some(path) = &args.report {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(
            path,
            format!(
                "{}
",
                serde_json::to_string_pretty(&report)?
            ),
        )?;
    }

    println!(
        "safe deobfuscation changed={} iterations={} transforms={:?}",
        report.changed, report.iterations, report.transforms
    );
    Ok(())
}
