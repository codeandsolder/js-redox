use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_codegen::Codegen;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::{collections::BTreeMap, fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(version, about = "Conservative static JS deobfuscation; never executes sample code")]
struct Args {
    input: PathBuf,
    output: PathBuf,
    #[arg(long)]
    report: Option<PathBuf>,
    #[arg(long, default_value_t = 16)]
    max_iterations: usize,
    /// Pretty-print the final analyst view. This is intentionally opt-in:
    /// Function#toString and related self-defending code can observe formatting.
    #[arg(long)]
    format_output: bool,
}

fn canonicalize(source: &str) -> Option<String> {
    for source_type in [SourceType::mjs(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, source_type);
        if !parsed.is_clean() {
            continue;
        }
        return Some(Codegen::new().build(&parsed.program).code);
    }
    None
}

fn sha256(bytes: &[u8]) -> String {
    jsvm_lift::sha256_hex(bytes)
}

#[derive(Serialize)]
struct ArithmeticStateProofReport {
    iteration: usize,
    input_start: usize,
    input_end: usize,
    state_var: String,
    state_path: Vec<String>,
    termination: String,
    register_reads_rewritten: usize,
    branch_test: Option<String>,
    branch_paths: Vec<Vec<String>>,
    branch_terminations: Vec<String>,
}

#[derive(Serialize)]
struct StaticAliasInstallerCallReport {
    start: u32,
    end: u32,
    installer: String,
    resolver: String,
    resolver_member: Option<String>,
    source_property: String,
    target_selector: u8,
    target_hint: Option<String>,
    alias_property: String,
    forwarding_installer_proven: bool,
    semantics_proven: bool,
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
    analysis_source_sha256: String,
    static_alias_installer_calls: Vec<StaticAliasInstallerCallReport>,
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
    let result = jsvm_safe_core::deobfuscate(&original, args.max_iterations).ok_or_else(|| {
        anyhow::anyhow!("source failed parse or semantic validation during safe deobfuscation")
    })?;

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
            register_reads_rewritten: proof.register_reads_rewritten,
            branch_test: proof.branch_test.clone(),
            branch_paths: proof.branch_paths.clone(),
            branch_terminations: proof.branch_terminations.clone(),
        })
        .collect::<Vec<_>>();
    let iterations = result.iterations;
    let analysis_source_sha256 = sha256(result.source.as_bytes());
    let static_alias_installer_calls =
        jsvm_lift::forwarding_alias::static_alias_installer_calls(&result.source)
            .into_iter()
            .map(|call| {
                let target_hint = match (&call.resolver_member, call.target_selector) {
                    (Some(member), 0) => Some(member.clone()),
                    (Some(member), 1) => Some(format!("{member}.prototype")),
                    (None, _) => None,
                    _ => None,
                };
                StaticAliasInstallerCallReport {
                    start: call.start,
                    end: call.end,
                    installer: call.installer,
                    resolver: call.resolver,
                    resolver_member: call.resolver_member,
                    source_property: call.source_property,
                    target_selector: call.target_selector,
                    target_hint,
                    alias_property: call.alias_property,
                    forwarding_installer_proven: call.forwarding_installer_proven,
                    semantics_proven: call.semantics_proven,
                }
            })
            .collect::<Vec<_>>();

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
        schema: "js-safe-deobfuscate/v1",
        input: args.input.display().to_string(),
        input_sha256: sha256(original.as_bytes()),
        output_sha256: sha256(source.as_bytes()),
        changed: source != original,
        iterations,
        transforms,
        arithmetic_state_proofs,
        analysis_source_sha256,
        static_alias_installer_calls,
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
