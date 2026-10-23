use anyhow::{Context, Result};
use clap::Parser;
use jsvm_lift::static_bytes::analyze_webassembly_byte_artifacts;
use serde::Serialize;
use std::{fs, path::PathBuf};

#[derive(Parser, Debug)]
#[command(about = "Recover exact statically constructed byte artifacts reaching WebAssembly sinks")]
struct Args {
    input: PathBuf,
    #[arg(long)]
    output_dir: PathBuf,
}

#[derive(Debug, Serialize)]
struct InlineWasmLiteralReport {
    sha256: String,
    byte_len: usize,
    output_path: String,
    source_start: u32,
    source_end: u32,
    encoding: &'static str,
    carrier_path: Option<String>,
}

#[derive(Debug, Serialize)]
struct ArtifactReport {
    sha256: String,
    byte_len: usize,
    output_path: String,
    sink_kind: &'static str,
    sink_start: u32,
    sink_end: u32,
    allocation_start: u32,
    allocation_end: u32,
    copy_writes: usize,
    standard_builtins_required: bool,
}

#[derive(Debug, Serialize)]
struct SinkDiagnosticReport {
    sink_start: u32,
    sink_end: u32,
    sink_kind: &'static str,
    recovered: bool,
    buffers_allocated: usize,
    valid_buffers: usize,
    helper_calls_succeeded: usize,
    last_invalidation_reason: Option<&'static str>,
    sink_failure: Option<&'static str>,
}

#[derive(Debug, Serialize)]
struct Report {
    schema: &'static str,
    input: String,
    source_bytes: usize,
    proven_copy_helpers: usize,
    webassembly_sinks: usize,
    sink_diagnostics: Vec<SinkDiagnosticReport>,
    inline_wasm_literals: Vec<InlineWasmLiteralReport>,
    artifacts: Vec<ArtifactReport>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let recovery = analyze_webassembly_byte_artifacts(&source)
        .with_context(|| format!("analyzing {}", args.input.display()))?;
    fs::create_dir_all(&args.output_dir)
        .with_context(|| format!("creating {}", args.output_dir.display()))?;

    let mut inline_wasm_literals = Vec::with_capacity(recovery.inline_wasm_literals.len());
    for artifact in recovery.inline_wasm_literals {
        let output = args.output_dir.join(format!("{}.wasm", artifact.sha256));
        if !output.exists() {
            fs::write(&output, &artifact.bytes)
                .with_context(|| format!("writing {}", output.display()))?;
        }
        inline_wasm_literals.push(InlineWasmLiteralReport {
            sha256: artifact.sha256,
            byte_len: artifact.bytes.len(),
            output_path: output.display().to_string(),
            source_start: artifact.source_start,
            source_end: artifact.source_end,
            encoding: artifact.encoding,
            carrier_path: artifact.carrier_path,
        });
    }

    let mut report_artifacts = Vec::with_capacity(recovery.artifacts.len());
    for artifact in recovery.artifacts {
        let output = args.output_dir.join(format!("{}.wasm", artifact.sha256));
        fs::write(&output, &artifact.bytes)
            .with_context(|| format!("writing {}", output.display()))?;
        report_artifacts.push(ArtifactReport {
            sha256: artifact.sha256,
            byte_len: artifact.bytes.len(),
            output_path: output.display().to_string(),
            sink_kind: artifact.sink_kind,
            sink_start: artifact.sink_start,
            sink_end: artifact.sink_end,
            allocation_start: artifact.allocation_start,
            allocation_end: artifact.allocation_end,
            copy_writes: artifact.copy_writes,
            standard_builtins_required: artifact.standard_builtins_required,
        });
    }

    let sink_diagnostics = recovery
        .sink_diagnostics
        .into_iter()
        .map(|diagnostic| SinkDiagnosticReport {
            sink_start: diagnostic.sink_start,
            sink_end: diagnostic.sink_end,
            sink_kind: diagnostic.sink_kind,
            recovered: diagnostic.recovered,
            buffers_allocated: diagnostic.buffers_allocated,
            valid_buffers: diagnostic.valid_buffers,
            helper_calls_succeeded: diagnostic.helper_calls_succeeded,
            last_invalidation_reason: diagnostic.last_invalidation_reason,
            sink_failure: diagnostic.sink_failure,
        })
        .collect();

    let report = Report {
        schema: "js-static-byte-artifacts/v2",
        input: args.input.display().to_string(),
        source_bytes: source.len(),
        proven_copy_helpers: recovery.proven_copy_helpers,
        webassembly_sinks: recovery.webassembly_sinks,
        sink_diagnostics,
        inline_wasm_literals,
        artifacts: report_artifacts,
    };
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}
