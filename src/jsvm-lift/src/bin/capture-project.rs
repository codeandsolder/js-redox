use anyhow::{Context, Result};
use clap::Parser;
use jsvm_lift::{
    analysis_artifacts::{
        load_artifact, load_optional_artifact, ArtifactSpec, API_SURFACE, BUNDLES, DEOBFUSCATION,
        GENERATED_RECOVERY, JSVM_INDEX, JS_REFERENCES, OBSERVED_SOURCE, RUNTIME_SCRIPTS,
        SOURCEMAPS, SOURCE_GRAPH, SOURCE_INDEX, WASM_INDEX, WASM_JS_BOUNDARY,
        WASM_RESOURCE_PROVENANCE,
    },
    analysis_budget::AnalysisBudgets,
    capture_pipeline::{
        recover_capture_project, CapturePipelineOptions, CaptureStages, SourceRecovery,
    },
    capture_project::{read_manifest, write_manifest, MANIFEST_NAME},
    http_capture::{capture_url_to_har, HttpCaptureLimits, HttpCaptureSummary},
    project_readme::refresh_project_readme,
};
use serde_json::Value;
use std::{
    env,
    path::{Path, PathBuf},
};

#[derive(Parser, Debug)]
#[command(about = "Recover a readable provenance-preserving project from a browser capture")]
struct Args {
    capture: String,
    output: PathBuf,
    #[arg(long)]
    assets_dir: Option<PathBuf>,
    #[arg(long)]
    overwrite: bool,
    #[arg(long)]
    jobs: Option<usize>,
    #[command(flatten)]
    source: SourceArgs,
    #[arg(long)]
    skip_vm_scan: bool,
    #[arg(long)]
    skip_wasm_analysis: bool,
    /// Maximum HTTP resources when the input is a URL.
    #[arg(long, default_value_t = 128)]
    http_max_resources: usize,
    /// Maximum cumulative HTTP response bytes in MiB.
    #[arg(long, default_value_t = 64)]
    http_max_total_mib: usize,
    /// Per-response HTTP byte cap in MiB.
    #[arg(long, default_value_t = 8)]
    http_max_resource_mib: usize,
}

#[derive(clap::Args, Debug)]
struct SourceArgs {
    #[arg(long)]
    skip_safe_deobfuscation: bool,
    #[arg(long)]
    skip_bundle_unpack: bool,
}

impl SourceArgs {
    const fn recovery(&self) -> SourceRecovery {
        if self.skip_safe_deobfuscation {
            SourceRecovery::Disabled
        } else if self.skip_bundle_unpack {
            SourceRecovery::Deobfuscate
        } else {
            SourceRecovery::Bundles
        }
    }
}

fn optional_artifact(project: &Path, spec: ArtifactSpec) -> Result<Value> {
    Ok(load_optional_artifact(project, spec)?.unwrap_or(Value::Null))
}

fn summary_u64(document: &Value, field: &str) -> u64 {
    document
        .get("summary")
        .and_then(|summary| summary.get(field))
        .and_then(Value::as_u64)
        .unwrap_or(0)
}

fn recovered_sourcemap_sources(document: &Value) -> usize {
    document
        .get("source_maps")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .flat_map(|source_map| {
            let preferred = source_map
                .get("composed_recovered")
                .and_then(Value::as_array)
                .filter(|rows| !rows.is_empty())
                .or_else(|| source_map.get("recovered").and_then(Value::as_array));
            preferred.into_iter().flatten()
        })
        .filter(|row| row.get("status").and_then(Value::as_str) == Some("recovered"))
        .count()
}

fn print_summary(project: &Path, stages: CaptureStages) -> Result<()> {
    let wasm_analysis = stages.wasm_analysis;
    let vm_scan = stages.vm_scan;
    let manifest = read_manifest(&project.join(MANIFEST_NAME))?;
    let source_index = load_artifact(project, SOURCE_INDEX)?;
    let sourcemaps = load_artifact(project, SOURCEMAPS)?;
    let references = load_artifact(project, JS_REFERENCES)?;
    let api = load_artifact(project, API_SURFACE)?;
    let graph = load_artifact(project, SOURCE_GRAPH)?;
    let runtime = optional_artifact(project, RUNTIME_SCRIPTS)?;
    let observed = optional_artifact(project, OBSERVED_SOURCE)?;

    let javascript_units = source_index
        .get("units")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter(|unit| unit.get("kind").and_then(Value::as_str) == Some("javascript"))
        .count();

    let runtime_events = summary_u64(&runtime, "script_parsed_events");
    let runtime_sources = summary_u64(&runtime, "unique_javascript_sources");
    let graph_nodes = summary_u64(&graph, "nodes");
    let graph_edges = summary_u64(&graph, "edges");
    let graph_unresolved = summary_u64(&graph, "unresolved_edges");

    println!("\nProject ready: {}", project.display());
    println!("  input kind:           {}", manifest.source.kind);
    println!(
        "  capture state:        {}",
        if manifest.source.salvaged {
            "SALVAGED / truncated"
        } else {
            "complete"
        }
    );
    println!("  captured resources:   {}", manifest.resources.len());
    println!("  JavaScript units:     {javascript_units}");
    println!(
        "  source-map originals: {}",
        recovered_sourcemap_sources(&sourcemaps)
    );
    println!(
        "  JS references:        {}",
        summary_u64(&references, "references")
    );
    println!("  API callsites:        {}", summary_u64(&api, "callsites"));
    print_source_summary(project, stages.source)?;
    if wasm_analysis {
        print_wasm_summary(project, stages.source)?;
    }
    if vm_scan {
        print_vm_summary(project)?;
    }
    if runtime_events != 0 {
        println!("  runtime scripts:      {runtime_events} events -> {runtime_sources} unique");
    }
    if !observed.is_null() {
        println!(
            "  observed JS sources:  {} positive witness(es), {} formatted",
            summary_u64(&observed, "witnessed_sources"),
            summary_u64(&observed, "formatted_sources")
        );
    }
    println!("  source graph:         {graph_nodes} nodes / {graph_edges} edges / {graph_unresolved} unresolved claims");
    Ok(())
}

fn print_source_summary(project: &Path, source: SourceRecovery) -> Result<()> {
    if source.deobfuscates() {
        let deob = optional_artifact(project, DEOBFUSCATION)?;
        println!(
            "  safe-deob changed:    {}",
            summary_u64(&deob, "changed_units")
        );
    }
    if source.materializes_bundles() {
        let bundles = optional_artifact(project, BUNDLES)?;
        println!(
            "  bundle modules:       {}",
            summary_u64(&bundles, "modules")
        );
    }
    Ok(())
}

fn print_wasm_summary(project: &Path, source: SourceRecovery) -> Result<()> {
    let wasm = optional_artifact(project, WASM_INDEX)?;
    let runtime = optional_artifact(project, WASM_RESOURCE_PROVENANCE)?;
    println!(
        "  WebAssembly modules:  {} ({} origin(s))",
        summary_u64(&wasm, "modules"),
        summary_u64(&wasm, "origins")
    );
    if runtime
        .get("summary")
        .and_then(|summary| summary.get("applicable"))
        .and_then(Value::as_bool)
        .unwrap_or(false)
    {
        println!(
            "  runtime WASM:         {} observation(s)",
            summary_u64(&runtime, "observations")
        );
    }
    if source.deobfuscates() {
        let boundary = optional_artifact(project, WASM_JS_BOUNDARY)?;
        println!(
            "  copied-input proofs:  {}/{}",
            summary_u64(&boundary, "proven_js_typed_array_copy_semantics"),
            summary_u64(&boundary, "copied_input_candidates")
        );
    }
    Ok(())
}

fn print_vm_summary(project: &Path) -> Result<()> {
    let vm = optional_artifact(project, JSVM_INDEX)?;
    let generated = optional_artifact(project, GENERATED_RECOVERY)?;
    let dynamic_units = vm
        .get("dynamic_code_units")
        .and_then(Value::as_array)
        .map_or(0, Vec::len);
    let devirtualized_units = vm
        .get("devirtualized_units")
        .and_then(Value::as_array)
        .map_or(0, Vec::len);
    println!("  dynamic units:        {dynamic_units}");
    println!("  devirtualized VMs:    {devirtualized_units}");
    println!(
        "  generated recovery:   safe={} string-only={} exact-fallback={}",
        summary_u64(&generated, "safe_deobfuscation"),
        summary_u64(&generated, "string_recovery_only"),
        summary_u64(&generated, "exact_fallback")
    );
    Ok(())
}

fn archive_http_capture(
    capture: &Path,
    output: &Path,
    requested_url: &str,
    summary: &HttpCaptureSummary,
) -> Result<()> {
    let analysis = output.join("analysis");
    let archived = analysis.join("http-capture.har");
    jsvm_lift::report_file::copy_snapshot(
        capture,
        &archived,
        &AnalysisBudgets::standard("http-capture-archive").scope("snapshot"),
    )?;
    jsvm_lift::report_file::write_json(&analysis.join("http-static.json"), summary)?;
    let manifest_path = output.join(MANIFEST_NAME);
    let mut manifest = read_manifest(&manifest_path)?;
    manifest.source.kind = "http_static".into();
    requested_url.clone_into(&mut manifest.source.input);
    manifest
        .source
        .extra
        .insert("requested_url".into(), summary.requested_url.clone().into());
    manifest
        .source
        .extra
        .insert("final_url".into(), summary.final_url.clone().into());
    manifest
        .source
        .extra
        .insert("captured_har".into(), "analysis/http-capture.har".into());
    manifest
        .source
        .extra
        .insert("http_static".into(), serde_json::to_value(summary)?);
    write_manifest(&manifest_path, &manifest)?;
    refresh_project_readme(output, &AnalysisBudgets::standard("http-project-readme"))?;
    Ok(())
}

fn main() -> Result<()> {
    let args = Args::parse();
    let caller_cwd = env::current_dir()?;
    let output = if args.output.is_absolute() {
        args.output.clone()
    } else {
        caller_cwd.join(&args.output)
    };
    let remote = url::Url::parse(&args.capture)
        .ok()
        .filter(|url| matches!(url.scheme(), "http" | "https"));
    let temp_capture = if remote.is_some() {
        Some(tempfile::tempdir().context("staging HTTP-only capture")?)
    } else {
        None
    };
    let http_summary = if let Some(temp) = &temp_capture {
        Some(capture_url_to_har(
            &args.capture,
            &temp.path().join("capture.har"),
            HttpCaptureLimits {
                max_resources: args.http_max_resources,
                max_resource_bytes: args.http_max_resource_mib.saturating_mul(1024 * 1024),
                max_total_bytes: args.http_max_total_mib.saturating_mul(1024 * 1024),
            },
        )?)
    } else {
        None
    };
    let capture = if let Some(temp) = &temp_capture {
        temp.path().join("capture.har")
    } else {
        PathBuf::from(&args.capture)
            .canonicalize()
            .with_context(|| format!("capture does not exist: {}", args.capture))?
    };
    let assets_dir = args
        .assets_dir
        .as_ref()
        .map(|path| {
            let path = if path.is_absolute() {
                path.clone()
            } else {
                caller_cwd.join(path)
            };
            path.canonicalize()
                .with_context(|| format!("assets directory does not exist: {}", path.display()))
        })
        .transpose()?;

    let stages = CaptureStages {
        source: args.source.recovery(),
        wasm_analysis: !args.skip_wasm_analysis,
        vm_scan: !args.skip_vm_scan,
    };

    recover_capture_project(&CapturePipelineOptions {
        input: capture.clone(),
        output: output.clone(),
        assets_dir,
        overwrite: args.overwrite,
        jobs: args.jobs,
        stages,
        budgets: AnalysisBudgets::standard("capture-project"),
    })?;

    if let Some(summary) = http_summary {
        archive_http_capture(&capture, &output, &args.capture, &summary)?;
    }

    print_summary(&output, stages)
}
