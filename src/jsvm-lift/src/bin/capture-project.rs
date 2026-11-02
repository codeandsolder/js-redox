use anyhow::{Context, Result};
use clap::Parser;
use jsvm_lift::{
    analysis_artifacts::{
        load_artifact, ArtifactSpec, API_SURFACE, BUNDLES, DEOBFUSCATION, GENERATED_RECOVERY,
        JSVM_INDEX, JS_REFERENCES, RUNTIME_SCRIPTS, SOURCEMAPS, SOURCE_GRAPH, SOURCE_INDEX,
        WASM_INDEX, WASM_JS_BOUNDARY, WASM_RESOURCE_PROVENANCE,
    },
    analysis_budget::AnalysisBudgets,
    capture_pipeline::{recover_capture_project, CapturePipelineOptions},
    capture_project::{read_manifest, MANIFEST_NAME},
};
use serde_json::Value;
use std::{
    env,
    path::{Path, PathBuf},
};

#[derive(Parser, Debug)]
#[command(about = "Recover a readable provenance-preserving project from a browser capture")]
struct Args {
    capture: PathBuf,
    output: PathBuf,
    #[arg(long)]
    assets_dir: Option<PathBuf>,
    #[arg(long)]
    overwrite: bool,
    #[arg(long)]
    jobs: Option<usize>,
    #[arg(long)]
    skip_safe_deobfuscation: bool,
    #[arg(long)]
    skip_bundle_unpack: bool,
    #[arg(long)]
    skip_vm_scan: bool,
    #[arg(long)]
    skip_wasm_analysis: bool,
}

fn required_artifact(project: &Path, spec: ArtifactSpec) -> Result<Value> {
    load_artifact(project, spec, false)?.with_context(|| format!("missing {}", spec.name))
}

fn optional_artifact(project: &Path, spec: ArtifactSpec) -> Result<Value> {
    Ok(load_artifact(project, spec, true)?.unwrap_or(Value::Null))
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

fn print_summary(
    project: &Path,
    wasm_analysis: bool,
    safe_deob: bool,
    bundle_unpack: bool,
    vm_scan: bool,
) -> Result<()> {
    let manifest = read_manifest(&project.join(MANIFEST_NAME))?;
    let source_index = required_artifact(project, SOURCE_INDEX)?;
    let sourcemaps = required_artifact(project, SOURCEMAPS)?;
    let references = required_artifact(project, JS_REFERENCES)?;
    let api = required_artifact(project, API_SURFACE)?;
    let graph = required_artifact(project, SOURCE_GRAPH)?;
    let runtime = optional_artifact(project, RUNTIME_SCRIPTS)?;

    let javascript_units = source_index
        .get("units")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter(|unit| unit.get("kind").and_then(Value::as_str) == Some("javascript"))
        .count();

    let wasm = if wasm_analysis {
        optional_artifact(project, WASM_INDEX)?
    } else {
        Value::Null
    };
    let wasm_runtime = if wasm_analysis {
        optional_artifact(project, WASM_RESOURCE_PROVENANCE)?
    } else {
        Value::Null
    };
    let wasm_boundary = if wasm_analysis && safe_deob {
        optional_artifact(project, WASM_JS_BOUNDARY)?
    } else {
        Value::Null
    };
    let deob = if safe_deob {
        optional_artifact(project, DEOBFUSCATION)?
    } else {
        Value::Null
    };
    let bundles = if safe_deob && bundle_unpack {
        optional_artifact(project, BUNDLES)?
    } else {
        Value::Null
    };
    let generated = if vm_scan {
        optional_artifact(project, GENERATED_RECOVERY)?
    } else {
        Value::Null
    };
    let vm = if vm_scan {
        optional_artifact(project, JSVM_INDEX)?
    } else {
        Value::Null
    };

    let dynamic_units = vm
        .get("dynamic_code_units")
        .and_then(Value::as_array)
        .map_or(0, Vec::len);
    let devirtualized_units = vm
        .get("devirtualized_units")
        .and_then(Value::as_array)
        .map_or(0, Vec::len);
    let runtime_events = summary_u64(&runtime, "script_parsed_events");
    let runtime_sources = summary_u64(&runtime, "unique_javascript_sources");
    let graph_nodes = summary_u64(&graph, "nodes");
    let graph_edges = summary_u64(&graph, "edges");

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
    if safe_deob {
        println!(
            "  safe-deob changed:    {}",
            summary_u64(&deob, "changed_units")
        );
    }
    if safe_deob && bundle_unpack {
        println!(
            "  bundle modules:       {}",
            summary_u64(&bundles, "modules")
        );
    }
    if wasm_analysis {
        println!(
            "  WebAssembly modules:  {} ({} origin(s))",
            summary_u64(&wasm, "modules"),
            summary_u64(&wasm, "origins")
        );
        if wasm_runtime
            .get("summary")
            .and_then(|summary| summary.get("applicable"))
            .and_then(Value::as_bool)
            .unwrap_or(false)
        {
            println!(
                "  runtime WASM:         {} observation(s)",
                summary_u64(&wasm_runtime, "observations")
            );
        }
        if safe_deob {
            println!(
                "  copied-input proofs:  {}/{}",
                summary_u64(&wasm_boundary, "proven_js_typed_array_copy_semantics"),
                summary_u64(&wasm_boundary, "copied_input_candidates")
            );
        }
    }
    if vm_scan {
        println!("  dynamic units:        {dynamic_units}");
        println!("  devirtualized VMs:    {devirtualized_units}");
        println!(
            "  generated recovery:   safe={} string-only={} exact-fallback={}",
            summary_u64(&generated, "safe_deobfuscation"),
            summary_u64(&generated, "string_recovery_only"),
            summary_u64(&generated, "exact_fallback")
        );
    }
    if runtime_events != 0 {
        println!("  runtime scripts:      {runtime_events} events -> {runtime_sources} unique");
    }
    println!("  source graph:         {graph_nodes} nodes / {graph_edges} edges");
    Ok(())
}

fn main() -> Result<()> {
    let args = Args::parse();
    let caller_cwd = env::current_dir()?;
    let capture = args
        .capture
        .canonicalize()
        .with_context(|| format!("capture does not exist: {}", args.capture.display()))?;
    let output = if args.output.is_absolute() {
        args.output.clone()
    } else {
        caller_cwd.join(&args.output)
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

    let safe_deob = !args.skip_safe_deobfuscation;
    let bundle_unpack = safe_deob && !args.skip_bundle_unpack;
    let wasm_analysis = !args.skip_wasm_analysis;

    recover_capture_project(&CapturePipelineOptions {
        input: capture,
        output: output.clone(),
        assets_dir,
        overwrite: args.overwrite,
        jobs: args.jobs,
        safe_deobfuscation: safe_deob,
        bundle_materialization: bundle_unpack,
        wasm_analysis,
        vm_scan: !args.skip_vm_scan,
        budgets: AnalysisBudgets::standard("capture-project"),
    })?;

    print_summary(
        &output,
        wasm_analysis,
        safe_deob,
        bundle_unpack,
        !args.skip_vm_scan,
    )
}
