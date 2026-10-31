use anyhow::{bail, Context, Result};
use clap::Parser;
use jsvm_lift::{
    analysis_artifacts::{
        load_artifact, ArtifactSpec, API_SURFACE, BUNDLES, DEOBFUSCATION, GENERATED_RECOVERY,
        JSVM_INDEX, JS_REFERENCES, RUNTIME_SCRIPTS, SOURCEMAPS, SOURCE_GRAPH, SOURCE_INDEX,
        WASM_INDEX, WASM_JS_BOUNDARY, WASM_RESOURCE_PROVENANCE,
    },
    capture_project::{read_manifest, MANIFEST_NAME},
    project_scan::{scan_project, ProjectScanOptions},
    tool_environment::{repository_root, tool_dir},
};
use serde_json::Value;
use std::{
    env,
    ffi::OsStr,
    path::{Path, PathBuf},
    process::Command,
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

fn tool(root: &Path, name: &str) -> PathBuf {
    root.join(name)
}

fn push_jobs(command: &mut Command, jobs: Option<usize>) {
    if let Some(jobs) = jobs {
        command.arg("--jobs").arg(jobs.to_string());
    }
}

fn run(command: &mut Command, cwd: &Path) -> Result<()> {
    command.current_dir(cwd);
    let rendered = format!("{command:?}");
    let output = command
        .output()
        .with_context(|| format!("launching {rendered}"))?;
    if !output.status.success() {
        bail!(
            "command failed ({}): {rendered}\n{}{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    if !output.stdout.is_empty() {
        print!("{}", String::from_utf8_lossy(&output.stdout));
    }
    Ok(())
}

fn run_tool<I, S>(tool_root: &Path, repo: &Path, name: &str, args: I) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut command = Command::new(tool(tool_root, name));
    command.args(args);
    run(&mut command, repo)
}

fn run_python<I, S>(repo: &Path, script: &str, args: I) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut command = Command::new("uv");
    command
        .arg("run")
        .arg("--no-project")
        .arg("python")
        .arg(repo.join("scripts").join(script))
        .args(args);
    run(&mut command, repo)
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
    let repo = repository_root()?;
    let tool_root = tool_dir()?;
    let capture = args
        .capture
        .canonicalize()
        .with_context(|| format!("capture does not exist: {}", args.capture.display()))?;
    let caller_cwd = env::current_dir()?;
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

    let mut import = Command::new(tool(&tool_root, "capture-import"));
    import.arg(&capture).arg("--output").arg(&output);
    if let Some(assets) = &assets_dir {
        import.arg("--assets-dir").arg(assets);
    }
    if args.overwrite {
        import.arg("--overwrite");
    }
    run(&mut import, &repo)?;

    let manifest_path = output.join(MANIFEST_NAME);
    let manifest = read_manifest(&manifest_path).with_context(|| {
        format!(
            "capture importer did not create a valid {}",
            manifest_path.display()
        )
    })?;

    let mut materialize = Command::new(tool(&tool_root, "source-materialize"));
    materialize.arg(&output);
    push_jobs(&mut materialize, args.jobs);
    run(&mut materialize, &repo)?;

    let wasm_analysis = !args.skip_wasm_analysis;
    let safe_deob = !args.skip_safe_deobfuscation;
    let bundle_unpack = safe_deob && !args.skip_bundle_unpack;
    let vm_scan = !args.skip_vm_scan;

    if wasm_analysis {
        run_tool(&tool_root, &repo, "wasm-materialize", [&output])?;
        if manifest.source.kind == "recorder" {
            run_tool(&tool_root, &repo, "wasm-resource-provenance", [&output])?;
        }
    }

    run_tool(
        &tool_root,
        &repo,
        "sourcemaps",
        [OsStr::new("project"), output.as_os_str()],
    )?;

    let mut refs = Command::new(tool(&tool_root, "js-refs"));
    refs.arg("--project").arg(&output);
    push_jobs(&mut refs, args.jobs);
    run(&mut refs, &repo)?;

    if safe_deob {
        let mut deob = Command::new(tool(&tool_root, "deobfuscate-safe"));
        deob.arg("project").arg(&output);
        push_jobs(&mut deob, args.jobs);
        run(&mut deob, &repo)?;
        if bundle_unpack {
            let mut bundle = Command::new(tool(&tool_root, "bundle-materialize"));
            bundle.arg(&output);
            push_jobs(&mut bundle, args.jobs);
            run(&mut bundle, &repo)?;
        }
    }

    if wasm_analysis && safe_deob {
        run_python(
            &repo,
            "correlate-wasm-js-boundary.py",
            [
                output.as_os_str(),
                OsStr::new("--analyzer"),
                tool(&tool_root, "wasm-import-semantics").as_os_str(),
            ],
        )?;
    }

    if vm_scan {
        let summary = scan_project(
            &output,
            &ProjectScanOptions::with_defaults(
                repo.clone(),
                repo.join("scripts/recover-js-obfuscator-strings.py"),
                tool(&tool_root, "switch-ir"),
                tool(&tool_root, "table-ir"),
            ),
        )?;
        println!(
            "VM scan: {} units; {} scanner invocations / {} exact-hash reuses; {} generated units; {} confirmed VM units; {} handler-table candidates; {} failures",
            summary.code_units,
            summary.scanner_invocations,
            summary.deduplicated_scans,
            summary.dynamic_units,
            summary.confirmed_vm_units,
            summary.handler_table_candidates,
            summary.failures,
        );
        run_tool(&tool_root, &repo, "vm-materialize", [&output])?;
    }

    run_tool(
        &tool_root,
        &repo,
        "api-surface",
        [OsStr::new("--project"), output.as_os_str()],
    )?;
    run_tool(&tool_root, &repo, "source-graph", [&output])?;
    run_tool(&tool_root, &repo, "project-readme", [&output])?;

    print_summary(&output, wasm_analysis, safe_deob, bundle_unpack, vm_scan)
}
