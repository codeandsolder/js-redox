//! Connect a captured HTML document to exact source-local direct-call graphs.
use anyhow::{ensure, Context, Result};
use clap::Parser;
use jsvm_lift::{
    analysis_artifacts::{load_artifact, JS_REFERENCES, SOURCE_INDEX},
    capture_project::read_manifest,
    document_entrypoints::captured_document_entrypoints,
    safe_deob::SourceMode,
    sha256_hex,
    static_calls::analyze_static_calls,
    static_module_graph::link_static_modules,
};
use oxc_allocator::Allocator;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::PathBuf,
    time::Duration,
};
use work_budget::{BudgetLimits, WorkBudget};

#[derive(Debug, Parser)]
#[command(
    about = "Recover source-linked static script roots and direct JS calls from a capture project"
)]
struct Args {
    /// Already imported capture project with capture-manifest.json and resources.
    project: PathBuf,
    /// Save JSON report. Refuses to overwrite a pre-existing file.
    #[arg(long)]
    output: PathBuf,
    /// Limit total analysis wall time (seconds).
    #[arg(long, default_value_t = 240)]
    max_secs: u64,
}

fn analyze_source(
    source: &str,
    source_path: &std::path::Path,
    is_module: bool,
    budget: &WorkBudget,
) -> Result<Value> {
    let allocator = Allocator::default();
    let source_type = if is_module {
        SourceType::mjs()
    } else {
        SourceMode::for_path(source_path).source_type()
    };
    let parsed = parse_program(&allocator, source, source_type);
    if !parsed.is_clean() {
        return Ok(json!({
            "status":"syntax_diagnostics",
            "source_sha256":sha256_hex(source.as_bytes()),
        }));
    }
    let built = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_check_syntax_error(true)
        .build(&parsed.program);
    if !built.diagnostics.is_empty() {
        return Ok(json!({
            "status":"semantic_diagnostics",
            "source_sha256":sha256_hex(source.as_bytes()),
        }));
    }
    let graph = analyze_static_calls(&built.semantic, budget)?;
    Ok(json!({
        "status":"analyzed",
        "source_sha256":sha256_hex(source.as_bytes()),
        "graph":graph
    }))
}

fn main() -> Result<()> {
    let args = Args::parse();
    ensure!(
        !args.output.exists(),
        "refusing to replace {}",
        args.output.display()
    );
    let project = args
        .project
        .canonicalize()
        .with_context(|| format!("capture project does not exist: {}", args.project.display()))?;
    let manifest = read_manifest(&project.join("capture-manifest.json"))?;
    let budget = WorkBudget::new(
        "static-document-entrypoint-analysis",
        BudgetLimits::wall_time(Duration::from_secs(args.max_secs)),
    );
    let documents = captured_document_entrypoints(&project, &manifest, &budget)?;
    let mut source_graphs = BTreeMap::<String, Value>::new();
    let mut candidates = BTreeSet::<(String, bool)>::new();
    for document in &documents {
        for script in &document.scripts {
            budget.consume(1)?;
            if !script.executable {
                continue;
            }
            for source in &script.captured_sources {
                candidates.insert((source.output_path.clone(), script.is_module));
            }
        }
    }
    for (output_path, is_module) in candidates {
        budget.consume(1)?;
        let file = project.join(&output_path);
        let source = fs::read_to_string(&file)
            .with_context(|| format!("reading captured script {}", file.display()))?;
        let proof = analyze_source(&source, &file, is_module, &budget)?;
        let key = serde_json::to_string(&(&output_path, is_module))?;
        source_graphs.insert(
            key,
            json!({
                "output_path":output_path,
                "is_module":is_module,
                "analysis":proof
            }),
        );
    }
    let module_graph = match (
        load_artifact(&project, SOURCE_INDEX, true)?,
        load_artifact(&project, JS_REFERENCES, true)?,
    ) {
        (Some(source_index), Some(js_references)) => json!({
            "status":"available",
            "analysis":link_static_modules(
                &project, &documents, &source_index, &js_references, &budget,
            )?,
            "references_schema": JS_REFERENCES.schema,
            "source_index_schema": SOURCE_INDEX.schema,
        }),
        _ => json!({
            "status":"unavailable",
            "reason":"Existing source-index and JS-reference artifacts are both required for contextual module resolution",
        }),
    };
    let root_count: usize = documents
        .iter()
        .map(|document| {
            document
                .scripts
                .iter()
                .filter(|script| script.executable)
                .count()
        })
        .sum();
    let analyzed_count = source_graphs
        .values()
        .filter(|value| value["analysis"]["status"] == "analyzed")
        .count();
    let output = json!({
        "schema":"jsvm-document-static-entrypoints/v2",
        "capture_project":project,
        "document_count":documents.len(),
        "executable_parser_script_roots":root_count,
        "source_graphs_analyzed":analyzed_count,
        "documents":documents,
        "source_graphs":source_graphs,
        "static_module_dependencies":module_graph,
        "limitations":[
            "HTML script ordinals and scheduler classes are source-level candidates, not observed completion order.",
            "Async, defer, module, nomodule, dynamic script insertions and module imports require independent browser-semantic and input-dependent resolution.",
            "Direct JS function-call edges are source-local candidates, including conditional branches; they are not actual invocation witnesses.",
            "Calls through properties, dynamic lexical bindings, callbacks, and unobserved network resources remain unresolved; no missing source is invented.",
            "Source identities are SHA-256-bound to captured bytes and matched by URL rather than filename.",
            "Static module resolution composes the existing import-map-aware JS-reference analysis and explicitly distinguishes original raw from transformed analysis SHA and offsets.",
            "Import-map resolution timing and module loading/order are not proven by source-only analysis."
        ]
    });
    fs::write(&args.output, serde_json::to_vec_pretty(&output)?)
        .with_context(|| format!("writing {}", args.output.display()))?;
    println!(
        "Documents: {}; executable script roots: {}; source-local static graphs: {}; output: {}",
        output["document_count"],
        root_count,
        analyzed_count,
        args.output.display()
    );
    Ok(())
}
