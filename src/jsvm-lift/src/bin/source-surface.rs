//! Inspect syntactic function behavior without requiring a VM handler proof.
use anyhow::{ensure, Context, Result};
use clap::Parser;
use jsvm_lift::{
    function_surface::analyze_function_source_surfaces, safe_deob::SourceMode, sha256_hex,
};
use oxc_allocator::Allocator;
use oxc_ast::AstKind;
use oxc_semantic::SemanticBuilder;
use oxc_span::Span;
use rolldown_redox::ecmascript::parse_program;
use serde_json::json;
use std::{fs, path::PathBuf, time::Duration};
use work_budget::{BudgetLimits, WorkBudget};

#[derive(Parser, Debug)]
#[command(
    about = "Inventory source-bound calls, external references and effects in arbitrary JavaScript functions"
)]
struct Args {
    /// Original or extracted JavaScript file to inspect.
    input: PathBuf,
    /// Inspect one exact function span START:END; repeat to inspect several.
    /// With no spans, list all function spans for selection.
    #[arg(long = "function", value_name = "START:END")]
    functions: Vec<String>,
    /// Save JSON to a file; default is stdout.
    #[arg(long)]
    output: Option<PathBuf>,
    /// Maximum proof-analysis wall-time in seconds.
    #[arg(long, default_value_t = 120)]
    max_secs: u64,
}

fn parse_span(s: &str) -> Result<Span> {
    let (start, end) = s
        .split_once(':')
        .context("function span must be START:END in original bytes")?;
    let start: u32 = start.parse().context("invalid function start byte")?;
    let end: u32 = end.parse().context("invalid function end byte")?;
    ensure!(start < end, "function span must be nonempty and ordered");
    Ok(Span::new(start, end))
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let allocator = Allocator::default();
    let parsed = parse_program(
        &allocator,
        &source,
        SourceMode::for_path(&args.input).source_type(),
    );
    ensure!(parsed.is_clean(), "input has JavaScript syntax diagnostics");
    let built = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_check_syntax_error(true)
        .build(&parsed.program);
    ensure!(
        built.diagnostics.is_empty(),
        "input has JavaScript semantic diagnostics"
    );
    let semantic = &built.semantic;
    let budget = WorkBudget::new(
        "source-function-surface",
        BudgetLimits::wall_time(Duration::from_secs(args.max_secs)),
    );
    let source_sha256 = sha256_hex(source.as_bytes());

    let mut spans = Vec::new();
    for string in &args.functions {
        spans.push(parse_span(string)?);
    }

    let output = if spans.is_empty() {
        let mut functions = Vec::new();
        let nodes = semantic.nodes();
        for (node_id, node) in nodes.iter_enumerated() {
            budget.consume(1)?;
            let (kind, span) = match node.kind() {
                AstKind::Function(function) => ("function", function.span),
                AstKind::ArrowFunctionExpression(function) => ("arrow", function.span),
                _ => continue,
            };
            let parents = nodes
                .ancestor_ids(node_id)
                .filter_map(|id| match nodes.kind(id) {
                    AstKind::Function(parent) => Some(parent.span),
                    AstKind::ArrowFunctionExpression(parent) => Some(parent.span),
                    _ => None,
                })
                .collect::<Vec<_>>();
            functions.push(json!({
                "span":[span.start,span.end],
                "kind":kind,
                "lexical_depth":parents.len(),
                "parent_function":parents.first().map(|parent|[parent.start,parent.end]),
            }));
        }
        functions.sort_by_key(|value| {
            (
                value["span"][0].as_u64().unwrap_or_default(),
                value["span"][1].as_u64().unwrap_or_default(),
            )
        });
        json!({
            "schema":"jsvm-source-surface/v1",
            "source_sha256":source_sha256,
            "source_bytes":source.len(),
            "mode":"function_index",
            "functions":functions,
            "interpretation":"Original-source byte spans, not execution or invocation evidence"
        })
    } else {
        let functions = analyze_function_source_surfaces(&source, semantic, &spans, &budget)?
            .into_iter()
            .zip(spans)
            .map(|(surface, span)| {
                surface.with_context(|| {
                    format!("no unique source function at {}:{}", span.start, span.end)
                })
            })
            .collect::<Result<Vec<_>>>()?;
        json!({
            "schema":"jsvm-source-surface/v1",
            "source_sha256":source_sha256,
            "source_bytes":source.len(),
            "mode":"function_evidence",
            "functions":functions,
            "interpretation":"Syntactic evidence with nested lexical depth; no execution claim"
        })
    };
    let encoded = serde_json::to_vec_pretty(&output)?;
    if let Some(path) = args.output {
        ensure!(
            !path.exists(),
            "refusing to overwrite existing output: {}",
            path.display()
        );
        fs::write(&path, &encoded).with_context(|| format!("writing {}", path.display()))?;
    } else {
        println!("{}", String::from_utf8(encoded)?);
    }
    Ok(())
}
