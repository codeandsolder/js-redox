use anyhow::{Context, Result};
use jsvm_lift::forwarding_semantics::structurally_proven_lazy_registry_read_calls;
use oxc_allocator::Allocator;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde_json::json;
use std::{env, fs, path::PathBuf};

fn snippet(source: &str, start: u32, end: u32) -> String {
    source
        .get(start as usize..(end as usize).min(source.len()))
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn main() -> Result<()> {
    let path = env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .context("usage: cargo run -p jsvm-lift --example lazy-registry-inventory -- <file.js>")?;
    let source =
        fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &source, SourceType::cjs());
    anyhow::ensure!(parsed.is_clean(), "parse diagnostics");
    let semantic = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(&parsed.program);
    anyhow::ensure!(semantic.diagnostics.is_empty(), "semantic diagnostics");

    let proven = structurally_proven_lazy_registry_read_calls(
        &parsed.program,
        semantic.semantic.scoping(),
    )
    .into_iter()
    .map(|proof| {
        json!({
            "call": [proof.read.call_start, proof.read.call_end],
            "call_source": snippet(&source, proof.read.call_start, proof.read.call_end),
            "registry_path": proof.read.registry_path,
            "accessor_function": [proof.accessor_function_start, proof.accessor_function_end],
            "cell_assignment": [proof.cell_assignment_start, proof.cell_assignment_end],
            "probe_property": proof.probe_property,
            "update_property": proof.update_property,
            "projection_property": proof.projection_property,
            "selector": [proof.selector_start, proof.selector_end],
            "selector_source": snippet(&source, proof.selector_start, proof.selector_end),
        })
    })
    .collect::<Vec<_>>();
    println!("{}", serde_json::to_string_pretty(&proven)?);
    Ok(())
}
