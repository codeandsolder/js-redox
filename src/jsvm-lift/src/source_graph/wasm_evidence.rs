//! Captured and statically recovered WebAssembly source graph evidence.
//!
//! Resource and inline-script origins preserve exact capture identity. Unknown
//! or incomplete origin descriptions remain unlinked rather than guessed.

use super::{array_field, bool_field, field, string_field, u64_field, GraphBuilder};
use anyhow::{Context, Result};
use serde_json::{json, Value};
use work_budget::WorkBudget;

/// Materialize captured and statically recovered WebAssembly module origins.
pub(super) fn seed_static_wasm_modules(
    graph: &mut GraphBuilder,
    wasm: &Value,
    budget: &WorkBudget,
) -> Result<()> {
    // Captured or statically recovered WebAssembly modules are first-class derived sources.
    for module in array_field(wasm, "modules") {
        budget.checkpoint()?;
        let digest = string_field(module, "sha256").context("WASM module sha256 is required")?;
        let node_id = format!("wasm:{}", &digest[..digest.len().min(20)]);
        graph.intern_node(
            node_id.clone(),
            json!({
                "type":"wasm_module",
                "sha256":digest,
                "bytes":field(module,"byte_len"),
                "binary_path":field(module,"binary_path"),
                "extracted":bool_field(module,"extracted"),
                "status":field(module,"status"),
                "report_path":field(module,"report_path"),
                "readable_wat_path":field(module,"wat_path"),
                "deep_analysis_path":field(module,"deep_path"),
            }),
        )?;
        for origin in array_field(module, "origins") {
            let kind = string_field(origin, "type");
            let parent = match kind {
                Some("resource" | "resource_inline_base64" | "resource_static_bytes") => {
                    u64_field(origin, "resource_id")
                        .map(|resource_id| format!("resource:{resource_id}"))
                }
                Some("inline_script_base64" | "inline_script_static_bytes") => {
                    match (
                        u64_field(origin, "parent_resource_id"),
                        u64_field(origin, "ordinal"),
                    ) {
                        (Some(parent_resource_id), Some(ordinal)) => {
                            Some(format!("inline:{parent_resource_id}:{ordinal}"))
                        }
                        _ => None,
                    }
                }
                _ => None,
            };
            let Some(parent) = parent else {
                continue;
            };
            let edge_kind = match kind {
                Some("resource") => "wasm_resource",
                Some("resource_static_bytes" | "inline_script_static_bytes") => "wasm_static_bytes",
                _ => "wasm_inline_base64",
            };
            graph.add_edge(
                &parent,
                &node_id,
                edge_kind,
                json!({
                    "encoding":field(origin,"encoding"),
                    "recovery_kind":field(origin,"recovery_kind"),
                    "start":field(origin,"byte_start"),
                    "end":field(origin,"byte_end"),
                }),
            )?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn budget() -> WorkBudget {
        WorkBudget::new("static-wasm-test", work_budget::BudgetLimits::unlimited())
    }

    #[test]
    fn static_wasm_keeps_distinct_captured_origins_and_proof_kinds() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let sha = "a".repeat(64);
        let wasm = json!({"modules":[{
            "sha256":sha, "byte_len":24, "status":"recovered",
            "origins":[
                {"type":"resource", "resource_id":7, "encoding":"raw"},
                {"type":"resource_inline_base64", "resource_id":8, "encoding":"base64"},
                {"type":"resource_static_bytes", "resource_id":9, "recovery_kind":"static_bytes"},
                {"type":"inline_script_base64", "parent_resource_id":3, "ordinal":2},
                {"type":"inline_script_static_bytes", "parent_resource_id":3, "ordinal":4},
                {"type":"inline_script_static_bytes", "parent_resource_id":3},
                {"type":"unverified", "resource_id":99}
            ]
        }]});
        seed_static_wasm_modules(&mut graph, &wasm, &budget())?;
        let wasm_id = format!("wasm:{}", "a".repeat(20));
        assert_eq!(graph.nodes()[&wasm_id]["sha256"], sha);
        assert_eq!(graph.edges().len(), 5);
        for (from, kind) in [
            ("resource:7", "wasm_resource"),
            ("resource:8", "wasm_inline_base64"),
            ("resource:9", "wasm_static_bytes"),
            ("inline:3:2", "wasm_inline_base64"),
            ("inline:3:4", "wasm_static_bytes"),
        ] {
            assert!(
                graph.edges().values().any(|edge| {
                    edge["from"] == from && edge["to"] == wasm_id && edge["kind"] == kind
                }),
                "missing {kind} edge from {from}"
            );
        }
        assert!(!graph
            .edges()
            .values()
            .any(|edge| edge["from"] == "resource:99" || edge["from"] == "inline:3:0"));
        Ok(())
    }

    #[test]
    fn static_wasm_requires_digest_but_not_guessed_owners() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let sha = "b".repeat(64);
        seed_static_wasm_modules(
            &mut graph,
            &json!({"modules":[{
                "sha256":sha,
                "origins":[
                    {"type":"inline_script_static_bytes","parent_resource_id":3},
                    {"type":"resource","url":"https://example.test/only-url.wasm"},
                    {"type":"unknown","resource_id":8}
                ]
            }]}),
            &budget(),
        )?;
        assert_eq!(graph.nodes().len(), 1);
        assert!(graph.edges().is_empty());
        assert!(seed_static_wasm_modules(
            &mut GraphBuilder::default(),
            &json!({"modules":[{"origins":[]}]}),
            &budget()
        )
        .is_err());
        Ok(())
    }
}
