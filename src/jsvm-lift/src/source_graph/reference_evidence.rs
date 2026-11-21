//! Captured import-map definitions and source-backed JavaScript reference edges.
//!
//! Keep individual document context and blocked resolution choices as
//! first-class provenance. No summary resolved URL may override the
//! authoritative contextual candidate inventory.

use super::{
    array_field, digest_id, field, nonempty_string_field, object_field, string_field, u64_field,
    GraphBuilder, InlineSourceIndex,
};
use anyhow::{Context, Result};
use serde_json::{json, Value};
use work_budget::WorkBudget;

fn reference_resolutions(reference: &Value) -> &[Value] {
    // The contextual inventory is authoritative, even when empty or malformed.
    // Summary fields are only used when no contextual inventory exists.
    match reference.get("resolution_candidates") {
        None => std::slice::from_ref(reference),
        Some(Value::Array(choices)) => choices,
        Some(_) => &[],
    }
}

fn is_blocked_resolution(value: &Value) -> bool {
    string_field(value, "resolution").is_some_and(|status| {
        status == "import_map_blocked" || status.ends_with("_import_map_blocked")
    })
}

fn add_reference_edges(
    graph: &mut GraphBuilder,
    source: &str,
    reference: &Value,
    budget: &WorkBudget,
) -> Result<()> {
    let kind = format!(
        "js_{}",
        string_field(reference, "kind").unwrap_or("reference")
    );
    let choices = reference_resolutions(reference);
    budget.consume(u64::try_from(choices.len().max(1))?)?;
    if choices.is_empty() {
        return add_unresolved_reference(graph, source, reference, &kind, None);
    }
    for choice in choices {
        let blocked = is_blocked_resolution(choice);
        if blocked || nonempty_string_field(choice, "resolved_url").is_none() {
            add_unresolved_reference(graph, source, reference, &kind, Some(choice))?;
            continue;
        }
        let url = nonempty_string_field(choice, "resolved_url")
            .context("checked nonempty candidate URL disappeared")?;
        for target in graph.targets_for(url, budget)? {
            graph.add_edge(
                source,
                &target,
                &kind,
                json!({
                    "specifier":field(reference,"specifier"),
                    "glob":field(reference,"glob"),
                    "glob_match_url":field(choice,"glob_match_url"),
                    "resolved_url":url,
                    "resolution":field(choice,"resolution"),
                    "bare_specifier":choice.get("bare_specifier").and_then(Value::as_bool),
                    "import_map_key":field(choice,"import_map_key"),
                    "scope":field(choice,"scope"),
                    "document_resource_id":field(choice,"document_resource_id"),
                    "start":field(reference,"start"),
                    "end":field(reference,"end"),
                }),
            )?;
        }
    }
    Ok(())
}

fn add_unresolved_reference(
    graph: &mut GraphBuilder,
    source: &str,
    reference: &Value,
    kind: &str,
    context: Option<&Value>,
) -> Result<()> {
    let specifier = string_field(reference, "specifier").unwrap_or("");
    let node_id = digest_id("specifier:", specifier);
    graph.intern_node(
        node_id.clone(),
        json!({
            "type":"module_specifier",
            "specifier":specifier,
            "captured":false,
        }),
    )?;
    // A missing authoritative contextual choice is not summary evidence.
    // Non-contextual references are passed as their own choice by the caller.
    let proof = context.unwrap_or(&Value::Null);
    let blocked = is_blocked_resolution(proof);
    graph.add_edge(
        source,
        &node_id,
        kind,
        json!({
            "specifier":specifier,
            "glob":field(reference,"glob"),
            "resolved_url":Value::Null,
            "resolution":if context.is_none()
                {json!("no_matching_contextual_resolution")}
                else {field(proof,"resolution")},
            "import_map_key":field(proof,"import_map_key"),
            "scope":field(proof,"scope"),
            "document_resource_id":field(proof,"document_resource_id"),
            "blocked":blocked,
            "bare_specifier":proof.get("bare_specifier").and_then(Value::as_bool),
            "start":field(reference,"start"),
            "end":field(reference,"end"),
        }),
    )
}

pub(super) fn seed_js_reference_edges(
    graph: &mut GraphBuilder,
    jsrefs: &Value,
    inline_nodes: &InlineSourceIndex,
    budget: &WorkBudget,
) -> Result<()> {
    for unit in array_field(jsrefs, "code_units") {
        budget.checkpoint()?;
        let Some(resource_id) = u64_field(unit, "resource_id") else {
            continue;
        };
        let source = if string_field(unit, "origin") == Some("inline_script") {
            let raw =
                string_field(unit, "raw_path").context("inline reference missing raw path")?;
            let ordinal = u64_field(unit, "ordinal").context("inline reference missing ordinal")?;
            inline_nodes
                .exact(raw, resource_id, ordinal)
                .with_context(|| format!("inline reference has no exact captured source {raw} ({resource_id}, {ordinal})"))?
        } else {
            format!("resource:{resource_id}")
        };
        for reference in array_field(unit, "references") {
            add_reference_edges(graph, &source, reference, budget)?;
        }
    }
    Ok(())
}

/// Attach captured definition edges for every import-map declaration.
/// Entries blocked explicitly by null remain connected to an unresolved
/// specifier rather than disappearing from the evidence graph.
pub(super) fn seed_import_map_definitions(
    graph: &mut GraphBuilder,
    import_maps: &Value,
    inline_nodes: &InlineSourceIndex,
    budget: &WorkBudget,
) -> Result<()> {
    for record in array_field(import_maps, "maps") {
        budget.checkpoint()?;
        let Some(raw_path) = string_field(record, "raw_path") else {
            continue;
        };
        let Some(src) = (|| {
            let parent = u64_field(record, "document_resource_id")?;
            let ordinal = u64_field(record, "ordinal")?;
            inline_nodes.exact(raw_path, parent, ordinal)
        })() else {
            continue;
        };

        let document_resource_id = field(record, "document_resource_id");
        if let Some(imports) = object_field(record, "imports") {
            for (specifier, resolved) in imports {
                let Some(resolved) = resolved.as_str() else {
                    if resolved.is_null() {
                        add_blocked_import_map_entry(
                            graph,
                            &src,
                            specifier,
                            document_resource_id.clone(),
                            Value::Null,
                        )?;
                    }
                    continue;
                };
                for dst in graph.targets_for(resolved, budget)? {
                    graph.add_edge(
                        &src,
                        &dst,
                        "import_map_entry",
                        json!({
                            "specifier":specifier,
                            "resolved_url":resolved,
                            "document_resource_id":document_resource_id.clone(),
                            "scope":Value::Null,
                        }),
                    )?;
                }
            }
        }
        if let Some(scopes) = object_field(record, "scopes") {
            for (scope, entries) in scopes {
                let Some(entries) = entries.as_object() else {
                    continue;
                };
                for (specifier, resolved) in entries {
                    let Some(resolved) = resolved.as_str() else {
                        if resolved.is_null() {
                            add_blocked_import_map_entry(
                                graph,
                                &src,
                                specifier,
                                document_resource_id.clone(),
                                json!(scope),
                            )?;
                        }
                        continue;
                    };
                    for dst in graph.targets_for(resolved, budget)? {
                        graph.add_edge(
                            &src,
                            &dst,
                            "import_map_entry",
                            json!({
                                "specifier":specifier,
                                "resolved_url":resolved,
                                "document_resource_id":document_resource_id.clone(),
                                "scope":scope,
                            }),
                        )?;
                    }
                }
            }
        }
    }

    Ok(())
}

fn add_blocked_import_map_entry(
    graph: &mut GraphBuilder,
    source: &str,
    specifier: &str,
    document_resource_id: Value,
    scope: Value,
) -> Result<()> {
    let target = digest_id("specifier:", specifier);
    graph.intern_node(
        target.clone(),
        json!({
            "type":"module_specifier",
            "specifier":specifier,
            "captured":false,
        }),
    )?;
    graph.add_edge(
        source,
        &target,
        "import_map_entry_blocked",
        json!({
            "specifier":specifier,
            "resolved_url":Value::Null,
            "document_resource_id":document_resource_id,
            "scope":scope,
            "blocked":true,
        }),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn budget() -> WorkBudget {
        WorkBudget::new(
            "reference-evidence-test",
            work_budget::BudgetLimits::unlimited(),
        )
    }

    #[test]
    fn import_map_definitions_keep_exact_inline_owner_and_null_blockers() -> Result<()> {
        let mut graph = GraphBuilder::default();
        graph.register_resource_url("https://example.test/dep.js", "resource:8");
        graph.register_resource_url("https://example.test/dep.js", "resource:9");
        let mut inline = InlineSourceIndex::default();
        inline.insert("resources/shared-map.json", 3, 1, "inline:3:1".into())?;
        inline.insert("resources/shared-map.json", 4, 1, "inline:4:1".into())?;

        let maps = json!({"maps":[
            {
                "raw_path":"resources/shared-map.json",
                "document_resource_id":3, "ordinal":1,
                "imports":{
                    "blocked":null,
                    "mapped":"https://example.test/dep.js",
                    "malformed":17
                },
                "scopes":{
                    "https://example.test/sub/":{
                        "blocked":null,
                        "extra":"https://example.test/dep.js"
                    }
                }
            },
            {
                "raw_path":"resources/shared-map.json",
                "document_resource_id":4, "ordinal":1,
                "imports":{"blocked":null}
            },
            {
                "raw_path":"resources/shared-map.json",
                "document_resource_id":99, "ordinal":1,
                "imports":{"ghost":null}
            }
        ]});
        seed_import_map_definitions(&mut graph, &maps, &inline, &budget())?;
        let blocked = graph
            .edges()
            .values()
            .filter(|edge| edge["kind"] == "import_map_entry_blocked")
            .collect::<Vec<_>>();
        assert_eq!(blocked.len(), 3);
        assert!(blocked.iter().any(|edge| {
            edge["from"] == "inline:3:1"
                && edge["document_resource_id"] == 3
                && edge["scope"].is_null()
                && edge["blocked"] == true
        }));
        assert!(blocked.iter().any(|edge| {
            edge["from"] == "inline:3:1"
                && edge["document_resource_id"] == 3
                && edge["scope"] == "https://example.test/sub/"
        }));
        assert!(blocked.iter().any(|edge| {
            edge["from"] == "inline:4:1"
                && edge["document_resource_id"] == 4
                && edge["scope"].is_null()
        }));
        let target = digest_id("specifier:", "blocked");
        assert!(blocked.iter().all(|edge| edge["to"] == target));
        assert_eq!(graph.node_value(&target)["type"], "module_specifier");
        let mapped = graph
            .edges()
            .values()
            .filter(|edge| edge["kind"] == "import_map_entry")
            .collect::<Vec<_>>();
        assert_eq!(mapped.len(), 4);
        assert!(mapped.iter().all(|edge| edge["from"] == "inline:3:1"));
        assert!(mapped.iter().any(|edge| edge["to"] == "resource:8"));
        assert!(mapped.iter().any(|edge| edge["to"] == "resource:9"));
        assert!(!graph.has_node(&digest_id("specifier:", "ghost")));
        assert!(!graph.has_node(&digest_id("specifier:", "malformed")));
        Ok(())
    }

    #[test]
    fn inline_reference_contexts_are_not_collapsed_by_shared_raw_path() -> Result<()> {
        let mut inline = InlineSourceIndex::default();
        inline.insert("resources/inline.js", 3, 1, "inline:3:1".into())?;
        inline.insert("resources/inline.js", 4, 1, "inline:4:1".into())?;
        let mut graph = GraphBuilder::default();
        graph.register_resource_url("https://example.test/a.js", "resource:12");
        let refs = json!({"code_units":[
            {
                "resource_id":3, "origin":"inline_script",
                "raw_path":"resources/inline.js", "ordinal":1,
                "references":[{
                    "kind":"import_static", "specifier":"pkg",
                    "resolved_url":"https://example.test/WRONG.js",
                    "resolution_candidates":[{
                        "document_resource_id":3,
                        "resolved_url":"https://example.test/a.js",
                        "resolution":"import_map"
                    }]
                }]
            },
            {
                "resource_id":4, "origin":"inline_script",
                "raw_path":"resources/inline.js", "ordinal":1,
                "references":[{
                    "kind":"import_static", "specifier":"pkg",
                    "resolution_candidates":[{
                        "document_resource_id":4,
                        "resolved_url":null,
                        "resolution":"import_map_blocked"
                    }]
                }]
            }
        ]});
        seed_js_reference_edges(&mut graph, &refs, &inline, &budget())?;
        assert_eq!(graph.edges().len(), 2);
        assert!(graph.edges().values().any(|edge| {
            edge["from"] == "inline:3:1"
                && edge["to"] == "resource:12"
                && edge["document_resource_id"] == 3
                && edge["resolution"] == "import_map"
        }));
        let unresolved = graph
            .edges()
            .values()
            .find(|edge| edge["from"] == "inline:4:1" && edge["document_resource_id"] == 4)
            .context("missing blocked inline reference")?;
        assert!(unresolved["to"]
            .as_str()
            .is_some_and(|to| to.starts_with("specifier:")));
        assert_eq!(unresolved["blocked"], true);
        assert_eq!(unresolved["resolution"], "import_map_blocked");
        assert!(!graph
            .edges()
            .values()
            .any(|edge| edge["resolved_url"] == "https://example.test/WRONG.js"));
        Ok(())
    }

    #[test]
    fn import_map_blocker_and_js_unresolved_share_exact_specifier_identity() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let mut inline = InlineSourceIndex::default();
        inline.insert("resources/map.json", 3, 1, "inline:3:1".into())?;
        seed_import_map_definitions(
            &mut graph,
            &json!({"maps":[{
                "raw_path":"resources/map.json", "document_resource_id":3, "ordinal":1,
                "imports":{"pkg":null}
            }]}),
            &inline,
            &budget(),
        )?;
        seed_js_reference_edges(
            &mut graph,
            &json!({"code_units":[{
                "resource_id":3,
                "references":[{
                    "kind":"import_static", "specifier":"pkg",
                    "bare_specifier":true, "resolution":"import_map_blocked",
                    "resolved_url":null
                }]
            }]}),
            &inline,
            &budget(),
        )?;
        let target = digest_id("specifier:", "pkg");
        assert_eq!(graph.node_value(&target)["type"], "module_specifier");
        assert!(graph.node_value(&target).get("bare").is_none());
        assert!(graph
            .edges()
            .values()
            .any(|edge| edge["kind"] == "js_import_static" && edge["bare_specifier"] == true));
        assert_eq!(graph.edges().len(), 2);
        assert!(graph.edges().values().all(|edge| edge["to"] == target));
        Ok(())
    }
    #[test]
    fn specifier_bare_classification_is_contextual_edge_evidence() -> Result<()> {
        let mut graph = GraphBuilder::default();
        let refs = json!({"code_units":[{"resource_id":5,"references":[{
            "kind":"import_static","specifier":"./pkg.js","bare_specifier":true,
            "resolution_candidates":[
                {"document_resource_id":1,"bare_specifier":true,"resolved_url":null},
                {"document_resource_id":2,"bare_specifier":false,"resolution":"import_map_blocked","resolved_url":null}
            ]
        }, {"kind":"import_static","specifier":"./pkg.js","bare_specifier":true,"resolution":"import_map_blocked","document_resource_id":99,"import_map_key":"stale","scope":"stale","resolution_candidates":[]}]}]});
        seed_js_reference_edges(&mut graph, &refs, &InlineSourceIndex::default(), &budget())?;
        let target = digest_id("specifier:", "./pkg.js");
        assert_eq!(graph.node_count(), 1);
        assert!(graph.node_value(&target).get("bare").is_none());
        assert_eq!(graph.edges().len(), 3);
        for (document, bare) in [
            (json!(1), json!(true)),
            (json!(2), json!(false)),
            (Value::Null, Value::Null),
        ] {
            assert!(graph.edges().values().any(|edge| edge["to"] == target
                && edge["document_resource_id"] == document
                && edge["bare_specifier"] == bare));
        }
        let unmatched = graph
            .edges()
            .values()
            .find(|edge| edge["resolution"] == "no_matching_contextual_resolution")
            .context("missing unmatched contextual edge")?;
        assert_eq!(unmatched["blocked"], false);
        assert!(unmatched["import_map_key"].is_null());
        assert!(unmatched["scope"].is_null());
        Ok(())
    }
}
