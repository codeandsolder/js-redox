//! Runtime script evidence and session-scoped identity resolution.
//!
//! Resource matches, framework families, generated origins and observed script
//! instances describe different evidence; only unambiguous full digests can
//! identify the source of a later debugger witness.

use super::{
    array_field, bool_field, compact_key, digest_id, field, nonempty_string_field, string_field,
    GraphBuilder,
};
use crate::runtime_identity::script_id_text;
use anyhow::{Context, Result};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};

/// CDP script IDs are scoped to their session. Store full source digests,
/// not the abbreviated graph node IDs, and make conflicts permanent.
#[derive(Default)]
pub(super) struct RuntimeInstances {
    sessions: BTreeMap<String, BTreeMap<String, InstanceSource>>,
}

enum InstanceSource {
    Unique(String),
    Conflict,
}

pub(super) fn runtime_node_id(digest: &str) -> String {
    format!("runtime:{}", digest.get(..20).unwrap_or(digest))
}

/// A display ID is only a lookup hint; the complete captured digest must agree.
pub(super) fn captured_runtime_source(graph: &GraphBuilder, digest: &str) -> Option<String> {
    let node = runtime_node_id(digest);
    let record = graph.node(&node)?;
    (string_field(record, "type") == Some("runtime_script")
        && string_field(record, "sha256") == Some(digest))
    .then_some(node)
}

impl RuntimeInstances {
    pub(super) fn register(&mut self, session: &str, script_id: &str, digest: &str) {
        use std::collections::btree_map::Entry;
        match self
            .sessions
            .entry(session.to_owned())
            .or_default()
            .entry(script_id.to_owned())
        {
            Entry::Vacant(entry) => {
                entry.insert(InstanceSource::Unique(digest.to_owned()));
            }
            Entry::Occupied(mut entry) => {
                if matches!(entry.get(), InstanceSource::Unique(previous) if previous != digest) {
                    entry.insert(InstanceSource::Conflict);
                }
            }
        }
    }

    fn register_source(&mut self, source: &Value, digest: &str) {
        for instance in array_field(source, "script_instances") {
            let Some(script_id) = instance.get("script_id").and_then(script_id_text) else {
                continue;
            };
            let session = nonempty_string_field(instance, "cdp_session").unwrap_or("main");
            self.register(session, &script_id, digest);
        }
    }

    fn lookup(&self, session: &str, script_id: &str) -> Option<&InstanceSource> {
        self.sessions.get(session)?.get(script_id)
    }

    fn digest(&self, session: &str, script_id: &str) -> Option<&str> {
        match self.lookup(session, script_id)? {
            InstanceSource::Unique(digest) => Some(digest),
            InstanceSource::Conflict => None,
        }
    }

    pub(super) fn exact_node(
        &self,
        session: &str,
        script_id: &str,
        digest: &str,
    ) -> Option<String> {
        (self.digest(session, script_id)? == digest).then(|| runtime_node_id(digest))
    }

    pub(super) fn observed_node(
        &self,
        session: &str,
        script_id: &Value,
        expected_digest: Option<&str>,
    ) -> Option<String> {
        let id = script_id_text(script_id)?;
        let digest = self.digest(session, &id)?;
        if expected_digest.is_some_and(|expected| expected != digest) {
            return None;
        }
        Some(runtime_node_id(digest))
    }
}

/// Relate a runtime script to captured HTTP responses without upgrading URL
/// coincidence or parser observation into proof of response execution.
pub(super) fn add_runtime_network_source_edges(
    graph: &mut GraphBuilder,
    runtime: &Value,
    runtime_node: &str,
    resource_nodes_by_sha: &BTreeMap<String, Vec<String>>,
) -> Result<()> {
    let Some(digest) = nonempty_string_field(runtime, "sha256") else {
        return Ok(());
    };
    let urls = array_field(runtime, "urls")
        .iter()
        .filter_map(Value::as_str)
        .collect::<BTreeSet<_>>();
    let hash_matches = resource_nodes_by_sha
        .get(digest)
        .map_or_default(Vec::as_slice);
    let exact = hash_matches
        .iter()
        .filter(|node| {
            graph.node(node).is_some_and(|resource| {
                nonempty_string_field(resource, "kind") == Some("javascript")
                    && nonempty_string_field(resource, "url").is_some_and(|url| urls.contains(url))
            })
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    let (parents, basis) = if !exact.is_empty() {
        (exact, "sha256_and_url")
    } else if urls.is_empty() && !hash_matches.is_empty() {
        (
            hash_matches
                .iter()
                .filter(|node| {
                    graph.node(node).is_some_and(|resource| {
                        nonempty_string_field(resource, "kind") == Some("javascript")
                    })
                })
                .cloned()
                .collect::<BTreeSet<_>>(),
            "sha256_only",
        )
    } else {
        // A runtime URL cannot identify which captured HTTP response supplied
        // script bytes. Preserve all URL candidates without asserting execution.
        (
            urls.iter()
                .flat_map(|url| graph.captured_targets(url).into_iter().flatten())
                .filter(|node| {
                    graph.node(node).is_some_and(|resource| {
                        nonempty_string_field(resource, "kind") == Some("javascript")
                    })
                })
                .cloned()
                .collect::<BTreeSet<_>>(),
            "url_only",
        )
    };
    let uniquely_verified = basis == "sha256_and_url" && parents.len() == 1;
    for parent in &parents {
        let parent_url = graph
            .node(parent)
            .and_then(|resource| nonempty_string_field(resource, "url"));
        let execution_observed = parent_url.is_some_and(|url| {
            array_field(runtime, "script_instances")
                .iter()
                .any(|instance| {
                    nonempty_string_field(instance, "script_url") == Some(url)
                        && nonempty_string_field(&instance["execution"], "status")
                            == Some("positive")
                })
        });
        let kind = if uniquely_verified && execution_observed {
            "runtime_execution"
        } else if uniquely_verified {
            "runtime_source_match"
        } else {
            "runtime_source_candidate"
        };
        graph.add_edge(
            parent,
            runtime_node,
            kind,
            json!({
                "identity_basis":basis,
                "candidate_count":parents.len(),
                "exact_response_identity":uniquely_verified,
                "runtime_execution_observed":execution_observed,
                "coverage_mode":field(runtime,"coverage_mode"),
            }),
        )?;
    }
    Ok(())
}

/// Contextual evidence for runtime-source classification. Identity candidates
/// remain distinct: neither a matching URL nor matching bytes prove execution.
struct RuntimeClassificationContext<'a> {
    resource_nodes_by_sha: &'a BTreeMap<String, Vec<String>>,
    inline_nodes_by_sha: &'a BTreeMap<String, Vec<String>>,
    family_counts: &'a BTreeMap<String, Value>,
    gtm_family_counts: &'a BTreeMap<String, Value>,
}

fn runtime_family_counts(runtime: &Value, field_name: &str) -> BTreeMap<String, Value> {
    array_field(runtime, field_name)
        .iter()
        .filter_map(|row| {
            Some((
                nonempty_string_field(row, "shape")?.to_string(),
                row.get("source_count").cloned().unwrap_or_else(|| json!(0)),
            ))
        })
        .collect()
}

/// A generation claim refers to a recorded parent frame, not a new execution
/// observation. Resolve source content and session-local instance independently.
struct GenerationParent<'a> {
    frame: &'a Value,
    session: &'a str,
}

impl GenerationParent<'_> {
    fn claimed_digest(&self) -> Option<&str> {
        nonempty_string_field(self.frame, "sha256")
    }

    fn resolve(
        &self,
        graph: &GraphBuilder,
        instances: &RuntimeInstances,
    ) -> GenerationParentResolution {
        let event_status = string_field(self.frame, "parent_event_status");
        if event_status == Some("conflicting_source_claims") {
            return GenerationParentResolution::Unresolved("conflicting_parent_event_claims");
        }
        let registered = self
            .frame
            .get("script_id")
            .and_then(script_id_text)
            .and_then(|id| instances.lookup(self.session, &id));
        let claimed = self.claimed_digest();
        let (digest, basis) = match (registered, claimed) {
            (Some(InstanceSource::Conflict), _) => {
                return GenerationParentResolution::Unresolved("conflicting_script_instance")
            }
            (Some(InstanceSource::Unique(registered)), Some(claimed)) if registered != claimed => {
                return GenerationParentResolution::Unresolved("conflicting_parent_digest")
            }
            (Some(InstanceSource::Unique(registered)), _) => (
                registered.as_str(),
                if event_status == Some("ambiguous_ancestry") {
                    "captured_digest_with_ambiguous_ancestry"
                } else {
                    "session_script_id_and_captured_digest"
                },
            ),
            (None, Some(claimed)) => (claimed, "captured_digest_only"),
            (None, None) => {
                return if nonempty_string_field(self.frame, "url").is_some() {
                    GenerationParentResolution::UrlOnly
                } else {
                    GenerationParentResolution::Unresolved("parent_source_unavailable")
                }
            }
        };
        captured_runtime_source(graph, digest).map_or(
            GenerationParentResolution::Unresolved("parent_source_unavailable"),
            |node| GenerationParentResolution::Captured { node, basis },
        )
    }
}

enum GenerationParentResolution {
    Captured { node: String, basis: &'static str },
    UrlOnly,
    Unresolved(&'static str),
}

fn add_runtime_generated_code_edges(
    graph: &mut GraphBuilder,
    generated: &Value,
    runtime_node: &str,
    instances: &RuntimeInstances,
    budget: &work_budget::WorkBudget,
) -> Result<()> {
    for (ordinal, origin) in array_field(generated, "origins").iter().enumerate() {
        budget.consume(1)?;
        let chain = array_field(origin, "chain");
        let Some(frame) = chain.first() else {
            continue;
        };
        let child_session = nonempty_string_field(origin, "cdp_session").unwrap_or("main");
        let parent = GenerationParent {
            frame,
            session: nonempty_string_field(frame, "cdp_session").unwrap_or(child_session),
        };
        let mut fields = json!({
            "origin_ordinal":ordinal,
            "chain_termination":field(origin,"chain_termination"),
            "parent_event_status":field(frame,"parent_event_status"),
            "parent_event_count":field(frame,"parent_event_count"),
            "parent_event_digest_claims":field(frame,"parent_event_digest_claims"),
            "cdp_session":child_session,
            "parent_cdp_session":parent.session,
            "child_script_id":field(origin,"child_script_id"),
            "parent_script_id":field(frame,"script_id"),
            "claimed_parent_sha256":parent.claimed_digest(),
            "parent_url":field(frame,"url"),
            "function_name":field(frame,"function_name"),
            "line_number":field(frame,"line_number"),
            "column_number":field(frame,"column_number"),
            "generation_depth":chain.len(),
        });
        match parent.resolve(graph, instances) {
            GenerationParentResolution::Captured { node, basis } => {
                fields["identity_basis"] = json!(basis);
                fields["exact_parent_source_identity"] = json!(true);
                fields["exact_parent_runtime_instance"] =
                    json!(basis == "session_script_id_and_captured_digest");
                graph.add_edge(&node, runtime_node, "runtime_generated_code", fields)?;
            }
            GenerationParentResolution::UrlOnly => {
                let url =
                    nonempty_string_field(frame, "url").context("URL-only parent requires URL")?;
                let candidates = graph.targets_for(url, budget)?;
                fields["identity_basis"] = json!("url_only");
                fields["candidate_count"] = json!(candidates.len());
                fields["exact_parent_source_identity"] = json!(false);
                fields["exact_parent_runtime_instance"] = json!(false);
                for node in &candidates {
                    graph.add_edge(
                        node,
                        runtime_node,
                        "runtime_generated_code_candidate",
                        fields.clone(),
                    )?;
                }
            }
            GenerationParentResolution::Unresolved(reason) => {
                let reference = format!("runtime-parent-reference:{runtime_node}:{ordinal}");
                graph.insert_node(
                    reference.clone(),
                    json!({
                        "type":"runtime_parent_reference",
                        "captured":false,
                        "child_runtime_node":runtime_node,
                        "parent_claim":frame,
                        "parent_cdp_session":parent.session,
                        "resolution":reason,
                    }),
                )?;
                fields["identity_basis"] = json!(reason);
                fields["exact_parent_source_identity"] = json!(false);
                fields["exact_parent_runtime_instance"] = json!(false);
                graph.add_edge(
                    &reference,
                    runtime_node,
                    "runtime_generated_code_unresolved",
                    fields,
                )?;
            }
        }
    }
    Ok(())
}

fn add_runtime_document_inline_edges(
    graph: &mut GraphBuilder,
    source: &Value,
    runtime_node: &str,
) -> Result<()> {
    for origin in array_field(source, "document_inline_origins") {
        let document_key = compact_key((
            field(origin, "cdp_session"),
            field(origin, "url"),
            field(origin, "frame_id"),
        ))?;
        let document_node = digest_id("runtime-document:", &document_key);
        graph.intern_node(
            document_node.clone(),
            json!({
                "type":"runtime_document",
                "cdp_session":field(origin,"cdp_session"),
                "url":field(origin,"url"),
                "frame_id":field(origin,"frame_id"),
            }),
        )?;
        graph.add_edge(
            &document_node,
            runtime_node,
            "runtime_document_inline",
            json!({
                "script_id":field(origin,"script_id"),
                "start_line":field(origin,"start_line"),
                "start_column":field(origin,"start_column"),
                "end_line":field(origin,"end_line"),
                "end_column":field(origin,"end_column"),
            }),
        )?;
    }
    Ok(())
}

fn add_runtime_alpine_edges(
    graph: &mut GraphBuilder,
    alpine: &Value,
    runtime_node: &str,
    family_counts: &BTreeMap<String, Value>,
) -> Result<()> {
    if let Some(shape) = nonempty_string_field(alpine, "shape") {
        let family_node = digest_id("runtime-family:", shape);
        graph.intern_node(
            family_node.clone(),
            json!({
                "type":"runtime_expression_family",
                "framework":"alpine",
                "shape":shape,
                "source_count":family_counts.get(shape).cloned().unwrap_or(Value::Null),
            }),
        )?;
        graph.add_edge(
            runtime_node,
            &family_node,
            "runtime_expression_family",
            json!({}),
        )?;
    }
    for dom_match in array_field(alpine, "dom_matches") {
        let snapshot_key = compact_key((field(dom_match, "source"), field(dom_match, "path")))?;
        let snapshot_node = digest_id("dom-snapshot:", &snapshot_key);
        graph.intern_node(
                        snapshot_node.clone(),
                        json!({"type":"dom_snapshot", "source":field(dom_match,"source"), "path":field(dom_match,"path")}),
                    )?;
        let directive_key = compact_key((
            field(dom_match, "source"),
            field(dom_match, "path"),
            field(dom_match, "tag_ordinal"),
            field(dom_match, "tag"),
            field(dom_match, "attribute"),
        ))?;
        let directive_node = digest_id("dom-directive:", &directive_key);
        graph.intern_node(
                        directive_node.clone(),
                        json!({
                            "type":"dom_directive", "source":field(dom_match,"source"), "path":field(dom_match,"path"),
                            "tag_ordinal":field(dom_match,"tag_ordinal"), "tag":field(dom_match,"tag"), "attribute":field(dom_match,"attribute")
                        }),
                    )?;
        graph.add_edge(&snapshot_node, &directive_node, "dom_directive", json!({}))?;
        graph.add_edge(
            &directive_node,
            runtime_node,
            "runtime_alpine_compile",
            json!({
                "mapping_kind":field(alpine,"dom_mapping_kind"),
                "expression":field(alpine,"expression"),
                "compiled_expression":field(alpine,"compiled_expression"),
                "shape":field(alpine,"shape"),
            }),
        )?;
    }
    Ok(())
}

fn add_runtime_classification_edges(
    graph: &mut GraphBuilder,
    source: &Value,
    digest: &str,
    runtime_node: &str,
    context: &RuntimeClassificationContext<'_>,
) -> Result<()> {
    let classification = string_field(source, "classification");
    let alpine = source.get("alpine").unwrap_or(&Value::Null);
    let gtm = source.get("gtm").unwrap_or(&Value::Null);
    match classification {
        Some("network_response" | "network_observed") => {
            add_runtime_network_source_edges(
                graph,
                source,
                runtime_node,
                context.resource_nodes_by_sha,
            )?;
        }
        Some("inline_script") => {
            if let Some(parents) = context.inline_nodes_by_sha.get(digest) {
                // Matching inline bytes do not identify the document or
                // script ordinal whose browser instance was parsed.
                for parent in parents {
                    graph.add_edge(
                        parent,
                        runtime_node,
                        "runtime_source_candidate",
                        json!({
                            "identity_basis":"sha256_only_inline_script",
                            "candidate_count":parents.len(),
                            "exact_response_identity":false,
                            "runtime_execution_observed":bool_field(source,"observed_executed"),
                            "coverage_mode":field(source,"coverage_mode"),
                        }),
                    )?;
                }
            }
        }
        Some("document_inline_script") => {
            add_runtime_document_inline_edges(graph, source, runtime_node)?;
        }
        Some("alpine_expression") => {
            add_runtime_alpine_edges(graph, alpine, runtime_node, context.family_counts)?;
        }
        Some("gtm_custom_javascript") => {
            if let Some(shape) = nonempty_string_field(gtm, "shape") {
                let family_node =
                    digest_id("runtime-family:", &format!("google_tag_manager\0{shape}"));
                graph.intern_node(
                        family_node.clone(),
                        json!({
                            "type":"runtime_expression_family", "framework":"google_tag_manager", "shape":shape,
                            "source_count":context.gtm_family_counts.get(shape).cloned().unwrap_or(Value::Null)
                        }),
                    )?;
                graph.add_edge(
                    runtime_node,
                    &family_node,
                    "runtime_expression_family",
                    json!({}),
                )?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Register runtime script observations without treating URL/SHA coincidence as execution proof.
/// Conflicting (CDP session, script ID) assertions cannot identify any runtime source.
pub(super) fn seed_runtime_script_evidence(
    graph: &mut GraphBuilder,
    runtime: &Value,
    source_index: &Value,
    deobfuscation: &Value,
    resource_nodes_by_sha: &BTreeMap<String, Vec<String>>,
    inline_nodes_by_sha: &BTreeMap<String, Vec<String>>,
    budget: &work_budget::WorkBudget,
) -> Result<RuntimeInstances> {
    // Debugger-observed runtime scripts are provenance, not independent resources.
    let family_counts = runtime_family_counts(runtime, "alpine_families");
    let gtm_family_counts = runtime_family_counts(runtime, "gtm_families");
    let runtime_general_paths = array_field(source_index, "units")
        .iter()
        .filter(|unit| string_field(unit, "origin") == Some("runtime_script"))
        .filter_map(|unit| {
            Some((
                nonempty_string_field(unit, "input_sha256")?.to_owned(),
                nonempty_string_field(unit, "source_path")?.to_owned(),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let runtime_readable_paths = array_field(deobfuscation, "units")
        .iter()
        .filter_map(|unit| {
            let digest = nonempty_string_field(unit, "raw_path")?
                .strip_prefix("resources/runtime-scripts/")?
                .strip_suffix(".js")?;
            let readable = nonempty_string_field(unit, "readable_output_path")?;
            (readable == format!("src/_readable/runtime-scripts/{digest}.js"))
                .then(|| (digest.to_owned(), readable.to_owned()))
        })
        .collect::<BTreeMap<_, _>>();

    let mut instances = RuntimeInstances::default();
    let context = RuntimeClassificationContext {
        resource_nodes_by_sha,
        inline_nodes_by_sha,
        family_counts: &family_counts,
        gtm_family_counts: &gtm_family_counts,
    };

    for source in array_field(runtime, "sources") {
        budget.checkpoint()?;
        let Some(digest) = nonempty_string_field(source, "sha256") else {
            continue;
        };
        let runtime_node = runtime_node_id(digest);
        // Abbreviated graph IDs are presentation identifiers, never a proof
        // that two different full digests denote the same source.
        if let Some(existing) = graph.node(&runtime_node) {
            anyhow::ensure!(
                string_field(existing, "sha256") == Some(digest),
                "runtime graph node ID collision for {runtime_node}"
            );
        }
        let classification = string_field(source, "classification");
        let generated = source.get("generated").unwrap_or(&Value::Null);
        graph.insert_node(
            runtime_node.clone(),
            json!({
                "type":"runtime_script",
                "classification":field(source,"classification"),
                "sha256":digest,
                "bytes":field(source,"size"),
                "capture_path":field(source,"path"),
                "event_count":field(source,"event_count"),
                "script_ids":source.get("script_ids").cloned().unwrap_or_else(|| json!([])),
                "cdp_sessions":source.get("cdp_sessions").cloned().unwrap_or_else(|| json!([])),
                "execution_context_ids":source.get("execution_context_ids").cloned().unwrap_or_else(|| json!([])),
                "script_instances":source.get("script_instances").cloned().unwrap_or_else(|| json!([])),
                "observed_executed":field(source,"observed_executed"),
                "coverage_mode":field(source,"coverage_mode"),
                "observed_source_path":field(source,"observed_source_path"),
                "general_source_path":runtime_general_paths.get(digest),
                "safe_readable_source_path":runtime_readable_paths.get(digest),
                "urls":source.get("urls").cloned().unwrap_or_else(|| json!([])),
                "instrumentation_kind":field(source,"instrumentation_kind"),
                "generated_root_sha256s":generated.get("root_sha256s").cloned().unwrap_or_else(|| json!([])),
                "generated_root_urls":generated.get("root_urls").cloned().unwrap_or_else(|| json!([])),
                "generation_max_depth":field(generated,"max_depth"),
                "application_source":classification != Some("capture_instrumentation"),
            }),
        )?;

        instances.register_source(source, digest);
    }
    // Resolve only against the complete source and instance inventory. A parent
    // may occur later in artifact order; a late conflict must invalidate proof.
    for source in array_field(runtime, "sources") {
        budget.checkpoint()?;
        let Some(digest) = nonempty_string_field(source, "sha256") else {
            continue;
        };
        let runtime_node = runtime_node_id(digest);
        let generated = source.get("generated").unwrap_or(&Value::Null);
        add_runtime_generated_code_edges(graph, generated, &runtime_node, &instances, budget)?;
        add_runtime_classification_edges(graph, source, digest, &runtime_node, &context)?;
    }
    Ok(instances)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_instance_identity_uses_full_digest_and_session() {
        let first = format!("{}{}", "a".repeat(20), "b".repeat(44));
        let second = format!("{}{}", "a".repeat(20), "c".repeat(44));
        let mut index = RuntimeInstances::default();
        index.register("main", "7", &first);
        index.register("worker", "7", &second);
        index.register("main", "7", &first);
        assert_eq!(
            index.exact_node("main", "7", &first),
            Some(runtime_node_id(&first))
        );
        assert_eq!(
            index.exact_node("worker", "7", &second),
            Some(runtime_node_id(&second))
        );
        assert!(index.exact_node("main", "7", &second).is_none());
        assert!(index.exact_node("worker", "7", &first).is_none());
        index.register("main", "7", &second);
        index.register("main", "7", &first);
        assert!(index.observed_node("main", &json!(7), None).is_none());
        assert_eq!(
            index.observed_node("worker", &json!(7), None),
            Some(runtime_node_id(&second))
        );
        assert!(index.observed_node("worker", &Value::Null, None).is_none());
        for invalid in [
            json!(""),
            json!(true),
            json!({"id":7}),
            json!(-7),
            json!(7.5),
        ] {
            assert!(script_id_text(&invalid).is_none());
        }
    }

    #[test]
    fn runtime_graph_rejects_distinct_digests_with_same_node_prefix() {
        let runtime = json!({"sources":[
            {"sha256":format!("{}b", "a".repeat(20))},
            {"sha256":format!("{}c", "a".repeat(20))},
        ]});
        let budget = work_budget::WorkBudget::new(
            "runtime-digest-collision",
            work_budget::BudgetLimits::unlimited(),
        );
        let result = seed_runtime_script_evidence(
            &mut GraphBuilder::default(),
            &runtime,
            &json!({}),
            &json!({}),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &budget,
        );
        assert!(result.err().is_some_and(|error| error
            .to_string()
            .contains("runtime graph node ID collision")));
    }
    #[test]
    fn generation_resolution_uses_complete_runtime_inventory_and_full_digest() -> Result<()> {
        let parent = format!("{}{}", "a".repeat(20), "b".repeat(44));
        let absent = format!("{}{}", "a".repeat(20), "c".repeat(44));
        let child = "d".repeat(64);
        let other = "e".repeat(64);
        let origin = |session: &str, script: &str, sha: Value| json!({"cdp_session":session,"child_script_id":"9","chain":[{"cdp_session":session,"script_id":script,"sha256":sha,"url":"https://fixture.test/parent.js"}]});
        let artifact = json!({"sources":[
            {"sha256":child,"generated":{"origins":[origin("main","1",json!(parent)),origin("other","1",json!(absent)),origin("main","1",json!(other)),origin("main","2",json!(parent)),origin("main","1",Value::Null),origin("unknown","1",Value::Null),origin("unknown","1",json!(parent))]}},
            {"sha256":parent,"script_instances":[{"cdp_session":"main","script_id":"1"},{"cdp_session":"main","script_id":"2"}]},
            {"sha256":other,"script_instances":[{"cdp_session":"main","script_id":"2"}]}
        ]});
        let mut graph = GraphBuilder::default();
        let budget = work_budget::WorkBudget::unlimited("generated-parent-inventory");
        seed_runtime_script_evidence(
            &mut graph,
            &artifact,
            &json!({}),
            &json!({}),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &budget,
        )?;
        let parent_node = runtime_node_id(&parent);
        let child_node = runtime_node_id(&child);
        let edges = graph
            .edges()
            .values()
            .filter(|edge| edge["to"] == child_node)
            .collect::<Vec<_>>();
        assert_eq!(edges.len(), 7);
        let proven = edges
            .iter()
            .filter(|edge| edge["kind"] == "runtime_generated_code")
            .collect::<Vec<_>>();
        assert_eq!(proven.len(), 3);
        assert!(proven.iter().all(
            |edge| edge["from"] == parent_node && edge["exact_parent_source_identity"] == true
        ));
        assert_eq!(
            proven
                .iter()
                .filter(|edge| edge["exact_parent_runtime_instance"] == true)
                .count(),
            2
        );
        for (ordinal, reason) in [
            (1, "parent_source_unavailable"),
            (2, "conflicting_parent_digest"),
            (3, "conflicting_script_instance"),
        ] {
            let id = format!("runtime-parent-reference:{child_node}:{ordinal}");
            assert_eq!(graph.node_value(&id)["resolution"], reason);
            assert!(edges.iter().any(|edge| edge["from"] == id
                && edge["kind"] == "runtime_generated_code_unresolved"
                && edge["exact_parent_source_identity"] == false));
        }
        assert!(edges
            .iter()
            .any(|edge| edge["kind"] == "runtime_generated_code_candidate"
                && edge["identity_basis"] == "url_only"));
        assert!(edges
            .iter()
            .all(|edge| edge["from"].as_str().is_some_and(|id| graph.has_node(id))));
        assert!(captured_runtime_source(&graph, &absent).is_none());
        Ok(())
    }
}
