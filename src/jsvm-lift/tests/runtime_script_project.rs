use anyhow::{Context, Result};
use jsvm_lift::{
    analysis_budget::AnalysisBudgets,
    capture_import::{import_capture_project, CaptureImportOptions},
    sha256_hex,
    source_graph::build_source_graph,
};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

fn digest(source: &str) -> String {
    sha256_hex(source.as_bytes())
}

fn alpine(expression: &str) -> String {
    format!(
        "(async function anonymous(__self,scope\n) {{\nwith (scope) {{ __self.result = {expression} }}; __self.finished = true; return __self.result;\n}})"
    )
}

fn har_entry(url: &str, mime: &str, text: &str) -> Value {
    let size = text.len();
    json!({
        "startedDateTime": "2026-10-08T00:00:00.000Z",
        "time": 0,
        "request": {
            "method": "GET",
            "url": url,
            "httpVersion": "HTTP/2",
            "headers": [],
            "queryString": [],
            "cookies": [],
            "headersSize": -1,
            "bodySize": 0,
        },
        "response": {
            "status": 200,
            "statusText": "OK",
            "httpVersion": "HTTP/2",
            "headers": [],
            "cookies": [],
            "content": {"size": size, "mimeType": mime, "text": text},
            "redirectURL": "",
            "headersSize": -1,
            "bodySize": size,
        },
        "cache": {},
        "timings": {"send": 0, "wait": 0, "receive": 0},
    })
}

fn read_json(path: &Path) -> Result<Value> {
    serde_json::from_slice(&fs::read(path).with_context(|| format!("reading {}", path.display()))?)
        .with_context(|| format!("parsing {}", path.display()))
}

fn value_counts(rows: &[Value], field: &str) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for value in rows
        .iter()
        .filter_map(|row| row.get(field).and_then(Value::as_str))
    {
        *counts.entry(value.to_owned()).or_default() += 1;
    }
    counts
}

#[test]
fn recorder_runtime_provenance_flows_into_source_graph() -> Result<()> {
    let workspace = tempfile::tempdir()?;
    let capture = workspace.path().join("capture");
    let runtime = capture.join("runtime-scripts");
    let bodies = capture.join("bodies");
    let frames = capture.join("frames");
    for directory in [&runtime, &bodies, &frames] {
        fs::create_dir_all(directory)?;
    }

    let network = "globalThis.networkFixture = 1;";
    let network_other = "globalThis.otherCapturedResponse = 2;";
    let missed_other = "globalThis.missedResponse = 3;";
    let inline = "globalThis.inlineFixture = 1;";
    let exact = alpine("app.foo");
    let model = alpine("form.name = __placeholder");
    let xfor = alpine("items");
    let instrumentation =
        "() => Math.max(document.documentElement.scrollHeight, document.body?.scrollHeight || 0)";
    let gtm = "(function(){return google_tag_manager[\"rm\"][\"123\"](7).href})();";
    let generated = "globalThis.dynamicFixture = 1;";
    let generated_leaf = "globalThis.dynamicLeaf = 2;";
    let observed_network = "globalThis.crlfFixture = 1;\r\n";
    let sources = [
        network,
        inline,
        exact.as_str(),
        model.as_str(),
        xfor.as_str(),
        instrumentation,
        gtm,
        generated,
        generated_leaf,
        observed_network,
    ];
    for source in sources {
        fs::write(runtime.join(format!("{}.js", digest(source))), source)?;
    }
    fs::write(bodies.join(digest(network)), network)?;

    // Identical inline script bytes in two distinct ordinal positions are
    // separate capture candidates, not two observed executions.
    let initial_html = format!("<!doctype html><script>{inline}</script><script>{inline}</script>");
    let har = json!({
        "log": {
            "version": "1.2",
            "creator": {"name": "runtime-regression", "version": "1"},
            "pages": [],
            "entries": [
                har_entry("https://fixture.invalid/", "text/html", &initial_html),
                har_entry("https://fixture.invalid/app.js", "application/javascript", network),
                // Same URL, different source bytes: only the exact body can
                // substantiate a source match with the captured runtime script.
                har_entry("https://fixture.invalid/app.js", "application/javascript", network_other),
                // Same bytes at a different URL must not borrow app.js identity.
                har_entry("https://fixture.invalid/copy.js", "application/javascript", network),
                har_entry("https://fixture.invalid/body-missed.js", "application/javascript", ""),
                har_entry("https://fixture.invalid/body-missed.js", "application/javascript", missed_other),
            ],
        }
    });
    fs::write(capture.join("capture.har"), serde_json::to_vec(&har)?)?;
    fs::write(
        capture.join("recorder-manifest.json"),
        serde_json::to_vec(&json!({"schema": "fixture"}))?,
    )?;
    fs::write(
        frames.join("000.html"),
        concat!(
            "<div x-text=\"app.foo\"></div>",
            "<input x-model=\"form.name\">",
            "<template x-for=\"item in items\"></template>",
        ),
    )?;

    let mut events = sources
        .iter()
        .enumerate()
        .map(|(index, source)| {
            let source = *source;
            let sha = digest(source);
            json!({
                "scriptId": (index + 1).to_string(),
                "executionContextId": 1,
                "url": if source == network {
                    "https://fixture.invalid/app.js"
                } else if source == observed_network {
                    "https://fixture.invalid/body-missed.js"
                } else {
                    ""
                },
                "captured": {
                    "kind": "javascript",
                    "sha256": sha,
                    "size": source.len(),
                    "path": format!("runtime-scripts/{sha}.js"),
                },
            })
        })
        .collect::<Vec<_>>();
    events[7]["stackTrace"] = json!({
        "callFrames": [{
            "functionName": "eval",
            "scriptId": "1",
            "url": "https://fixture.invalid/app.js",
            "lineNumber": 0,
            "columnNumber": 1,
        }]
    });
    events[8]["stackTrace"] = json!({
        "callFrames": [{
            "functionName": "eval",
            "scriptId": "8",
            "url": "",
            "lineNumber": 0,
            "columnNumber": 2,
        }]
    });
    fs::write(
        capture.join("runtime-scripts.json"),
        serde_json::to_vec(&events)?,
    )?;

    let project = workspace.path().join("project");
    let summary = import_capture_project(
        &CaptureImportOptions {
            input: capture,
            output: project.clone(),
            assets_dir: None,
            overwrite: false,
        },
        &AnalysisBudgets::standard("runtime-script-project-test"),
    )?;
    assert_eq!(summary.kind.as_str(), "recorder");

    let report = read_json(&project.join("analysis/runtime-scripts.json"))?;
    let summary = &report["summary"];
    assert_eq!(summary["script_parsed_events"], 10);
    assert_eq!(summary["unique_javascript_sources"], 10);
    assert_eq!(
        summary["classifications"],
        json!({
            "alpine_expression": 3,
            "capture_instrumentation": 1,
            "generated_runtime": 2,
            "gtm_custom_javascript": 1,
            "inline_script": 1,
            "network_observed": 1,
            "network_response": 1,
        })
    );
    assert_eq!(summary["alpine_dom_mapped_sources"], 3);
    assert_eq!(summary["alpine_expression_shapes"], 3);
    assert_eq!(summary["gtm_expression_shapes"], 1);
    assert_eq!(summary["generated_runtime_sources"], 2);
    assert_eq!(summary["anonymous_runtime_sources"], 0);

    let report_sources = report
        .get("sources")
        .and_then(Value::as_array)
        .context("runtime sources missing")?;
    let mappings = report_sources
        .iter()
        .filter(|source| {
            source.get("classification").and_then(Value::as_str) == Some("alpine_expression")
        })
        .filter_map(|source| {
            source
                .pointer("/alpine/dom_mapping_kind")
                .and_then(Value::as_str)
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        mappings,
        BTreeSet::from(["exact", "x-for-rhs", "x-model-setter"])
    );

    let observed = report_sources
        .iter()
        .find(|source| {
            source.get("classification").and_then(Value::as_str) == Some("network_observed")
        })
        .context("network-observed runtime source missing")?;
    assert_eq!(observed["sha256"], digest(observed_network));
    assert_eq!(observed["event_count"], 1);

    build_source_graph(
        &project,
        &AnalysisBudgets::standard("runtime-script-graph-test"),
    )?;
    let graph = read_json(&project.join("analysis/source-graph.json"))?;
    let nodes = graph
        .get("nodes")
        .and_then(Value::as_array)
        .context("source-graph nodes missing")?;
    let edges = graph
        .get("edges")
        .and_then(Value::as_array)
        .context("source-graph edges missing")?;
    let node_types = value_counts(nodes, "type");
    let edge_kinds = value_counts(edges, "kind");
    assert_eq!(node_types.get("runtime_script"), Some(&10));
    assert_eq!(node_types.get("runtime_expression_family"), Some(&4));
    assert_eq!(node_types.get("dom_snapshot"), Some(&1));
    assert_eq!(node_types.get("dom_directive"), Some(&3));
    assert_eq!(edge_kinds.get("runtime_execution"), None);
    assert_eq!(edge_kinds.get("runtime_source_match"), Some(&1));
    assert_eq!(edge_kinds.get("runtime_source_candidate"), Some(&4));
    assert_eq!(edge_kinds.get("runtime_generated_code"), Some(&2));
    let inline_sha = digest(inline);
    let inline_runtime = format!("runtime:{}", &inline_sha[..20]);
    let inline_candidates = edges
        .iter()
        .filter(|edge| edge["to"] == inline_runtime && edge["kind"] == "runtime_source_candidate")
        .collect::<Vec<_>>();
    assert_eq!(inline_candidates.len(), 2);
    assert_ne!(inline_candidates[0]["from"], inline_candidates[1]["from"]);
    for candidate in inline_candidates {
        assert_eq!(candidate["identity_basis"], "sha256_only_inline_script");
        assert_eq!(candidate["candidate_count"], 2);
        assert_eq!(candidate["exact_response_identity"], false);
    }

    let manifest = read_json(&project.join("capture-manifest.json"))?;
    let resources = manifest["resources"]
        .as_array()
        .context("capture resources missing")?;
    let network_sha = digest(network);
    let network_runtime = format!("runtime:{}", &network_sha[..20]);
    let network_edges = edges
        .iter()
        .filter(|edge| edge["to"] == network_runtime && edge["kind"] == "runtime_source_match")
        .collect::<Vec<_>>();
    assert_eq!(network_edges.len(), 1);
    let exact_capture = resources
        .iter()
        .find(|resource| {
            resource["url"] == "https://fixture.invalid/app.js" && resource["sha256"] == network_sha
        })
        .context("exact app.js capture missing")?;
    assert_eq!(
        network_edges[0]["from"],
        format!(
            "resource:{}",
            exact_capture["id"].as_u64().context("capture ID missing")?
        )
    );
    assert_eq!(network_edges[0]["identity_basis"], "sha256_and_url");
    assert_eq!(network_edges[0]["candidate_count"], 1);
    assert_eq!(network_edges[0]["exact_response_identity"], true);
    assert_eq!(network_edges[0]["runtime_execution_observed"], false);
    let observed_sha = digest(observed_network);
    let observed_runtime = format!("runtime:{}", &observed_sha[..20]);
    let url_only = edges
        .iter()
        .filter(|edge| edge["to"] == observed_runtime && edge["kind"] == "runtime_source_candidate")
        .collect::<Vec<_>>();
    assert_eq!(url_only.len(), 2);
    for candidate in url_only {
        assert_eq!(candidate["identity_basis"], "url_only");
        assert_eq!(candidate["candidate_count"], 2);
        assert_eq!(candidate["exact_response_identity"], false);
        let response_id = candidate["from"]
            .as_str()
            .and_then(|value| value.strip_prefix("resource:"))
            .and_then(|value| value.parse::<u64>().ok())
            .context("missing candidate capture resource ID")?;
        assert!(resources
            .iter()
            .any(|resource| resource["id"] == response_id
                && resource["url"] == "https://fixture.invalid/body-missed.js"));
    }
    assert!(!edges
        .iter()
        .any(|edge| edge["to"] == network_runtime && edge["kind"] == "runtime_execution"));

    assert_eq!(edge_kinds.get("runtime_expression_family"), Some(&4));
    assert_eq!(edge_kinds.get("dom_directive"), Some(&3));
    assert_eq!(edge_kinds.get("runtime_alpine_compile"), Some(&3));

    let gtm_family = nodes
        .iter()
        .find(|node| {
            node.get("type").and_then(Value::as_str) == Some("runtime_expression_family")
                && node.get("framework").and_then(Value::as_str) == Some("google_tag_manager")
        })
        .context("GTM runtime family missing")?;
    assert_eq!(gtm_family["source_count"], 1);

    let generated_leaf_node = nodes
        .iter()
        .find(|node| {
            node.get("type").and_then(Value::as_str) == Some("runtime_script")
                && node.get("sha256").and_then(Value::as_str)
                    == Some(digest(generated_leaf).as_str())
        })
        .context("generated leaf runtime node missing")?;
    assert_eq!(generated_leaf_node["generation_max_depth"], 2);
    assert_eq!(
        generated_leaf_node["generated_root_sha256s"],
        json!([digest(network)])
    );

    let helper = nodes
        .iter()
        .find(|node| {
            node.get("type").and_then(Value::as_str) == Some("runtime_script")
                && node.get("classification").and_then(Value::as_str)
                    == Some("capture_instrumentation")
        })
        .context("capture instrumentation runtime node missing")?;
    assert_eq!(helper["application_source"], false);
    Ok(())
}

#[test]
fn missing_conflicting_parent_body_does_not_turn_claim_into_exact_graph_link() -> Result<()> {
    let workspace = tempfile::tempdir()?;
    let capture = workspace.path().join("capture");
    let runtime = capture.join("runtime-scripts");
    fs::create_dir_all(&runtime)?;
    let parent = "let parent = 1;";
    let missing = "let otherParent = 2;";
    let child = "let child = 3;";
    for body in [parent, child] {
        fs::write(runtime.join(format!("{}.js", digest(body))), body)?;
    }
    fs::write(capture.join("recorder-manifest.json"), b"{}")?;
    let har = json!({"log":{"version":"1.2","creator":{"name":"fixture","version":"1"},"pages":[],"entries":[har_entry("https://fixture.invalid/", "text/html", "<!doctype html>")]}});
    fs::write(capture.join("capture.har"), serde_json::to_vec(&har)?)?;
    let row = |id: &str, source: &str| json!({"cdpSession":"main","scriptId":id,"captured":{"kind":"javascript","sha256":digest(source),"size":source.len(),"path":format!("runtime-scripts/{}.js",digest(source))}});
    let mut child_event = row("2", child);
    child_event["stackTrace"] = json!({"callFrames":[{"scriptId":"1","url":"https://fixture.invalid/parent.js","lineNumber":0,"columnNumber":0}]});
    let events = [
        row("1", parent),
        row("1", missing),
        child_event.clone(),
        child_event,
    ];
    fs::write(
        capture.join("runtime-scripts.json"),
        serde_json::to_vec(&events)?,
    )?;
    let profile = |id: &str| json!({"scriptId":id,"functions":[{"ranges":[{"startOffset":0,"endOffset":3,"count":1}]}]});
    let coverage = json!({"schema":"js-redox/execution-coverage/v2","mode":"best-effort","offsetUnits":"utf16","sessions":[{"cdpSession":"main","status":"captured","scripts":[profile("1"),profile("2"),profile("2")]}]});
    fs::write(
        capture.join("execution-coverage.json"),
        serde_json::to_vec(&coverage)?,
    )?;
    let project = workspace.path().join("project");
    let budget = AnalysisBudgets::standard("missing-conflicting-parent-body");
    import_capture_project(
        &CaptureImportOptions {
            input: capture,
            output: project.clone(),
            assets_dir: None,
            overwrite: false,
        },
        &budget,
    )?;
    let report = read_json(&project.join("analysis/runtime-scripts.json"))?;
    let sources = report["sources"]
        .as_array()
        .context("runtime sources missing")?;
    assert_eq!(sources.len(), 2);
    let child_row = sources
        .iter()
        .find(|row| row["sha256"] == digest(child))
        .context("child source missing")?;
    let parent_row = sources
        .iter()
        .find(|row| row["sha256"] == digest(parent))
        .context("parent source missing")?;
    assert_eq!(parent_row["observed_executed"], false);
    assert_eq!(
        parent_row["script_instances"][0]["execution"]["status"],
        "unresolved_source_identity"
    );
    assert_eq!(
        parent_row["script_instances"][0]["execution"]["unattributed_coverage"]["positive_ranges"],
        1
    );
    assert_eq!(child_row["observed_executed"], true);
    let conflicts = report["script_identity_conflicts"]
        .as_array()
        .context("raw conflict inventory missing")?;
    assert_eq!(conflicts.len(), 1);
    assert_eq!(conflicts[0]["script_id"], "1");
    assert_eq!(conflicts[0]["event_count"], 2);
    let claim = &child_row["generated"]["origins"][0]["chain"][0];
    assert_eq!(claim["parent_event_status"], "conflicting_source_claims");
    assert!(claim["sha256"].is_null());
    let expected = BTreeSet::from([digest(parent), digest(missing)]);
    let actual = claim["parent_event_digest_claims"]
        .as_array()
        .context("parent claims missing")?
        .iter()
        .filter_map(Value::as_str)
        .map(ToOwned::to_owned)
        .collect::<BTreeSet<_>>();
    assert_eq!(actual, expected);
    assert_eq!(child_row["generated"]["root_sha256s"], json!([]));
    build_source_graph(&project, &budget)?;
    let graph = read_json(&project.join("analysis/source-graph.json"))?;
    let edges = graph["edges"].as_array().context("graph edges missing")?;
    assert!(!edges
        .iter()
        .any(|edge| edge["kind"] == "runtime_generated_code"
            || edge["kind"] == "runtime_generated_code_candidate"));
    let unresolved = edges
        .iter()
        .find(|edge| edge["kind"] == "runtime_generated_code_unresolved")
        .context("unresolved generated parent missing")?;
    assert_eq!(
        unresolved["identity_basis"],
        "conflicting_parent_event_claims"
    );
    assert_eq!(unresolved["exact_parent_source_identity"], false);
    assert_eq!(unresolved["exact_parent_runtime_instance"], false);
    assert_eq!(
        unresolved["parent_event_digest_claims"],
        claim["parent_event_digest_claims"]
    );
    let nodes = graph["nodes"].as_array().context("graph nodes missing")?;
    let parent_node = nodes
        .iter()
        .find(|row| row["type"] == "runtime_script" && row["sha256"] == digest(parent))
        .context("parent node missing")?;
    let child_node = nodes
        .iter()
        .find(|row| row["type"] == "runtime_script" && row["sha256"] == digest(child))
        .context("child node missing")?;
    assert_eq!(parent_node["observed_executed"], false);
    assert_eq!(parent_node["positive_coverage_witnesses"], json!([]));
    let child_witnesses = child_node["positive_coverage_witnesses"]
        .as_array()
        .context("child coverage missing")?;
    assert_eq!(child_witnesses.len(), 1);
    assert_eq!(child_witnesses[0]["positive_ranges"], 1);
    let observed =
        jsvm_lift::observed_runtime::materialize_observed_runtime_sources(&project, &budget)?;
    assert_eq!(observed.witnessed_sources, 1);
    assert!(project
        .join(format!("src/_observed/{}.js", digest(child)))
        .is_file());
    assert!(!project
        .join(format!("src/_observed/{}.js", digest(parent)))
        .is_file());
    assert_eq!(graph["unresolved_edges"], json!([]));
    Ok(())
}
