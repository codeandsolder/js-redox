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

    let initial_html = format!("<!doctype html><script>{inline}</script>");
    let har = json!({
        "log": {
            "version": "1.2",
            "creator": {"name": "runtime-regression", "version": "1"},
            "pages": [],
            "entries": [
                har_entry("https://fixture.invalid/", "text/html", &initial_html),
                har_entry("https://fixture.invalid/app.js", "application/javascript", network),
                har_entry("https://fixture.invalid/body-missed.js", "application/javascript", ""),
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
    assert_eq!(edge_kinds.get("runtime_execution"), Some(&3));
    assert_eq!(edge_kinds.get("runtime_generated_code"), Some(&2));
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
