use anyhow::{Context, Result};
use jsvm_lift::{
    sha256_hex, source_graph::build_source_graph,
    wasm_resource_provenance::correlate_wasm_resource_provenance,
};
use serde_json::{json, Value};
use std::{fs, path::Path};

const JS_URL: &str = "https://cdn.example.test/loader.js";
const INITIATOR_URL: &str = "https://cdn.example.test/loader";
const WASM_URL: &str = "https://cdn.example.test/module.wasm?v=1";
const BRIDGE_WASM_URL: &str = "https://cdn.example.test/bridge.wasm";
const HEAD_WASM_URL: &str = "https://cdn.example.test/probe.wasm";
const NO_CONTENT_WASM_URL: &str = "https://cdn.example.test/no-content.wasm";
const JS: &str = "export async function load() { return fetch('dynamic'); }\n";
const CONFLICT_JS: &str = "globalThis.conflictingLoader = true;\n";
const WASM: &[u8] = b"\0asm\x01\0\0\0";
const BRIDGE_WASM: &[u8] = b"\0asm\x01\0\0\0\x00";

fn read_json(path: &Path) -> Result<Value> {
    serde_json::from_slice(&fs::read(path).with_context(|| format!("reading {}", path.display()))?)
        .with_context(|| format!("parsing {}", path.display()))
}

fn write_json(path: &Path, value: &Value) -> Result<()> {
    fs::write(path, serde_json::to_vec(value)?)?;
    Ok(())
}

fn runtime_source(
    digest: &str,
    path: &str,
    execution_context_id: u64,
    classification: &str,
) -> Value {
    json!({
        "sha256": digest,
        "size": if digest == sha256_hex(JS.as_bytes()) { JS.len() } else { CONFLICT_JS.len() },
        "path": path,
        "event_count": 1,
        "script_ids": ["606"],
        "cdp_sessions": ["main"],
        "execution_context_ids": [execution_context_id],
        "script_instances": [{
            "cdp_session": "main",
            "script_id": "606",
            "execution_context_id": execution_context_id,
        }],
        "urls": [if classification == "network_response" { JS_URL } else { "https://cdn.example.test/conflict.js" }],
        "classification": classification,
    })
}

#[test]
fn runtime_wasm_provenance_is_exact_and_fails_closed() -> Result<()> {
    let workspace = tempfile::tempdir()?;
    let capture = workspace.path().join("capture");
    let project = workspace.path().join("project");
    fs::create_dir_all(capture.join("runtime-scripts"))?;
    fs::create_dir_all(capture.join("bodies"))?;
    fs::create_dir_all(project.join("analysis"))?;

    let js_sha = sha256_hex(JS.as_bytes());
    let wasm_sha = sha256_hex(WASM);
    let bridge_wasm_sha = sha256_hex(BRIDGE_WASM);
    fs::write(capture.join(format!("runtime-scripts/{js_sha}.js")), JS)?;
    fs::write(capture.join(format!("bodies/{js_sha}")), JS)?;
    fs::write(capture.join(format!("bodies/{wasm_sha}")), WASM)?;
    fs::write(
        capture.join(format!("bodies/{bridge_wasm_sha}")),
        BRIDGE_WASM,
    )?;

    let runtime_event = json!({
        "cdpSession": "main",
        "scriptId": "606",
        "url": JS_URL,
        "executionContextId": 1,
        "captured": {
            "kind": "javascript",
            "sha256": js_sha,
            "size": JS.len(),
            "path": format!("runtime-scripts/{js_sha}.js"),
        },
    });
    write_json(
        &capture.join("runtime-scripts.json"),
        &json!([runtime_event]),
    )?;

    let good = json!({
        "cdpSession": "main",
        "requestId": "req-good",
        "url": WASM_URL,
        "status": 200,
        "mimeType": "application/wasm",
        "resourceType": "Fetch",
        "initiator": {
            "type": "script",
            "stack": {
                "callFrames": [{
                    "functionName": "load",
                    "scriptId": "606",
                    "url": INITIATOR_URL,
                    "lineNumber": 0,
                    "columnNumber": 37,
                }],
            },
        },
        "body": {"sha256": wasm_sha, "size": WASM.len(), "path": format!("bodies/{wasm_sha}")},
    });
    let mut bridge = good.clone();
    bridge["requestId"] = json!("req-bridge");
    bridge["url"] = json!(BRIDGE_WASM_URL);
    bridge["body"] = Value::Null;
    let mut bad = good.clone();
    bad["requestId"] = json!("req-bad");
    bad["body"] = json!({"sha256": "f".repeat(64), "size": WASM.len(), "path": "bodies/mismatch"});
    let mut head = good.clone();
    head["requestId"] = json!("req-head");
    head["url"] = json!(HEAD_WASM_URL);
    head["method"] = json!("HEAD");
    head["body"] = Value::Null;
    let mut no_content = good.clone();
    no_content["requestId"] = json!("req-no-content");
    no_content["url"] = json!(NO_CONTENT_WASM_URL);
    no_content["method"] = json!("GET");
    no_content["status"] = json!(204);
    no_content["body"] = Value::Null;
    write_json(
        &capture.join("cdp-streams.json"),
        &json!([good, bridge, bad, head, no_content]),
    )?;

    write_json(
        &project.join("capture-manifest.json"),
        &json!({
            "schema": "capture-project/v1",
            "source": {"kind": "recorder", "input": capture, "salvaged": false},
            "pages": [],
            "resources": [
                {
                    "id": 1,
                    "kind": "javascript",
                    "url": JS_URL,
                    "body_present": true,
                    "output_path": format!("resources/{js_sha}.js"),
                    "sha256": js_sha,
                    "status": 200,
                },
                {
                    "id": 2,
                    "kind": "wasm",
                    "url": WASM_URL,
                    "body_present": true,
                    "body_complete": true,
                    "body_bytes": WASM.len(),
                    "output_path": format!("resources/{wasm_sha}.wasm"),
                    "sha256": wasm_sha,
                    "status": 200,
                },
                {
                    "id": 3,
                    "kind": "wasm",
                    "url": BRIDGE_WASM_URL,
                    "body_present": true,
                    "body_complete": true,
                    "body_bytes": BRIDGE_WASM.len(),
                    "output_path": format!("resources/{bridge_wasm_sha}.wasm"),
                    "sha256": bridge_wasm_sha,
                    "status": 200,
                },
                {
                    "id": 4,
                    "kind": "wasm",
                    "url": HEAD_WASM_URL,
                    "method": "HEAD",
                    "status": 200,
                    "body_expected": false,
                    "body_present": false,
                    "body_complete": false,
                    "body_bytes": 0,
                    "sha256": null,
                },
                {
                    "id": 5,
                    "kind": "wasm",
                    "url": NO_CONTENT_WASM_URL,
                    "method": "GET",
                    "status": 204,
                    "body_expected": false,
                    "body_present": false,
                    "body_complete": true,
                    "body_bytes": 0,
                    "sha256": null,
                },
            ],
            "inline_scripts": [],
            "counts": {},
        }),
    )?;

    let mut runtime_artifact = json!({
        "schema": "js-redox-runtime-scripts/v1",
        "sources": [runtime_source(
            &js_sha,
            &format!("runtime-scripts/{js_sha}.js"),
            1,
            "network_response",
        )],
        "alpine_families": [],
        "gtm_families": [],
        "summary": {},
    });
    write_json(
        &project.join("analysis/runtime-scripts.json"),
        &runtime_artifact,
    )?;

    let summary = correlate_wasm_resource_provenance(&project)?;
    assert_eq!(summary.observations, 2);
    assert_eq!(summary.runtime_script_identities, 2);
    assert_eq!(summary.unmatched_wasm_events, 1);
    assert_eq!(summary.ignored_non_body_wasm_events, 2);
    assert!(summary.applicable);

    let provenance = read_json(&project.join("analysis/wasm-resource-provenance.json"))?;
    assert_eq!(provenance["summary"]["direct_body_identities"], 1);
    assert_eq!(provenance["summary"]["url_unique_body_identities"], 1);
    let ignored = provenance["ignored_non_body"]
        .as_array()
        .context("ignored_non_body missing")?;
    assert_eq!(
        ignored
            .iter()
            .find(|row| row["request_id"] == "req-head")
            .context("HEAD observation missing")?["reason"],
        "method_HEAD"
    );
    assert_eq!(
        ignored
            .iter()
            .find(|row| row["request_id"] == "req-no-content")
            .context("204 observation missing")?["reason"],
        "status_204"
    );
    let observations = provenance["observations"]
        .as_array()
        .context("observations missing")?;
    let observation = observations
        .iter()
        .find(|row| row["request_id"] == "req-good")
        .context("good observation missing")?;
    assert_eq!(observation["wasm_resource_ids"], json!([2]));
    assert_eq!(observation["response_identity_basis"], "cdp_body_sha256");
    assert_eq!(observation["initiator_runtime_sha256"], js_sha);
    assert_eq!(observation["initiator_resource_ids"], json!([]));
    let bridge_observation = observations
        .iter()
        .find(|row| row["request_id"] == "req-bridge")
        .context("bridge observation missing")?;
    assert_eq!(bridge_observation["wasm_resource_ids"], json!([3]));
    assert_eq!(bridge_observation["sha256"], bridge_wasm_sha);
    assert_eq!(
        bridge_observation["response_identity_basis"],
        "unique_url_body_and_request_cardinality"
    );
    assert_eq!(provenance["unmatched"][0]["request_id"], "req-bad");

    build_source_graph(&project)?;
    let graph = read_json(&project.join("analysis/source-graph.json"))?;
    let nodes = graph["nodes"].as_array().context("graph nodes missing")?;
    let edges = graph["edges"].as_array().context("graph edges missing")?;
    let observation_nodes = nodes
        .iter()
        .filter(|node| node["type"] == "runtime_wasm_request")
        .collect::<Vec<_>>();
    assert_eq!(observation_nodes.len(), 2);
    assert!(observation_nodes.iter().all(|node| {
        !matches!(
            node["request_id"].as_str(),
            Some("req-head" | "req-no-content")
        )
    }));
    for request_id in ["req-good", "req-bridge"] {
        let observation_id = observation_nodes
            .iter()
            .find(|node| node["request_id"] == request_id)
            .context("runtime WASM observation node missing")?["id"]
            .as_str()
            .context("runtime WASM observation id missing")?;
        assert!(edges.iter().any(|edge| {
            edge["from"] == format!("runtime:{}", &js_sha[..20])
                && edge["to"] == observation_id
                && edge["kind"] == "runtime_wasm_request_initiator"
        }));
        let (resource_id, digest, basis) = if request_id == "req-good" {
            (2, wasm_sha.as_str(), "cdp_body_sha256")
        } else {
            (
                3,
                bridge_wasm_sha.as_str(),
                "unique_url_body_and_request_cardinality",
            )
        };
        assert!(edges.iter().any(|edge| {
            edge["from"] == observation_id
                && edge["to"] == format!("resource:{resource_id}")
                && edge["kind"] == "runtime_observed_wasm_response"
                && edge["sha256"] == digest
                && edge["response_identity_basis"] == basis
        }));
    }
    assert!(edges
        .iter()
        .all(|edge| edge.get("sha256") != Some(&json!("f".repeat(64)))));

    let conflict_sha = sha256_hex(CONFLICT_JS.as_bytes());
    fs::write(
        capture.join(format!("runtime-scripts/{conflict_sha}.js")),
        CONFLICT_JS,
    )?;
    let mut conflict_event = runtime_event.clone();
    conflict_event["url"] = json!("https://cdn.example.test/conflict.js");
    conflict_event["executionContextId"] = json!(2);
    conflict_event["captured"] = json!({
        "kind": "javascript",
        "sha256": conflict_sha,
        "size": CONFLICT_JS.len(),
        "path": format!("runtime-scripts/{conflict_sha}.js"),
    });
    write_json(
        &capture.join("runtime-scripts.json"),
        &json!([runtime_event, conflict_event]),
    )?;
    runtime_artifact["sources"]
        .as_array_mut()
        .context("runtime artifact sources missing")?
        .push(runtime_source(
            &conflict_sha,
            &format!("runtime-scripts/{conflict_sha}.js"),
            2,
            "network_observed",
        ));
    write_json(
        &project.join("analysis/runtime-scripts.json"),
        &runtime_artifact,
    )?;

    let conflicted = correlate_wasm_resource_provenance(&project)?;
    assert_eq!(conflicted.observations, 2);
    assert_eq!(conflicted.runtime_script_identities, 0);
    let conflicted_artifact = read_json(&project.join("analysis/wasm-resource-provenance.json"))?;
    assert!(conflicted_artifact["observations"]
        .as_array()
        .context("conflicted observations missing")?
        .iter()
        .all(|row| row["initiator_runtime_sha256"].is_null()));
    build_source_graph(&project)?;
    let conflict_graph = read_json(&project.join("analysis/source-graph.json"))?;
    let runtime_nodes = [
        format!("runtime:{}", &js_sha[..20]),
        format!("runtime:{}", &conflict_sha[..20]),
    ];
    assert!(conflict_graph["edges"]
        .as_array()
        .context("conflict graph edges missing")?
        .iter()
        .all(|edge| {
            edge["kind"] != "runtime_wasm_request_initiator"
                || !runtime_nodes
                    .iter()
                    .any(|node| edge["from"] == node.as_str())
        }));

    fs::remove_file(capture.join("cdp-streams.json"))?;
    let unavailable = correlate_wasm_resource_provenance(&project)?;
    assert!(!unavailable.applicable);
    let unavailable_artifact = read_json(&project.join("analysis/wasm-resource-provenance.json"))?;
    assert_eq!(
        unavailable_artifact["summary"]["unavailable_reason"],
        "missing_cdp_stream"
    );
    assert_eq!(unavailable_artifact["observations"], json!([]));
    Ok(())
}
