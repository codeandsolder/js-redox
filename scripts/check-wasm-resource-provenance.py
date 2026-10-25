#!/usr/bin/env python3
"""Regression: CDP-observed WASM request provenance stays exact and fail-closed."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "work" / "wasm-resource-provenance-regression"
CAPTURE = WORK / "capture"
PROJECT = WORK / "project"
CORRELATOR = ROOT / "scripts" / "correlate-wasm-resource-provenance.py"
GRAPH = ROOT / "scripts" / "build-source-graph.py"

JS_URL = "https://cdn.example.test/loader.js"
INITIATOR_URL = "https://cdn.example.test/loader"
WASM_URL = "https://cdn.example.test/module.wasm?v=1"
BRIDGE_WASM_URL = "https://cdn.example.test/bridge.wasm"
JS = "export async function load() { return fetch('dynamic'); }\n"
CONFLICT_JS = "globalThis.conflictingLoader = true;\n"
WASM = b"\0asm\x01\0\0\0"
BRIDGE_WASM = b"\0asm\x01\0\0\0\x00"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    shutil.rmtree(WORK, ignore_errors=True)
    (CAPTURE / "runtime-scripts").mkdir(parents=True)
    (CAPTURE / "bodies").mkdir(parents=True)
    (PROJECT / "analysis").mkdir(parents=True)

    js_sha = digest(JS.encode())
    wasm_sha = digest(WASM)
    bridge_wasm_sha = digest(BRIDGE_WASM)
    (CAPTURE / "runtime-scripts" / f"{js_sha}.js").write_text(JS)
    (CAPTURE / "bodies" / js_sha).write_text(JS)
    (CAPTURE / "bodies" / wasm_sha).write_bytes(WASM)
    (CAPTURE / "bodies" / bridge_wasm_sha).write_bytes(BRIDGE_WASM)

    runtime_event = {
        "cdpSession": "main",
        "scriptId": "606",
        "url": JS_URL,
        "executionContextId": 1,
        "captured": {
            "kind": "javascript",
            "sha256": js_sha,
            "size": len(JS.encode()),
            "path": f"runtime-scripts/{js_sha}.js",
        },
    }
    (CAPTURE / "runtime-scripts.json").write_text(json.dumps([runtime_event]))

    good = {
        "cdpSession": "main",
        "requestId": "req-good",
        "url": WASM_URL,
        "status": 200,
        "mimeType": "application/wasm",
        "resourceType": "Fetch",
        "initiator": {
            "type": "script",
            "stack": {
                "callFrames": [
                    {
                        "functionName": "load",
                        "scriptId": "606",
                        "url": INITIATOR_URL,
                        "lineNumber": 0,
                        "columnNumber": 37,
                    }
                ]
            },
        },
        "body": {"sha256": wasm_sha, "size": len(WASM), "path": f"bodies/{wasm_sha}"},
    }
    bridge = {
        **good,
        "requestId": "req-bridge",
        "url": BRIDGE_WASM_URL,
        "body": None,
    }
    bad = {
        **good,
        "requestId": "req-bad",
        "body": {"sha256": "f" * 64, "size": len(WASM), "path": "bodies/mismatch"},
    }
    (CAPTURE / "cdp-streams.json").write_text(json.dumps([good, bridge, bad]))

    manifest = {
        "schema": "capture-project/v1",
        "source": {"kind": "recorder", "input": str(CAPTURE), "salvaged": False},
        "pages": [],
        "resources": [
            {
                "id": 1,
                "kind": "javascript",
                "url": JS_URL,
                "body_present": True,
                "output_path": f"resources/{js_sha}.js",
                "sha256": js_sha,
                "status": 200,
            },
            {
                "id": 2,
                "kind": "wasm",
                "url": WASM_URL,
                "body_present": True,
                "body_complete": True,
                "body_bytes": len(WASM),
                "output_path": f"resources/{wasm_sha}.wasm",
                "sha256": wasm_sha,
                "status": 200,
            },
            {
                "id": 3,
                "kind": "wasm",
                "url": BRIDGE_WASM_URL,
                "body_present": True,
                "body_complete": True,
                "body_bytes": len(BRIDGE_WASM),
                "output_path": f"resources/{bridge_wasm_sha}.wasm",
                "sha256": bridge_wasm_sha,
                "status": 200,
            },
        ],
        "inline_scripts": [],
        "counts": {},
    }
    (PROJECT / "capture-manifest.json").write_text(json.dumps(manifest))

    runtime_artifact = {
        "schema": "js-redox-runtime-scripts/v1",
        "sources": [
            {
                "sha256": js_sha,
                "size": len(JS.encode()),
                "path": f"runtime-scripts/{js_sha}.js",
                "event_count": 1,
                "script_ids": ["606"],
                "cdp_sessions": ["main"],
                "execution_context_ids": [1],
                "script_instances": [
                    {"cdp_session": "main", "script_id": "606", "execution_context_id": 1}
                ],
                "urls": [JS_URL],
                "classification": "network_response",
            }
        ],
        "alpine_families": [],
        "gtm_families": [],
        "summary": {},
    }
    (PROJECT / "analysis" / "runtime-scripts.json").write_text(json.dumps(runtime_artifact))

    subprocess.run([sys.executable, str(CORRELATOR), str(PROJECT)], cwd=ROOT, check=True)
    provenance = json.loads((PROJECT / "analysis" / "wasm-resource-provenance.json").read_text())
    assert provenance["summary"]["observations"] == 2, provenance
    assert provenance["summary"]["runtime_script_identities"] == 2, provenance
    assert provenance["summary"]["direct_body_identities"] == 1, provenance
    assert provenance["summary"]["url_unique_body_identities"] == 1, provenance
    assert provenance["summary"]["unmatched_wasm_events"] == 1, provenance
    by_request = {row["request_id"]: row for row in provenance["observations"]}
    observation = by_request["req-good"]
    assert observation["wasm_resource_ids"] == [2], observation
    assert observation["response_identity_basis"] == "cdp_body_sha256", observation
    assert observation["initiator_runtime_sha256"] == js_sha, observation
    assert observation["initiator_resource_ids"] == [], observation
    bridge_observation = by_request["req-bridge"]
    assert bridge_observation["wasm_resource_ids"] == [3], bridge_observation
    assert bridge_observation["sha256"] == bridge_wasm_sha, bridge_observation
    assert bridge_observation["response_identity_basis"] == "unique_url_body_and_request_cardinality", bridge_observation
    assert provenance["unmatched"][0]["request_id"] == "req-bad", provenance

    subprocess.run([sys.executable, str(GRAPH), str(PROJECT)], cwd=ROOT, check=True)
    graph = json.loads((PROJECT / "analysis" / "source-graph.json").read_text())
    observation_nodes = [n for n in graph["nodes"] if n["type"] == "runtime_wasm_request"]
    assert len(observation_nodes) == 2, observation_nodes
    observation_ids = {node["request_id"]: node["id"] for node in observation_nodes}
    for request_id in ("req-good", "req-bridge"):
        assert any(
            e["from"] == f"runtime:{js_sha[:20]}"
            and e["to"] == observation_ids[request_id]
            and e["kind"] == "runtime_wasm_request_initiator"
            for e in graph["edges"]
        ), graph["edges"]
    assert any(
        e["from"] == observation_ids["req-good"]
        and e["to"] == "resource:2"
        and e["kind"] == "runtime_observed_wasm_response"
        and e["sha256"] == wasm_sha
        for e in graph["edges"]
    ), graph["edges"]
    assert any(
        e["from"] == observation_ids["req-bridge"]
        and e["to"] == "resource:3"
        and e["kind"] == "runtime_observed_wasm_response"
        and e["sha256"] == bridge_wasm_sha
        and e["response_identity_basis"] == "unique_url_body_and_request_cardinality"
        for e in graph["edges"]
    ), graph["edges"]
    assert not any("f" * 64 == e.get("sha256") for e in graph["edges"]), graph["edges"]

    conflict_sha = digest(CONFLICT_JS.encode())
    (CAPTURE / "runtime-scripts" / f"{conflict_sha}.js").write_text(CONFLICT_JS)
    conflict_event = {
        **runtime_event,
        "url": "https://cdn.example.test/conflict.js",
        "captured": {
            "kind": "javascript",
            "sha256": conflict_sha,
            "size": len(CONFLICT_JS.encode()),
            "path": f"runtime-scripts/{conflict_sha}.js",
        },
    }
    (CAPTURE / "runtime-scripts.json").write_text(json.dumps([runtime_event, conflict_event]))
    runtime_artifact["sources"].append(
        {
            "sha256": conflict_sha,
            "size": len(CONFLICT_JS.encode()),
            "path": f"runtime-scripts/{conflict_sha}.js",
            "event_count": 1,
            "script_ids": ["606"],
            "cdp_sessions": ["main"],
            "execution_context_ids": [2],
            "script_instances": [
                {"cdp_session": "main", "script_id": "606", "execution_context_id": 2}
            ],
            "urls": ["https://cdn.example.test/conflict.js"],
            "classification": "network_observed",
        }
    )
    (PROJECT / "analysis" / "runtime-scripts.json").write_text(json.dumps(runtime_artifact))
    subprocess.run([sys.executable, str(CORRELATOR), str(PROJECT)], cwd=ROOT, check=True)
    conflicted = json.loads((PROJECT / "analysis" / "wasm-resource-provenance.json").read_text())
    assert conflicted["summary"]["observations"] == 2, conflicted
    assert conflicted["summary"]["runtime_script_identities"] == 0, conflicted
    assert all(row["initiator_runtime_sha256"] is None for row in conflicted["observations"]), conflicted
    subprocess.run([sys.executable, str(GRAPH), str(PROJECT)], cwd=ROOT, check=True)
    conflict_graph = json.loads((PROJECT / "analysis" / "source-graph.json").read_text())
    runtime_nodes = {f"runtime:{js_sha[:20]}", f"runtime:{conflict_sha[:20]}"}
    assert not any(
        edge["kind"] == "runtime_wasm_request_initiator" and edge["from"] in runtime_nodes
        for edge in conflict_graph["edges"]
    ), conflict_graph["edges"]

    (CAPTURE / "cdp-streams.json").unlink()
    subprocess.run([sys.executable, str(CORRELATOR), str(PROJECT)], cwd=ROOT, check=True)
    unavailable = json.loads((PROJECT / "analysis" / "wasm-resource-provenance.json").read_text())
    assert unavailable["summary"]["applicable"] is False, unavailable
    assert unavailable["summary"]["unavailable_reason"] == "missing_cdp_stream", unavailable
    assert unavailable["observations"] == [], unavailable

    print("PASS: exact CDP/unique-URL WASM provenance -> runtime initiator -> captured resource; conflicting script IDs drop identity; missing CDP stays no-claim")


if __name__ == "__main__":
    main()
