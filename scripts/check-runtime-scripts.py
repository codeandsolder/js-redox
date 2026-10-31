#!/usr/bin/env python3
"""Regression for recorder runtime-script provenance classification."""

from __future__ import annotations

import hashlib
import json
import shutil
from collections import Counter
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "work/runtime-script-regression"
CAPTURE_PROJECT = ROOT / ".cargo-target-nodebug/debug/capture-project"


def digest(source: str) -> str:
    return hashlib.sha256(source.encode()).hexdigest()


def alpine(expression: str) -> str:
    return (
        "(async function anonymous(__self,scope\n) {\n"
        f"with (scope) {{ __self.result = {expression} }}; "
        "__self.finished = true; return __self.result;\n})"
    )


def har_entry(url: str, mime: str, text: str) -> dict:
    return {
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
            "content": {"size": len(text.encode()), "mimeType": mime, "text": text},
            "redirectURL": "",
            "headersSize": -1,
            "bodySize": len(text.encode()),
        },
        "cache": {},
        "timings": {"send": 0, "wait": 0, "receive": 0},
    }


def main() -> None:
    shutil.rmtree(WORK, ignore_errors=True)
    capture = WORK / "capture"
    runtime = capture / "runtime-scripts"
    bodies = capture / "bodies"
    frames = capture / "frames"
    for directory in (runtime, bodies, frames):
        directory.mkdir(parents=True, exist_ok=True)

    network = "globalThis.networkFixture = 1;"
    inline = "globalThis.inlineFixture = 1;"
    exact = alpine("app.foo")
    model = alpine("form.name = __placeholder")
    xfor = alpine("items")
    instrumentation = "() => Math.max(document.documentElement.scrollHeight, document.body?.scrollHeight || 0)"
    gtm = '(function(){return google_tag_manager["rm"]["123"](7).href})();'
    generated = "globalThis.dynamicFixture = 1;"
    generated_leaf = "globalThis.dynamicLeaf = 2;"
    observed_network = "globalThis.crlfFixture = 1;\r\n"
    sources = [
        network,
        inline,
        exact,
        model,
        xfor,
        instrumentation,
        gtm,
        generated,
        generated_leaf,
        observed_network,
    ]

    for source in sources:
        raw = source.encode()
        (runtime / f"{hashlib.sha256(raw).hexdigest()}.js").write_bytes(raw)
    (bodies / digest(network)).write_text(network)

    initial_html = f"<!doctype html><script>{inline}</script>"
    har = {
        "log": {
            "version": "1.2",
            "creator": {"name": "runtime-regression", "version": "1"},
            "pages": [],
            "entries": [
                har_entry("https://fixture.invalid/", "text/html", initial_html),
                har_entry("https://fixture.invalid/app.js", "application/javascript", network),
                har_entry("https://fixture.invalid/body-missed.js", "application/javascript", ""),
            ],
        }
    }
    (capture / "capture.har").write_text(json.dumps(har))
    (capture / "recorder-manifest.json").write_text(json.dumps({"schema": "fixture"}))
    (frames / "000.html").write_text(
        '<div x-text="app.foo"></div>'
        '<input x-model="form.name">'
        '<template x-for="item in items"></template>'
    )

    events = []
    for index, source in enumerate(sources, 1):
        sha = digest(source)
        events.append(
            {
                "scriptId": str(index),
                "executionContextId": 1,
                "url": (
                    "https://fixture.invalid/app.js"
                    if source == network
                    else "https://fixture.invalid/body-missed.js"
                    if source == observed_network
                    else ""
                ),
                "captured": {
                    "kind": "javascript",
                    "sha256": sha,
                    "size": len(source.encode()),
                    "path": f"runtime-scripts/{sha}.js",
                },
            }
        )
    events[-3]["stackTrace"] = {
        "callFrames": [
            {
                "functionName": "eval",
                "scriptId": "1",
                "url": "https://fixture.invalid/app.js",
                "lineNumber": 0,
                "columnNumber": 1,
            }
        ]
    }
    events[-2]["stackTrace"] = {
        "callFrames": [
            {
                "functionName": "eval",
                "scriptId": "8",
                "url": "",
                "lineNumber": 0,
                "columnNumber": 2,
            }
        ]
    }
    (capture / "runtime-scripts.json").write_text(json.dumps(events))

    project = WORK / "project"
    subprocess.run(
        [
            str(CAPTURE_PROJECT),
            str(capture),
            str(project),
            "--overwrite",
            "--jobs",
            "2",
            "--skip-safe-deobfuscation",
            "--skip-bundle-unpack",
            "--skip-vm-scan",
            "--skip-wasm-analysis",
        ],
        cwd=ROOT,
        check=True,
    )
    report = json.loads((project / "analysis/runtime-scripts.json").read_text())
    summary = report["summary"]
    assert summary["script_parsed_events"] == 10, summary
    assert summary["unique_javascript_sources"] == 10, summary
    assert summary["classifications"] == {
        "alpine_expression": 3,
        "capture_instrumentation": 1,
        "generated_runtime": 2,
        "gtm_custom_javascript": 1,
        "inline_script": 1,
        "network_observed": 1,
        "network_response": 1,
    }, summary
    assert summary["alpine_dom_mapped_sources"] == 3, summary
    assert summary["alpine_expression_shapes"] == 3, summary
    assert summary["gtm_expression_shapes"] == 1, summary
    assert summary["generated_runtime_sources"] == 2, summary
    assert summary["anonymous_runtime_sources"] == 0, summary
    mappings = {
        source["alpine"]["dom_mapping_kind"]
        for source in report["sources"]
        if source["classification"] == "alpine_expression"
    }
    assert mappings == {"exact", "x-model-setter", "x-for-rhs"}, mappings

    graph = json.loads((project / "analysis/source-graph.json").read_text())
    node_types = Counter(node["type"] for node in graph["nodes"])
    edge_kinds = Counter(edge["kind"] for edge in graph["edges"])
    assert node_types["runtime_script"] == 10, node_types
    assert node_types["runtime_expression_family"] == 4, node_types
    assert node_types["dom_snapshot"] == 1, node_types
    assert node_types["dom_directive"] == 3, node_types
    assert edge_kinds["runtime_execution"] == 3, edge_kinds
    assert edge_kinds["runtime_generated_code"] == 2, edge_kinds
    assert edge_kinds["runtime_expression_family"] == 4, edge_kinds
    assert edge_kinds["dom_directive"] == 3, edge_kinds
    assert edge_kinds["runtime_alpine_compile"] == 3, edge_kinds
    gtm_family = next(
        node
        for node in graph["nodes"]
        if node.get("type") == "runtime_expression_family"
        and node.get("framework") == "google_tag_manager"
    )
    assert gtm_family["source_count"] == 1, gtm_family
    generated_leaf_node = next(
        node
        for node in graph["nodes"]
        if node.get("type") == "runtime_script"
        and node.get("sha256") == digest(generated_leaf)
    )
    assert generated_leaf_node["generation_max_depth"] == 2, generated_leaf_node
    assert generated_leaf_node["generated_root_sha256s"] == [digest(network)], generated_leaf_node
    observed = next(
        source
        for source in report["sources"]
        if source.get("classification") == "network_observed"
    )
    assert observed["sha256"] == hashlib.sha256(observed_network.encode()).hexdigest(), observed
    assert observed["event_count"] == 1, observed
    helper = next(
        node
        for node in graph["nodes"]
        if node.get("type") == "runtime_script"
        and node.get("classification") == "capture_instrumentation"
    )
    assert helper["application_source"] is False, helper
    print(
        "PASS: recorder runtime provenance -> network/network-observed/inline/Alpine/GTM/generated/instrumentation "
        "+ DOM/runtime source graph"
    )


if __name__ == "__main__":
    main()
