#!/usr/bin/env python3
"""Public synthetic regression for static API callsite extraction and graph linkage."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

from analysis_artifacts import API_SURFACE, SOURCE_GRAPH, load_artifact

ROOT = Path(__file__).resolve().parents[1]
ANALYZER = ROOT / ".cargo-target-nodebug/debug/api-surface"


def run(*args: object) -> None:
    cp = subprocess.run(
        [str(arg) for arg in args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if cp.returncode:
        raise SystemExit(cp.stdout + cp.stderr)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="js-redox-api-surface-") as tmp:
        project = Path(tmp)
        raw = project / "resources/app.js"
        src = project / "src/app.js"
        deob = project / "src/_deobfuscated/app.js"
        rejected_raw = project / "resources/rejected.js"
        rejected_src = project / "src/rejected.js"
        for path in (raw, src, deob, rejected_raw, rejected_src):
            path.parent.mkdir(parents=True, exist_ok=True)
        source = """
const apiOrigin = "https://api.example.test";
const usersUrl = apiOrigin + "/v1/users";
const writeMethod = "POST";
fetch(usersUrl);
fetch("/relative");
fetch("/unknown-method", opts);
fetch(apiOrigin + "/write", { ...opts, method: writeMethod });
fetch("https://api.example.test/forbidden", { method: "trace" });
navigator.sendBeacon("https://api.example.test/beacon", body);
const xhr = new XMLHttpRequest();
xhr.open("PATCH", "https://api.example.test/items");
new WebSocket("wss://socket.example.test/ws");
function shadow(fetch) { fetch("https://fake.invalid/"); }
"""
        raw.write_text(source)
        src.write_text(source)
        deob.write_text(source)
        rejected_source = 'with (scope) { fetch("https://rejected.invalid/"); }\n'
        rejected_raw.write_text(rejected_source)
        rejected_src.write_text(rejected_source)
        (project / "capture-manifest.json").write_text(
            json.dumps(
                {
                    "schema": "capture-project/v1",
                    "source": {"kind": "synthetic", "input": "synthetic-api-surface.js", "salvaged": False},
                    "pages": [],
                    "resources": [
                        {
                            "id": 0,
                            "url": "https://app.example.test/app.js",
                            "kind": "javascript",
                            "output_path": "resources/app.js",
                            "body_present": True,
                            "references": [],
                            "response_headers": [],
                        },
                        {
                            "id": 1,
                            "url": "https://app.example.test/rejected.js",
                            "kind": "javascript",
                            "output_path": "resources/rejected.js",
                            "body_present": True,
                            "references": [],
                            "response_headers": [],
                        },
                    ],
                    "inline_scripts": [],
                    "counts": {"pages": 0, "resources": 2, "inline_scripts": 0},
                }
            )
        )
        analysis = project / "analysis"
        analysis.mkdir()
        (analysis / "source-index.json").write_text(
            json.dumps(
                {
                    "schema": "capture-source-index/v1",
                    "units": [
                        {
                            "kind": "html",
                            "resource_id": 0,
                            "source_path": "src/page.html",
                        },
                        {
                            "kind": "javascript",
                            "raw_path": "resources/app.js",
                            "resource_id": 0,
                            "url": "https://app.example.test/app.js",
                            "source_path": "src/app.js",
                        },
                        {
                            "kind": "javascript",
                            "raw_path": "resources/rejected.js",
                            "resource_id": 1,
                            "url": "https://app.example.test/rejected.js",
                            "source_path": "src/rejected.js",
                        },
                    ],
                    "summary": {},
                }
            )
        )
        (analysis / "deobfuscation.json").write_text(
            json.dumps(
                {
                    "schema": "capture-safe-deobfuscation/v1",
                    "units": [
                        {
                            "ordinal": 0,
                            "resource_id": 0,
                            "raw_path": "resources/app.js",
                            "output_path": "src/_deobfuscated/app.js",
                            "exit": 0,
                        }
                    ],
                    "summary": {},
                }
            )
        )

        run(ANALYZER, "--project", project)
        artifact = load_artifact(project, API_SURFACE)
        assert artifact["summary"] == {
            "units": 2,
            "callsites": 8,
            "failures": 1,
            "kinds": {
                "fetch": 5,
                "send_beacon": 1,
                "websocket": 1,
                "xhr_open": 1,
            },
            "static_urls": 8,
            "absolute_network_urls": 6,
            "static_methods": 5,
            "invalid_methods": 1,
        }, artifact["summary"]
        assert all("fake.invalid" not in str(row) for row in artifact["callsites"])
        assert {row["source_index_ordinal"] for row in artifact["callsites"]} == {1}
        assert len(artifact["failures"]) == 1, artifact["failures"]
        assert artifact["failures"][0]["source_index_ordinal"] == 2, artifact["failures"]
        assert artifact["failures"][0]["error"].strip(), artifact["failures"]
        users = next(
            row
            for row in artifact["callsites"]
            if row.get("url") == "https://api.example.test/v1/users"
        )
        assert users["url_expression"] == "usersUrl", users
        assert users["method"] == "GET", users
        relative = next(row for row in artifact["callsites"] if row.get("url") == "/relative")
        assert relative["absolute_network_url"] is False
        write = next(
            row
            for row in artifact["callsites"]
            if row.get("url") == "https://api.example.test/write"
        )
        assert write["method"] == "POST", write
        assert write["url_expression"] == 'apiOrigin + "/write"', write
        assert write["method_expression"] == "writeMethod", write
        forbidden = next(
            row
            for row in artifact["callsites"]
            if row.get("url") == "https://api.example.test/forbidden"
        )
        assert forbidden.get("method") is None, forbidden
        assert forbidden.get("method_expression") == '"trace"', forbidden
        assert forbidden.get("method_status") == "invalid", forbidden

        run(sys.executable, ROOT / "scripts/build-source-graph.py", project)
        graph = load_artifact(project, SOURCE_GRAPH)
        api_nodes = [node for node in graph["nodes"] if node["type"] == "api_callsite"]
        assert len(api_nodes) == 8, api_nodes
        assert all(node["source_index_ordinal"] == 1 for node in api_nodes), api_nodes
        assert all(node["id"].startswith("api-call:1:") for node in api_nodes), api_nodes
        request_edges = [edge for edge in graph["edges"] if edge["kind"] == "api_target"]
        assert len(request_edges) == 5, request_edges
        assert not any(
            node.get("url") == "https://api.example.test/forbidden"
            for node in graph["nodes"]
            if node["type"] == "external_url"
        ), graph["nodes"]
        assert any(
            node.get("url") == "wss://socket.example.test/ws"
            for node in graph["nodes"]
            if node["type"] == "external_url"
        )

        run(sys.executable, ROOT / "scripts/refresh-project-readme.py", project)
        readme = (project / "README.md").read_text()
        assert "[analysis/api-surface.json](analysis/api-surface.json)" in readme, readme
        assert "Static browser API callsites: **8**" in readme, readme
        assert "callsites with exact absolute network URLs: **6**" in readme, readme
        assert "proven invalid methods: **1**" in readme, readme
        assert "failed source units: **1**" in readme, readme

        print(
            "static API surface regression: exact callsites + ordered fetch init + method semantics + per-unit fail-closed handling + URL graph + analyst README OK"
        )


if __name__ == "__main__":
    main()
