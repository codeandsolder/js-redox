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
        for path in (raw, src, deob):
            path.parent.mkdir(parents=True, exist_ok=True)
        source = """
fetch("https://api.example.test/v1" + "/users");
fetch("/relative");
fetch("/unknown-method", opts);
navigator.sendBeacon("https://api.example.test/beacon", body);
const xhr = new XMLHttpRequest();
xhr.open("PATCH", "https://api.example.test/items");
new WebSocket("wss://socket.example.test/ws");
function shadow(fetch) { fetch("https://fake.invalid/"); }
"""
        raw.write_text(source)
        src.write_text(source)
        deob.write_text(source)
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
                        }
                    ],
                    "inline_scripts": [],
                    "counts": {"pages": 0, "resources": 1, "inline_scripts": 0},
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
                        }
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

        run(
            sys.executable,
            ROOT / "scripts/analyze-api-surface.py",
            project,
            "--analyzer",
            ANALYZER,
        )
        artifact = load_artifact(project, API_SURFACE)
        assert artifact["summary"] == {
            "units": 1,
            "callsites": 6,
            "failures": 0,
            "kinds": {
                "fetch": 3,
                "send_beacon": 1,
                "websocket": 1,
                "xhr_open": 1,
            },
            "static_urls": 6,
            "absolute_network_urls": 4,
            "static_methods": 4,
        }, artifact["summary"]
        assert all("fake.invalid" not in str(row) for row in artifact["callsites"])
        assert {row["source_index_ordinal"] for row in artifact["callsites"]} == {1}
        relative = next(row for row in artifact["callsites"] if row.get("url") == "/relative")
        assert relative["absolute_network_url"] is False

        run(sys.executable, ROOT / "scripts/build-source-graph.py", project)
        graph = load_artifact(project, SOURCE_GRAPH)
        api_nodes = [node for node in graph["nodes"] if node["type"] == "api_callsite"]
        assert len(api_nodes) == 6, api_nodes
        assert all(node["source_index_ordinal"] == 1 for node in api_nodes), api_nodes
        assert all(node["id"].startswith("api-call:1:") for node in api_nodes), api_nodes
        request_edges = [edge for edge in graph["edges"] if edge["kind"] == "api_target"]
        assert len(request_edges) == 4, request_edges
        assert any(
            node.get("url") == "wss://socket.example.test/ws"
            for node in graph["nodes"]
            if node["type"] == "external_url"
        )
        print("static API surface regression: exact callsites + fail-closed URL graph linkage OK")


if __name__ == "__main__":
    main()
