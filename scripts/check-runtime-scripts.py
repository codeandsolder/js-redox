#!/usr/bin/env python3
"""Regression for recorder runtime-script provenance classification."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "work/runtime-script-regression"
ANALYZER = ROOT / "scripts/analyze-runtime-scripts.py"
sys.path.insert(0, str(ROOT / "scripts"))
from capture_pipeline import detect_capture  # noqa: E402


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
    sources = [network, inline, exact, model, xfor, instrumentation]

    for source in sources:
        (runtime / f"{digest(source)}.js").write_text(source)
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
                "url": "https://fixture.invalid/app.js" if source == network else "",
                "captured": {
                    "kind": "javascript",
                    "sha256": sha,
                    "size": len(source.encode()),
                    "path": f"runtime-scripts/{sha}.js",
                },
            }
        )
    (capture / "runtime-scripts.json").write_text(json.dumps(events))

    assert detect_capture(capture) == "recorder"
    report_path = WORK / "runtime-analysis.json"
    subprocess.run(
        [sys.executable, str(ANALYZER), str(capture), "--output", str(report_path)],
        cwd=ROOT,
        check=True,
    )
    report = json.loads(report_path.read_text())
    summary = report["summary"]
    assert summary["script_parsed_events"] == 6, summary
    assert summary["unique_javascript_sources"] == 6, summary
    assert summary["classifications"] == {
        "alpine_expression": 3,
        "capture_instrumentation": 1,
        "inline_script": 1,
        "network_response": 1,
    }, summary
    assert summary["alpine_dom_mapped_sources"] == 3, summary
    assert summary["alpine_expression_shapes"] == 3, summary
    assert summary["anonymous_runtime_sources"] == 0, summary
    mappings = {
        source["alpine"]["dom_mapping_kind"]
        for source in report["sources"]
        if source["classification"] == "alpine_expression"
    }
    assert mappings == {"exact", "x-model-setter", "x-for-rhs"}, mappings
    print("PASS: recorder runtime provenance -> network/inline/Alpine/instrumentation with DOM mappings")


if __name__ == "__main__":
    main()
