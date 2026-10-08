#!/usr/bin/env python3
"""Regression: CDP script ids are target/session-local, not globally unique."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "work" / "runtime-session-scope-regression"
CAPTURE = WORK / "capture"
ANALYZER = ROOT / "scripts" / "analyze-runtime-scripts.py"


def digest(source: str) -> str:
    return hashlib.sha256(source.encode()).hexdigest()


def event(session: str, script_id: str, source: str, url: str = "", parent: str | None = None) -> dict:
    row = {
        "cdpSession": session,
        "scriptId": script_id,
        "url": url,
        "executionContextId": 1,
        "stackTrace": None,
        "captured": {
            "kind": "javascript",
            "sha256": digest(source),
            "size": len(source.encode()),
            "path": f"runtime-scripts/{digest(source)}.js",
        },
    }
    if parent is not None:
        row["stackTrace"] = {
            "callFrames": [
                {
                    "functionName": "eval",
                    "scriptId": parent,
                    "url": "",
                    "lineNumber": 0,
                    "columnNumber": 0,
                }
            ]
        }
    return row


def main() -> None:
    shutil.rmtree(WORK, ignore_errors=True)
    runtime = CAPTURE / "runtime-scripts"
    runtime.mkdir(parents=True)

    main_parent = "globalThis.mainParent = 1;"
    main_child = "globalThis.mainChild = 2;"
    frame_parent = "globalThis.frameParent = 3;"
    frame_child = "globalThis.frameChild = 4;"
    srcdoc_inline = "globalThis.srcdocInline = 5;"
    for source in (main_parent, main_child, frame_parent, frame_child, srcdoc_inline):
        (runtime / f"{digest(source)}.js").write_bytes(source.encode())

    events = [
        event("main", "1", main_parent, "https://main.invalid/root.js"),
        event("main", "2", main_child, parent="1"),
        event("oopif-1", "1", frame_parent, "https://frame.invalid/root.js"),
        event("oopif-1", "2", frame_child, parent="1"),
        {
            **event("oopif-2", "1", srcdoc_inline, "about:srcdoc"),
            "startLine": 0,
            "startColumn": 17,
            "endLine": 0,
            "endColumn": 45,
            "executionContextAuxData": {"isDefault": True, "frameId": "fixture-frame"},
            "embedderName": "about:srcdoc",
        },
    ]
    (CAPTURE / "runtime-scripts.json").write_text(json.dumps(events))
    (CAPTURE / "network.json").write_text(json.dumps([
        {"url": "https://main.invalid/root.js"},
        {"url": "https://frame.invalid/root.js"},
    ]))

    output = WORK / "runtime-analysis.json"
    subprocess.run(
        [sys.executable, str(ANALYZER), str(CAPTURE), "--output", str(output)],
        cwd=ROOT,
        check=True,
    )
    report = json.loads(output.read_text())
    assert report["summary"]["anonymous_runtime_sources"] == 0, report["summary"]
    assert report["summary"]["classifications"] == {
        "document_inline_script": 1,
        "generated_runtime": 2,
        "network_observed": 2,
    }, report["summary"]

    by_hash = {row["sha256"]: row for row in report["sources"]}
    main_row = by_hash[digest(main_child)]
    frame_row = by_hash[digest(frame_child)]
    assert main_row["cdp_sessions"] == ["main"], main_row
    assert frame_row["cdp_sessions"] == ["oopif-1"], frame_row
    assert main_row["script_instances"] == [{
        "cdp_session": "main", "script_id": "2", "execution_context_id": 1
    }], main_row
    assert frame_row["script_instances"] == [{
        "cdp_session": "oopif-1", "script_id": "2", "execution_context_id": 1
    }], frame_row
    assert main_row["generated"]["root_sha256s"] == [digest(main_parent)], main_row
    assert frame_row["generated"]["root_sha256s"] == [digest(frame_parent)], frame_row
    assert main_row["generated"]["origins"][0]["cdp_session"] == "main", main_row
    assert frame_row["generated"]["origins"][0]["cdp_session"] == "oopif-1", frame_row
    srcdoc_row = by_hash[digest(srcdoc_inline)]
    assert srcdoc_row["classification"] == "document_inline_script", srcdoc_row
    assert srcdoc_row["document_inline_origins"] == [{
        "cdp_session": "oopif-2",
        "script_id": "1",
        "url": "about:srcdoc",
        "frame_id": "fixture-frame",
        "start_line": 0,
        "start_column": 17,
        "end_line": 0,
        "end_column": 45,
        "embedder_name": "about:srcdoc",
    }], srcdoc_row
    print("PASS: CDP script ids stay session-scoped and ephemeral document-inline provenance is preserved")


if __name__ == "__main__":
    main()
