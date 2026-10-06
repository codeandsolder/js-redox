#!/usr/bin/env python3
import base64
import json
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL_ROOT = Path(os.environ.get("JSVM_TOOL_ROOT", ROOT / ".cargo-target-nodebug/debug"))
WORK = ROOT / "work/wasm-capture-regression"
HAR = WORK / "fixture.har"
PROJECT = WORK / "project"

WASM = bytes.fromhex(
    "0061736d01000000"
    "0105016000017f"
    "03020100"
    "0707010372756e0000"
    "0a0601040041070b"
)
WASM_B64 = base64.b64encode(WASM).decode()

def run(*args):
    cp = subprocess.run([str(x) for x in args], cwd=ROOT, text=True,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    if cp.returncode:
        raise RuntimeError(f"{' '.join(map(str, args))} failed {cp.returncode}:\n{cp.stdout}\n{cp.stderr}")
    return cp

def entry(url, mime, text, *, encoding=None):
    content = {"size": len(text), "mimeType": mime, "text": text}
    if encoding:
        content["encoding"] = encoding
    return {
        "pageref": "page_1",
        "startedDateTime": "2026-10-06T00:00:00.000Z",
        "time": 1,
        "request": {"method": "GET", "url": url, "httpVersion": "HTTP/2", "headers": [],
                    "queryString": [], "cookies": [], "headersSize": -1, "bodySize": 0},
        "response": {"status": 200, "statusText": "OK", "httpVersion": "HTTP/2",
                     "headers": [{"name": "content-type", "value": mime}], "cookies": [],
                     "content": content, "redirectURL": "", "headersSize": -1, "bodySize": len(text)},
        "cache": {},
        "timings": {"send": 0, "wait": 1, "receive": 0},
    }

def main():
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    html = f'<!doctype html><script>const embedded = "{WASM_B64}";</script>'
    fixture = {"log": {"version": "1.2",
        "creator": {"name": "wasm capture regression", "version": "1"},
        "pages": [{"startedDateTime": "2026-10-06T00:00:00.000Z", "id": "page_1",
                   "title": "wasm fixture", "pageTimings": {}}],
        "entries": [
            entry("https://fixture.invalid/index.html", "text/html", html),
            entry("https://fixture.invalid/module.wasm", "application/wasm", WASM_B64, encoding="base64"),
        ]}}
    HAR.write_text(json.dumps(fixture))
    run(TOOL_ROOT / "har-project", HAR, "--output", PROJECT)
    manifest = json.loads((PROJECT / "har-manifest.json").read_text())
    wasm_resource = next(row for row in manifest["resources"] if row["kind"] == "wasm")
    assert wasm_resource["output_path"].endswith(".wasm")
    assert (PROJECT / wasm_resource["output_path"]).read_bytes() == WASM
    run("uv", "run", "--no-project", "python", "scripts/materialize-wasm.py",
        PROJECT, "--wasm-redox", TOOL_ROOT / "wasm-redox")
    index = json.loads((PROJECT / "analysis/wasm/index.json").read_text())
    assert index["summary"] == {"modules": 1, "direct_resources": 1,
        "inline_extracted": 1, "failed": 0, "origins": 2}
    module = index["modules"][0]
    assert module["status"] == "ok"
    assert module["has_direct_resource"] is True
    assert module["has_inline_origin"] is True
    assert (PROJECT / module["report_path"]).is_file()
    assert (PROJECT / module["deep_path"]).is_file()
    run("uv", "run", "--no-project", "python", "scripts/build-source-graph.py", PROJECT)
    graph = json.loads((PROJECT / "analysis/source-graph.json").read_text())
    wasm_nodes = [node for node in graph["nodes"] if node["type"] == "wasm_module"]
    assert len(wasm_nodes) == 1
    wasm_edges = [edge for edge in graph["edges"] if edge["to"] == wasm_nodes[0]["id"]]
    assert {edge["kind"] for edge in wasm_edges} == {"wasm_resource", "wasm_inline_base64"}
    print("wasm capture regression: direct + inline dedup + provenance OK")

if __name__ == "__main__":
    main()
