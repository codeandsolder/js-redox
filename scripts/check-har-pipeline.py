#!/usr/bin/env python3
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL_ROOT = Path(os.environ.get("JSVM_TOOL_ROOT", ROOT / ".cargo-target-nodebug/debug"))
WORK = ROOT / "work/har-pipeline-regression"
HAR = WORK / "fixture.har"
PROJECT = WORK / "project"
TRUNCATED_HAR = WORK / "fixture-truncated.har"
TRUNCATED_PROJECT = WORK / "project-truncated"
BUNDLE_FIXTURE = ROOT / "corpus/generated/reversible-obfuscation/bundle-module-tables.js"
HAR_PROJECT = TOOL_ROOT / "har-project"


def run(*args):
    cp = subprocess.run(
        [str(x) for x in args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=240,
    )
    if cp.returncode:
        raise RuntimeError(
            f"{' '.join(map(str, args))} failed {cp.returncode}:\n{cp.stdout}\n{cp.stderr}"
        )
    return cp


def entry(url, mime, text, when="2026-09-29T00:00:00.000Z"):
    size = len(text.encode())
    return {
        "pageref": "page_1",
        "startedDateTime": when,
        "time": 1,
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
            "headers": [{"name": "content-type", "value": mime}],
            "cookies": [],
            "content": {"size": size, "mimeType": mime, "text": text},
            "redirectURL": "",
            "headersSize": -1,
            "bodySize": size,
        },
        "cache": {},
        "timings": {"send": 0, "wait": 1, "receive": 0},
    }


def main():
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)

    app_js = (
        BUNDLE_FIXTURE.read_text()
        + '\nnew Worker("./worker.js");\n'
        + 'globalThis.__generated = Function("return 7");\n'
        + '//# sourceMappingURL=app.js.map\n'
    )
    html = (
        "<!doctype html><html><body>"
        '<script src="/assets/app.js"></script>'
        "<script>globalThis.inlineHar = 1;</script>"
        "</body></html>"
    )
    worker_js = 'postMessage("ready");\n'
    source_map = {
        "version": 3,
        "file": "app.js",
        "sources": ["src/app-original.js"],
        "names": [],
        "mappings": "",
        "sourcesContent": ["export function originalAnswer() { return 42; }\n"],
    }

    fixture = {
        "log": {
            "version": "1.2",
            "creator": {"name": "capture pipeline regression", "version": "1"},
            "pages": [
                {
                    "startedDateTime": "2026-09-29T00:00:00.000Z",
                    "id": "page_1",
                    "title": "capture pipeline fixture",
                    "pageTimings": {},
                }
            ],
            "entries": [
                entry("https://fixture.invalid/index.html", "text/html", html),
                entry("https://fixture.invalid/assets/app.js", "application/javascript", app_js),
                entry("https://fixture.invalid/assets/worker.js", "application/javascript", worker_js),
                entry(
                    "https://fixture.invalid/assets/app.js.map",
                    "application/json",
                    json.dumps(source_map),
                ),
            ],
        }
    }
    HAR.write_text(json.dumps(fixture))

    raw_fixture = HAR.read_text()
    cut_marker = "https://fixture.invalid/assets/app.js.map"
    cut = raw_fixture.index(cut_marker) + len(cut_marker) + 32
    TRUNCATED_HAR.write_text(raw_fixture[:cut])

    cp = run(
        "uv",
        "run",
        "--no-project",
        "python",
        "scripts/capture-to-project.py",
        HAR,
        PROJECT,
        "--har-project-bin",
        TOOL_ROOT / "har-project",
        "--scanner",
        TOOL_ROOT / "jsvm-lift",
        "--formatter",
        TOOL_ROOT / "js-format",
        "--switch-ir",
        TOOL_ROOT / "switch-ir",
        "--js-refs",
        TOOL_ROOT / "js-refs",
        "--deobfuscator",
        TOOL_ROOT / "deobfuscate-safe",
        "--bundle-inventory",
        TOOL_ROOT / "bundle-unpack",
    )

    manifest = json.loads((PROJECT / "har-manifest.json").read_text())
    assert manifest["schema"] == "har-project/v0"
    assert len(manifest["resources"]) == 4
    assert (PROJECT / "capture-manifest.json").is_file()
    app_resource = next(r for r in manifest["resources"] if r["url"].endswith("/app.js"))
    assert app_resource["sha256"] == hashlib.sha256(app_js.encode()).hexdigest()

    source_index = json.loads((PROJECT / "analysis/source-index.json").read_text())
    js_units = [u for u in source_index["units"] if u["kind"] == "javascript"]
    assert len(js_units) == 3

    deob = json.loads((PROJECT / "analysis/deobfuscation.json").read_text())
    assert deob["summary"]["failed_units"] == 0
    app_deob = next(u for u in deob["units"] if u.get("raw_path") == app_resource["output_path"])
    assert app_deob["input_sha256"] == app_resource["sha256"]
    assert app_deob["input_path"] == app_resource["output_path"]
    assert (PROJECT / app_deob["output_path"]).is_file()
    assert (PROJECT / app_deob["readable_output_path"]).is_file()
    assert app_deob["readable_formatted"] is True

    sourcemaps = json.loads((PROJECT / "analysis/sourcemaps.json").read_text())
    recovered = [
        rec
        for sm in sourcemaps["source_maps"]
        for rec in sm.get("recovered", [])
        if rec.get("status") == "recovered"
    ]
    assert len(recovered) == 1
    assert "originalAnswer" in (PROJECT / recovered[0]["source_path"]).read_text()

    jsrefs = json.loads((PROJECT / "analysis/js-references.json").read_text())
    worker_ref = next(
        ref
        for unit in jsrefs["code_units"]
        for ref in unit["references"]
        if ref["kind"] == "worker"
    )
    assert worker_ref["resolved_url"] == "https://fixture.invalid/assets/worker.js"

    bundles = json.loads((PROJECT / "analysis/bundles.json").read_text())
    assert bundles["summary"]["failed_units"] == 0
    assert bundles["summary"]["bundles"] >= 1
    assert bundles["summary"]["modules"] >= 2
    assert bundles["summary"]["literal_module_dependencies"] >= 1

    analysis = json.loads((PROJECT / "analysis/jsvm/index.json").read_text())
    app_scan = next(u for u in analysis["code_units"] if u.get("raw_path") == app_resource["output_path"])
    assert app_scan["analysis_origin"] == "safe_deobfuscation"
    assert app_scan["path"] == app_deob["output_path"]
    assert app_scan["scanner_exit"] == 0

    graph = json.loads((PROJECT / "analysis/source-graph.json").read_text())
    edge_kinds = graph["summary"]["edge_kinds"]
    assert edge_kinds.get("inline_script") == 1
    assert edge_kinds.get("script_src", 0) >= 1
    assert edge_kinds.get("source_map_source") == 1
    assert edge_kinds.get("js_worker") == 1
    assert edge_kinds.get("safe_deobfuscation") == 3
    assert edge_kinds.get("bundle_payload", 0) >= 1
    assert edge_kinds.get("bundle_module", 0) >= 2
    assert edge_kinds.get("bundle_module_dependency", 0) >= 1

    readme = (PROJECT / "README.md").read_text()
    assert "# Recovered source project" in readme
    assert "src/_readable/" in readme
    assert "## Structured bundle modules" in readme
    assert "## VM analysis" in readme
    assert "## Provenance graph" in readme

    run(HAR_PROJECT, TRUNCATED_HAR, "--output", TRUNCATED_PROJECT)
    truncated_manifest = json.loads(
        (TRUNCATED_PROJECT / "har-manifest.json").read_text()
    )
    assert truncated_manifest["salvaged"] is True
    assert truncated_manifest["parse_error"]
    assert len(truncated_manifest["resources"]) == 3

    print(cp.stdout.rstrip())
    print(
        "PASS: HAR -> exact-safe + readable deob views + source map + generated code "
        f"+ {bundles['summary']['modules']} bundle modules + provenance graph; "
        "truncated HAR salvage preserved"
    )


if __name__ == "__main__":
    main()
