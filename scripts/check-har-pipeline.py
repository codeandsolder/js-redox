#!/usr/bin/env python3
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "work" / "har-pipeline-regression"
HAR = WORK / "fixture.har"
PROJECT = WORK / "project"
TRUNCATED_HAR = WORK / "fixture-truncated.har"
TRUNCATED_PROJECT = WORK / "project-truncated"
PAYLOAD = ROOT / "corpus/generated/js-virtualizer/vm-obfuscated.js"
HAR_PROJECT = ROOT / ".cargo-target-nodebug/debug/har-project"


def run(*args):
    cp = subprocess.run(
        [str(x) for x in args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=180,
    )
    if cp.returncode:
        raise RuntimeError(
            f"{' '.join(map(str,args))} failed {cp.returncode}:\n{cp.stdout}\n{cp.stderr}"
        )
    return cp


def main():
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    source = PAYLOAD.read_text()
    mapped_js = (
        'console.log(42);\n'
        'new Worker("./fixture-worker.js");\n'
        '//# sourceMappingURL=app.min.js.map\n'
    )
    source_map = {
        "version": 3,
        "file": "app.min.js",
        "sources": ["src/app-original.js"],
        "names": [],
        "mappings": "",
        "sourcesContent": ["export function answer() {\n  return 42;\n}\n"],
    }

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

    fixture = {
        "log": {
            "version": "1.2",
            "creator": {"name": "jsvm-lift regression", "version": "0"},
            "pages": [
                {
                    "startedDateTime": "2026-09-29T00:00:00.000Z",
                    "id": "page_1",
                    "title": "embedded VM fixture",
                    "pageTimings": {},
                }
            ],
            "entries": [
                entry("https://fixture.invalid/assets/vm.js?build=1", "application/javascript", source),
                entry("https://fixture.invalid/assets/app.min.js", "application/javascript", mapped_js),
                entry(
                    "https://fixture.invalid/assets/app.min.js.map",
                    "application/json",
                    json.dumps(source_map),
                ),
            ],
        }
    }
    HAR.write_text(json.dumps(fixture))


    # Simulate a browser/export crash in the middle of the final response.
    raw_fixture = HAR.read_text()
    cut_marker = "https://fixture.invalid/assets/app.min.js.map"
    cut = raw_fixture.index(cut_marker) + len(cut_marker) + 32
    TRUNCATED_HAR.write_text(raw_fixture[:cut])

    run(HAR_PROJECT, HAR, "--output", PROJECT)
    run("uv", "run", "python", "scripts/materialize-har-source.py", PROJECT)
    run("uv", "run", "python", "scripts/recover-sourcemaps.py", PROJECT)
    run("uv", "run", "python", "scripts/scan-js-references.py", PROJECT)
    run("uv", "run", "python", "scripts/materialize-safe-deobfuscation.py", PROJECT)
    run("uv", "run", "python", "scripts/scan-har-project.py", PROJECT)
    run("uv", "run", "python", "scripts/build-source-graph.py", PROJECT)
    run("uv", "run", "python", "scripts/refresh-project-readme.py", PROJECT)

    manifest = json.loads((PROJECT / "har-manifest.json").read_text())
    assert manifest["schema"] == "har-project/v0"
    resources = manifest["resources"]
    assert len(resources) == 3
    resource = resources[0]
    assert resource["kind"] == "javascript"
    assert resource["sha256"] == hashlib.sha256(source.encode()).hexdigest()

    source_index = json.loads((PROJECT / "analysis/source-index.json").read_text())
    js_units = [u for u in source_index["units"] if u["kind"] == "javascript"]
    assert len(js_units) == 2
    assert all(u["transform"] == "oxc_parse_codegen" for u in js_units)

    deob = json.loads((PROJECT / "analysis/deobfuscation.json").read_text())
    assert deob["schema"] == "har-safe-deobfuscation/v1"
    assert deob["summary"]["javascript_units"] == 2
    assert deob["summary"]["failed_units"] == 0
    assert deob["summary"]["string_recovery_replacements"] == 0
    assert len(deob["units"]) == 2
    assert all((PROJECT / u["output_path"]).is_file() for u in deob["units"])
    assert all("arithmetic_state_proofs" in u for u in deob["units"])
    assert all("string_recovery_report_path" in u for u in deob["units"])

    string_recovery = json.loads(
        (PROJECT / "analysis/string-recovery.json").read_text()
    )
    assert string_recovery["schema"] == "har-static-string-recovery/v1"
    assert string_recovery["safe_static_only"] is True
    assert string_recovery["summary"]["javascript_units"] == 2
    assert string_recovery["summary"]["failed_units"] == 0
    assert string_recovery["summary"]["replacements"] == 0

    sourcemaps = json.loads((PROJECT / "analysis/sourcemaps.json").read_text())
    recovered_maps = [
        x for m in sourcemaps["source_maps"]
        for x in m.get("recovered", [])
        if x.get("status") == "recovered"
    ]
    assert len(recovered_maps) == 1
    original = PROJECT / recovered_maps[0]["source_path"]
    assert "return 42" in original.read_text()

    analysis = json.loads((PROJECT / "analysis/jsvm/index.json").read_text())
    assert len(analysis["code_units"]) == 2
    dynamic = analysis["dynamic_code_units"]
    assert len(dynamic) >= 1
    first = dynamic[0]
    assert first["body_bytes"] > 250_000
    assert first["handler_tables"] >= 1
    assert (PROJECT / first["raw_dump"]).is_file()
    assert (PROJECT / first["source_path"]).is_file()

    report = json.loads((PROJECT / analysis["code_units"][0]["report"]).read_text())
    embedded = report["embedded"]
    assert embedded
    biggest = max(
        (
            table["function_values"]
            for node in embedded
            for table in node.get("handler_function_tables", [])
        ),
        default=0,
    )
    assert biggest >= 74, biggest

    jsrefs = json.loads((PROJECT / "analysis/js-references.json").read_text())
    assert jsrefs["summary"]["references"] == 1
    worker_ref = next(
        ref
        for unit in jsrefs["code_units"]
        for ref in unit["references"]
        if ref["kind"] == "worker"
    )
    assert worker_ref["resolved_url"] == "https://fixture.invalid/assets/fixture-worker.js"

    graph = json.loads((PROJECT / "analysis/source-graph.json").read_text())
    edge_kinds = graph["summary"]["edge_kinds"]
    assert edge_kinds.get("generated_code") == 1
    assert edge_kinds.get("source_map_source") == 1
    assert edge_kinds.get("source_map", 0) >= 1
    assert edge_kinds.get("js_worker") == 1
    assert edge_kinds.get("safe_deobfuscation") == 2
    deob_nodes = [node for node in graph["nodes"] if node["type"] == "deobfuscated_source"]
    assert len(deob_nodes) == 2
    assert all("arithmetic_state_proofs" in node for node in deob_nodes)
    assert all("string_recovery_replacements" in node for node in deob_nodes)
    assert all(node["string_recovery_replacements"] == 0 for node in deob_nodes)
    worker_edge = next(edge for edge in graph["edges"] if edge["kind"] == "js_worker")
    worker_node = next(node for node in graph["nodes"] if node["id"] == worker_edge["to"])
    assert worker_node["type"] == "external_url"
    assert worker_node["url"] == "https://fixture.invalid/assets/fixture-worker.js"

    readme = (PROJECT / "README.md").read_text()
    assert "## Start here" in readme
    assert "## Safe static deobfuscation" in readme
    assert "Encoded string-decoder recovery: **0** call sites across **0** unit(s)" in readme
    assert "Proven arithmetic-state unflattenings: **0**" in readme
    assert "## VM analysis" in readme
    assert "## Provenance graph" in readme
    assert "resources/ is capture truth" in readme

    run(HAR_PROJECT, TRUNCATED_HAR, "--output", TRUNCATED_PROJECT)
    truncated_manifest = json.loads(
        (TRUNCATED_PROJECT / "har-manifest.json").read_text()
    )
    assert truncated_manifest["salvaged"] is True
    assert truncated_manifest["parse_error"]
    assert len(truncated_manifest["resources"]) == 2

    print(
        "PASS: HAR -> resources/src/analysis/source graph + truncated HAR salvage; "
        f"{len(dynamic)} dynamic unit(s); 1 source-map original; "
        f"1 worker edge; biggest embedded handler table={biggest}"
    )


if __name__ == "__main__":
    main()
