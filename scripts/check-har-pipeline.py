#!/usr/bin/env python3
import hashlib
import json
import runpy
import sys
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
SAFE_MATERIALIZER = ROOT / "scripts/materialize-safe-deobfuscation.py"
GENERATED_CHILD_FIXTURE = ROOT / "corpus/generated/reversible-obfuscation/generated-child-safe.js"
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


def check_optional_helper_timeout():
    run_helper = runpy.run_path(SAFE_MATERIALIZER, run_name="safe_materializer_test")["run"]
    cp = run_helper(
        [sys.executable, "-c", "import time; time.sleep(5)"],
        timeout=0.02,
    )
    assert cp.returncode == 124
    assert "timed out" in cp.stderr


def main():
    check_optional_helper_timeout()
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)

    generated_child = GENERATED_CHILD_FIXTURE.read_text().strip()
    app_js = (
        BUNDLE_FIXTURE.read_text()
        + '\nnew Worker("./worker.js");\n'
        + generated_child + "\n"
        + generated_child + "\n"
        + '//# sourceMappingURL=app.js.map\n'
    )
    html = (
        "<!doctype html><html><body>"
        '<script src="/assets/app.js"></script>'
        '<script type="application/javascript; charset=utf-8">globalThis.inlineHar = 1;</script>'
        '<script type="speculationrules">{"prefetch":[{"source":"list","urls":["/next"]}]}</script>'
        "</body></html>"
    )
    worker_js = 'postMessage("ready");\n'
    source_map = {
        "version": 3,
        "file": "app.js",
        "sources": ["src/intermediate.js", "src/side.js"],
        "names": [],
        "mappings": "AAAA;ACAA",
        "sourcesContent": [
            "export function intermediateAnswer() { return 42; }\n"
            "//# sourceMappingURL=intermediate.js.map\n",
            "export const side = 'preserved';\n",
        ],
    }
    nested_source_map = {
        "version": 3,
        "file": "intermediate.js",
        "sources": ["../original/app-original.ts"],
        "names": [],
        "mappings": "AAAA",
        "sourcesContent": [
            "export function originalAnswer(): number { return 42; }\n"
        ],
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
                entry("https://fixture.invalid/assets/worker-copy.js", "application/javascript", worker_js),
                entry(
                    "https://fixture.invalid/assets/app.js.map",
                    "application/json",
                    json.dumps(source_map),
                ),
                entry(
                    "https://fixture.invalid/assets/src/intermediate.js.map",
                    "application/json",
                    json.dumps(nested_source_map),
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
        "--sourcemap-composer",
        TOOL_ROOT / "sourcemap-compose",
    )

    manifest = json.loads((PROJECT / "har-manifest.json").read_text())
    assert manifest["schema"] == "har-project/v0"
    assert len(manifest["resources"]) == 6
    assert (PROJECT / "capture-manifest.json").is_file()
    speculation = next(
        script
        for script in manifest["inline_scripts"]
        if script.get("script_type") == "speculationrules"
    )
    assert speculation["output_path"].endswith(".json")
    assert json.loads((PROJECT / speculation["output_path"]).read_text())["prefetch"]
    executable_inline = next(
        script
        for script in manifest["inline_scripts"]
        if script.get("output_path", "").endswith(".js")
    )
    assert executable_inline["script_type"] == "application/javascript"
    app_resource = next(r for r in manifest["resources"] if r["url"].endswith("/app.js"))
    assert app_resource["sha256"] == hashlib.sha256(app_js.encode()).hexdigest()

    source_index = json.loads((PROJECT / "analysis/source-index.json").read_text())
    js_units = [u for u in source_index["units"] if u["kind"] == "javascript"]
    assert len(js_units) == 4
    assert source_index["summary"]["unique_javascript_inputs"] == 3
    assert source_index["summary"]["deduplicated_javascript_units"] == 1
    speculation_unit = next(
        unit
        for unit in source_index["units"]
        if unit.get("raw_path") == speculation["output_path"]
    )
    assert speculation_unit["kind"] == "json"

    deob = json.loads((PROJECT / "analysis/deobfuscation.json").read_text())
    assert deob["summary"]["failed_units"] == 0
    assert deob["summary"]["javascript_units"] == 4
    assert deob["summary"]["unique_raw_inputs"] == 3
    assert deob["summary"]["deduplicated_raw_units"] == 1
    assert deob["summary"]["string_recovery_invocations"] == 3
    assert deob["summary"]["safe_deob_invocations"] == 3
    assert deob["summary"]["readable_format_invocations"] == 3
    app_deob = next(u for u in deob["units"] if u.get("raw_path") == app_resource["output_path"])
    assert app_deob["input_sha256"] == app_resource["sha256"]
    assert app_deob["input_path"] == app_resource["output_path"]
    assert (PROJECT / app_deob["output_path"]).is_file()
    assert (PROJECT / app_deob["readable_output_path"]).is_file()
    assert app_deob["readable_formatted"] is True

    sourcemaps = json.loads((PROJECT / "analysis/sourcemaps.json").read_text())
    assert sourcemaps["schema"] == "har-sourcemap-recovery/v1"
    app_sourcemap = next(
        sm for sm in sourcemaps["source_maps"] if sm.get("resource_id") == app_resource["id"]
    )
    recovered = [rec for rec in app_sourcemap["recovered"] if rec.get("status") == "recovered"]
    assert len(recovered) == 2
    direct_text = [(PROJECT / rec["source_path"]).read_text() for rec in recovered]
    assert any("intermediateAnswer" in text for text in direct_text)
    assert any("preserved" in text for text in direct_text)
    composition = app_sourcemap["composition"]
    assert composition["status"] == "composed"
    assert composition["composed_links"] == 1
    assert composition["composed_sources"] == 2
    assert Path(composition["composed_map_path"]).suffix == ".map"
    composed_map = json.loads((PROJECT / composition["composed_map_path"]).read_text())
    assert composed_map["sources"] == [
        "https://fixture.invalid/assets/original/app-original.ts",
        "https://fixture.invalid/assets/src/side.js",
    ]
    final_recovered = [
        rec for rec in app_sourcemap["composed_recovered"] if rec.get("status") == "recovered"
    ]
    assert len(final_recovered) == 2
    final_text = [(PROJECT / rec["source_path"]).read_text() for rec in final_recovered]
    assert any("originalAnswer" in text for text in final_text)
    assert any("preserved" in text for text in final_text)

    jsrefs = json.loads((PROJECT / "analysis/js-references.json").read_text())
    assert jsrefs["summary"]["javascript_units"] == 4
    assert jsrefs["summary"]["unique_input_bodies"] == 3
    assert jsrefs["summary"]["deduplicated_units"] == 1
    assert jsrefs["summary"]["extractor_invocations"] == 3
    worker_ref = next(
        ref
        for unit in jsrefs["code_units"]
        for ref in unit["references"]
        if ref["kind"] == "worker"
    )
    assert worker_ref["resolved_url"] == "https://fixture.invalid/assets/worker.js"

    bundles = json.loads((PROJECT / "analysis/bundles.json").read_text())
    assert bundles["summary"]["failed_units"] == 0
    assert bundles["summary"]["eligible_units"] == 4
    assert bundles["summary"]["unique_input_bodies"] == 3
    assert bundles["summary"]["deduplicated_units"] == 1
    assert bundles["summary"]["inventory_invocations"] == 3
    assert bundles["summary"]["module_format_invocations"] < bundles["summary"]["modules"]
    assert bundles["summary"]["deduplicated_module_formats"] > 0
    assert bundles["summary"]["bundles"] >= 1
    assert bundles["summary"]["modules"] >= 2
    assert bundles["summary"]["literal_module_dependencies"] >= 1
    direct_modules = [
        row
        for row in bundles["modules"]
        if not row.get("chunk_ids")
        and row.get("bundle_kind") not in {"amd_named_modules", "member_named_modules"}
    ]
    assert direct_modules
    assert all("/module-table-" in row["source_path"] for row in direct_modules)
    assert all("/chunk-/" not in row["source_path"] for row in direct_modules)
    module_20001 = next(row for row in bundles["modules"] if row["module_id"] == "20001")
    module_20002 = next(row for row in bundles["modules"] if row["module_id"] == "20002")
    assert module_20001["dependencies"] == ["20002", "40000"]
    assert module_20001["export_names"] == ["name", "named"]
    assert "29999" not in module_20001["dependencies"]
    assert "29996" not in module_20001["dependencies"]
    assert "shadowed" not in module_20001["export_names"]
    assert "shadowedNested" not in module_20001["export_names"]
    assert module_20002["commonjs_export"] is True
    amd_alpha = next(row for row in bundles["modules"] if row["module_id"] == "amd/alpha")
    amd_beta = next(row for row in bundles["modules"] if row["module_id"] == "amd/beta")
    assert amd_alpha["bundle_kind"] == "amd_named_modules"
    assert amd_alpha["dependencies"] == ["amd/beta"]
    assert amd_alpha["export_names"] == ["value"]
    assert amd_beta["export_names"] == ["value"]
    assert "/amd-modules/" in amd_alpha["source_path"]
    assert bundles["summary"]["amd_named_modules"] >= 3
    assert any(row["module_id"] == "amd/local" for row in bundles["modules"])
    embedded_alpha = next(
        row for row in bundles["modules"] if row["module_id"] == "embedded/alpha"
    )
    embedded_beta = next(
        row for row in bundles["modules"] if row["module_id"] == "embedded/beta"
    )
    embedded_no_deps = next(
        row for row in bundles["modules"] if row["module_id"] == "embedded/no-deps"
    )
    assert embedded_alpha["bundle_kind"] == "member_named_modules"
    assert embedded_alpha["dependencies"] == ["embedded/beta"]
    assert embedded_beta["dependencies"] == []
    assert embedded_no_deps["dependencies"] == []
    assert "/member-named-modules/" in embedded_alpha["source_path"]
    assert bundles["summary"]["member_named_modules"] >= 2
    assert not any(row["module_id"] == "not-amd/local-helper" for row in bundles["modules"])
    assert not any(row["module_id"] == "not-amd/member-helper" for row in bundles["modules"])
    assert not any(
        row["module_id"] == "not-amd/single-loaderlike"
        for row in bundles["modules"]
    )
    load_alpha = next(
        row for row in bundles["modules"] if row["module_id"] == "loadmodules/alpha"
    )
    global_alpha = next(
        row for row in bundles["modules"] if row["module_id"] == "global/alpha"
    )
    assert load_alpha["bundle_kind"] == "member_named_modules"
    assert load_alpha["dependencies"] == ["loadmodules/beta"]
    assert global_alpha["bundle_kind"] == "member_named_modules"
    assert global_alpha["dependencies"] == ["global/beta"]
    assert not any(
        row["module_id"] == "not-module-inline-function"
        for row in bundles["modules"]
    )
    module_20001_source = (PROJECT / module_20001["source_path"]).read_text()
    assert "exports.name = require(20002).name" in module_20001_source
    assert "Static export names: name, named" in module_20001_source
    assert bundles["summary"]["modules_with_named_exports"] >= 1
    assert bundles["summary"]["commonjs_export_modules"] >= 1
    module_readme = (PROJECT / "src/_modules/README.md").read_text()
    assert "Recovered structured modules" in module_readme
    assert "module 20001" in module_readme
    assert "name, named" in module_readme

    analysis = json.loads((PROJECT / "analysis/jsvm/index.json").read_text())
    app_scan = next(u for u in analysis["code_units"] if u.get("raw_path") == app_resource["output_path"])
    assert app_scan["analysis_origin"] == "safe_deobfuscation"
    assert app_scan["path"] == app_deob["output_path"]
    assert app_scan["scanner_exit"] == 0
    assert analysis["scanner_invocations"] == 4
    assert analysis["deduplicated_scans"] == 2
    generated_recovery = json.loads(
        (PROJECT / "analysis/generated-recovery.json").read_text()
    )
    assert generated_recovery["summary"]["generated_units"] == 2
    assert generated_recovery["summary"]["unique_raw_inputs"] == 1
    assert generated_recovery["summary"]["deduplicated_units"] == 1
    assert generated_recovery["summary"]["safe_deobfuscation"] == 2

    graph = json.loads((PROJECT / "analysis/source-graph.json").read_text())
    edge_kinds = graph["summary"]["edge_kinds"]
    assert edge_kinds.get("inline_script") == 2
    assert edge_kinds.get("script_src", 0) >= 1
    assert edge_kinds.get("source_map_source") == 2
    assert edge_kinds.get("source_map_composed") == 1
    assert edge_kinds.get("source_map_chain") == 1
    assert edge_kinds.get("source_map_chain_resource") == 1
    assert edge_kinds.get("source_map_composed_source") == 2
    assert edge_kinds.get("js_worker") == 1
    assert edge_kinds.get("safe_deobfuscation") == 4
    assert edge_kinds.get("generated_code") == 2
    assert edge_kinds.get("generated_safe_recovery") == 2
    assert edge_kinds.get("bundle_payload", 0) >= 1
    assert edge_kinds.get("bundle_module", 0) >= 2
    assert edge_kinds.get("bundle_module_dependency", 0) >= 1
    graph_module_20001 = next(
        node
        for node in graph["nodes"]
        if node.get("type") == "bundle_module" and node.get("module_id") == "20001"
    )
    assert graph_module_20001["export_names"] == ["name", "named"]
    graph_module_40000_peer = next(
        node
        for node in graph["nodes"]
        if node.get("type") == "bundle_module"
        and node.get("module_id") == "40000"
        and node.get("chunk_ids") == ["78"]
    )
    peer_dependency = next(
        edge
        for edge in graph["edges"]
        if edge.get("from") == graph_module_20001["id"]
        and edge.get("kind") == "bundle_module_dependency"
        and edge.get("module_id") == "40000"
    )
    assert peer_dependency["to"] == graph_module_40000_peer["id"]
    assert peer_dependency["excluded_nested_module_tables"] == 1
    assert not any(
        edge.get("from") == graph_module_20001["id"]
        and edge.get("kind") == "bundle_module_dependency_unresolved"
        and edge.get("module_id") == "40000"
        for edge in graph["edges"]
    )

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
    assert len(truncated_manifest["resources"]) == 4

    print(cp.stdout.rstrip())
    print(
        "PASS: HAR -> exact-safe + readable deob views + source map + generated code "
        f"+ {bundles['summary']['modules']} bundle modules + provenance graph; "
        "truncated HAR salvage preserved"
    )


if __name__ == "__main__":
    main()
