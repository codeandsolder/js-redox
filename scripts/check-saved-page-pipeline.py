#!/usr/bin/env python3
import json
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL_ROOT = Path(os.environ.get("JSVM_TOOL_ROOT", ROOT / ".cargo-target-nodebug/debug"))
WORK = ROOT / "work/saved-page-pipeline-regression"
PAGE = WORK / "Saved.html"
ASSETS = WORK / "Saved_files"
PROJECT = WORK / "project"
BUNDLE_FIXTURE = ROOT / "corpus/generated/reversible-obfuscation/bundle-module-tables.js"


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


def main():
    shutil.rmtree(WORK, ignore_errors=True)
    ASSETS.mkdir(parents=True)
    execution_marker = WORK / "hostile-js-was-executed.txt"

    PAGE.write_bytes(
        b"<!-- saved from url=(0032)https://example.invalid/demo -->\n"
        b'<!doctype html><html><head><meta charset="windows-1252">\n'
        b'  <link rel="stylesheet" href="./Saved_files/site.css">\n'
        b"</head><body>\n"
        b'  <script type="text/javascript" charset="windows-1252" src="./Saved_files/app.js"></script>\n'
        b'  <script type="module">import "./Saved_files/inline-dep.js"; console.log("\xa9");</script>\n'
        b'  <script type="speculationrules">{"prefetch":[{"source":"list","urls":["/next"]}]}</script>\n'
        b"</body></html>\n"
    )

    app = (
        BUNDLE_FIXTURE.read_text()
        + '\nnew Worker("./worker.js");\n'
        + 'const fakeSourceMap = "/*# sourceMappingURL=fake-string.js.map */";\n'
        + 'const fakeRuntimeMap = "/*# sourceMappingURL=data:application/json;base64," + globalThis.payload + " */";\n'
        + f'if (typeof require === "function") require("node:fs").writeFileSync({json.dumps(execution_marker.as_posix())}, "executed");\n'
        + '//# sourceMappingURL=app.js.map\n'
    )
    (ASSETS / "app.js").write_text(app)
    (ASSETS / "worker.js").write_text('postMessage("ready");\n')
    (ASSETS / "inline-dep.js").write_text('export const dep = 42;\n')
    (ASSETS / "site.css").write_text('body { color: #123; }\n')
    outside = WORK / "do-not-ingest.txt"
    outside.write_text("local secret that a saved page must not pull into the project\n")
    (ASSETS / "linked-secret.txt").symlink_to(outside)

    source_map = {
        "version": 3,
        "file": "app.js",
        "sources": ["src/app-original.js"],
        "names": [],
        "mappings": "",
        "sourcesContent": ["export function originalAnswer() { return 42; }\n"],
    }
    (ASSETS / "app.js.map").write_text(json.dumps(source_map))

    cp = run(
        "uv",
        "run",
        "--no-project",
        "python",
        "scripts/capture-to-project.py",
        PAGE,
        PROJECT,
        "--capture-import",
        TOOL_ROOT / "capture-import",
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
        "--bundle-materializer",
        TOOL_ROOT / "bundle-materialize",
        "--sourcemaps",
        TOOL_ROOT / "sourcemaps",
    )

    manifest = json.loads((PROJECT / "capture-manifest.json").read_text())
    assert manifest["schema"] == "capture-project/v1"
    assert manifest["source"]["kind"] == "saved_page_complete"
    assert manifest["source"]["original_page_url"] == "https://example.invalid/demo"
    assert len(manifest["resources"]) == 6
    assert any(r["kind"] == "javascript" for r in manifest["resources"])
    assert any(
        ref["kind"] == "script_src"
        for r in manifest["resources"]
        for ref in r.get("references", [])
    )
    app_resource = next(r for r in manifest["resources"] if r["url"].endswith("/app.js"))
    app_source_maps = [
        ref for ref in app_resource.get("references", []) if ref.get("kind") == "source_map"
    ]
    assert [ref["raw"] for ref in app_source_maps] == ["app.js.map"]
    assert all("fake-string.js.map" not in str(ref) for ref in app_resource.get("references", []))
    assert sum(bool(s.get("output_path")) for s in manifest["inline_scripts"]) == 2
    external_app = next(
        script
        for script in manifest["inline_scripts"]
        if str(script.get("src", "")).endswith("app.js")
    )
    assert external_app["script_type"] == "text/javascript"
    assert external_app["charset"] == "windows-1252"
    assert external_app["parent_document_encoding"] == "windows-1252"
    assert external_app["parent_decode_source"] == "html-meta"
    assert external_app["parent_decode_uncertain"] is False
    page_resource = next(r for r in manifest["resources"] if r["url"].endswith("/Saved.html"))
    assert page_resource["document_encoding"] == "windows-1252"
    assert page_resource["document_decode_source"] == "html-meta"
    assert page_resource["document_decode_had_errors"] is False
    assert page_resource["document_decode_uncertain"] is False
    module_inline = next(
        script for script in manifest["inline_scripts"]
        if script.get("script_type") == "module"
    )
    assert "©" in (PROJECT / module_inline["output_path"]).read_text()
    speculation = next(
        script
        for script in manifest["inline_scripts"]
        if script.get("script_type") == "speculationrules"
    )
    assert speculation["output_path"].endswith(".json")
    assert json.loads((PROJECT / speculation["output_path"]).read_text())["prefetch"]

    source_index = json.loads((PROJECT / "analysis/source-index.json").read_text())
    assert sum(u["kind"] == "javascript" for u in source_index["units"]) == 4
    speculation_unit = next(
        unit
        for unit in source_index["units"]
        if unit.get("raw_path") == speculation["output_path"]
    )
    assert speculation_unit["kind"] == "json"

    sourcemaps = json.loads((PROJECT / "analysis/sourcemaps.json").read_text())
    assert all(sm.get("raw_reference") != "fake-string.js.map" for sm in sourcemaps["source_maps"])
    assert all(sm.get("status") != "decode_error" for sm in sourcemaps["source_maps"])
    recovered = [
        rec
        for sm in sourcemaps["source_maps"]
        for rec in sm.get("recovered", [])
        if rec.get("status") == "recovered"
    ]
    assert len(recovered) == 1
    recovered_source = PROJECT / recovered[0]["source_path"]
    assert "originalAnswer" in recovered_source.read_text()

    refs = json.loads((PROJECT / "analysis/js-references.json").read_text())
    kinds = {
        ref["kind"]
        for unit in refs["code_units"]
        for ref in unit.get("references", [])
    }
    assert "worker" in kinds
    assert "import_static" in kinds

    deob = json.loads((PROJECT / "analysis/deobfuscation.json").read_text())
    assert deob["summary"]["failed_units"] == 0

    bundles = json.loads((PROJECT / "analysis/bundles.json").read_text())
    assert bundles["summary"]["failed_units"] == 0
    assert bundles["summary"]["bundles"] >= 1
    assert bundles["summary"]["modules"] >= 2
    amd_alpha = next(row for row in bundles["modules"] if row["module_id"] == "amd/alpha")
    assert amd_alpha["bundle_kind"] == "amd_named_modules"
    assert amd_alpha["dependencies"] == ["amd/beta"]
    assert amd_alpha["export_names"] == ["value"]
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
    assert bundles["summary"]["literal_module_dependencies"] >= 1
    direct_modules = [
        row
        for row in bundles["modules"]
        if not row.get("chunk_ids")
        and row.get("bundle_kind")
        not in {"amd_named_modules", "member_named_modules", "browserify_module_table"}
    ]
    assert direct_modules
    assert all("/module-table-" in row["source_path"] for row in direct_modules)
    assert all("/chunk-/" not in row["source_path"] for row in direct_modules)
    browserify_alpha = next(row for row in bundles["modules"] if row["module_id"] == "50001")
    browserify_beta = next(row for row in bundles["modules"] if row["module_id"] == "50002")
    assert browserify_alpha["bundle_kind"] == "browserify_module_table"
    assert browserify_alpha["dependencies"] == ["50002"]
    assert browserify_alpha["dependency_map"] == {
        "./beta": "50002",
        "external-package": "external-package",
    }
    assert browserify_alpha["export_names"] == ["value"]
    assert browserify_beta["commonjs_export"] is True
    returned_browserify = next(row for row in bundles["modules"] if row["module_id"] == "51001")
    assert returned_browserify["bundle_kind"] == "browserify_module_table"
    assert returned_browserify["dependencies"] == ["51002"]
    assert returned_browserify["dependency_map"] == {
        "./beta": "51002",
        "external-missing": "external-missing",
    }
    assert not any(row["module_id"] in {"52001", "52002"} for row in bundles["modules"])
    rspack_alpha = next(row for row in bundles["modules"] if row["module_id"] == "rspA")
    rspack_beta = next(row for row in bundles["modules"] if row["module_id"] == "rspB")
    assert rspack_alpha["bundle_kind"] == "webpack_modules_binding"
    assert rspack_alpha["dependencies"] == ["rspB"]
    assert rspack_alpha["export_names"] == ["value"]
    assert rspack_beta["commonjs_export"] is True
    runtime_alpha = next(row for row in bundles["modules"] if row["module_id"] == "runA")
    runtime_beta = next(row for row in bundles["modules"] if row["module_id"] == "runB")
    assert runtime_alpha["bundle_kind"] == "webpack_runtime_module_table"
    assert runtime_alpha["dependencies"] == ["runB"]
    assert runtime_alpha["export_names"] == ["value"]
    assert runtime_beta["commonjs_export"] is True
    array_alpha = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "0" and row["bundle_kind"] == "webpack_array_bootstrap"
    )
    array_beta = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "1" and row["bundle_kind"] == "webpack_array_bootstrap"
    )
    assert array_alpha["dependencies"] == ["1"]
    assert array_alpha["export_names"] == ["value"]
    assert array_beta["commonjs_export"] is True
    named_array_alpha = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "0" and row["bundle_kind"] == "webpack_modules_binding"
    )
    named_array_beta = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "1" and row["bundle_kind"] == "webpack_modules_binding"
    )
    assert named_array_alpha["dependencies"] == ["1"]
    assert named_array_alpha["export_names"] == ["namedArray"]
    assert named_array_beta["commonjs_export"] is True
    arrow_array_alpha = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "3" and row["bundle_kind"] == "webpack_array_bootstrap"
    )
    arrow_array_beta = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "4" and row["bundle_kind"] == "webpack_array_bootstrap"
    )
    assert arrow_array_alpha["dependencies"] == ["4"]
    assert arrow_array_alpha["export_names"] == ["arrowValue"]
    assert arrow_array_beta["commonjs_export"] is True
    assert not any(
        row["module_id"] == "7" and row["bundle_kind"] == "webpack_array_bootstrap"
        for row in bundles["modules"]
    )
    push_array_alpha = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "5"
        and row["bundle_kind"] == "webpack_chunk_push"
        and row["chunk_ids"] == ["94"]
    )
    push_array_beta = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "6"
        and row["bundle_kind"] == "webpack_chunk_push"
        and row["chunk_ids"] == ["94"]
    )
    assert push_array_alpha["dependencies"] == ["6"]
    assert push_array_alpha["export_names"] == ["pushArray"]
    assert push_array_beta["commonjs_export"] is True
    assert not any(
        row["module_id"] == "8"
        and row["bundle_kind"] == "webpack_chunk_push"
        and row["chunk_ids"] == ["95"]
        for row in bundles["modules"]
    )
    assert not any(
        row["module_id"] == "0"
        and row["bundle_kind"] == "webpack_chunk_push"
        and row["chunk_ids"] == ["96"]
        for row in bundles["modules"]
    )
    namespaced_push = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "0"
        and row["bundle_kind"] == "webpack_chunk_push"
        and row["chunk_ids"] == ["97"]
    )
    assert namespaced_push["commonjs_export"] is True
    jsonp_alpha = next(row for row in bundles["modules"] if row["module_id"] == "jsonpA")
    jsonp_beta = next(row for row in bundles["modules"] if row["module_id"] == "jsonpB")
    assert jsonp_alpha["bundle_kind"] == "webpack_jsonp_call"
    assert jsonp_alpha["chunk_ids"] == ["91"]
    assert jsonp_alpha["dependencies"] == ["jsonpB"]
    assert jsonp_alpha["export_names"] == ["value"]
    assert jsonp_beta["commonjs_export"] is True
    sparse_alpha = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "1"
        and row["bundle_kind"] == "webpack_jsonp_call"
        and row["chunk_ids"] == ["92"]
    )
    sparse_beta = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "2"
        and row["bundle_kind"] == "webpack_jsonp_call"
        and row["chunk_ids"] == ["92"]
    )
    assert sparse_alpha["dependencies"] == ["2"]
    assert sparse_alpha["export_names"] == ["value"]
    assert sparse_beta["commonjs_export"] is True
    assert not any(row["module_id"] == "jsonpShadow" for row in bundles["modules"])
    object_bootstrap_alpha = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "objectBootstrapA"
        and row["bundle_kind"] == "webpack_object_bootstrap"
    )
    object_bootstrap_beta = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "objectBootstrapB"
        and row["bundle_kind"] == "webpack_object_bootstrap"
    )
    assert object_bootstrap_alpha["dependencies"] == ["objectBootstrapB"]
    assert object_bootstrap_alpha["export_names"] == ["value"]
    assert object_bootstrap_beta["commonjs_export"] is True
    concat_alpha = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "3"
        and row["bundle_kind"] == "webpack_chunk_push"
        and row["chunk_ids"] == ["99"]
    )
    concat_beta = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "4"
        and row["bundle_kind"] == "webpack_chunk_push"
        and row["chunk_ids"] == ["99"]
    )
    assert concat_alpha["dependencies"] == ["4"]
    assert concat_alpha["export_names"] == ["concatValue"]
    assert concat_beta["commonjs_export"] is True
    assert not any(
        row["bundle_kind"] == "webpack_chunk_push" and row["chunk_ids"] == ["100"]
        for row in bundles["modules"]
    )
    firebase_alpha = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "firebaseA"
        and row["bundle_kind"] == "webpack_jsonp_call"
        and row["chunk_ids"] == ["98"]
    )
    firebase_beta = next(
        row
        for row in bundles["modules"]
        if row["module_id"] == "firebaseB"
        and row["bundle_kind"] == "webpack_jsonp_call"
        and row["chunk_ids"] == ["98"]
    )
    assert firebase_alpha["dependencies"] == ["firebaseB"]
    assert firebase_alpha["export_names"] == ["value"]
    assert firebase_beta["commonjs_export"] is True
    assert not any(row["module_id"] == "firebaseShadow" for row in bundles["modules"])
    assert "/browserify-modules/" in browserify_alpha["source_path"]
    assert bundles["summary"]["browserify_modules"] >= 4
    module_20001 = next(row for row in bundles["modules"] if row["module_id"] == "20001")
    module_20002 = next(row for row in bundles["modules"] if row["module_id"] == "20002")
    assert module_20001["dependencies"] == ["20002", "40000"]
    assert module_20001["export_names"] == ["name", "named"]
    assert "29999" not in module_20001["dependencies"]
    assert "29996" not in module_20001["dependencies"]
    assert "shadowed" not in module_20001["export_names"]
    assert "shadowedNested" not in module_20001["export_names"]
    assert module_20002["commonjs_export"] is True
    module_20001_source = (PROJECT / module_20001["source_path"]).read_text()
    assert "exports.name = require(20002).name" in module_20001_source
    assert "Static export names: name, named" in module_20001_source
    assert bundles["summary"]["modules_with_named_exports"] >= 1
    assert bundles["summary"]["commonjs_export_modules"] >= 1
    module_readme = (PROJECT / "src/_modules/README.md").read_text()
    assert "Recovered structured modules" in module_readme
    assert "module 20001" in module_readme
    assert "name, named" in module_readme
    assert all((PROJECT / row["source_path"]).is_file() for row in bundles["modules"])

    vm = json.loads((PROJECT / "analysis/jsvm/index.json").read_text())
    app_unit = next(
        u for u in vm["code_units"]
        if u.get("raw_path", "").endswith("/app.js")
    )
    assert app_unit["analysis_origin"] == "safe_deobfuscation"
    assert app_unit["path"].startswith("src/_deobfuscated/")

    graph = json.loads((PROJECT / "analysis/source-graph.json").read_text())
    edge_kinds = graph["summary"]["edge_kinds"]
    assert edge_kinds.get("script_src", 0) >= 1
    assert edge_kinds.get("stylesheet", 0) >= 1
    assert edge_kinds.get("source_map_source") == 1
    assert edge_kinds.get("js_worker", 0) >= 1
    assert edge_kinds.get("js_import_static", 0) >= 1
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

    assert not execution_marker.exists(), "hostile JavaScript was executed by the static pipeline"

    readme = (PROJECT / "README.md").read_text()
    assert "# Recovered source project" in readme
    assert "## Structured bundle modules" in readme
    assert "Original page URL recorded by the saved page" in readme
    assert "src/_modules/" in readme

    print(cp.stdout.rstrip())
    print(
        "PASS: saved Webpage Complete -> normalized capture + readable/deobfuscated source "
        f"+ {bundles['summary']['modules']} structured bundle modules + source map + graph"
    )


if __name__ == "__main__":
    main()
