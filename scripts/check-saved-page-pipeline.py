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

    PAGE.write_text(
        "<!-- saved from url=(0032)https://example.invalid/demo -->\n"
        "<!doctype html><html><head>\n"
        '  <link rel="stylesheet" href="./Saved_files/site.css">\n'
        "</head><body>\n"
        '  <script src="./Saved_files/app.js"></script>\n'
        '  <script type="module">import "./Saved_files/inline-dep.js"; console.log("inline");</script>\n'
        "</body></html>\n"
    )

    app = (
        BUNDLE_FIXTURE.read_text()
        + '\nnew Worker("./worker.js");\n'
        + '//# sourceMappingURL=app.js.map\n'
    )
    (ASSETS / "app.js").write_text(app)
    (ASSETS / "worker.js").write_text('postMessage("ready");\n')
    (ASSETS / "inline-dep.js").write_text('export const dep = 42;\n')
    (ASSETS / "site.css").write_text('body { color: #123; }\n')

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

    manifest = json.loads((PROJECT / "capture-manifest.json").read_text())
    assert manifest["schema"] == "saved-page-project/v0"
    assert manifest["source_kind"] == "saved_page_complete"
    assert manifest["original_page_url"] == "https://example.invalid/demo"
    assert len(manifest["resources"]) == 6
    assert any(r["kind"] == "javascript" for r in manifest["resources"])
    assert any(
        ref["kind"] == "script_src"
        for r in manifest["resources"]
        for ref in r.get("references", [])
    )
    assert sum(bool(s.get("output_path")) for s in manifest["inline_scripts"]) == 1

    source_index = json.loads((PROJECT / "analysis/source-index.json").read_text())
    assert sum(u["kind"] == "javascript" for u in source_index["units"]) == 4

    sourcemaps = json.loads((PROJECT / "analysis/sourcemaps.json").read_text())
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
