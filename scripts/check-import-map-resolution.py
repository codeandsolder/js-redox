#!/usr/bin/env python3
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "work/import-map-regression"
HAR_PROJECT = ROOT / ".cargo-target-nodebug/debug/har-project"
FORMATTER = ROOT / ".cargo-target-nodebug/debug/js-format"
JS_REFS = ROOT / ".cargo-target-nodebug/debug/js-refs"


def run(*args):
    cp = subprocess.run(
        [str(x) for x in args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=120,
    )
    if cp.returncode:
        raise RuntimeError(
            f"{' '.join(map(str, args))} failed {cp.returncode}:\n{cp.stdout}\n{cp.stderr}"
        )
    return cp


def har_entry(url: str, mime: str, text: str):
    size = len(text.encode())
    return {
        "pageref": "page_1",
        "startedDateTime": "2026-10-04T00:00:00.000Z",
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


def stages(project: Path):
    run(
        "uv",
        "run",
        "--no-project",
        "python",
        "scripts/materialize-capture-source.py",
        project,
        "--formatter",
        FORMATTER,
    )
    run(
        "uv",
        "run",
        "--no-project",
        "python",
        "scripts/scan-js-references.py",
        project,
        "--extractor",
        JS_REFS,
    )
    run(
        "uv",
        "run",
        "--no-project",
        "python",
        "scripts/build-source-graph.py",
        project,
    )


def ref_map(row):
    return {ref["specifier"]: ref for ref in row["references"]}


def assert_common(project: Path, root_url: str, child_url: str, worker_url: str, expected):
    source_index = json.loads((project / "analysis/source-index.json").read_text())
    assert any(
        unit["kind"] == "json" and ".inline/" in unit["raw_path"]
        for unit in source_index["units"]
    )
    assert not any(
        unit["kind"] == "javascript"
        and ".inline/" in unit["raw_path"]
        and "importmap" in (unit.get("source_path") or "")
        for unit in source_index["units"]
    )

    maps = json.loads((project / "analysis/import-maps.json").read_text())
    assert maps["summary"]["import_map_scripts"] == 2
    assert maps["summary"]["documents_with_import_maps"] == 1
    assert maps["summary"]["parse_failures"] == 0
    assert maps["summary"]["imports"] == 3
    assert maps["summary"]["scopes"] == 1

    refs = json.loads((project / "analysis/js-references.json").read_text())
    rows = refs["code_units"]
    root = next(row for row in rows if row["url"] == root_url)
    child = next(row for row in rows if row["url"] == child_url)
    worker = next(row for row in rows if row["url"] == worker_url)

    root_refs = ref_map(root)
    assert root_refs["pkg"]["resolved_url"] == expected["pkg"]
    assert root_refs["pkg"]["resolution"] == "import_map"
    assert root_refs["lib/util.js"]["resolved_url"] == expected["lib"]
    assert root_refs["lib/util.js"]["resolution"] == "import_map"
    assert root_refs["extra"]["resolved_url"] == expected["extra"]
    assert root_refs["extra"]["resolution"] == "import_map"
    assert root_refs[expected["child_specifier"]]["resolved_url"] == child_url
    assert root_refs[expected["child_specifier"]]["resolution"] == "url"

    child_ref = ref_map(child)["pkg"]
    assert child_ref["resolved_url"] == expected["scoped"]
    assert child_ref["resolution"] == "import_map_scope"
    assert child_ref["scope"] == expected["scope"]

    worker_ref = ref_map(worker)["pkg"]
    assert worker_ref["resolved_url"] is None
    assert worker_ref["resolution"] == "unresolved_bare"
    assert worker["document_resource_ids"] == []

    assert refs["summary"]["resolved_by_import_map"] == 4
    assert refs["summary"]["unresolved_bare_specifiers"] == 1
    assert refs["summary"]["ambiguous_document_contexts"] == 0

    graph = json.loads((project / "analysis/source-graph.json").read_text())
    edge_kinds = graph["summary"]["edge_kinds"]
    assert edge_kinds.get("import_map_entry") == 5
    assert edge_kinds.get("js_import_static") == 6
    mapped_imports = [
        edge
        for edge in graph["edges"]
        if edge["kind"] == "js_import_static"
        and str(edge.get("resolution", "")).startswith("import_map")
    ]
    assert len(mapped_imports) == 4
    assert all(edge.get("document_resource_id") is not None for edge in mapped_imports)


def check_har():
    work = WORK / "har"
    project = work / "project"
    work.mkdir(parents=True)

    map1 = json.dumps(
        {
            "imports": {
                "pkg": "/modules/pkg-v1.js",
                "lib/": "/modules/lib/",
            },
            "scopes": {
                "/modules/scoped/": {
                    "pkg": "/modules/pkg-scoped.js",
                }
            },
        }
    )
    map2 = json.dumps(
        {
            "imports": {
                "pkg": "/modules/pkg-v2-ignored.js",
                "extra": "/modules/extra.js",
            }
        }
    )
    html = (
        "<!doctype html>"
        f'<script type="importmap">{map1}</script>'
        f'<script type="importmap">{map2}</script>'
        '<script type="module" src="/modules/root.js"></script>'
    )
    root = (
        'import "pkg";\n'
        'import "lib/util.js";\n'
        'import "extra";\n'
        'import "./scoped/child.js";\n'
        'new Worker("/worker.js", {type: "module"});\n'
    )
    child = 'import "pkg"; export const child = true;\n'
    worker = 'import "pkg"; postMessage("ready");\n'

    entries = [
        har_entry("https://fixture.invalid/index.html", "text/html", html),
        har_entry("https://fixture.invalid/modules/root.js", "application/javascript", root),
        har_entry("https://fixture.invalid/modules/scoped/child.js", "application/javascript", child),
        har_entry("https://fixture.invalid/worker.js", "application/javascript", worker),
        har_entry("https://fixture.invalid/modules/pkg-v1.js", "application/javascript", "export default 1;"),
        har_entry("https://fixture.invalid/modules/pkg-scoped.js", "application/javascript", "export default 2;"),
        har_entry("https://fixture.invalid/modules/lib/util.js", "application/javascript", "export const util = 1;"),
        har_entry("https://fixture.invalid/modules/extra.js", "application/javascript", "export const extra = 1;"),
    ]
    har = {
        "log": {
            "version": "1.2",
            "creator": {"name": "import map regression", "version": "1"},
            "pages": [
                {
                    "startedDateTime": "2026-10-04T00:00:00.000Z",
                    "id": "page_1",
                    "title": "import map regression",
                    "pageTimings": {},
                }
            ],
            "entries": entries,
        }
    }
    har_path = work / "fixture.har"
    har_path.write_text(json.dumps(har))
    run(HAR_PROJECT, har_path, "--output", project)
    stages(project)

    assert_common(
        project,
        "https://fixture.invalid/modules/root.js",
        "https://fixture.invalid/modules/scoped/child.js",
        "https://fixture.invalid/worker.js",
        {
            "pkg": "https://fixture.invalid/modules/pkg-v1.js",
            "lib": "https://fixture.invalid/modules/lib/util.js",
            "extra": "https://fixture.invalid/modules/extra.js",
            "scoped": "https://fixture.invalid/modules/pkg-scoped.js",
            "scope": "https://fixture.invalid/modules/scoped/",
            "child_specifier": "./scoped/child.js",
        },
    )


def check_saved_page():
    work = WORK / "saved"
    project = work / "project"
    assets = work / "Saved_files"
    assets.mkdir(parents=True)

    map1 = json.dumps(
        {
            "imports": {
                "pkg": "./Saved_files/pkg-v1.js",
                "lib/": "./Saved_files/lib/",
            },
            "scopes": {
                "./Saved_files/scoped/": {
                    "pkg": "./Saved_files/pkg-scoped.js",
                }
            },
        }
    )
    map2 = json.dumps(
        {
            "imports": {
                "pkg": "./Saved_files/pkg-v2-ignored.js",
                "extra": "./Saved_files/extra.js",
            }
        }
    )
    page = work / "Saved.html"
    page.write_text(
        "<!doctype html>"
        f'<script type="importmap">{map1}</script>'
        f'<script type="importmap">{map2}</script>'
        '<script type="module" src="./Saved_files/root.js"></script>'
    )
    (assets / "root.js").write_text(
        'import "pkg";\n'
        'import "lib/util.js";\n'
        'import "extra";\n'
        'import "./scoped/child.js";\n'
        'new Worker("./worker.js", {type: "module"});\n'
    )
    (assets / "scoped").mkdir()
    (assets / "scoped/child.js").write_text('import "pkg"; export const child = true;\n')
    (assets / "worker.js").write_text('import "pkg"; postMessage("ready");\n')
    (assets / "pkg-v1.js").write_text("export default 1;\n")
    (assets / "pkg-scoped.js").write_text("export default 2;\n")
    (assets / "lib").mkdir()
    (assets / "lib/util.js").write_text("export const util = 1;\n")
    (assets / "extra.js").write_text("export const extra = 1;\n")

    run(
        "uv",
        "run",
        "--no-project",
        "python",
        "scripts/saved-page-to-manifest.py",
        page,
        "--output",
        project,
    )
    stages(project)

    base = "https://saved-page.invalid/saved-page/Saved_files/"
    assert_common(
        project,
        base + "root.js",
        base + "scoped/child.js",
        base + "worker.js",
        {
            "pkg": base + "pkg-v1.js",
            "lib": base + "lib/util.js",
            "extra": base + "extra.js",
            "scoped": base + "pkg-scoped.js",
            "scope": base + "scoped/",
            "child_specifier": "./scoped/child.js",
        },
    )


def main():
    shutil.rmtree(WORK, ignore_errors=True)
    check_har()
    check_saved_page()
    print(
        "PASS: HAR + Webpage Complete import maps: exact/prefix/scoped mappings, "
        "first-definition-wins merge, recursive module context, and worker isolation"
    )


if __name__ == "__main__":
    main()
