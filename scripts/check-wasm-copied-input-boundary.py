#!/usr/bin/env python3
import base64
import json
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL_ROOT = Path(os.environ.get("JSVM_TOOL_ROOT", ROOT / ".cargo-target-nodebug/debug"))
WORK = ROOT / "work/wasm-copied-input-boundary-regression"
HAR = WORK / "fixture.har"
PROJECT = WORK / "project"

# Deliberate nop padding keeps the exported core above wasm-redox deep-analysis
# minimum body size; removing it would make this boundary fixture skip deep analysis.
WASM = bytes.fromhex(
    "0061736d01000000011f066000016f60016f016f60036f6f7f006000017f60017f017f60026f7f017f022e0303776267115f5f7762696e6467656e5f6d656d6f72790000037762670463746f7200010377626703736574000203"
    "04030304050404016f00040503010001071102066d656d6f7279020004636f707900050aa501030e01017f410222001000260020000b040020000b8e010001010101010101010101010101010101010101010101010101010101"
    "010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010141002000260041011003100425001001260041012500"
    "4100250020014102761002200128020020012802046a0b0058046e616d65012e0500066d656d6f7279010463746f720203736574030b6d656d6f72795f736c6f74040b6275666665725f736c6f7402210303010004736c6f7404"
    "010004736c6f7405020006736f75726365010462617365"
)


WASM_B64 = base64.b64encode(WASM).decode()

def run(*args):
    cp = subprocess.run(
        [str(arg) for arg in args],
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


def entry(url: str, mime: str, text: str):
    return {
        "pageref": "page_1",
        "startedDateTime": "2026-10-11T00:00:00.000Z",
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
            "content": {"size": len(text), "mimeType": mime, "text": text},
            "redirectURL": "",
            "headersSize": -1,
            "bodySize": len(text),
        },
        "cache": {},
        "timings": {"send": 0, "wait": 1, "receive": 0},
    }


def main() -> None:
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    html = '<!doctype html><script src="https://fixture.invalid/carrier.js"></script>'
    js = (
        "var host = window;\n"
        "var exportsBinding;\n"
        "function init(instance) { exportsBinding = instance.exports; return exportsBinding; }\n"
        "function tQ() {\n"
        "    var imports = {wbg: {}};\n"
        "    imports.wbg.__wbindgen_memory = function() { return exportsBinding.memory; };\n"
        "    imports.wbg.ctor = function(value) { return new host.Uint32Array(value); };\n"
        "    imports.wbg.set = function(receiver, source, offset) {\n"
        "        receiver.set(source, offset >>> 0);\n"
        "    };\n"
        "    return imports;\n"
        "}\n"
        "function bA(A) {\n"
        "    if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false];\n"
        "    for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) g[E] = Q.charCodeAt(E);\n"
        "    return [g.buffer, false];\n"
        "}\n"
        f'const embedded = "{WASM_B64}";\n'
        "var bytes = bA(embedded)[0], imports = tQ();\n"
        "var module = new host.WebAssembly.Module(bytes);\n"
        "var instance = new host.WebAssembly.Instance(module, imports);\n"
        "init(instance);\n"
        "instance.exports.copy(input, 0);\n"
    )
    fixture = {
        "log": {
            "version": "1.2",
            "creator": {"name": "copied-input boundary regression", "version": "1"},
            "pages": [
                {
                    "startedDateTime": "2026-10-11T00:00:00.000Z",
                    "id": "page_1",
                    "title": "copied-input fixture",
                    "pageTimings": {},
                }
            ],
            "entries": [
                entry("https://fixture.invalid/index.html", "text/html", html),
                entry("https://fixture.invalid/carrier.js", "application/javascript", js),
            ],
        }
    }
    HAR.write_text(json.dumps(fixture))

    run(TOOL_ROOT / "har-project", HAR, "--output", PROJECT)
    run(
        "uv", "run", "--no-project", "python",
        "scripts/materialize-capture-source.py", PROJECT,
        "--formatter", TOOL_ROOT / "js-format",
    )
    run(
        "uv", "run", "--no-project", "python",
        "scripts/materialize-safe-deobfuscation.py", PROJECT,
        "--deobfuscator", TOOL_ROOT / "deobfuscate-safe",
        "--string-recoverer", ROOT / "scripts/recover-js-obfuscator-strings.py",
        "--formatter", TOOL_ROOT / "js-format",
        "--jobs", 1,
    )
    run(
        "uv", "run", "--no-project", "python",
        "scripts/materialize-wasm.py", PROJECT,
        "--wasm-redox", TOOL_ROOT / "wasm-redox",
    )

    index = json.loads((PROJECT / "analysis/wasm/index.json").read_text())
    assert index["summary"] == {
        "modules": 1,
        "direct_resources": 0,
        "inline_extracted": 1,
        "failed": 0,
        "origins": 1,
    }, index
    module = index["modules"][0]
    deep = json.loads((PROJECT / module["deep_path"]).read_text())
    assert deep["schema"] == "wasm-redox/deep-v6", deep
    copy_export = next(row for row in deep["exports"] if row.get("export") == "copy")
    candidates = copy_export["analysis"]["externref_bulk_copy_candidates"]
    assert len(candidates) == 1, candidates
    candidate = candidates[0]
    assert candidate["set_import_function"] == 2, candidate
    assert candidate["constructor_import_function"] == 1, candidate
    assert candidate["source_entry_parameter"] == 0, candidate
    assert candidate["constructor_input_memory_import_function"] == 0, candidate
    assert candidate["destination_element_index_shift"] == 2, candidate
    assert [load["byte_offset"] for load in candidate["destination_loads"]] == [0, 4], candidate

    run(
        "uv", "run", "--no-project", "python",
        "scripts/correlate-wasm-js-boundary.py", PROJECT,
        "--analyzer", TOOL_ROOT / "wasm-import-semantics",
    )
    boundary = json.loads((PROJECT / "analysis/wasm-js-boundary.json").read_text())
    assert boundary["schema"] == "wasm-js-boundary-correlation/v1", boundary
    assert boundary["summary"]["host_effect_pairs"] == 0, boundary
    assert boundary["summary"]["copied_input_candidates"] == 1, boundary
    assert boundary["summary"]["proven_js_typed_array_copy_semantics"] == 1, boundary
    assert boundary["summary"]["proven_copied_input_binding_identities"] == 1, boundary
    assert boundary["summary"]["proven_module_memory_identities"] == 1, boundary
    [row] = boundary["copied_input_rows"]
    assert row["raw_constructor_import_module"] == "wbg", row
    assert row["raw_constructor_import"] == "ctor", row
    assert row["raw_memory_import_module"] == "wbg", row
    assert row["raw_memory_import"] == "__wbindgen_memory", row
    assert row["raw_set_import_module"] == "wbg", row
    assert row["raw_set_import"] == "set", row
    assert row["js_typed_array_copy_semantics_proven"] is True, row
    assert row["import_binding_identity_proven"] is True, row
    assert len(row["import_binding_identity_proofs"]) == 1, row
    assert row["module_memory_identity_proven"] is True, row
    assert len(row["module_memory_identity_proofs"]) == 1, row
    assert row["module_memory_identity_proofs"][0]["memory_export"]["name"] == "memory", row
    assert row["module_memory_identity_proofs"][0]["memory_export"]["index"] == 0, row
    assert row["destination_load_interpretation_proven"] is False, row

    print(
        "WASM copied-input boundary regression: inline extraction + structural copy + "
        "1/1 JS Uint32Array semantics + exact module/import binding + exact module-memory identity OK"
    )


if __name__ == "__main__":
    main()
