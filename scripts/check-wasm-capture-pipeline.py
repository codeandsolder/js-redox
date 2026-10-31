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

WASM = bytes.fromhex("0061736d010000000131096000016f60026f7f017f60016f016f60016f017f60036f7f7f016f60036f7f7f006000017f60017f017f60037f7f7f0002f7010803776267115f5f7762696e6467656e5f6d656d6f72790000037762671b5f5f7762675f67726f775f343364333639303838613337303639340001037762671d5f5f7762675f6275666665725f36303963633365656535316564313538000203776267215f5f7762675f627974654c656e6774685f656135326163336465383832623438330003037762671a5f5f7762675f6e65775f37653037396661323565313335656231000403776267205f5f7762675f67657455696e7433325f39633363633866646537393139656434000103776267145f5f7762675f7369676e616c5f66697874757265000504686f737405616c6c6f63000603060506070708060404016f00100707010372756e000c0a8502050e01017f100722001000260020000b1802016f017f2000250010022101100722022001260020020b3003027f016f017f100810092201250010032102200125004100200210042103100722042003260020042500200010050b0c00200025002001200210060b9c0101027f010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101011008220025004101100141107421012000200141d01b100b200141d01b72100a1a200020014184bb03100b20014184bb0372100a0b008402046e616d650180010c00066d656d6f7279010467726f770206627566666572030b627974655f6c656e6774680408766965775f6e657705076765745f753332060d6f70617175655f7369676e616c0705616c6c6f63080b6d656d6f72795f736c6f74090b6275666665725f736c6f740a0a6d656d6f72795f6765740b0b686f73745f656666656374027a0508010004736c6f740903000b6d656d6f72795f736c6f7401066275666665720204736c6f740a0500066f6666736574010b6275666665725f736c6f7402066c656e6774680304766965770409766965775f736c6f740b030004736c6f7401046261736502066f66667365740c020004736c6f74010462617365")
WASM_B64 = base64.b64encode(WASM).decode()


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


def entry(url, mime, text, *, encoding=None):
    content = {"size": len(text), "mimeType": mime, "text": text}
    if encoding:
        content["encoding"] = encoding
    return {
        "pageref": "page_1",
        "startedDateTime": "2026-10-06T00:00:00.000Z",
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
            "content": content,
            "redirectURL": "",
            "headersSize": -1,
            "bodySize": len(text),
        },
        "cache": {},
        "timings": {"send": 0, "wait": 1, "receive": 0},
    }


def main():
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
    html = '<!doctype html><script src="https://fixture.invalid/fixture.js"></script>'
    js = (
        "var host = window;\n"
        "var imports = {wbg: {}};\n"
        "imports.wbg.__wbg_signal_fixture = function(memory, base, offset) {\n"
        "    var view = new host.DataView(memory.buffer), address = base + offset;\n"
        "    offset === 56708 || view.setUint32(address, 1, false);\n"
        "};\n"
        "function bA(A) {\n"
        "    if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false];\n"
        "    for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) g[E] = Q.charCodeAt(E);\n"
        "    return [g.buffer, false];\n"
        "}\n"
        f'const embedded = "{WASM_B64}";\n'
        "var bytes = bA(embedded)[0];\n"
        "host.WebAssembly.instantiate(bytes, imports);\n"
    )
    split_at = len(WASM) // 2
    left_b64 = base64.b64encode(WASM[:split_at]).decode()
    right_b64 = base64.b64encode(WASM[split_at:]).decode()
    split_js = (
        "function loadSplit() {\n"
        f"  const left = atob(\"{left_b64}\");\n"
        f"  const right = atob(\"{right_b64}\");\n"
        f"  const output = new Uint8Array({len(WASM)});\n"
        "  function copy(chunk, offset) {\n"
        "    for (let i = 0; i < chunk.length; i++) output[offset + i] = chunk.charCodeAt(i);\n"
        "  }\n"
        "  copy(left, 0);\n"
        f"  copy(right, {split_at});\n"
        "  return new WebAssembly.Module(output);\n"
        "}\n"
    )
    fixture = {
        "log": {
            "version": "1.2",
            "creator": {"name": "wasm capture regression", "version": "1"},
            "pages": [
                {
                    "startedDateTime": "2026-10-06T00:00:00.000Z",
                    "id": "page_1",
                    "title": "wasm fixture",
                    "pageTimings": {},
                }
            ],
            "entries": [
                entry("https://fixture.invalid/index.html", "text/html", html),
                entry("https://fixture.invalid/fixture.js", "application/javascript", js),
                entry("https://fixture.invalid/split.js", "application/javascript", split_js),
                entry(
                    "https://fixture.invalid/module.wasm",
                    "application/wasm",
                    WASM_B64,
                    encoding="base64",
                ),
            ],
        }
    }
    HAR.write_text(json.dumps(fixture))

    run(TOOL_ROOT / "capture-import", HAR, "--output", PROJECT)
    manifest = json.loads((PROJECT / "capture-manifest.json").read_text())
    wasm_resource = next(row for row in manifest["resources"] if row["kind"] == "wasm")
    assert wasm_resource["output_path"].endswith(".wasm")
    assert (PROJECT / wasm_resource["output_path"]).read_bytes() == WASM

    run(TOOL_ROOT / "source-materialize", PROJECT)
    run(
        "uv",
        "run",
        "--no-project",
        "python",
        "scripts/materialize-safe-deobfuscation.py",
        PROJECT,
        "--deobfuscator",
        TOOL_ROOT / "deobfuscate-safe",
        "--string-recoverer",
        ROOT / "scripts/recover-js-obfuscator-strings.py",
        "--formatter",
        TOOL_ROOT / "js-format",
        "--jobs",
        1,
    )
    run(TOOL_ROOT / "wasm-materialize", PROJECT)

    index = json.loads((PROJECT / "analysis/wasm/index.json").read_text())
    assert index["summary"] == {
        "modules": 1,
        "direct_resources": 1,
            "inline_extracted": 1,
        "failed": 0,
        "origins": 3,
    }
    module = index["modules"][0]
    assert module["status"] == "ok"
    assert module["has_direct_resource"] is True
    assert module["has_inline_origin"] is True
    assert {
        origin.get("recovery_kind")
        for origin in module["origins"]
        if origin.get("recovery_kind")
    } == {"validated_static_wasm_carrier", "proven_static_byte_assembly"}
    assert (PROJECT / module["report_path"]).is_file()

    deep_path = PROJECT / module["deep_path"]
    assert deep_path.is_file()
    deep = json.loads(deep_path.read_text())
    assert deep["schema"] == "wasm-redox/deep-v14"
    pairs = [
        pair
        for export in deep["exports"]
        for pair in export.get("analysis", {}).get("opaque_host_effect_memory_reads", [])
    ]
    assert sorted(pair["offset"] for pair in pairs) == [3536, 56708], pairs

    run(
        "uv",
        "run",
        "--no-project",
        "python",
        "scripts/correlate-wasm-js-boundary.py",
        PROJECT,
        "--analyzer",
        TOOL_ROOT / "wasm-import-semantics",
   )
    boundary = json.loads((PROJECT / "analysis/wasm-js-boundary.json").read_text())
    assert boundary["schema"] == "wasm-js-boundary-correlation/v6", boundary
    assert boundary["summary"]["host_effect_pairs"] == 2, boundary
    assert boundary["summary"]["proven_js_set_u32_shapes"] == 1, boundary
    assert boundary["summary"]["proven_js_import_object_instantiation_sites"] == 2, boundary
    assert boundary["summary"]["proven_host_import_binding_identities"] == 2, boundary
    by_offset = {row["offset"]: row for row in boundary["host_effect_rows"]}
    assert by_offset[3536]["js_set_u32_shape_proven"] is True, by_offset
    assert by_offset[56708]["js_set_u32_shape_proven"] is False, by_offset
    assert by_offset[3536]["js_set_u32_shape_proofs"][0]["method"] == "setUint32"
    assert all(
        row["js_import_object_instantiation_site_proven"] is True
        and row["import_binding_identity_proven"] is True
        and len(row["import_binding_identity_proofs"]) == 1
        and row["js_import_object_instantiation_site_proofs"][0]["import_object"] == "imports"
        for row in by_offset.values()
    ), by_offset

    run("uv", "run", "--no-project", "python", "scripts/build-source-graph.py", PROJECT)
    graph = json.loads((PROJECT / "analysis/source-graph.json").read_text())
    wasm_nodes = [node for node in graph["nodes"] if node["type"] == "wasm_module"]
    assert len(wasm_nodes) == 1
    wasm_edges = [edge for edge in graph["edges"] if edge["to"] == wasm_nodes[0]["id"]]
    assert {edge["kind"] for edge in wasm_edges} == {
        "wasm_resource",
        "wasm_inline_base64",
        "wasm_static_bytes",
    }
    print(
        "wasm capture regression: dedup + provenance + 1/2 host DataView.setUint32 "
        "shape + 2/2 exact module/import-object binding correlation OK"
    )


if __name__ == "__main__":
    main()
