#!/usr/bin/env python3
import base64
import json
import os
import runpy
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL_ROOT = Path(os.environ.get("JSVM_TOOL_ROOT", ROOT / ".cargo-target-nodebug/debug"))
WORK = ROOT / "work/wasm-copied-input-boundary-regression"
HAR = WORK / "fixture.har"
PROJECT = WORK / "project"
FRESH_HAR = WORK / "fresh-fixture.har"
FRESH_PROJECT = WORK / "fresh-project"
CLEANUP_HAR = WORK / "cleanup-fixture.har"
CLEANUP_PROJECT = WORK / "cleanup-project"
CLEANUP_OVERLAP_HAR = WORK / "cleanup-overlap-fixture.har"
CLEANUP_OVERLAP_PROJECT = WORK / "cleanup-overlap-project"

# Deliberate nop padding keeps the exported core above wasm-redox deep-analysis
# minimum body size; removing it would make this boundary fixture skip deep analysis.
WASM = bytes.fromhex(
    "0061736d01000000011f066000016f60016f016f60036f6f7f006000017f60017f017f60026f7f017f022e0303776267115f5f7762696e6467656e5f6d656d6f72790000037762670463746f72000103"
    "7762670373657400020304030304050404016f00040503010001071102066d656d6f7279020004636f707900050aad01030e01017f410222001000260020000b040020000b960101017f010101010101"
    "0101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101"
    "0101010101010101012001417c712102410020002600410110031004250010012600410125004100250020024102761002200228020020022802046a0b0061046e616d65012e0500066d656d6f727901"
    "0463746f720203736574030b6d656d6f72795f736c6f74040b6275666665725f736c6f74022a0303010004736c6f7404010004736c6f7405030006736f757263650104626173650207616c69676e6564"
)


WASM_B64 = base64.b64encode(WASM).decode()

FRESH_WASM = bytes.fromhex(
    "0061736d0100000001270860016f017f6000016f60016f016f60036f6f7f006000006000017f60017f017f60026f7f017f02610503776267066c656e677468000003776267115f5f7762696e6467656e5f6d656d6f72790001037762670463746f72000203776267037365740003037762671f5f5f7762696e6467656e5f696e69745f65787465726e7265665f7461626c65000403060505060606070404016f00080503010001073a04135f5f7762696e6467656e5f6578706f72745f300100066d656d6f72790200105f5f7762696e6467656e5f7374617274000404636f707900090ace01050e01017f410222001001260020000b040020000b08002000250010000b0a00410028020020006a0ba30101017f0101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101014100200026004101100510062500100226002001047f4104054100100741027410080b2102410125004100250020024102761003200228020020022802046a0b0b0a010041000b0408000000009701046e616d6501530900066c656e67746801066d656d6f7279020463746f72030373657404057374617274050b6d656d6f72795f736c6f74060b6275666665725f736c6f74070d6c656e6774685f68656c7065720805616c6c6f63023b0505010004736c6f7406010004736c6f7407010004736c6f7408010005627974657309030006736f7572636501077573655f616c74020462617365"
)
FRESH_WASM_B64 = base64.b64encode(FRESH_WASM).decode()

CLEANUP_WASM = bytes.fromhex(
    "0061736d01000000012b0960016f017f6000016f60016f016f60036f6f7f006000006000017f60017f017f60017f0060026f7f017f026e0603776267"
    "066c656e677468000003776267115f5f7762696e6467656e5f6d656d6f7279000103776267066275666665720002037762670463746f720002037762"
    "67037365740003037762671f5f5f7762696e6467656e5f696e69745f65787465726e7265665f7461626c650004030807050506060607080404016f00"
    "0805030100010606017f0141080b073a04135f5f7762696e6467656e5f6578706f72745f300100066d656d6f72790200105f5f7762696e6467656e5f"
    "7374617274000504636f7079000c0a9d02070f01017f2300220041016a240020000b0e01017f100622001001260020000b1802016f017f2000250010"
    "022101100622022001260020020b08002000250010000b0a00410028020020006a0b100020004102744180086a41003602000bbd0103037f016f017f"
    "010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101"
    "010101010101010101010101010101010101010101010101010101010101010101010101410020002600100722021008220325001003210510062204"
    "200526002003100b2001047f41040541001009410274100a0b21062004250041002500200641027610042004100b2002100b20062802002006280204"
    "6a0b0b0a010041000b0408000000009a02046e616d6501700c00066c656e67746801066d656d6f72790206627566666572030463746f720403736574"
    "05057374617274060a736c6f745f616c6c6f63070b6d656d6f72795f736c6f74080b6275666665725f736c6f74090d6c656e6774685f68656c706572"
    "0a05616c6c6f630b07636c65616e75700292010706010004736c6f7407010004736c6f740803000b6d656d6f72795f736c6f74010576616c75650204"
    "736c6f7409010004736c6f740a01000562797465730b010004736c6f740c070006736f7572636501077573655f616c74020b6d656d6f72795f736c6f"
    "74030b6275666665725f736c6f74040d72656365697665725f736c6f7405087265636569766572060462617365070c0100096e6578745f736c6f74"
)
CLEANUP_WASM_B64 = base64.b64encode(CLEANUP_WASM).decode()

CLEANUP_OVERLAP_WASM = bytes.fromhex(
    "0061736d01000000012b0960016f017f6000016f60016f016f60036f6f7f006000006000017f60017f017f60017f0060026f7f017f026e0603776267"
    "066c656e677468000003776267115f5f7762696e6467656e5f6d656d6f7279000103776267066275666665720002037762670463746f720002037762"
    "67037365740003037762671f5f5f7762696e6467656e5f696e69745f65787465726e7265665f7461626c650004030807050506060607080404016f00"
    "0805030100010606017f0141080b073a04135f5f7762696e6467656e5f6578706f72745f300100066d656d6f72790200105f5f7762696e6467656e5f"
    "7374617274000504636f7079000c0a9902070f01017f2300220041016a240020000b0e01017f100622001001260020000b1802016f017f2000250010"
    "022101100622022001260020020b08002000250010000b0a00410028020020006a0b0c0020001a411041003602000bbd0103037f016f017f01010101"
    "010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101"
    "010101010101010101010101010101010101010101010101010101010101010141002000260010072202100822032500100321051006220420052600"
    "2003100b2001047f41040541001009410274100a0b21062004250041002500200641027610042004100b2002100b200628020020062802046a0b0b0a"
    "010041000b0408000000009a02046e616d6501700c00066c656e67746801066d656d6f72790206627566666572030463746f72040373657405057374"
    "617274060a736c6f745f616c6c6f63070b6d656d6f72795f736c6f74080b6275666665725f736c6f74090d6c656e6774685f68656c7065720a05616c"
    "6c6f630b07636c65616e75700292010706010004736c6f7407010004736c6f740803000b6d656d6f72795f736c6f74010576616c75650204736c6f74"
    "09010004736c6f740a01000562797465730b010004736c6f740c070006736f7572636501077573655f616c74020b6d656d6f72795f736c6f74030b62"
    "75666665725f736c6f74040d72656365697665725f736c6f7405087265636569766572060462617365070c0100096e6578745f736c6f74"
)
CLEANUP_OVERLAP_WASM_B64 = base64.b64encode(CLEANUP_OVERLAP_WASM).decode()

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


def write_fixture(path: Path, title: str, js: str) -> None:
    html = '<!doctype html><script src="https://fixture.invalid/carrier.js"></script>'
    fixture = {
        "log": {
            "version": "1.2",
            "creator": {"name": title, "version": "1"},
            "pages": [
                {
                    "startedDateTime": "2026-10-11T00:00:00.000Z",
                    "id": "page_1",
                    "title": title,
                    "pageTimings": {},
                }
            ],
            "entries": [
                entry("https://fixture.invalid/index.html", "text/html", html),
                entry("https://fixture.invalid/carrier.js", "application/javascript", js),
            ],
        }
    }
    path.write_text(json.dumps(fixture))


def materialize_and_correlate(har: Path, project: Path) -> None:
    run(TOOL_ROOT / "har-project", har, "--output", project)
    run(TOOL_ROOT / "source-materialize", project)
    run(
        "uv", "run", "--no-project", "python",
        "scripts/materialize-safe-deobfuscation.py", project,
        "--deobfuscator", TOOL_ROOT / "deobfuscate-safe",
        "--string-recoverer", ROOT / "scripts/recover-js-obfuscator-strings.py",
        "--formatter", TOOL_ROOT / "js-format",
        "--jobs", 1,
    )
    run(
        "uv", "run", "--no-project", "python",
        "scripts/materialize-wasm.py", project,
        "--wasm-redox", TOOL_ROOT / "wasm-redox",
    )
    run(
        "uv", "run", "--no-project", "python",
        "scripts/correlate-wasm-js-boundary.py", project,
        "--analyzer", TOOL_ROOT / "wasm-import-semantics",
        "--fresh-evaluator", TOOL_ROOT / "fresh-eval",
    )


def cleanup_fixture_js(wasm_b64: str) -> str:
    return (
        "var host = window;\n"
        "var exportsBinding;\n"
        "function init(instance) {\n"
        "    exportsBinding = instance.exports;\n"
        "    exportsBinding.__wbindgen_start();\n"
        "    return exportsBinding;\n"
        "}\n"
        "function tQ() {\n"
        "    var imports = {wbg: {}};\n"
        "    imports.wbg.length = function(value) { return value.length; };\n"
        "    imports.wbg.__wbindgen_memory = function() { return exportsBinding.memory; };\n"
        "    imports.wbg.buffer = function(value) { return value.buffer; };\n"
        "    imports.wbg.ctor = function(value) { return new host.Uint32Array(value); };\n"
        "    imports.wbg.set = function(receiver, source, offset) { receiver.set(source, offset >>> 0); };\n"
        "    imports.wbg.__wbindgen_init_externref_table = function() {\n"
        "        var table, base;\n"
        "        table = exportsBinding.__wbindgen_export_0;\n"
        "        base = table.grow(4);\n"
        "        table.set(0, void 0);\n"
        "        table.set(base + 0, void 0);\n"
        "        table.set(base + 1, null);\n"
        "        table.set(base + 2, true);\n"
        "        table.set(base + 3, false);\n"
        "    };\n"
        "    return imports;\n"
        "}\n"
        "function bA(A) {\n"
        "    if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false];\n"
        "    for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) g[E] = Q.charCodeAt(E);\n"
        "    return [g.buffer, false];\n"
        "}\n"
        f'const embedded = "{wasm_b64}";\n'
        "var bytes = bA(embedded)[0], imports = tQ();\n"
        "var module = new host.WebAssembly.Module(bytes);\n"
        "var instance = new host.WebAssembly.Instance(module, imports);\n"
        "init(instance);\n"
        "var input = new host.Uint32Array([11, 22]);\n"
        "instance.exports.copy(input, 0);\n"
    )


def check_transitive_runtime_dependency_overlay() -> None:
    correlation = runpy.run_path(ROOT / "scripts/correlate-wasm-js-boundary.py")
    overlay = correlation["source_word_semantic_overlay"]
    analysis = {
        "runtime_bindings": [
            {
                "value": 10,
                "name": "$runtime0",
                "expression": "i32load<memory0, align=2, offset=8>($arg0)",
                "semantic_ir": {
                    "kind": "operation",
                    "value": 10,
                    "operator": "i32load<memory0, align=2, offset=8>",
                    "arguments": [{"kind": "argument", "index": 0}],
                },
                "runtime_dependencies": [],
            },
            {
                "value": 20,
                "name": "$runtime1",
                "expression": "host.transform($runtime0)",
                "semantic_ir": {
                    "kind": "operation",
                    "value": 20,
                    "operator": "host.transform",
                    "arguments": [{"kind": "runtime", "value": 10, "name": "$runtime0"}],
                },
                "runtime_dependencies": [10],
            },
        ],
        "returns": [
            {
                "value": 30,
                "expression": "$runtime1",
                "semantic_ir": {"kind": "runtime", "value": 20, "name": "$runtime1"},
                "runtime_dependencies": [20],
            }
        ],
    }
    for binding in analysis["runtime_bindings"]:
        binding["normalized_semantic_ir"] = json.loads(json.dumps(binding["semantic_ir"]))
    for report in analysis["returns"]:
        report["normalized_semantic_ir"] = json.loads(json.dumps(report["semantic_ir"]))

    interpretations = [
        {
            "load_value": 10,
            "source_parameter": 0,
            "source_element_index": 2,
            "source_conversion": "ToUint32",
        }
    ]
    bindings, returns, graph_proven = overlay(analysis, interpretations)
    assert graph_proven is True, (bindings, returns)
    assert [binding["load_value"] for binding in bindings] == [10], bindings
    [semantic_return] = returns
    assert semantic_return["runtime_dependencies"] == [20], semantic_return
    assert semantic_return["transitive_runtime_dependencies"] == [10, 20], semantic_return
    assert [
        dependency["source_element_index"]
        for dependency in semantic_return["source_word_dependencies"]
    ] == [2], semantic_return
    # Presentation rewriting cannot see through runtime1. The structured DAG and
    # source-aware IR can: runtime1 remains a runtime leaf but carries the exact
    # copied source word reachable through runtime1 -> runtime0.
    assert semantic_return["raw_source_word_expression"] == "$runtime1", semantic_return
    assert semantic_return["source_word_expression"] == "$runtime1", semantic_return
    assert semantic_return["source_word_semantic_ir"] == {
        "kind": "runtime",
        "value": 20,
        "name": "$runtime1",
        "source_word_dependencies": [
            {
                "load_value": 10,
                "runtime_binding": "$runtime0",
                "source_parameter": 0,
                "source_element_index": 2,
                "source_conversion": "ToUint32",
            }
        ],
    }, semantic_return

    inconsistent = json.loads(json.dumps(analysis))
    inconsistent["returns"][0]["semantic_ir"] = {
        "kind": "runtime",
        "value": 10,
        "name": "$runtime0",
    }
    bad_bindings, bad_returns, bad_graph = overlay(inconsistent, interpretations)
    assert bad_graph is False, (bad_bindings, bad_returns)
    assert bad_bindings == [] and bad_returns == [], (bad_bindings, bad_returns)

    normalization_mismatch = json.loads(json.dumps(analysis))
    normalization_mismatch["returns"][0]["normalized_semantic_ir"] = {
        "kind": "runtime",
        "value": 10,
        "name": "$runtime0",
    }
    norm_bindings, norm_returns, norm_graph = overlay(
        normalization_mismatch, interpretations
    )
    assert norm_graph is False, (norm_bindings, norm_returns)
    assert norm_bindings == [] and norm_returns == [], (norm_bindings, norm_returns)

    cyclic = json.loads(json.dumps(analysis))
    cyclic["runtime_bindings"][0]["runtime_dependencies"] = [20]
    cyclic["runtime_bindings"][0]["semantic_ir"] = {
        "kind": "runtime",
        "value": 20,
        "name": "$runtime1",
    }
    cyclic["runtime_bindings"][0]["normalized_semantic_ir"] = json.loads(
        json.dumps(cyclic["runtime_bindings"][0]["semantic_ir"])
    )
    cyclic["runtime_bindings"][1]["runtime_dependencies"] = [10]
    cyclic["runtime_bindings"][1]["semantic_ir"] = {
        "kind": "runtime",
        "value": 10,
        "name": "$runtime0",
    }
    cyclic["runtime_bindings"][1]["normalized_semantic_ir"] = json.loads(
        json.dumps(cyclic["runtime_bindings"][1]["semantic_ir"])
    )
    cycle_bindings, cycle_returns, cycle_graph = overlay(cyclic, interpretations)
    assert cycle_graph is False, (cycle_bindings, cycle_returns)
    assert cycle_bindings == [] and cycle_returns == [], (cycle_bindings, cycle_returns)


def source_word_ir_indices(expression: dict) -> list[int]:
    if expression.get("kind") == "source_word":
        return [expression["source_element_index"]]
    if expression.get("kind") == "operation":
        return [
            index
            for argument in expression.get("arguments", [])
            for index in source_word_ir_indices(argument)
        ]
    return []


def main() -> None:
    check_transitive_runtime_dependency_overlay()
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)
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
        "var input = new host.Uint32Array([11, 22]);\n"
        "instance.exports.copy(input, 0);\n"
    )
    write_fixture(HAR, "copied-input boundary regression", js)


    materialize_and_correlate(HAR, PROJECT)

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
    assert deep["schema"] == "wasm-redox/deep-v14", deep
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
    assert all(load["copied_bytes_unmodified_since_set"] for load in candidate["destination_loads"]), candidate

    boundary = json.loads((PROJECT / "analysis/wasm-js-boundary.json").read_text())
    assert boundary["schema"] == "wasm-js-boundary-correlation/v6", boundary
    assert boundary["summary"]["host_effect_pairs"] == 0, boundary
    assert boundary["summary"]["copied_input_candidates"] == 1, boundary
    assert boundary["summary"]["proven_js_typed_array_copy_semantics"] == 1, boundary
    assert boundary["summary"]["proven_copied_input_binding_identities"] == 1, boundary
    assert boundary["summary"]["proven_module_memory_identities"] == 1, boundary
    assert boundary["summary"]["proven_destination_base_alignments"] == 1, boundary
    assert boundary["bounded_wasm_ir_interpretation"] is True, boundary
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
    assert row["destination_byte_integrity_proven"] is True, row
    assert row["destination_base_alignment_proven"] is True, row
    assert row["destination_base_alignment_basis"] == "static_ssa", row
    assert row["destination_load_interpretation_proven"] is True, row
    assert row["source_uint32_array_length_lower_bound"] == 2, row
    assert [
        proof["source_element_index"] for proof in row["destination_load_interpretations"]
    ] == [0, 1], row
    assert row["source_word_semantic_overlay_proven"] is True, row
    assert row["runtime_dependency_graph_proven"] is True, row
    assert row["source_word_return_dependencies_proven"] is True, row
    assert boundary["summary"]["proven_source_word_return_dependencies"] == 1, boundary
    assert [binding["load_value"] for binding in row["source_word_runtime_bindings"]] == [
        proof["load_value"] for proof in row["destination_load_interpretations"]
    ], row
    assert [binding["semantic_expression"] for binding in row["source_word_runtime_bindings"]] == [
        "source_u32(arg0, 0)", "source_u32(arg0, 1)"
    ], row
    [source_word_return] = row["source_word_returns"]
    assert [
        dependency["source_element_index"]
        for dependency in source_word_return["source_word_dependencies"]
    ] == [0, 1], source_word_return
    assert set(source_word_return["runtime_dependencies"]) <= set(
        source_word_return["transitive_runtime_dependencies"]
    ), source_word_return
    assert "source_u32(arg0, 0)" in source_word_return["source_word_expression"], source_word_return
    assert "source_u32(arg0, 1)" in source_word_return["source_word_expression"], source_word_return
    assert "source_u32(arg0, 0)" in source_word_return["raw_source_word_expression"], source_word_return
    assert "source_u32(arg0, 1)" in source_word_return["raw_source_word_expression"], source_word_return
    assert sorted(source_word_ir_indices(source_word_return["source_word_semantic_ir"])) == [0, 1], source_word_return
    assert sorted(
        source_word_ir_indices(source_word_return["normalized_source_word_semantic_ir"])
    ) == [0, 1], source_word_return

    fresh_js = (
        "var host = window;\n"
        "var exportsBinding;\n"
        "function init(instance) {\n"
        "    exportsBinding = instance.exports;\n"
        "    exportsBinding.__wbindgen_start();\n"
        "    return exportsBinding;\n"
        "}\n"
        "function tQ() {\n"
        "    var imports = {wbg: {}};\n"
        "    imports.wbg.length = function(value) { return value.length; };\n"
        "    imports.wbg.__wbindgen_memory = function() { return exportsBinding.memory; };\n"
        "    imports.wbg.ctor = function(value) { return new host.Uint32Array(value); };\n"
        "    imports.wbg.set = function(receiver, source, offset) { receiver.set(source, offset >>> 0); };\n"
        "    imports.wbg.__wbindgen_init_externref_table = function() {\n"
        "        var table, base;\n"
        "        table = exportsBinding.__wbindgen_export_0;\n"
        "        base = table.grow(4);\n"
        "        table.set(0, void 0);\n"
        "        table.set(base + 0, void 0);\n"
        "        table.set(base + 1, null);\n"
        "        table.set(base + 2, true);\n"
        "        table.set(base + 3, false);\n"
        "    };\n"
        "    return imports;\n"
        "}\n"
        "function bA(A) {\n"
        "    if (Uint8Array.fromBase64) return [Uint8Array.fromBase64(A).buffer, false];\n"
        "    for (var Q = atob(A), g = new Uint8Array(Q.length), E = 0; E < Q.length; E++) g[E] = Q.charCodeAt(E);\n"
        "    return [g.buffer, false];\n"
        "}\n"
        f'const embedded = "{FRESH_WASM_B64}";\n'
        "var bytes = bA(embedded)[0], imports = tQ();\n"
        "var module = new host.WebAssembly.Module(bytes);\n"
        "var instance = new host.WebAssembly.Instance(module, imports);\n"
        "init(instance);\n"
        "var input = new host.Uint32Array([11, 22]);\n"
        "instance.exports.copy(input, 0);\n"
    )
    write_fixture(FRESH_HAR, "fresh copied-input alignment regression", fresh_js)
    materialize_and_correlate(FRESH_HAR, FRESH_PROJECT)

    fresh_index = json.loads((FRESH_PROJECT / "analysis/wasm/index.json").read_text())
    assert fresh_index["summary"]["modules"] == 1, fresh_index
    fresh_module = fresh_index["modules"][0]
    fresh_deep = json.loads((FRESH_PROJECT / fresh_module["deep_path"]).read_text())
    assert fresh_deep["schema"] == "wasm-redox/deep-v14", fresh_deep
    fresh_copy = next(row for row in fresh_deep["exports"] if row.get("export") == "copy")
    [fresh_candidate] = fresh_copy["analysis"]["externref_bulk_copy_candidates"]
    assert fresh_candidate["destination_base_guaranteed_trailing_zero_bits"] == 0, fresh_candidate
    assert fresh_candidate["fresh_destination_base_recipe"] == {
        "function": 8,
        "source_length_helper_function": 7,
        "source_length_import_function": 0,
        "source_length_byte_shift": 2,
        "alternate_constant_bases": [4],
    }, fresh_candidate

    fresh_boundary = json.loads(
        (FRESH_PROJECT / "analysis/wasm-js-boundary.json").read_text()
    )
    [fresh_row] = fresh_boundary["copied_input_rows"]
    assert fresh_row["module_memory_identity_proven"] is True, fresh_row
    assert fresh_row["destination_byte_integrity_proven"] is True, fresh_row
    assert fresh_row["static_destination_base_alignment_proven"] is False, fresh_row
    assert fresh_row["destination_base_alignment_proven"] is True, fresh_row
    assert fresh_row["destination_base_alignment_basis"] == "fresh_exact_evaluation", fresh_row
    fresh_proof = fresh_row["fresh_destination_base_alignment_proof"]
    assert fresh_proof["source_uint32_array_length"] == 2, fresh_proof
    assert fresh_proof["allocator_byte_count"] == 8, fresh_proof
    assert fresh_proof["evaluated_destination_base"] == 16, fresh_proof
    assert fresh_proof["evaluated_destination_base_trailing_zero_bits"] == 4, fresh_proof
    assert fresh_proof["fresh_evaluation"]["outcome"] == "returned", fresh_proof
    assert fresh_proof["start_handler"]["kind"] == "table_initializer_only", fresh_proof
    assert fresh_row["destination_load_interpretation_proven"] is True, fresh_row
    assert [
        proof["source_element_index"] for proof in fresh_row["destination_load_interpretations"]
    ] == [0, 1], fresh_row
    assert fresh_row["source_word_semantic_overlay_proven"] is True, fresh_row
    assert fresh_row["runtime_dependency_graph_proven"] is True, fresh_row
    assert fresh_row["source_word_return_dependencies_proven"] is True, fresh_row
    [fresh_source_word_return] = fresh_row["source_word_returns"]
    assert [
        dependency["source_element_index"]
        for dependency in fresh_source_word_return["source_word_dependencies"]
    ] == [0, 1], fresh_source_word_return

    cleanup_cases = [
        (CLEANUP_WASM_B64, CLEANUP_HAR, CLEANUP_PROJECT, True),
        (CLEANUP_OVERLAP_WASM_B64, CLEANUP_OVERLAP_HAR, CLEANUP_OVERLAP_PROJECT, False),
    ]
    for wasm_b64, har, project, expect_disjoint in cleanup_cases:
        write_fixture(har, "cleanup copied-input regression", cleanup_fixture_js(wasm_b64))
        materialize_and_correlate(har, project)
        cleanup_index = json.loads((project / "analysis/wasm/index.json").read_text())
        cleanup_module = cleanup_index["modules"][0]
        cleanup_deep = json.loads((project / cleanup_module["deep_path"]).read_text())
        cleanup_copy = next(row for row in cleanup_deep["exports"] if row.get("export") == "copy")
        [cleanup_candidate] = cleanup_copy["analysis"]["externref_bulk_copy_candidates"]
        assert cleanup_candidate["fresh_cleanup_disjointness_recipe"] == {
            "slot_allocator_function": 6,
            "cleanup_function": 11,
            "bypassed_setup_import_functions": [1, 2],
            "pre_copy_cleanup": "buffer",
            "post_copy_cleanups": ["receiver", "memory"],
        }, cleanup_candidate
        assert all(
            load["internal_memory_mutation_call_barriers"] == [11]
            and load["copied_bytes_unmodified_since_set"] is False
            for load in cleanup_candidate["destination_loads"]
        ), cleanup_candidate

        cleanup_boundary = json.loads((project / "analysis/wasm-js-boundary.json").read_text())
        [cleanup_row] = cleanup_boundary["copied_input_rows"]
        assert cleanup_row["destination_base_alignment_proven"] is True, cleanup_row
        cleanup_proof = cleanup_row["fresh_cleanup_disjointness_proof"]
        if expect_disjoint:
            assert cleanup_row["destination_byte_integrity_proven"] is True, cleanup_row
            assert cleanup_row["destination_load_interpretation_proven"] is True, cleanup_row
            assert cleanup_proof["protected_memory"] == 0, cleanup_proof
            assert cleanup_proof["protected_range_start"] == 16, cleanup_proof
            assert cleanup_proof["protected_range_end"] == 24, cleanup_proof
            assert cleanup_proof["post_copy_accesses_disjoint_from_copied_range"] is True, cleanup_proof
            assert [
                (access["kind"], access["addr"], access["len"])
                for access in cleanup_proof["post_copy_memory_accesses"]
            ] == [("write", 1064, 4), ("write", 1056, 4)], cleanup_proof
            assert [
                proof["source_element_index"]
                for proof in cleanup_row["destination_load_interpretations"]
            ] == [0, 1], cleanup_row
            assert cleanup_row["source_word_semantic_overlay_proven"] is True, cleanup_row
            assert cleanup_row["runtime_dependency_graph_proven"] is True, cleanup_row
            assert cleanup_row["source_word_return_dependencies_proven"] is True, cleanup_row
            [cleanup_source_word_return] = cleanup_row["source_word_returns"]
            assert [
                dependency["source_element_index"]
                for dependency in cleanup_source_word_return["source_word_dependencies"]
            ] == [0, 1], cleanup_source_word_return
        else:
            assert cleanup_proof is None, cleanup_row
            assert cleanup_row["destination_byte_integrity_proven"] is False, cleanup_row
            assert cleanup_row["destination_load_interpretation_proven"] is False, cleanup_row
            assert cleanup_row["source_word_semantic_overlay_proven"] is False, cleanup_row
            assert cleanup_row["source_word_return_dependencies_proven"] is False, cleanup_row
            assert cleanup_row["source_word_returns"] == [], cleanup_row

    print(
        "WASM copied-input boundary regression: inline extraction + structural copy + "
        "1/1 JS Uint32Array semantics + exact module/import binding + exact module-memory identity + "
        "static/fresh alignment + positive/overlapping cleanup disjointness + source-word dependency DAG OK"
    )


if __name__ == "__main__":
    main()
