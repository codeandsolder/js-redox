#!/usr/bin/env python3
import json
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL_ROOT = Path(os.environ.get("JSVM_TOOL_ROOT", ROOT / ".cargo-target-nodebug/debug"))
WORK = ROOT / "work/vm-capture-pipeline-regression"

CASES = {
    "direct-switch": ROOT / "corpus/generated/js-vm-obfuscator/virtualized.js",
    "function-table": ROOT / "corpus/generated/js-virtualizer/vm.js",
    "generated-safe": ROOT / "corpus/generated/reversible-obfuscation/generated-child-safe.js",
    "generated-packer": ROOT / "corpus/generated/reversible-obfuscation/packer-eval.js",
    "generated-obfuscated": ROOT / "corpus/generated/js-virtualizer/vm-obfuscated.js",
    "generated-obfuscated-affine-cff": (
        ROOT / "corpus/generated/js-virtualizer/vm-obfuscated-affine-cff.js"
    ),
    "generated-obfuscated-constructor-local": (
        ROOT / "corpus/generated/js-virtualizer/vm-obfuscated-constructor-local.js"
    ),
    "generated-obfuscated-flattened-base91": (
        ROOT / "corpus/generated/js-virtualizer/vm-obfuscated-flattened-base91.js"
    ),
}

OBFUSCATED_CASES = {
    "generated-obfuscated",
    "generated-obfuscated-affine-cff",
    "generated-obfuscated-constructor-local",
    "generated-obfuscated-flattened-base91",
}


def run(*args):
    cp = subprocess.run(
        [str(x) for x in args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=300,
    )
    if cp.returncode:
        raise RuntimeError(
            f"{' '.join(map(str, args))} failed {cp.returncode}:\n{cp.stdout}\n{cp.stderr}"
        )
    return cp


def har_entry(url: str, text: str):
    size = len(text.encode())
    return {
        "pageref": "page_1",
        "startedDateTime": "2026-10-03T00:00:00.000Z",
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
            "headers": [{"name": "content-type", "value": "application/javascript"}],
            "cookies": [],
            "content": {
                "size": size,
                "mimeType": "application/javascript",
                "text": text,
            },
            "redirectURL": "",
            "headersSize": -1,
            "bodySize": size,
        },
        "cache": {},
        "timings": {"send": 0, "wait": 1, "receive": 0},
    }


def make_har(name: str, source: Path, dest: Path):
    payload = source.read_text()
    har = {
        "log": {
            "version": "1.2",
            "creator": {"name": "vm capture regression", "version": "1"},
            "pages": [
                {
                    "startedDateTime": "2026-10-03T00:00:00.000Z",
                    "id": "page_1",
                    "title": name,
                    "pageTimings": {},
                }
            ],
            "entries": [
                har_entry(f"https://fixture.invalid/{name}.js", payload),
            ],
        }
    }
    dest.write_text(json.dumps(har))


def load(project: Path, rel: str):
    return json.loads((project / rel).read_text())


def main():
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir(parents=True)

    results = {}
    for name, source in CASES.items():
        har = WORK / f"{name}.har"
        project = WORK / name
        make_har(name, source, har)
        cp = run(
            TOOL_ROOT / "capture-project",
            har,
            project,
        )
        results[name] = cp.stdout

        analysis = load(project, "analysis/jsvm/index.json")
        assert analysis["recursive_generated_code"] is True
        assert not [
            unit
            for unit in analysis["code_units"]
            if unit.get("scanner_exit")
            or unit.get("switch_ir_exit")
            or unit.get("table_ir_exit")
        ]

        if name == "direct-switch":
            confirmed = [u for u in analysis["code_units"] if u.get("confirmed_vm_signal")]
            devirt = [
                u
                for u in analysis.get("devirtualized_units", [])
                if u.get("vm_kind") == "direct_switch"
            ]
            assert confirmed
            assert devirt
            assert all((project / u["source_path"]).is_file() for u in devirt)
            assert all((project / u["pseudocode_path"]).is_file() for u in devirt)
            graph = load(project, "analysis/source-graph.json")
            assert graph["summary"]["edge_kinds"].get("devirtualized_vm", 0) >= len(devirt)

        elif name == "function-table":
            table_units = [u for u in analysis["code_units"] if u.get("table_vms")]
            devirt = [
                u
                for u in analysis.get("devirtualized_units", [])
                if u.get("vm_kind") == "function_table"
            ]
            assert table_units
            assert devirt
            assert max(u["handler_count"] for u in devirt) >= 74
            assert all((project / u["source_path"]).is_file() for u in devirt)
            assert all((project / u["pseudocode_path"]).is_file() for u in devirt)
            graph = load(project, "analysis/source-graph.json")
            assert graph["summary"]["edge_kinds"].get("devirtualized_vm", 0) >= len(devirt)

        elif name == "generated-packer":
            assert len(analysis["dynamic_code_units"]) == 1
            dynamic = analysis["dynamic_code_units"][0]
            assert dynamic["kind"] == "Dean Edwards P.A.C.K.E.R."
            generated = [
                unit
                for unit in analysis["code_units"]
                if unit.get("origin") == "generated_dynamic_code"
            ]
            assert len(generated) == 1
            child = generated[0]
            assert child["analysis_origin"] == "safe_deobfuscation"
            recovery = load(project, "analysis/generated-recovery.json")
            assert recovery["summary"]["generated_units"] == 1
            assert recovery["summary"]["safe_deobfuscation"] == 1
            recovered = recovery["units"][0]
            assert (project / recovered["readable_path"]).is_file()
            readable = (project / recovered["readable_path"]).read_text()
            assert "var answer = fortytwo;" in readable
            assert "console.log(answer);" in readable
            graph = load(project, "analysis/source-graph.json")
            assert graph["summary"]["edge_kinds"].get("generated_code", 0) == 1
            assert graph["summary"]["edge_kinds"].get("generated_safe_recovery", 0) == 1

        elif name == "generated-safe":
            assert analysis["dynamic_code_units"]
            generated = [
                u
                for u in analysis["code_units"]
                if u.get("origin") == "generated_dynamic_code"
            ]
            assert generated
            child = generated[0]
            assert child["analysis_origin"] == "safe_deobfuscation"
            assert child["path"].startswith("src/_dynamic_deobfuscated/")

            recovery = load(project, "analysis/generated-recovery.json")
            assert recovery["summary"]["generated_units"] >= 1
            assert recovery["summary"]["safe_deobfuscation"] >= 1
            unit = recovery["units"][0]
            assert unit["selected_stage"] == "safe_deobfuscation"
            assert unit["deobfuscation"]["changed"] is True
            assert unit["deobfuscation"]["transforms"].get("constant_fold", 0) >= 1
            assert (project / unit["analysis_path"]).is_file()
            assert (project / unit["readable_path"]).is_file()
            graph = load(project, "analysis/source-graph.json")
            assert graph["summary"]["edge_kinds"].get("generated_safe_recovery", 0) >= 1
            recovered_nodes = [
                n for n in graph["nodes"] if n.get("type") == "generated_recovered_source"
            ]
            assert recovered_nodes
            assert recovered_nodes[0]["recovery_stage"] == "safe_deobfuscation"

        elif name in OBFUSCATED_CASES:
            assert analysis["dynamic_code_units"]
            assert len(analysis["code_units"]) >= 2
            generated = [
                u
                for u in analysis["code_units"]
                if u.get("origin") == "generated_dynamic_code"
            ]
            assert generated
            recovered_vm = max(
                generated,
                key=lambda unit: int(unit.get("largest_handler_table", 0)),
            )
            assert recovered_vm["analysis_origin"] == "string_recovery_only"
            assert recovered_vm["path"].startswith("src/_dynamic_deobfuscated/")
            assert recovered_vm["largest_handler_table"] >= 74
            assert recovered_vm["large_handler_table_candidate"] is False
            assert recovered_vm["confirmed_vm_signal"] is True
            assert recovered_vm["table_vms"] >= 1

            devirt = [
                u
                for u in analysis.get("devirtualized_units", [])
                if u.get("vm_kind") == "function_table"
                and u.get("parent_scan_id") == recovered_vm["scan_id"]
            ]
            assert devirt
            assert max(u["handler_count"] for u in devirt) >= 74
            assert all((project / u["source_path"]).is_file() for u in devirt)
            assert all((project / u["pseudocode_path"]).is_file() for u in devirt)

            recovery = load(project, "analysis/generated-recovery.json")
            assert recovery["summary"]["string_recovery_only"] >= 1
            assert recovery["summary"]["exact_fallback"] == 0
            recovered = next(
                unit
                for unit in recovery["units"]
                if unit["selected_stage"] == "string_recovery_only"
            )
            assert recovered["string_recovery"]["changed"] is True
            assert recovered["string_recovery"]["replacements"] >= 100
            assert recovered["deobfuscation"]["exit"] != 0
            assert recovered["analysis_path"] != recovered["raw_path"]

            string_report = load(project, recovered["string_recovery_report"])
            assert string_report["decoder_call_replacements"] >= 90
            base91 = [
                decoder
                for decoder in string_report["decoders"]
                if decoder.get("mode") == "rotated_base91"
            ]
            assert base91
            rotations = {decoder["rotation"] for decoder in base91}
            table_sizes = {decoder["table_entries"] for decoder in base91}
            assert len(rotations) == 1
            assert len(table_sizes) == 1
            assert next(iter(table_sizes)) >= 590
            assert any(decoder["replacements"] > 0 for decoder in base91)

            if name == "generated-obfuscated":
                assert rotations == {12}
                assert table_sizes == {668}
                assert any(
                    decoder["scope_start"] > 0
                    and decoder["replacements"] >= 10
                    for decoder in base91
                )
            elif name == "generated-obfuscated-affine-cff":
                assert rotations == {2}
                assert table_sizes == {613}
                assert any(
                    decoder["scope_start"] == 0
                    and decoder["replacements"] >= 500
                    for decoder in base91
                )
            elif name == "generated-obfuscated-flattened-base91":
                assert rotations == {7}
                assert table_sizes == {650}
                assert any(
                    decoder["decoder"] == "olQJbc"
                    and decoder["scope_start"] == 0
                    and decoder["replacements"] >= 400
                    for decoder in base91
                )
                iterations = string_report.get("base91_iterations", [])
                assert len(iterations) >= 2
                assert iterations[1]["decoder_calls"] >= 1
            else:
                assert rotations == {22}
                assert table_sizes == {604}
                assert any(
                    decoder["scope_start"] > 0
                    and decoder["replacements"] >= 10
                    for decoder in base91
                )

            graph = load(project, "analysis/source-graph.json")
            assert graph["summary"]["edge_kinds"].get("generated_code", 0) >= 1
            assert graph["summary"]["edge_kinds"].get("generated_safe_recovery", 0) >= 1
            assert graph["summary"]["edge_kinds"].get("devirtualized_vm", 0) >= 1
            dynamic_nodes = [
                n for n in graph["nodes"] if n.get("type") == "generated_dynamic_code"
            ]
            assert dynamic_nodes
            assert any(n.get("child_scan_id") is not None for n in dynamic_nodes)

    print("PASS: capture pipeline VM regressions")
    for name, output in results.items():
        summary = [
            line
            for line in output.splitlines()
            if line.startswith("Project ready:")
            or "confirmed VM units:" in line
            or "VM candidates:" in line
            or "readable devirtualized VM modules:" in line
            or "recovered dynamic units:" in line
        ]
        print(name)
        for line in summary:
            print(f"  {line.strip()}")


if __name__ == "__main__":
    main()
