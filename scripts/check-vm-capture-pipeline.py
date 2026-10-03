#!/usr/bin/env python3
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "work/vm-capture-pipeline-regression"

CASES = {
    "direct-switch": ROOT / "corpus/generated/js-vm-obfuscator/virtualized.js",
    "function-table": ROOT / "corpus/generated/js-virtualizer/vm.js",
    "generated-obfuscated": ROOT / "corpus/generated/js-virtualizer/vm-obfuscated.js",
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
            "uv",
            "run",
            "--no-project",
            "python",
            "scripts/capture-to-project.py",
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

        else:
            assert analysis["dynamic_code_units"]
            assert len(analysis["code_units"]) >= 2
            generated = [
                u
                for u in analysis["code_units"]
                if u.get("origin") == "generated_dynamic_code"
            ]
            assert generated
            candidate = max(
                generated,
                key=lambda unit: int(unit.get("largest_handler_table", 0)),
            )
            assert candidate["analysis_origin"] == "generated_code_exact"
            assert candidate["large_handler_table_candidate"] is True
            assert candidate["largest_handler_table"] >= 74

            graph = load(project, "analysis/source-graph.json")
            assert graph["summary"]["edge_kinds"].get("generated_code", 0) >= 1
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
