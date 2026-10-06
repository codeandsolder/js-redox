#!/usr/bin/env python3
import json
import os
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURE_ROOT = Path(os.environ.get("JSVM_FIXTURE_ROOT", ROOT))
SCANNER = ROOT / ".cargo-target-nodebug/debug/jsvm-lift"
LIFTER = ROOT / ".cargo-target-nodebug/debug/table-ir"

SOURCES = {
    "shape-raw": "third_party/shape-security-decompiler-toolkit/deobfuscator/input/raw.js",
    "shape-raw2": "third_party/shape-security-decompiler-toolkit/deobfuscator/input/raw2.js",
    "shape-raw3": "third_party/shape-security-decompiler-toolkit/deobfuscator/input/raw3.js",
    "rusty-runtime": "third_party/rusty-jsyc/vm/vm.js",
    "rusty-snake": "third_party/rusty-jsyc/playground/snake/obfuscated/vm.js",
    "jsv": "corpus/generated/js-virtualizer/vm.js",
    "ssukka": "corpus/generated/ssukka/virtualized.js",
}


def fixture(relative: str) -> Path:
    local = ROOT / relative
    if local.is_file():
        return local
    external = FIXTURE_ROOT / relative
    if external.is_file():
        return external
    raise FileNotFoundError(
        f"missing regression fixture {relative}; set JSVM_FIXTURE_ROOT to a workspace containing it"
    )


def run_checked(argv, *, stdout=None, timeout=300):
    cp = subprocess.run(
        [str(arg) for arg in argv],
        cwd=ROOT,
        text=True,
        stdout=stdout if stdout is not None else subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
    )
    if cp.returncode:
        rendered = " ".join(str(arg) for arg in argv)
        raise RuntimeError(f"{rendered} failed {cp.returncode}:\n{cp.stderr}")
    return cp


def generate(name: str, source: Path, base: Path):
    scan = base / f"{name}.scan.json"
    output = base / f"{name}.json"
    with scan.open("w") as stream:
        run_checked([SCANNER, "--json", source], stdout=stream)
    run_checked([LIFTER, source, scan, "--output", output])
    return json.loads(output.read_text())


def only_vm(doc, name):
    assert doc["schema"] == "jsvm-table-ir/v0", (name, doc.get("schema"))
    assert len(doc["vms"]) == 1, (name, len(doc["vms"]))
    return doc["vms"][0]


def main():
    if not SCANNER.is_file() or not LIFTER.is_file():
        raise SystemExit("build jsvm-lift and table-ir first")

    shape_expected = {
        "shape-raw": {
            "ip": "x", "opcode_state": "S", "stack": "j",
            "registers": "f", "control": "e", "control_stack": "T",
            "read_opcode": "ctx.s", "reg_get": "registers.F", "reg_set": "registers.w",
        },
        "shape-raw2": {
            "ip": "r", "opcode_state": "F", "stack": "q",
            "registers": "M", "control": "n", "control_stack": "j",
            "read_opcode": "ctx.S", "reg_get": "registers.y", "reg_set": "registers.l",
        },
        "shape-raw3": {
            "ip": "Z", "opcode_state": "P", "stack": "b",
            "registers": "C", "control": "r", "control_stack": "D",
            "read_opcode": "ctx.u", "reg_get": "registers.W", "reg_set": "registers.e",
        },
    }

    with tempfile.TemporaryDirectory(prefix="jsvm-table-ir-") as td:
        base = Path(td)
        docs = {
            name: generate(name, fixture(relative), base)
            for name, relative in SOURCES.items()
        }

        for name, exp in shape_expected.items():
            vm = only_vm(docs[name], name)
            assert len(vm["handlers"]) >= 239, (name, len(vm["handlers"]))
            for role in ("ip", "opcode_state", "stack", "registers", "control", "control_stack"):
                assert vm["role_bindings"].get(role) == exp[role], (
                    name, role, vm["role_bindings"].get(role), exp[role]
                )
            inv_methods = {v: k for k, v in vm["method_bindings"].items()}
            for role in ("read_opcode", "reg_get", "reg_set"):
                assert inv_methods.get(role) == exp[role], (
                    name, role, inv_methods.get(role), exp[role]
                )
            raw = sum(
                statement["ir"]["kind"] in {"raw_js", "raw_expression"}
                for handler in vm["handlers"]
                for statement in handler["statements"]
            )
            assert raw <= 25, (name, raw)

        rr = only_vm(docs["rusty-runtime"], "rusty-runtime")
        rs = only_vm(docs["rusty-snake"], "rusty-snake")
        for name, vm in (("rusty-runtime", rr), ("rusty-snake", rs)):
            assert len(vm["handlers"]) == 31, (name, len(vm["handlers"]))
            assert vm["role_bindings"] == {"control_stack": "reg_backups"}, (
                name, vm["role_bindings"]
            )
            assert vm["method_bindings"].get("ctx.getByte") == "read_byte"
            assert vm["method_bindings"].get("ctx.getReg") == "reg_get"
            assert vm["method_bindings"].get("ctx.setReg") == "reg_set"

        rr_hash = Counter(handler["semantic_hash"] for handler in rr["handlers"])
        rs_hash = Counter(handler["semantic_hash"] for handler in rs["handlers"])
        assert sum((rr_hash & rs_hash).values()) == 31

        jsv = only_vm(docs["jsv"], "jsv")
        assert len(jsv["handlers"]) == 74
        assert jsv["method_bindings"].get("ctx.readByte") == "read_byte"

        ssukka = only_vm(docs["ssukka"], "ssukka")
        assert len(ssukka["handlers"]) == 6
        ssukka_raw = sum(
            statement["ir"]["kind"] in {"raw_js", "raw_expression"}
            for handler in ssukka["handlers"]
            for statement in handler["statements"]
        )
        assert ssukka_raw == 0

    print("PASS: table IR regression regenerated from source fixtures")


if __name__ == "__main__":
    main()
