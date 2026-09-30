#!/usr/bin/env python3
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "work" / "table-ir-v2"

def load(name):
    return json.loads((BASE / f"{name}.json").read_text())

def only_vm(name):
    d = load(name)
    assert d["schema"] == "jsvm-table-ir/v0", (name, d.get("schema"))
    assert len(d["vms"]) == 1, (name, len(d["vms"]))
    return d["vms"][0]

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

for name, exp in shape_expected.items():
    vm = only_vm(name)
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
        s["ir"]["kind"] in {"raw_js", "raw_expression"}
        for h in vm["handlers"] for s in h["statements"]
    )
    assert raw <= 25, (name, raw)

rr = only_vm("rusty-runtime")
rs = only_vm("rusty-snake")
for name, vm in (("rusty-runtime", rr), ("rusty-snake", rs)):
    assert len(vm["handlers"]) == 31, (name, len(vm["handlers"]))
    assert vm["role_bindings"] == {"control_stack": "reg_backups"}, (
        name, vm["role_bindings"]
    )
    assert vm["method_bindings"].get("ctx.getByte") == "read_byte"
    assert vm["method_bindings"].get("ctx.getReg") == "reg_get"
    assert vm["method_bindings"].get("ctx.setReg") == "reg_set"

rr_hash = Counter(h["semantic_hash"] for h in rr["handlers"])
rs_hash = Counter(h["semantic_hash"] for h in rs["handlers"])
assert sum((rr_hash & rs_hash).values()) == 31

jsv = only_vm("jsv")
assert len(jsv["handlers"]) == 74
assert jsv["method_bindings"].get("ctx.readByte") == "read_byte"

ssukka = only_vm("ssukka")
assert len(ssukka["handlers"]) == 6
ssukka_raw = sum(
    s["ir"]["kind"] in {"raw_js", "raw_expression"}
    for h in ssukka["handlers"] for s in h["statements"]
)
assert ssukka_raw == 0

print("PASS: table IR regression")
