#!/usr/bin/env python3
import json
import re
from pathlib import Path

VM_SPECS = {
    "vm20": {
        "path": "work/fireye_opcode_routes.jsonl",
        "roles": {"a":"A", "u":"U", "v":"IP", "l":"CONST", "b":"STACK",
                  "g":"O1", "x":"O2", "F":"O3", "H":"ARGC"},
    },
    "vm24": {
        "path": "work/fireye_opcode_routes2.jsonl",
        "roles": {"a":"A", "u":"U", "v":"IP", "l":"CONST", "y":"STACK",
                  "g":"O1", "X":"O2", "R":"O3"},
    },
}

def load(path):
    out = []
    for line in Path(path).read_text().splitlines():
        if line.startswith('{"op"'):
            out.append(json.loads(line))
    return out

def norm_text(s, roles):
    for old, new in sorted(roles.items(), key=lambda kv: -len(kv[0])):
        s = re.sub(rf'(?<![\w$]){re.escape(old)}(?![\w$])', new, s)
    return re.sub(r'\s+', '', s)

def classify(row, roles):
    sem = [norm_text(x, roles) for x in row["semantic"]]
    blob = ";".join(sem)

    if re.search(r'A\[n=O1\]=U\[O2\]', blob):
        return "MOVE_U_TO_A"
    if re.search(r'A\[n=O1\]=A\[O2\]', blob):
        return "MOVE_A"
    if re.search(r'A\[n=O1\]=O2(?:;|$)', blob):
        return "LOAD_IMM_A"
    if re.search(r'IP\+=O1(?:;|$)', blob):
        return "JUMP_REL"
    if re.search(r'\(n=U\)\[t=O2\]=!A\[O1\]', blob):
        return "NOT_A"
    if "n=U" in blob and "t=O3" in blob and "A[O1]" in blob and "A[O2]" in blob and "===" in blob:
        return "STRICT_EQ_A"
    if "n=IP" in blob and "A[O1]" in blob and "IP=n+" in blob and "?O2:O3" in blob:
        return "BRANCH_A"
    if "n=IP" in blob and "U[O1]" in blob and "IP=n+" in blob and "?O2:O3" in blob:
        return "BRANCH_U"
    if blob.startswith("THROW:") and "newh(" in blob:
        return "VM_RETURN"
    if "n=functionc(" in blob and "f(n,this" in blob:
        return "MAKE_VM_CLOSURE"
    if "TRY:" in blob and "n=U[O1]" in blob and "STACK.length" in blob and "O2" in blob and "U)[t=O3]" in blob:
        return "CALL_U"
    if "TRY:" in blob and "n=CONST[O1]" in blob and "STACK.length" in blob and "O2" in blob and "U)[t=O3]" in blob:
        return "CALL_CONST"
    if re.fullmatch(r'e\(STACK,O1\)', blob):
        return "PUSH_IMM"
    if "U)[t=O3]" in blob and "A[O1]" in blob and "A[O2]" not in blob and "===" in blob:
        return "STRICT_EQ_IMM"
    if re.search(r'\(n=U\)\[t=O1\]=\[\]', blob):
        return "ALLOC_ARRAY"
    return None

classified = {}
for vm, spec in VM_SPECS.items():
    cmap = {}
    for row in load(spec["path"]):
        sig = classify(row, spec["roles"])
        if sig:
            cmap.setdefault(sig, []).append(row["op"])
    classified[vm] = cmap

common = sorted(set(classified["vm20"]) & set(classified["vm24"]))
print("| semantic signature | VM20 opcode | VM24 opcode |")
print("|---|---:|---:|")
for sig in common:
    print("| `%s` | %s | %s |" % (sig, classified["vm20"][sig], classified["vm24"][sig]))

print()
for vm in VM_SPECS:
    print(vm, json.dumps(classified[vm], sort_keys=True))

Path("work/fireye_cross_vm_semantic_map.json").write_text(
    json.dumps(classified, indent=2, sort_keys=True) + "\n"
)
