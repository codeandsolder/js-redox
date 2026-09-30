#!/usr/bin/env python3
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / ".cargo-target-nodebug/debug/reduce"
SCAN = ROOT / "work/scans/taobao-linked.jsonl"
GT = ROOT / "corpus/ground_truth/fireye_vm_fa8a_isa.json"

gt = json.loads(GT.read_text())
cp = subprocess.run(
    [str(BIN), str(SCAN), "--function-id", gt["decoder_function_id"]],
    cwd=ROOT,
    text=True,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    check=True,
    timeout=30,
)
rows = [json.loads(x) for x in cp.stdout.splitlines() if x.strip()]
if len(rows) != 1:
    raise SystemExit(f"expected one reduced VM, got {len(rows)}")

row = rows[0]
got = {o["opcode"]: o for o in row["opcodes"]}
fail = []
for key, expected in gt["opcodes"].items():
    op = int(key)
    actual = got.get(op)
    if actual is None:
        fail.append(f"opcode {op}: missing")
        continue
    paths = actual["paths"]
    if len(paths) != 1:
        fail.append(f"opcode {op}: expected one path, got {len(paths)}")
        continue
    path = paths[0]
    if path["states"] != expected["states"]:
        fail.append(
            f"opcode {op}: states {path['states']} != {expected['states']}"
        )
    joined = " ; ".join(path["effects"])
    if expected["effect_contains"] not in joined:
        fail.append(
            f"opcode {op}: missing effect signature "
            f"{expected['effect_contains']!r} in {joined!r}"
        )

if fail:
    print("\n".join(fail))
    raise SystemExit(1)

print(f"PASS: Rust reducer matches {len(gt['opcodes'])} Fireye opcode paths")
