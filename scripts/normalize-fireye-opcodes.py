#!/usr/bin/env python3
import json
from pathlib import Path

ROLES = {
    "z": "BYTECODE",
    "v": "IP",
    "b": "STACK",
    "a": "A",
    "u": "U",
    "l": "CONST",
    "g": "O1",
    "x": "O2",
    "F": "O3",
    "H": "ARGC",
}

KNOWN = {
    0: ("ALLOC_ARRAY",       "U[O1] = []"),
    1: ("PUSH_A",            "STACK.push(A[O1])"),
    2: ("BRANCH_U",          "IP += U[O1] ? O2 : O3"),
    3: ("MOVE_U_TO_A",       "A[O1] = U[O2]"),
    4: ("VM_RETURN",         "throw internal return tag with return-stack pop"),
    5: ("JUMP_REL",          "IP += O1"),
    6: ("CALL_METHOD_CONST", "U[O3] = A[O1][CONST[O2]].apply(A[O1], pop_args(ARGC))"),
    7: ("MAKE_VM_CLOSURE",   "U[O2] = closure(entry = O1 + 1)"),
    8: ("PROP_WRITE_A",      "A[O1][O2] = A[O3]"),
    9: ("CALL_U",             "U[O3] = U[O1].apply(null, pop_args(O2))"),
   10: ("MOVE_A",             "A[O1] = A[O2]"),
   11: ("CALL_CONST",         "U[O3] = CONST[O1].apply(null, pop_args(O2))"),
   12: ("SET_ARGC",           "ARGC = O1"),
   13: ("PUSH_IMM",           "STACK.push(O1)"),
   14: ("STRICT_EQ_IMM",      "U[O3] = (A[O1] === O2)"),
   15: ("NOT_A",              "U[O2] = !A[O1]"),
   16: ("STRICT_EQ_A",        "U[O3] = (A[O1] === A[O2])"),
   17: ("LOAD_IMM_A",         "A[O1] = O2"),
   18: ("BRANCH_A",           "IP += A[O1] ? O2 : O3"),
   19: ("PROP_READ_A",        "U[O3] = A[O1][O2]"),
}

def rows(path: Path):
    for line in path.read_text().splitlines():
        if line.startswith('{"op"'):
            yield json.loads(line)

def main():
    path = Path("work/fireye_opcode_routes.jsonl")
    out = []
    for r in rows(path):
        op = r["op"]
        name, effect = KNOWN.get(op, ("UNKNOWN", ""))
        out.append({
            "opcode": op,
            "name": name,
            "effect": effect,
            "trace": r["trace"],
            "terminal": r["terminal"],
            "raw_semantic": r["semantic"],
        })

    Path("work/fireye_vm20_opcode_map.json").write_text(
        json.dumps({"roles": ROLES, "opcodes": out}, indent=2) + "\n"
    )

    md = [
        "# Fireye VM20 normalized opcode map",
        "",
        "Statically recovered from the VM around source span `0xfc0-0x1ac2`.",
        "",
        "| op | normalized micro-op | effect | terminal trace |",
        "|---:|---|---|---|",
    ]
    for r in out:
        md.append(
            f"| {r['opcode']} | `{r['name']}` | `{r['effect']}` | "
            f"`{' → '.join(map(str, r['trace']))}` |"
        )
    md += [
        "",
        "## Role anchors",
        "",
        "- `BYTECODE`: instruction stream; fetch is `BYTECODE[4*IP + offset]`.",
        "- `IP`: virtual instruction pointer.",
        "- `STACK`: value/argument stack; call ops splice arguments from its tail.",
        "- `A`, `U`: two VM storage banks; names intentionally avoid overclaiming JS-level meaning.",
        "- `CONST`: outer constant/global table.",
        "- `O1/O2/O3`: bytes at instruction offsets 1/2/3.",
        "- `ARGC`: call-argument count latched by opcode 12.",
        "",
        "Opcode 4 uses the VM's internal exception tag to unwind a return; it is normalized as `VM_RETURN`, not a user-visible JavaScript throw.",
    ]
    Path("work/fireye_vm20_opcode_map.md").write_text("\n".join(md) + "\n")
    print("\n".join(md))

if __name__ == "__main__":
    main()
