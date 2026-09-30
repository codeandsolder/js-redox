#!/usr/bin/env python3
import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

EMPTY_SHA = "e3b0c44298fc1c14"

RULES = [
    ("JUMP_REL", re.compile(r"^ip\+=op1;$")),
    ("THROW_VM_EXCEPTION", re.compile(r"^throw:")),
    ("STORE_INDEXED_IMMEDIATE", re.compile(r"^v\d+\[v\d+=op1\]=op2;$")),
    ("MOVE_INDEXED_SAME_BANK", re.compile(r"^v\d+\[v\d+=op1\]=v\d+\[op2\];$")),
    ("MOVE_INDEXED_CROSS_BANK", re.compile(r"^v\d+\[v\d+=op1\]=v\d+\[op2\];$")),
    ("NEW_ARRAY_INDEXED", re.compile(r".*\[v\d+=op1\]=\[\];$")),
    ("BINARY_ADD_INDEXED", re.compile(r".*\[op1\].*\[op2\].*=.*\+.*;?$")),
    ("BINARY_SHIFT_RIGHT", re.compile(r".*=.*>>.*;?$")),
    ("BINARY_IN", re.compile(r".*\sin\s.*;?$")),
    ("LOGICAL_NOT_INDEXED", re.compile(r".*=!.*\[op1\];?$")),
    ("INDEXED_PROPERTY_READ", re.compile(r".*\[op1\].*\[op2\].*")),
    ("CALL_LIKE", re.compile(r"^v\d+\(.*\);$")),
]

def classify(s: str) -> str:
    for name, rx in RULES:
        if rx.fullmatch(s) or rx.match(s):
            return name
    if "function" in s and "=function" in s:
        return "CREATE_CLOSURE"
    if "try{" in s and "finally{" in s:
        return "CALL_OR_PROPERTY_HELPER"
    return "UNCLASSIFIED"

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("batch_json")
    ap.add_argument("-o","--output")
    args=ap.parse_args()

    xs=json.loads(Path(args.batch_json).read_text())
    clusters=defaultdict(list)
    for vm in xs:
        if vm.get("status")!="ok":
            continue
        for h in vm.get("handlers",[]):
            sig=h["signature"]
            if sig==EMPTY_SHA:
                continue
            clusters[sig].append({
                "decoder":vm["decoder"],
                "opcode":h["opcode"],
                "semantic":h["semantic"],
                "shape_signature":h.get("shape_signature"),
                "states":h.get("states",[]),
            })

    out=[]
    for sig,members in clusters.items():
        exemplar=members[0]["semantic"]
        out.append({
            "signature":sig,
            "label":classify(exemplar),
            "count":len(members),
            "vm_count":len({m["decoder"] for m in members}),
            "semantic":exemplar,
            "members":[{"decoder":m["decoder"],"opcode":m["opcode"]} for m in members],
        })
    out.sort(key=lambda x:(-x["count"],x["signature"]))

    summary={
        "signatures":len(out),
        "reused":sum(x["count"]>1 for x in out),
        "handlers":sum(x["count"] for x in out),
        "labels":{},
    }
    for x in out:
        summary["labels"][x["label"]]=summary["labels"].get(x["label"],0)+1

    doc={"summary":summary,"dictionary":out}
    text=json.dumps(doc,indent=2,ensure_ascii=False)+"\n"
    if args.output:
        Path(args.output).write_text(text)
    else:
        print(text,end="")

if __name__=="__main__":
    main()
