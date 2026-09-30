#!/usr/bin/env python3
import argparse
import ast
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def find_binary(explicit=None):
    if explicit:
        p=Path(explicit)
        if p.is_file():
            return p
        raise SystemExit(f"binary not found: {p}")
    local=ROOT/"src/jsvm-lift/target/debug/jsvm-lift"
    if local.is_file():
        return local
    cache=Path("/var/cache/sentinelx/cargo-target")
    hits=sorted(cache.glob("jsvm-lift_*/debug/jsvm-lift"), key=lambda p:p.stat().st_mtime, reverse=True)
    if hits:
        return hits[0]
    raise SystemExit("jsvm-lift binary not found")

def scan(path, binary):
    cp=subprocess.run(
        [str(binary),"--json",str(path)],
        cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120
    )
    if cp.returncode:
        raise SystemExit(cp.stderr or f"jsvm-lift exited {cp.returncode}")
    lines=[x for x in cp.stdout.splitlines() if x.strip()]
    if len(lines)!=1:
        raise SystemExit(f"expected one report, got {len(lines)}")
    return json.loads(lines[0])

def parse_js_string_literal(text):
    try:
        value=ast.literal_eval(text)
        return value if isinstance(value,str) else None
    except Exception:
        return None

def discover_parseint_aliases(source):
    aliases={"parseInt"}
    pattern=r'(?<![A-Za-z0-9_$])([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*(?:Number\.)?parseInt\b'
    for m in re.finditer(pattern, source):
        aliases.add(m.group(1))
    return aliases

def fold_symbolic(expr, parseint_aliases):
    expr=expr.strip()

    if re.fullmatch(r'[+-]?(?:0|[1-9][0-9]*)', expr):
        return {
            "kind":"folded",
            "value":int(expr,10),
            "expr":expr,
            "rule":"signed-integer-literal",
            "confidence":"exact",
        }

    call=re.fullmatch(
        r"""([A-Za-z_$][A-Za-z0-9_$]*)\(\s*("[^"]*"|'[^']*')\s*,\s*(2|8|10|16)\s*\)""",
        expr,
    )
    if call and call.group(1) in parseint_aliases:
        digits=parse_js_string_literal(call.group(2))
        radix=int(call.group(3))
        if digits is not None:
            try:
                value=int(digits,radix)
            except ValueError:
                pass
            else:
                return {
                    "kind":"folded",
                    "value":value,
                    "expr":expr,
                    "rule":"parseInt-alias-literal-radix",
                    "alias":call.group(1),
                    "radix":radix,
                    "confidence":"source-backed",
                }

    return {"kind":"symbolic","expr":expr}

def materialize_arg(values, unknowns, idx, parseint_aliases):
    v=values[idx]
    if v is not None:
        return {"kind":"literal","value":v}
    u=unknowns.get(idx)
    if u is None:
        return {"kind":"symbolic","expr":"<unknown>"}
    return fold_symbolic(u, parseint_aliases)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--binary")
    ap.add_argument("--out")
    ap.add_argument("--preview",type=int,default=12)
    args=ap.parse_args()

    path=(ROOT/args.file) if not Path(args.file).is_absolute() else Path(args.file)
    report=scan(path, find_binary(args.binary))
    source=path.read_text()
    parseint_aliases=discover_parseint_aliases(source)

    builders={(b["start"],b["end"]):b for b in report.get("push_builders",[])}
    groups=defaultdict(list)
    for d in report.get("decoder_candidates",[]):
        if d.get("builder_start") is None:
            continue
        groups[(d["builder_start"],d["builder_end"])].append(d)

    output={
        "file":report["file"],
        "streams":[]
    }

    for key, decoders in sorted(groups.items()):
        builder=builders.get(key)
        if not builder:
            continue

        width_counts=Counter(d["width"] for d in decoders)
        width=width_counts.most_common(1)[0][0]
        values=builder.get("values",[])
        unknowns={u["index"]:u["preview"] for u in builder.get("unknowns",[])}

        instructions=[]
        for pc in range(0,len(values),width):
            chunk=[]
            for idx in range(pc,min(pc+width,len(values))):
                chunk.append(materialize_arg(values,unknowns,idx,parseint_aliases))
            instructions.append({
                "pc":pc,
                "index":pc//width,
                "opcode":chunk[0] if chunk else None,
                "operands":chunk[1:],
                "complete":len(chunk)==width,
            })

        literal_known=sum(v is not None for v in values)
        resolved=sum(
            v is not None and v.get("kind") in {"literal","folded"}
            for ins in instructions
            for v in ([ins["opcode"]]+ins["operands"])
        )
        opcode_known=[ins["opcode"]["value"] for ins in instructions
                      if ins["opcode"] and ins["opcode"]["kind"] in {"literal","folded"}]
        stream={
            "builder_start":builder["start"],
            "builder_end":builder["end"],
            "receiver":builder["receiver"],
            "arguments":builder["arguments"],
            "decoder_width":width,
            "decoder_count":len(decoders),
            "decoder_functions":sorted({d["function_id"] for d in decoders}),
            "decoder_objects":sorted({d["object"] for d in decoders}),
            "ips":sorted({d["ip"] for d in decoders}),
            "literal_arguments":literal_known,
            "resolved_arguments":resolved,
            "resolved_ratio":resolved/len(values) if values else 0.0,
            "unknown_arguments":len(values)-resolved,
            "parseint_aliases":sorted(parseint_aliases),
            "opcode_known":len(opcode_known),
            "opcode_unique":len(set(opcode_known)),
            "instructions":instructions,
        }
        output["streams"].append(stream)

    if args.out:
        out=Path(args.out)
        if not out.is_absolute():
            out=ROOT/out
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_text(json.dumps(output,indent=2,ensure_ascii=False)+"\n")

    print(f"{Path(report['file']).name}: {len(output['streams'])} linked streams")
    for s in sorted(output["streams"],key=lambda x:-x["arguments"])[:args.preview]:
        print(
            f"  @{s['builder_start']:x}-{s['builder_end']:x} "
            f"args={s['arguments']} width={s['decoder_width']} "
            f"resolved={s['resolved_ratio']:.1%} opcodes={s['opcode_unique']} "
            f"ips={','.join(s['ips'])}"
        )
        for ins in s["instructions"][:3]:
            def fmt(v):
                if v is None: return "?"
                if v["kind"]=="literal": return str(v["value"])
                return v["expr"]
            fields=[fmt(ins["opcode"])]+[fmt(v) for v in ins["operands"]]
            print(f"    {ins['pc']:04x}: " + " | ".join(fields))

    if not args.out:
        json.dump(output,sys.stdout,indent=2,ensure_ascii=False)
        print()

if __name__=="__main__":
    main()
