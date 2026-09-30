#!/usr/bin/env python3
import json
import subprocess
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
scan=ROOT/'work/scans/taobao-linked.jsonl'
gt=json.loads((ROOT/'corpus/ground_truth/fireye_vm_fa8a_isa.json').read_text())
cp=subprocess.run(
    ['node',str(ROOT/'scripts/reduce-linked-vm.cjs'),str(scan),gt['decoder_function_id']],
    cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,
)
rows=[json.loads(x) for x in cp.stdout.splitlines() if x.strip()]
assert len(rows)==1, f'expected one reduced VM, got {len(rows)}'
row=rows[0]
assert row['decoder']==gt['decoder_function_id']
got={o['opcode']:o for o in row['opcodes']}
fail=[]
for k,e in gt['opcodes'].items():
    op=int(k)
    if op not in got:
        fail.append(f'op {op}: missing')
        continue
    r=got[op]
    if len(r['paths'])!=1:
        fail.append(f'op {op}: expected one path, got {len(r["paths"])}')
        continue
    p=r['paths'][0]
    if p['states']!=e['states']:
        fail.append(f'op {op}: states {p["states"]} != {e["states"]}')
    joined=' ; '.join(p['effects'])
    if e['effect_contains'] not in joined:
        fail.append(f'op {op}: missing effect signature {e["effect_contains"]!r} in {joined!r}')
if fail:
    print('\n'.join(fail))
    raise SystemExit(1)
print(f'PASS: {len(gt["opcodes"])} opcode paths match Fireye ground truth')
