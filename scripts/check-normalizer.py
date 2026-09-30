#!/usr/bin/env python3
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
rows=json.loads((ROOT/'work/scans/normalized-vms.json').read_text())
vm=next(x for x in rows if x['decoder']=='fn@fa8a-fb6d')
ops={x['opcode']:x for x in vm['opcodes']}

def effects(op):
    return ops[op]['paths'][0]['effects']

assert effects(0)==['push(stack,op1)'], effects(0)
assert effects(1)==['env[n=op1]=tmp[op2]'], effects(1)
assert effects(2)==['env[n=op1]=env[op2]'], effects(2)
assert effects(3)==['ip+=op1'], effects(3)
assert effects(7)==['env[n=op1]=op2'], effects(7)
assert effects(8)==['(n=tmp)[u=op1]=[]'], effects(8)
assert effects(10)==['argc=op1'], effects(10)

closure='\n'.join(effects(5))
assert 'function c(' in closure, closure[:300]
assert 'function splice(' not in closure, closure[:300]
assert 'tmp' in closure and 'args' in closure
assert 'push(control' in closure and 'fn_call' in closure

print('PASS: scope-aware normalization preserves locals and rewrites VM roles')
