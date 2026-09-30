#!/usr/bin/env python3
import argparse
import json
import re
from pathlib import Path


def load_js(path):
    out={}
    for line in Path(path).read_text().splitlines():
        if line.startswith('{"op"'):
            r=json.loads(line)
            out[r['op']]=r
    return out


def norm(s):
    return re.sub(r'\s+','',s)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('rust_json')
    ap.add_argument('decoder_id')
    ap.add_argument('js_routes')
    args=ap.parse_args()
    report=json.loads(Path(args.rust_json).read_text().splitlines()[0])
    maps=[m for m in report.get('opcode_maps',[]) if m['decoder_function_id']==args.decoder_id]
    print('decoder',args.decoder_id,'rust_maps',len(maps))
    if not maps:
        return 2
    js=load_js(args.js_routes)
    best=max(maps,key=lambda m: sum(1 for h in m['handlers'] if h['opcode'] in js and h['path']==js[h['opcode']]['trace']))
    rh={h['opcode']:h for h in best['handlers']}
    path_ok=term_ok=sem_exact=0
    mismatches=[]
    for op,j in sorted(js.items()):
        h=rh.get(op)
        if h is None:
            mismatches.append((op,'missing-rust-handler'))
            continue
        p=h['path']==j['trace']
        t=h['terminal']==j['terminal']
        rs=';'.join(norm(x) for x in h['semantic'])
        jsn=';'.join(norm(x) for x in j['semantic'])
        se=rs==jsn
        path_ok+=p; term_ok+=t; sem_exact+=se
        if not (p and t):
            mismatches.append((op,{'rust_path':h['path'],'js_path':j['trace'],'rust_terminal':h['terminal'],'js_terminal':j['terminal'],'rust_sem':h['semantic'][:3],'js_sem':j['semantic'][:3]}))
    print('parent',best['parent_function_id'],'state',best['state_var'],'opcode_max',best['opcode_max'])
    print('bindings',best['selector_bindings'])
    print('observed',len(js),'path_match',path_ok,'terminal_match',term_ok,'semantic_exact',sem_exact)
    for x in mismatches[:20]: print('MISMATCH',x)
    return 0 if path_ok==len(js) and term_ok==len(js) else 1

if __name__=='__main__':
    raise SystemExit(main())
