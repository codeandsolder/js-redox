import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import {correlateZippEvalSites} from '../scripts/link-zipp-eval-sites.mjs';

const zipp=process.env.ZIPP_NATIVE_OBSERVER_BIN;
const oxc=process.env.JSREDOX_DEOBFUSCATE_BIN;
const canRun=Boolean(zipp && oxc);
const exec=(binary,args)=>{
  const run=spawnSync(binary,args,{encoding:'utf8',timeout:90000,
    maxBuffer:64*1024*1024});
  assert.equal(run.status,0,run.error?.message??run.stderr);
  return JSON.parse(run.stdout);
};

test('real ZIPP native runtime and OXC AST agree on nested, cached and generated eval origins',
  {skip:!canRun},()=>{
    const dir=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-zipp-oxc-'));
    try{
      const script=[
        "const crab='🦀';",
        "function nested(D) { return eval(eval(D)); }",
        "function cached(n) { let captured=n; return eval('captured+1'); }",
        'if (nested(\'"40+2"\')!==42 || cached(1)!==2 || cached(5)!==6) throw Error("bad");',
        'eval("function later(){return eval(\'6+2\');}");',
        'if (later()!==8) throw Error("generated");',
        'const ctor=Function("return 4"); if(ctor()!==4) throw Error("ctor");',
        'const indirect=(0,eval)("3+4"); if(indirect!==7) throw Error("indirect");',
      ].join('\n');
      const src=path.join(dir,'original.js');
      fs.writeFileSync(src,script);
      const ast=exec(oxc,['eval-sites',src]);
      const runtime=exec(zipp,[src]);
      assert.equal(runtime.execution.initial.ok,true,
        runtime.execution.initial.error);
      assert.equal(runtime.truncated,false);
      assert.equal(ast.sites.length,4);
      assert.equal(ast.unsupported.length,0);
      assert.equal(runtime.events.length,8);
      const linked=correlateZippEvalSites(fs.readFileSync(src),ast,runtime);
      assert.deepEqual(linked.summary,{
        total:8,matched:5,ambiguous:0,unmatched:0,unavailable:3,
      });
      assert.deepEqual(linked.events.filter(e=>e.correlation.status==='matched')
        .map(e=>e.correlation.inventoryIndex),[1,0,2,2,3]);
      assert.ok(linked.events.some(e=>e.correlation.reason==='runtime-installed-caller'));
      assert.ok(linked.events.some(e=>e.kind==='function-constructor'));
      assert.ok(linked.events.some(e=>e.kind==='indirect-or-host'));
      assert.throws(()=>correlateZippEvalSites(Buffer.from(script+' '),ast,runtime),
        /SHA-256/);
    }finally{fs.rmSync(dir,{recursive:true,force:true});}
  });

test('a separate host entry is not assigned an original AST callsite', {
  skip:!canRun,
},()=>{
  const dir=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-zipp-entry-'));
  try{
    const src=path.join(dir,'original.js'),entry=path.join(dir,'entry.js');
    fs.writeFileSync(src,"const crab='🦀'; function target(D){return eval(D);}");
    fs.writeFileSync(entry,"if(target('4+6')!==10)throw Error('bad');");
    const ast=exec(oxc,['eval-sites',src]);
    const runtime=exec(zipp,[src,entry]);
    assert.equal(runtime.execution.initial.ok,true);
    assert.equal(runtime.execution.entry.ok,true,
      runtime.execution.entry.error);
    const report=correlateZippEvalSites(fs.readFileSync(src),ast,runtime);
    assert.equal(report.summary.matched,1);
    assert.ok(report.events.some(e=>e.kind==='indirect-or-host' &&
      e.correlation.status==='unavailable'));
  }finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('parentheses preserve direct-eval references; comma and optional calls do not',
  {skip:!canRun},()=>{
    const dir=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-zipp-parens-'));
    try{
      const source=[
        "const crab='🦀';",
        'let cap=10;',
        "const values=[eval('cap+1'),(eval)('cap+2'),((eval))('cap+3'),",
        " eval/*comment*/('cap+4'),eval",
        " ('cap+5'),(0,eval)('2+2'),eval?.('3+2')];",
        'if(JSON.stringify(values)!==JSON.stringify([11,12,13,14,15,4,5]))',
        " throw Error('wrong runtime semantics');",
      ].join('\n');
      const src=path.join(dir,'original.js');
      fs.writeFileSync(src,source);
      const ast=exec(oxc,['eval-sites',src]);
      const runtime=exec(zipp,[src]);
      assert.equal(runtime.execution.initial.ok,true,
        runtime.execution.initial.error);
      assert.equal(ast.sites.length,5);
      assert.equal(ast.unsupported.length,0);
      const linked=correlateZippEvalSites(fs.readFileSync(src),ast,runtime);
      assert.deepEqual(linked.summary,
        {total:7,matched:5,ambiguous:0,unmatched:0,unavailable:2});
    }finally{fs.rmSync(dir,{recursive:true,force:true});}
  });
