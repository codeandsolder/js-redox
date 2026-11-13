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
        returned:8,threw:0,pending:0,
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
        {total:7,matched:5,ambiguous:0,unmatched:0,unavailable:2,
          returned:7,threw:0,pending:0});
    }finally{fs.rmSync(dir,{recursive:true,force:true});}
  });

test('OXC-verified automatic Node capture accepts every parenthesized direct eval',
  {skip:!oxc},()=>{
    const dir=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-paren-capture-'));
    try{
      const source=[
        'let x=10;',
        "const values=[eval('x+1'),(eval)('x+2'),((eval))('x+3'),",
        "eval/*comment*/('x+4'),eval",
        "('x+5')];",
        'if(values.join()!="11,12,13,14,15")throw Error("bad");',
      ].join('\n');
      const src=path.join(dir,'original.js');
      fs.writeFileSync(src,source);
      const cfg=path.join(dir,'config.json'),out=path.join(dir,'captured');
      fs.writeFileSync(cfg,JSON.stringify({
        sourceFile:'original.js',sites:'all',parserBinary:oxc,
      }));
      const runner=path.resolve(import.meta.dirname,
        '../scripts/capture-direct-eval.mjs');
      const stats=exec(process.execPath,[runner,cfg,out]);
      assert.equal(stats.truncated,false);
      assert.equal(stats.events,5);
      const bundle=JSON.parse(fs.readFileSync(path.join(out,'bundle.json'),'utf8'));
      assert.equal(bundle.sites.length,5);
      assert.equal(bundle.captures.length,5);
      assert.deepEqual(bundle.sites.map(e=>e.eventCount),[1,1,1,1,1]);
    }finally{fs.rmSync(dir,{recursive:true,force:true});}
  });

test('real native ZIPP distinguishes caught syntax and runtime throws from returns',
  {skip:!canRun},()=>{
    const dir=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-zipp-throw-'));
    try{
      const source=[
        "const value = eval('4+8');",
        "try { eval('var ???'); } catch(e) {}",
        "try { eval('throw Error(\"fatal\")'); } catch(e) {}",
        "const after = eval('true');",
        "if(value!==12||after!==true)throw Error('behavior changed');",
      ].join('\n');
      const src=path.join(dir,'original.js');
      fs.writeFileSync(src,source);
      const ast=exec(oxc,['eval-sites',src]);
      const runtime=exec(zipp,[src]);
      assert.equal(runtime.execution.initial.ok,true,runtime.execution.initial.error);
      const linked=correlateZippEvalSites(fs.readFileSync(src),ast,runtime);
      assert.deepEqual(linked.summary,{
        total:4,matched:4,ambiguous:0,unmatched:0,unavailable:0,
        returned:2,threw:2,pending:0,
      });
      assert.deepEqual(linked.events.map(e=>e.outcome),[
        {status:'returned',type:'number'},
        {status:'threw'},
        {status:'threw'},
        {status:'returned',type:'boolean'},
      ]);
      assert.equal(linked.observerTruncated,false);
    }finally{fs.rmSync(dir,{recursive:true,force:true});}
  });

test('native ZIPP and Node agree on exact per-site direct eval sources and synchronous outcomes',
  {skip:!canRun},()=>{
    const dir=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-zipp-node-outcomes-'));
    try{
      const source=[
        'const values=[',
        ' eval("1+2"),',
        ' eval("\'hello\'"),',
        ' eval("false"),',
        ' eval("undefined"),',
        ' eval("null")',
        '];',
        'if(values[0]!==3||values[1]!=="hello"||values[2]!==false||',
        ' values[3]!==undefined||values[4]!==null)throw Error("changed");',
        'try{eval("var ???");}catch(e){}',
      ].join('\n');
      const src=path.join(dir,'original.js');
      fs.writeFileSync(src,source);
      const config=path.join(dir,'config.json');
      fs.writeFileSync(config,JSON.stringify({
        sourceFile:'original.js',sites:'all',parserBinary:oxc,
      }));
      const out=path.join(dir,'captured');
      const runner=path.resolve(import.meta.dirname,'../scripts/capture-direct-eval.mjs');
      const nodeStats=exec(process.execPath,[runner,config,out]);
      assert.equal(nodeStats.events,6);
      const nodeReport=JSON.parse(fs.readFileSync(path.join(out,'report.json'),'utf8'));
      const ast=exec(oxc,['eval-sites',src]);
      const runtime=exec(zipp,[src]);
      assert.equal(runtime.execution.initial.ok,true,runtime.execution.initial.error);
      const zippReport=correlateZippEvalSites(fs.readFileSync(src),ast,runtime);
      assert.equal(zippReport.observerTruncated,false);
      assert.deepEqual(zippReport.summary,{
        total:6,matched:6,ambiguous:0,unmatched:0,unavailable:0,
        returned:5,threw:1,pending:0,
      });
      const bySite=new Map(nodeReport.dynamicCodeEvents.map(e=>[e.siteIndex,e]));
      assert.equal(bySite.size,6);
      for(const event of zippReport.events){
        const observed=bySite.get(event.correlation.inventoryIndex);
        assert.ok(observed,'expected an independently observed Node site');
        assert.equal(event.sourceSha256,observed.sha256);
        assert.equal(event.outcome.status,
          observed.outcome==='return'?'returned':'threw');
        if(event.outcome.status==='returned'){
          assert.equal(event.outcome.type,observed.resultType);
        }
      }
    }finally{fs.rmSync(dir,{recursive:true,force:true});}
  });
