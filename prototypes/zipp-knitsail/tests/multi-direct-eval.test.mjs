import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';

const root=path.resolve(import.meta.dirname,'..');
const capture=path.join(root,'scripts/capture-direct-eval.mjs');
const exporter=path.join(root,'scripts/export-runtime-eval-bundle.mjs');
const sha256=x=>crypto.createHash('sha256').update(x).digest('hex');
const run=(cmd,args)=>spawnSync(cmd,args,{encoding:'utf8',timeout:60000});
function fixture(dir) {
  const source=[
    "const unicode='🦀';",
    "var first=function(D){return eval(D);};",
    "var second=function(D){return eval(D);};",
    "var dormant=function(D){return eval(D);};",
  ].join('\n');
  const entry=[
    "if(first('40 + 1')!==41) throw Error('first');",
    "if(second('40 + 1')!==41) throw Error('second');",
    "if(second('8*2')!==16) throw Error('third');",
    "if(first('40 + 1')!==41) throw Error('fourth');",
  ].join('\n');
  fs.writeFileSync(path.join(dir,'source.js'),source);
  fs.writeFileSync(path.join(dir,'entry.js'),entry);
  // Explicit UTF-16 intervals permit repeated identical eval(D) text.
  const starts=[...source.matchAll(/eval\(D\)/gu)].map(x=>x.index);
  assert.equal(starts.length,3);
  const sites=starts.map(start=>({
    evalSite:{start,end:start+7,expression:'eval(D)'},
    firstArgumentSite:{start:start+5,end:start+6,expression:'D'},
  }));
  fs.writeFileSync(path.join(dir,'config.json'),JSON.stringify({
    sourceFile:'source.js',entryFile:'entry.js',sites,
  }));
  return {source,sites};
}

test('one execution assigns identical raw strings independently to distinct direct eval sites',()=>{
  const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-multi-direct-'));
  try {
    const {source,sites}=fixture(tmp);
    const dest=path.join(tmp,'capture');
    const result=run(process.execPath,[capture,path.join(tmp,'config.json'),dest]);
    assert.equal(result.status,0,result.stderr);
    const summary=JSON.parse(result.stdout);
    assert.equal(summary.sites,3);
    assert.equal(summary.observedSites,2);
    assert.equal(summary.events,4);
    assert.equal(summary.unique,2);
    const report=JSON.parse(fs.readFileSync(path.join(dest,'report.json')));
    assert.equal(report.schemaVersion,4);
    assert.equal(report.sourceProvenance.kind,'direct-executable-multi');
    assert.deepEqual(report.dynamicCodeEvents.map(e=>e.siteIndex),[0,1,1,0]);
    assert.deepEqual(report.dynamicCodeEvents.map(e=>e.index),[0,1,2,3]);
    assert.equal(report.captureSha256,sha256(source));
    const bundle=JSON.parse(fs.readFileSync(path.join(dest,'bundle.json')));
    assert.deepEqual(bundle.sites.map(s=>s.eventCount),[2,2,0]);
    assert.deepEqual(bundle.captures.map(s=>s.directory),['site-0000','site-0001']);
    assert.deepEqual(bundle.sites.map(s=>s.evalSite),sites.map(s=>s.evalSite));
    const s0=JSON.parse(fs.readFileSync(path.join(dest,'site-0000','report.json')));
    const s1=JSON.parse(fs.readFileSync(path.join(dest,'site-0001','report.json')));
    assert.deepEqual(s0.dynamicCodeEvents.map(e=>e.globalEventIndex),[0,3]);
    assert.deepEqual(s1.dynamicCodeEvents.map(e=>e.globalEventIndex),[1,2]);
    assert.deepEqual(s0.dynamicCodeEvents.map(e=>e.index),[0,1]);
    assert.deepEqual(s1.dynamicCodeEvents.map(e=>e.index),[0,1]);
    assert.equal(s0.dynamicCodeEvents[0].sha256,s1.dynamicCodeEvents[0].sha256);
    assert.equal(s0.sourceProvenance.executable.evalSite.start,sites[0].evalSite.start);
    assert.equal(s1.sourceProvenance.executable.evalSite.start,sites[1].evalSite.start);
    assert.equal(fs.readFileSync(path.join(dest,'executable.js'),'utf8'),source);
    assert.equal(fs.readFileSync(path.join(dest,'sources',
      'eval-'+sha256('40 + 1')+'.js'),'utf8'),'40 + 1');
    assert.equal(fs.existsSync(path.join(dest,'site-0002')),false,
      'unexecuted sites must not claim observed source');

    const formatter=path.join(tmp,'formatter.cjs');
    fs.writeFileSync(formatter,[
      '#!/usr/bin/env node',
      'const fs=require("node:fs");',
      'fs.writeFileSync(process.argv[4],fs.readFileSync(process.argv[3]));',
    ].join('\n'));
    fs.chmodSync(formatter,0o755);
    const out=path.join(tmp,'export');
    const exported=run(process.execPath,[exporter,dest,out,formatter]);
    assert.equal(exported.status,0,exported.stderr);
    const exportedBundle=JSON.parse(fs.readFileSync(path.join(out,'bundle.json')));
    assert.equal(exportedBundle.captures.length,2);
    const m0=JSON.parse(fs.readFileSync(path.join(out,'site-0000','manifest.json')));
    const m1=JSON.parse(fs.readFileSync(path.join(out,'site-0001','manifest.json')));
    assert.equal(m0.schemaVersion,3);
    assert.equal(m0.eventCount,2);
    assert.equal(m0.uniqueSourceCount,1);
    assert.equal(m1.eventCount,2);
    assert.equal(m1.uniqueSourceCount,2);
    assert.equal(m0.entries[0].sha256,m1.entries[0].sha256);
    assert.deepEqual(m0.entries[0].globalEventIndices,[0,3]);
    assert.deepEqual(m1.entries[0].globalEventIndices,[1]);
    assert.deepEqual(m1.entries[1].globalEventIndices,[2]);
    assert.equal(m0.sourceProvenance.executable.evalSite.start,sites[0].evalSite.start);
    assert.equal(m1.sourceProvenance.executable.evalSite.start,sites[1].evalSite.start);
    assert.deepEqual(m0.entries[0].returnedTypes,{number:2});
    assert.equal(fs.readFileSync(path.join(out,'execution.json'),'utf8'),
      fs.readFileSync(path.join(dest,'report.json'),'utf8'));
  }finally{fs.rmSync(tmp,{recursive:true,force:true});}
});

test('ambiguous or overlapping site configurations refuse publication',()=>{
  const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-multi-reject-'));
  try{
    const {sites}=fixture(tmp);
    const file=path.join(tmp,'config.json');
    const config=JSON.parse(fs.readFileSync(file,'utf8'));
    config.sites=[sites[0],sites[0]];
    fs.writeFileSync(file,JSON.stringify(config));
    const dest=path.join(tmp,'bad');
    const result=run(process.execPath,[capture,file,dest]);
    assert.notEqual(result.status,0);
    assert.match(result.stderr,/Duplicate eval callsites/);
    assert.equal(fs.existsSync(dest),false);
    config.sites=[{evalExpression:'eval(D)',firstArgumentExpression:'D'}];
    fs.writeFileSync(file,JSON.stringify(config));
    const ambiguous=run(process.execPath,[capture,file,dest]);
    assert.notEqual(ambiguous.status,0);
    assert.match(ambiguous.stderr,/exactly once/);
    assert.equal(fs.existsSync(dest),false);
  }finally{fs.rmSync(tmp,{recursive:true,force:true});}
});

test('nested eval callsites retain original AST offsets and lexical evaluation order',()=>{
  const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-nested-eval-'));
  try {
    const source="var nested=function(D){return eval(eval(D));};";
    const expression='eval(eval(D))';
    const inner='eval(D)';
    const first=source.indexOf(expression);
    const second=source.indexOf(inner,first+5);
    const sites=[
      {evalSite:{start:first,end:first+expression.length,expression},
        firstArgumentSite:{start:second,end:second+inner.length,expression:inner}},
      {evalSite:{start:second,end:second+inner.length,expression:inner},
        firstArgumentSite:{start:second+5,end:second+6,expression:'D'}},
    ];
    fs.writeFileSync(path.join(tmp,'source.js'),source);
    fs.writeFileSync(path.join(tmp,'entry.js'),
      'if(nested("\\u002240+2\\u0022")!==42) throw Error("nested eval changed");');
    const config=path.join(tmp,'config.json');
    fs.writeFileSync(config,JSON.stringify({
      sourceFile:'source.js',entryFile:'entry.js',sites,
    }));
    const out=path.join(tmp,'out');
    const result=run(process.execPath,[capture,config,out]);
    assert.equal(result.status,0,result.stderr);
    const report=JSON.parse(fs.readFileSync(path.join(out,'report.json')));
    assert.equal(report.dynamicCodeEvents.length,2);
    assert.deepEqual(report.dynamicCodeEvents.map(e=>e.siteIndex),[1,0]);
    assert.deepEqual(report.dynamicCodeEvents.map(e=>e.outcome),['return','return']);
    const bundle=JSON.parse(fs.readFileSync(path.join(out,'bundle.json')));
    assert.deepEqual(bundle.captures.map(c=>c.siteIndex),[0,1]);
    assert.deepEqual(bundle.sites.map(c=>c.evalSite),sites.map(c=>c.evalSite));
  }finally{fs.rmSync(tmp,{recursive:true,force:true});}
});
