import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';

const root=path.resolve(import.meta.dirname,'..');
const capture=path.join(root,'scripts/capture-direct-eval.mjs');
const exporter=path.join(root,'scripts/export-runtime-eval.mjs');
const digest=value=>crypto.createHash('sha256').update(value).digest('hex');
const invoke=(tool,args)=>spawnSync(process.execPath,[tool,...args],
  {encoding:'utf8',timeout:30000});

test('single-stage eval source with lexical scope records direct provenance',()=>{
  const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-direct-'));
  try {
    const source=[
      "const marker='🦀';",
      "function worker(D) { const suffix=' + 2'; return eval(D + suffix); }",
    ].join('\n');
    const entry=[
      "if(worker('40')!==42) throw Error('direct eval not in lexical scope');",
      "if(worker('40')!==42) throw Error('second call failed');",
      "try { worker('missingName'); throw Error('should have thrown'); }",
      "catch (e) { if (!(e instanceof ReferenceError)) throw e; }",
    ].join('\n');
    fs.writeFileSync(path.join(tmp,'script.js'),source);
    fs.writeFileSync(path.join(tmp,'entry.js'),entry);
    const cfg={sourceFile:'script.js',entryFile:'entry.js',
      evalExpression:'eval(D + suffix)', firstArgumentExpression:'D + suffix'};
    fs.writeFileSync(path.join(tmp,'config.json'),JSON.stringify(cfg));
    const output=path.join(tmp,'direct');
    const result=invoke(capture,[path.join(tmp,'config.json'),output]);
    assert.equal(result.status,0,result.stderr);
    const report=JSON.parse(fs.readFileSync(path.join(output,'report.json')));
    assert.equal(report.schemaVersion,3);
    assert.equal(report.captureSha256,digest(source));
    assert.equal(report.sourceProvenance.kind,'direct-executable');
    assert.equal(report.sourceProvenance.executable.sha256,digest(source));
    assert.equal(report.sourceProvenance.executable.evalSite.expression,'eval(D + suffix)');
    assert.deepEqual(report.dynamicCodeEvents.map(x=>x.outcome),
      ['return','return','throw']);
    assert.equal(report.dynamicCodeEvents[0].length,6);
    assert.equal(fs.readFileSync(path.join(output,'executable.js'),'utf8'),source);
    assert.equal(fs.readFileSync(path.join(output,'sources',
      'eval-'+digest('40 + 2')+'.js'),'utf8'),'40 + 2');
    assert.notEqual(invoke(capture,[path.join(tmp,'config.json'),output]).status,0);
    const formatter=path.join(tmp,'formatter.cjs');
    fs.writeFileSync(formatter,[
      '#!/usr/bin/env node',
      'const fs=require("node:fs");',
      'fs.writeFileSync(process.argv[4],fs.readFileSync(process.argv[3]));',
    ].join('\n'));
    fs.chmodSync(formatter,0o755);
    const exported=path.join(tmp,'exported');
    const result2=invoke(exporter,[path.join(output,'report.json'),
      path.join(output,'sources'),exported,formatter]);
    assert.equal(result2.status,0,result2.stderr);
    const manifest=JSON.parse(fs.readFileSync(path.join(exported,'manifest.json')));
    assert.equal(manifest.schemaVersion,3);
    assert.equal(manifest.captureSha256,digest(source));
    assert.equal(manifest.sourceProvenance.kind,'direct-executable');
    assert.equal(manifest.eventCount,3);
    assert.equal(manifest.uniqueSourceCount,2);
    assert.equal(manifest.entries[0].occurrences,2);
    assert.equal(manifest.entries[1].threw,1);
  } finally {
    fs.rmSync(tmp,{recursive:true,force:true});
  }
});

test('single-stage capture refuses malformed direct source coordinates',()=>{
  const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-direct-invalid-'));
  try {
    fs.writeFileSync(path.join(tmp,'source.js'),"function oU(D){return eval(D);}");
    const cfg={sourceFile:'source.js',evalExpression:'eval(D)',
      firstArgumentExpression:'wrong'};
    const config=path.join(tmp,'config.json');
    fs.writeFileSync(config,JSON.stringify(cfg));
    const dest=path.join(tmp,'out');
    const result=invoke(capture,[config,dest]);
    assert.notEqual(result.status,0);
    assert.equal(fs.existsSync(dest),false);
    assert.equal(fs.readdirSync(tmp).filter(x=>x.startsWith('.jsredox-direct-')).length,0);
  } finally {fs.rmSync(tmp,{recursive:true,force:true});}
});

test('top-level direct eval needs neither entrypoint nor synthetic loader',()=>{
  const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-top-level-'));
  try{
    const source="const answer=eval('20+22'); if(answer!==42) throw Error('wrong answer');";
    const config=path.join(tmp,'config.json');
    fs.writeFileSync(path.join(tmp,'script.js'),source);
    fs.writeFileSync(config,JSON.stringify({
      sourceFile:'script.js',
      evalExpression:"eval('20+22')",
      firstArgumentExpression:"'20+22'",
    }));
    const output=path.join(tmp,'out');
    const result=invoke(capture,[config,output]);
    assert.equal(result.status,0,result.stderr);
    const report=JSON.parse(fs.readFileSync(path.join(output,'report.json')));
    assert.equal(report.schemaVersion,3);
    assert.equal(report.dynamicCodeEvents.length,1);
    assert.equal(report.dynamicCodeEvents[0].outcome,'return');
    assert.equal(report.sourceProvenance.kind,'direct-executable');
    assert.equal(fs.existsSync(path.join(output,'outer.js')),false);
    assert.equal(fs.readFileSync(path.join(output,'executable.js'),'utf8'),source);
  }finally{fs.rmSync(tmp,{recursive:true,force:true});}
});
