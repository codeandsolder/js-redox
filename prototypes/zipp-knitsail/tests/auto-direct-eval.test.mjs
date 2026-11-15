import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {spawnSync} from 'node:child_process';

const runner=path.resolve(import.meta.dirname,'../scripts/capture-direct-eval.mjs');
const invoke=(config,out)=>spawnSync(process.execPath,[runner,config,out],
  {encoding:'utf8',timeout:25000});

test('AST site enumeration is used exactly without manually supplying offsets',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-auto-site-'));
  try{
    const original=[
      "const emoji = '🦀';",
      'var first=function(D){return eval(D);};',
      'var second=function(D){return eval(D);};',
    ].join('\n');
    fs.writeFileSync(path.join(root,'source.js'),original);
    fs.writeFileSync(path.join(root,'entry.js'),
      "if(first('2+2')!==4 || second('2+2')!==4) throw Error('bad result');");
    const parser=path.join(root,'parser.cjs');
    fs.writeFileSync(parser,[
      '#!/usr/bin/env node',
      'const fs=require("node:fs");',
      'const crypto=require("node:crypto");',
      'if(process.argv[2]!=="eval-sites") process.exit(2);',
      'const code=fs.readFileSync(process.argv[3],"utf8");',
      'const sha256=crypto.createHash("sha256").update(code).digest("hex");',
      'const spans=[...code.matchAll(/eval\\(D\\)/g)].map(x=>x.index);',
      'console.log(JSON.stringify({schemaVersion:1,sourceSha256:sha256,',
      'sites:spans.map(start=>({evalSite:{start,end:start+7,expression:"eval(D)"},',
      'firstArgumentSite:{start:start+5,end:start+6,expression:"D"}})),',
      'unsupported:[]}));',
    ].join('\n'));
    fs.chmodSync(parser,0o755);
    const config=path.join(root,'config.json');
    fs.writeFileSync(config,JSON.stringify({
      sourceFile:'source.js',entryFile:'entry.js',sites:'all',
      parserBinary:'parser.cjs',
    }));
    const out=path.join(root,'out');
    const result=invoke(config,out);
    assert.equal(result.status,0,result.stderr);
    const report=JSON.parse(fs.readFileSync(path.join(out,'report.json')));
    assert.deepEqual(report.dynamicCodeEvents.map(e=>e.siteIndex),[0,1]);
    assert.equal(report.sourceProvenance.executable.evalSites.length,2);
    assert.equal(JSON.parse(fs.readFileSync(path.join(out,'bundle.json'))).captures.length,2);
    const bad=path.join(root,'bad');
    fs.writeFileSync(parser,fs.readFileSync(parser,'utf8')
      .replace('unsupported:[]','unsupported:[{reason:"spread argument"}]'));
    const fail=invoke(config,bad);
    assert.notEqual(fail.status,0);
    assert.match(fail.stderr,/cannot be captured/);
    assert.equal(fs.existsSync(bad),false);
  }finally{fs.rmSync(root,{recursive:true,force:true});}
});
