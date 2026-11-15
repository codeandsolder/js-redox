import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';

const exporter = path.resolve(import.meta.dirname, '../scripts/export-runtime-eval.mjs');
const digest = text => crypto.createHash('sha256').update(text).digest('hex');

test('preserves exact observed code, deduplicates, reports parse refusals and refuses tampered sources', () => {
  const root = fs.mkdtempSync(path.join(import.meta.dirname, '.runtime-eval-test-'));
  try {
    const sourceDir = path.join(root, 'source');
    fs.mkdirSync(sourceDir);
    const callable = '0,(function(x){return x+1})';
    const invalid = '{';
    const h1 = digest(callable), h2 = digest(invalid);
    for (const [hash, source] of [[h1,callable],[h2,invalid]]) {
      fs.writeFileSync(path.join(sourceDir, 'eval-' + hash + '.js'), source);
    }
    const report = {
      htmlSha256:'a'.repeat(64), outerVmSha256:'b'.repeat(64),
      sourceProvenance:{
        outerLoader:{
          sha256:'b'.repeat(64),decodedBy:'observed-first-indirect-eval',
          indirectEvalSite:{start:2,end:11,expression:'(0,eval)('},
        },
        innerExecutable:{
          sha256:'c'.repeat(64),strippedLeadingNewlineCodeUnits:25,
          evalSite:{start:12,end:19,expression:'eval(D)'},
        },
      },
      dynamicTruncated:false,
      dynamicCodeEvents:[
        {index:0,type:'string',length:callable.length,sha256:h1,outcome:'return',resultType:'function'},
        {index:1,type:'string',length:invalid.length,sha256:h2,outcome:'throw',thrownType:'object'},
        {index:2,type:'string',length:callable.length,sha256:h1,outcome:'return',resultType:'function'},
      ],
    };
    const reportFile = path.join(root, 'report.json');
    fs.writeFileSync(reportFile, JSON.stringify(report));
    const stub = path.join(root, 'formatter.cjs');
    fs.writeFileSync(stub, [
      '#!/usr/bin/env node',
      'const fs=require("node:fs");',
      'const s=fs.readFileSync(process.argv[3],"utf8");',
      'if(s==="{"){console.error("parse-failure");process.exit(1)}',
      'fs.writeFileSync(process.argv[4],s+String.fromCharCode(59,10));',
    ].join('\n'));
    fs.chmodSync(stub, 0o755);
    const out = path.join(root, 'out');
    const invoke = destination => spawnSync(process.execPath,
      [exporter,reportFile,sourceDir,destination,stub],{encoding:'utf8'});
    const result = invoke(out);
    assert.equal(result.status,0,result.stderr);
    const manifest = JSON.parse(fs.readFileSync(path.join(out,'manifest.json'),'utf8'));
    assert.equal(manifest.schemaVersion,2);
    assert.equal(manifest.sourceProvenance.outerLoader.sha256,'b'.repeat(64));
    assert.equal(manifest.sourceProvenance.innerExecutable.sha256,'c'.repeat(64));
    assert.equal(manifest.sourceProvenance.innerExecutable.evalSite.start,12);
    assert.equal(manifest.uniqueSourceCount,2);
    assert.equal(manifest.eventCount,3);
    assert.equal(manifest.entries[0].occurrences,2);
    assert.equal(manifest.entries[0].returnedTypes.function,2);
    assert.equal(manifest.entries[0].readableStatus,'formatted');
    assert.equal(manifest.entries[1].readableStatus,'standalone-parse-rejected');
    assert.equal(fs.readFileSync(path.join(out,'raw',h1+'.txt'),'utf8'),callable);
    assert.equal(fs.readFileSync(path.join(out,'readable',h1+'.js'),'utf8'),callable+';\n');
    assert.equal(fs.existsSync(path.join(out,'readable',h2+'.js')),false);
    assert.notEqual(invoke(out).status,0,'existing destinations must not be overwritten');

    const legacy={...report,sourceProvenance:undefined,vmSha256:'b'.repeat(64),
      dynamicEvalSite:{start:12,end:19}};
    fs.writeFileSync(reportFile,JSON.stringify(legacy));
    const oldFormat=invoke(path.join(root,'legacy'));
    assert.notEqual(oldFormat.status,0,'v1 data must not be silently accepted');
    assert.match(oldFormat.stderr,/dual-layer/);
    fs.writeFileSync(reportFile,JSON.stringify(report));
    fs.writeFileSync(path.join(sourceDir,'eval-'+h1+'.js'),'modified');
    const tamperedOut = path.join(root,'tampered');
    const failed = invoke(tamperedOut);
    assert.notEqual(failed.status,0,'tampered content must fail');
    assert.match(failed.stderr,/hash mismatch/);
    assert.equal(fs.existsSync(tamperedOut),false);
    assert.equal(fs.existsSync(tamperedOut+'.tmp-'+process.pid),false);
  } finally {
    fs.rmSync(root,{recursive:true,force:true});
  }
});
