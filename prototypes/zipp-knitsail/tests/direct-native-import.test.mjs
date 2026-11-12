import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {spawnSync} from 'node:child_process';

const project=path.resolve(import.meta.dirname,'..');
const runner=path.join(project,'scripts/capture-direct-eval.mjs');
const exporter=path.join(project,'scripts/export-runtime-eval-bundle.mjs');
const binary=process.env.JSREDOX_DEOBFUSCATE_BIN;
if (!binary) throw Error('Set JSREDOX_DEOBFUSCATE_BIN to the native import binary');
const run=(command,args)=>{
  const result=spawnSync(command,args,{encoding:'utf8',timeout:60000});
  assert.equal(result.status,0,result.stderr||result.stdout);
  return JSON.parse(result.stdout);
};

test('actual single-stage source -> v3 manifest -> native AST verified overlay',()=>{
  const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-direct-native-'));
  try{
    const original=[
      "const emoji = '🦀';",
      "var oU=function(D){return eval(D);};",
    ].join('\n');
    const entry=[
      "if (oU('40 + 1') !== 41) throw Error('wrong direct eval result');",
      "try {oU('unknown')} catch(e) {if (!(e instanceof ReferenceError)) throw e;}",
    ].join('\n');
    for (const [name,content] of [['source.js',original],['entry.js',entry]]) {
      fs.writeFileSync(path.join(tmp,name),content);
    }
    fs.writeFileSync(path.join(tmp,'config.json'),JSON.stringify({
      sourceFile:'source.js',entryFile:'entry.js',
      sites:[{evalExpression:'eval(D)',firstArgumentExpression:'D'}],
    }));
    const capture=path.join(tmp,'capture');
    const report=run(process.execPath,[runner,path.join(tmp,'config.json'),capture]);
    assert.equal(report.events,2);
    const exported=path.join(tmp,'exported');
    const exportedResult=run(process.execPath,[exporter,capture,exported,binary]);
    assert.equal(exportedResult.observedSites,1);
    const staticTree=path.join(tmp,'static');
    fs.mkdirSync(staticTree);
    fs.writeFileSync(path.join(staticTree,'original.js'),original);
    const staticOnly=path.join(tmp,'static-only');
    run(binary,['source-tree',staticTree,staticOnly,'--max-iterations','2']);
    const combined=path.join(tmp,'combined');
    run(binary,['source-tree',staticTree,combined,'--max-iterations','2',
      '--observed-direct-bundle',exported,path.join(capture,'executable.js')]);
    const index=JSON.parse(fs.readFileSync(path.join(combined,'runtime-observed/index.json')));
    assert.equal(index.schema,'js-redox/linked-runtime-source-tree/v3');
    assert.equal(index.captures.length,1);
    assert.equal(index.captures[0].provenanceKind,'direct');
    assert.equal(index.captures[0].calls,2);
    assert.equal(index.captures[0].sources,2);
    assert.equal(index.captures[0].staticAstMatches,1);
    const directory=index.captures[0].directory;
    const origin=JSON.parse(fs.readFileSync(path.join(combined,directory,'origin.json')));
    assert.equal(origin.sourceProvenance.kind,'direct-executable');
    assert.equal(origin.outerLoader,null);
    assert.equal(origin.originalEvalSite.argumentReferences[0].role,'formal:0:0');
    const a=fs.readFileSync(path.join(combined,'original.js'));
    const b=fs.readFileSync(path.join(staticOnly,'original.js'));
    assert.deepEqual(a,b);
    assert.deepEqual(fs.readFileSync(path.join(combined,'reconstruction.json')),
      fs.readFileSync(path.join(staticOnly,'reconstruction.json')));
    assert.deepEqual(fs.readFileSync(path.join(combined,directory,'manifest.json')),
      fs.readFileSync(path.join(exported,'site-0000','manifest.json')));

    // Original input is independently verified: mismatched source bytes must
    // not leave an output directory, and cannot reuse a previous success.
    const badSource=path.join(tmp,'wrong.js');
    fs.writeFileSync(badSource,original+'// tampered');
    const badDest=path.join(tmp,'bad-output');
    const failed=spawnSync(binary,['source-tree',staticTree,badDest,
      '--max-iterations','2','--observed-direct',exported,badSource],
      {encoding:'utf8',timeout:60000});
    assert.notEqual(failed.status,0);
    assert.match(failed.stderr,/SHA-256 mismatch/);
    assert.equal(fs.existsSync(badDest),false);
  } finally{fs.rmSync(tmp,{recursive:true,force:true});}
});
