import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {spawnSync} from 'node:child_process';

const binary=process.env.JSREDOX_DEOBFUSCATE_BIN;
if (!binary) throw Error('Set JSREDOX_DEOBFUSCATE_BIN to the built PR #184 deobfuscate-safe');
const project=path.resolve(import.meta.dirname,'..');
const runner=path.join(project,'scripts/capture-vm-eval.mjs');
const exporter=path.join(project,'scripts/export-runtime-eval.mjs');
const invoke=(program,args)=>spawnSync(program,args,{encoding:'utf8',timeout:30000});
const assertPass=(program,args)=>{
  const result=invoke(program,args);
  assert.equal(result.status,0,result.stderr || result.stdout);
  return result.stdout;
};
test('unrelated decoded VM -> generic capture -> v2 exporter -> native source-tree importer',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-v2-e2e-'));
  try {
    const inner="var marker='🦀'; var worker=function(D){return eval(D+' + 1');};";
    const outer='var packed='+JSON.stringify('\n'+inner)+'; (0,eval)(packed);';
    const entry=[
      "if(worker('1')!==2) throw Error('unexpected eval return');",
      "try { worker('missingVar'); } catch (error) {",
      " if(!(error instanceof ReferenceError)) throw error; }",
    ].join('\n');
    for(const [f,v] of [['outer.js',outer],['inner.js',inner],['entry.js',entry]]){
      fs.writeFileSync(path.join(root,f),v);
    }
    const config={
      outerFile:'outer.js',entryFile:'entry.js',innerFile:'inner.js',
      evalExpression:"eval(D+' + 1')",
      firstArgumentExpression:"D+' + 1'",
    };
    fs.writeFileSync(path.join(root,'config.json'),JSON.stringify(config));
    const captured=path.join(root,'capture'),exported=path.join(root,'exported');
    const originalTree=path.join(root,'static'),baseline=path.join(root,'baseline');
    const combined=path.join(root,'combined');
    fs.mkdirSync(originalTree);
    fs.writeFileSync(path.join(originalTree,'original.js'),inner);
    const summary=JSON.parse(assertPass(process.execPath,[runner,
      path.join(root,'config.json'),captured]));
    assert.equal(summary.events,2);
    assert.equal(summary.unique,2);
    const exportedSummary=JSON.parse(assertPass(process.execPath,[exporter,
      path.join(captured,'report.json'),path.join(captured,'sources'),exported,binary]));
    assert.equal(exportedSummary.events,2);
    assert.equal(exportedSummary.unique,2);
    assertPass(binary,['source-tree',originalTree,baseline,'--max-iterations','4']);
    assertPass(binary,['source-tree',originalTree,combined,'--max-iterations','4',
      '--observed-eval',exported,path.join(captured,'outer.js'),path.join(captured,'inner.js')]);
    const index=JSON.parse(fs.readFileSync(path.join(combined,'runtime-observed/index.json')));
    assert.equal(index.schema,'js-redox/linked-runtime-source-tree/v2');
    assert.equal(index.captures.length,1);
    assert.equal(index.captures[0].calls,2);
    assert.equal(index.captures[0].sources,2);
    assert.ok(index.captures[0].staticAstMatches>=1,'expected OXC lexical site match');
    assert.ok(fs.readFileSync(path.join(combined,'original.js')).equals(
      fs.readFileSync(path.join(baseline,'original.js'))),'static JS must be byte-identical');
    assert.ok(fs.readFileSync(path.join(combined,'reconstruction.json')).equals(
      fs.readFileSync(path.join(baseline,'reconstruction.json'))),'static metadata must match');
    const relative=index.captures[0].directory;
    assert.ok(fs.readFileSync(path.join(combined,relative,'manifest.json')).equals(
      fs.readFileSync(path.join(exported,'manifest.json'))),'complete original manifest survives');
    const origin=JSON.parse(fs.readFileSync(path.join(combined,relative,'origin.json')));
    assert.ok(origin.staticAstStructuralMatches.some(s=>s.path==='original.js'));
    assert.equal(origin.originalEvalSite.argumentShapes.length,1);
    assert.ok(origin.originalEvalSite.argumentReferences.some(x=>x.role==='formal:0:0'));
    assert.ok(fs.existsSync(path.join(combined,'original.js.runtime-evidence.md')));
    console.log(JSON.stringify({events:2,unique:2,matches:index.captures[0].staticAstMatches,
      originalSite:origin.originalEvalSite.argument,
      staticPreserved:true,manifestPreserved:true}));
  }finally{
    fs.rmSync(root,{recursive:true,force:true});
  }
});
