import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {spawnSync} from 'node:child_process';

const root=path.resolve(import.meta.dirname,'..');
const capture=path.join(root,'scripts/capture-direct-eval.mjs');
const exporter=path.join(root,'scripts/export-runtime-eval-bundle.mjs');
const binary=process.env.JSREDOX_DEOBFUSCATE_BIN;
if (!binary) throw Error('Set JSREDOX_DEOBFUSCATE_BIN to native importer binary');
const invoke=(cmd,args)=>spawnSync(cmd,args,{encoding:'utf8',timeout:75000});
const pass=(cmd,args)=>{
  const result=invoke(cmd,args);
  assert.equal(result.status,0,result.stderr||result.stdout);
  return JSON.parse(result.stdout);
};
test('native multi-site bundle keeps same raw source linked to distinct verified origins',()=>{
  const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-multi-native-'));
  try{
    const source=[
      "const marker='🦀';",
      "var alpha=function(D){return eval(D);};",
      "var beta=function(D){return eval(D);};",
      "var dormant=function(D){return eval(D);};",
    ].join('\n');
    const entry=[
      "if(alpha('40 + 2')!==42) throw Error('alpha');",
      "if(beta('40 + 2')!==42) throw Error('beta');",
      "if(beta('6*7')!==42) throw Error('beta other');",
      "if(alpha('40 + 2')!==42) throw Error('alpha again');",
    ].join('\n');
    const offsets=[...source.matchAll(/eval\(D\)/gu)].map(x=>x.index);
    const sites=offsets.map(start=>({
      evalSite:{start,end:start+7,expression:'eval(D)'},
      firstArgumentSite:{start:start+5,end:start+6,expression:'D'},
    }));
    fs.writeFileSync(path.join(tmp,'script.js'),source);
    fs.writeFileSync(path.join(tmp,'entry.js'),entry);
    fs.writeFileSync(path.join(tmp,'config.json'),JSON.stringify({
      sourceFile:'script.js',entryFile:'entry.js',sites,
    }));
    const captured=path.join(tmp,'capture');
    const run=pass(process.execPath,[capture,path.join(tmp,'config.json'),captured]);
    assert.equal(run.sites,3);
    assert.equal(run.observedSites,2);
    const exportDir=path.join(tmp,'exported');
    pass(process.execPath,[exporter,captured,exportDir,binary]);
    const tree=path.join(tmp,'static');
    fs.mkdirSync(tree);
    fs.writeFileSync(path.join(tree,'original.js'),source);
    const baseline=path.join(tmp,'baseline');
    pass(binary,['source-tree',tree,baseline,'--max-iterations','2']);
    const combined=path.join(tmp,'combined');
    pass(binary,['source-tree',tree,combined,'--max-iterations','2',
      '--observed-direct-bundle',exportDir,path.join(captured,'executable.js')]);
    const index=JSON.parse(fs.readFileSync(path.join(combined,'runtime-observed/index.json')));
    assert.equal(index.captures.length,2);
    assert.deepEqual(index.captures.map(x=>x.executableSite),
      offsets.slice(0,2).map(x=>[x,x+7]));
    assert.deepEqual(index.captures.map(x=>x.calls),[2,2]);
    assert.deepEqual(index.captures.map(x=>x.sources),[1,2]);
    assert.deepEqual(index.captures.map(x=>x.staticAstMatches),[1,1]);
    const origins=index.captures.map(x=>
      JSON.parse(fs.readFileSync(path.join(combined,x.directory,'origin.json'))));
    assert.equal(origins[0].sourceProvenance.executable.evalSite.start,offsets[0]);
    assert.equal(origins[1].sourceProvenance.executable.evalSite.start,offsets[1]);
    assert.deepEqual(fs.readFileSync(path.join(combined,'original.js')),
      fs.readFileSync(path.join(baseline,'original.js')));
    assert.deepEqual(fs.readFileSync(path.join(combined,'reconstruction.json')),
      fs.readFileSync(path.join(baseline,'reconstruction.json')));
    for(const [i,record] of index.captures.entries()) {
      assert.deepEqual(
        fs.readFileSync(path.join(combined,record.directory,'manifest.json')),
        fs.readFileSync(path.join(exportDir,'site-'+String(i).padStart(4,'0'),'manifest.json')));
    }
    const commonA=JSON.parse(fs.readFileSync(path.join(exportDir,'site-0000','manifest.json')));
    const commonB=JSON.parse(fs.readFileSync(path.join(exportDir,'site-0001','manifest.json')));
    assert.equal(commonA.entries[0].sha256,commonB.entries[0].sha256,
      'the identical string belongs to two distinct source locations');
    assert.deepEqual(commonA.entries[0].globalEventIndices,[0,3]);
    assert.deepEqual(commonB.entries[0].globalEventIndices,[1]);
    assert.notEqual(index.captures[0].directory,index.captures[1].directory);
    // A single corrupt source site must prevent publishing *any* overlay.
    const altered=path.join(exportDir,'site-0001','manifest.json');
    const metadata=JSON.parse(fs.readFileSync(altered));
    metadata.sourceProvenance.executable.evalSite.start+=1;
    fs.writeFileSync(altered,JSON.stringify(metadata));
    const bad=path.join(tmp,'bad');
    const failed=invoke(binary,['source-tree',tree,bad,'--max-iterations','2',
      '--observed-direct-bundle',exportDir,path.join(captured,'executable.js')]);
    assert.notEqual(failed.status,0);
    assert.match(failed.stderr,/bundle|source-site|witness/i);
    assert.equal(fs.existsSync(bad),false);

    // A per-site witness cannot smuggle duplicate session positions in a
    // single content-addressed source, even if its aggregate counts match.
    const wrongOrder=JSON.parse(fs.readFileSync(path.join(
      exportDir,'site-0000','manifest.json')));
    wrongOrder.entries[0].globalEventIndices=[0,0];
    fs.writeFileSync(path.join(exportDir,'site-0000','manifest.json'),
      JSON.stringify(wrongOrder));
    const badOrder=path.join(tmp,'bad-order');
    const denied=invoke(binary,['source-tree',tree,badOrder,'--max-iterations','2',
      '--observed-direct-bundle',exportDir,path.join(captured,'executable.js')]);
    assert.notEqual(denied.status,0);
    assert.match(denied.stderr,/event ordering|global event sequence/);
    assert.equal(fs.existsSync(badOrder),false);
  }finally{fs.rmSync(tmp,{recursive:true,force:true});}
});
