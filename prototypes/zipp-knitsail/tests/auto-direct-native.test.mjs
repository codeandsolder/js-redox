import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {spawnSync} from 'node:child_process';

const project=path.resolve(import.meta.dirname,'..');
const runner=path.join(project,'scripts/capture-direct-eval.mjs');
const exporter=path.join(project,'scripts/export-runtime-eval-bundle.mjs');
const binary=process.env.JSREDOX_DEOBFUSCATE_BIN;
if(!binary) throw Error('Set JSREDOX_DEOBFUSCATE_BIN to native deobfuscate-safe binary');
const pass=(command,args)=>{
  const r=spawnSync(command,args,{encoding:'utf8',timeout:90000});
  assert.equal(r.status,0,r.stderr||r.stdout);
  return JSON.parse(r.stdout);
};
test('AST auto-discovery finds nested and dormant direct eval sites, verifies full native import',()=>{
  const dir=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-real-ast-auto-'));
  try{
    const source=[
      "const emoji='🦀';",
      "var outer=function(D){return eval(eval(D));};",
      "var dormant=function(D){return eval(D);};",
    ].join('\n');
    const entry='if(outer(\'"40+2"\')!==42) throw Error("nested result changed");';
    const original=path.join(dir,'source.js');
    fs.writeFileSync(original,source);
    fs.writeFileSync(path.join(dir,'entry.js'),entry);
    const inventory=pass(binary,['eval-sites',original]);
    assert.equal(inventory.schemaVersion,1);
    assert.equal(inventory.sites.length,3);
    assert.equal(inventory.unsupported.length,0);
    assert.equal(inventory.sites[0].evalSite.expression,'eval(eval(D))');
    assert.equal(inventory.sites[1].evalSite.expression,'eval(D)');
    const config=path.join(dir,'config.json');
    fs.writeFileSync(config,JSON.stringify({
      sourceFile:'source.js',entryFile:'entry.js',
      sites:'all',parserBinary:binary,
    }));
    const captured=path.join(dir,'capture');
    const stats=pass(process.execPath,[runner,config,captured]);
    assert.equal(stats.sites,3);
    assert.equal(stats.observedSites,2);
    assert.equal(stats.events,2);
    const global=JSON.parse(fs.readFileSync(path.join(captured,'report.json')));
    assert.deepEqual(global.dynamicCodeEvents.map(e=>e.siteIndex),[1,0]);
    const bundle=JSON.parse(fs.readFileSync(path.join(captured,'bundle.json')));
    assert.deepEqual(bundle.sites.map(e=>e.eventCount),[1,1,0]);
    const out=path.join(dir,'exported');
    pass(process.execPath,[exporter,captured,out,binary]);
    const staticTree=path.join(dir,'static');
    fs.mkdirSync(staticTree);
    fs.writeFileSync(path.join(staticTree,'original.js'),source);
    const baseline=path.join(dir,'baseline');
    pass(binary,['source-tree',staticTree,baseline,'--max-iterations','2']);
    const combined=path.join(dir,'combined');
    pass(binary,['source-tree',staticTree,combined,'--max-iterations','2',
      '--observed-direct-bundle',out,path.join(captured,'executable.js')]);
    const idx=JSON.parse(fs.readFileSync(path.join(combined,'runtime-observed/index.json')));
    assert.equal(idx.captures.length,2);
    assert.deepEqual(idx.captures.map(e=>e.executableSite),
      inventory.sites.slice(0,2).map(e=>[e.evalSite.start,e.evalSite.end]));
    assert.deepEqual(fs.readFileSync(path.join(combined,'original.js')),
      fs.readFileSync(path.join(baseline,'original.js')));
    assert.deepEqual(fs.readFileSync(path.join(combined,'reconstruction.json')),
      fs.readFileSync(path.join(baseline,'reconstruction.json')));
    for (const [i,capture] of idx.captures.entries()){
      const name='site-'+String(i).padStart(4,'0');
      assert.deepEqual(
        fs.readFileSync(path.join(combined,capture.directory,'manifest.json')),
        fs.readFileSync(path.join(out,name,'manifest.json')));
    }
  }finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('automatic AST capture refuses a genuinely uninstrumentable direct eval site',()=>{
  const dir=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-auto-refusal-'));
  try{
    const original=[
      "var local=function(eval,D){return eval(D);};",
      "var spread=function(D){return eval(...D);};",
      "eval();",
    ].join('\n');
    const executable=path.join(dir,'source.js');
    fs.writeFileSync(executable,original);
    const inventory=pass(binary,['eval-sites',executable]);
    assert.equal(inventory.sites.length,0);
    assert.equal(inventory.unsupported.length,2);
    const config=path.join(dir,'config.json');
    fs.writeFileSync(config,JSON.stringify({
      sourceFile:'source.js',sites:'all',parserBinary:binary,
    }));
    const output=path.join(dir,'capture');
    const failed=spawnSync(process.execPath,[runner,config,output],
      {encoding:'utf8',timeout:25000});
    assert.notEqual(failed.status,0);
    assert.match(failed.stderr,/cannot be captured/);
    assert.equal(fs.existsSync(output),false);
  }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
