import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';

const script = path.resolve(import.meta.dirname, '../scripts/link-runtime-source-tree.mjs');
const sha = v => crypto.createHash('sha256').update(v).digest('hex');
const fixture = () => {
  const root = fs.mkdtempSync(path.join(import.meta.dirname,'.runtime-link-test-'));
  const staticTree = path.join(root,'static');
  fs.mkdirSync(path.join(staticTree,'lexical-context','helpers'),{recursive:true});
  fs.writeFileSync(path.join(staticTree,'README.md'),'# Static tree\n');
  fs.writeFileSync(path.join(staticTree,'reconstruction.json'),JSON.stringify({schema:'static/v1',count:1}));
  fs.writeFileSync(path.join(staticTree,'lexical-context','README.md'),'# Lexical code\n');
  const helper = 'const oU = function(x) {\n  return eval( D );\n};\n';
  fs.writeFileSync(path.join(staticTree,'lexical-context','helpers','oU.js'),helper);
  fs.writeFileSync(path.join(staticTree,'lexical-context','original.js'),
    'function x(D) { return eval(D); }\n');
  const vm = 'const wrapped = function(D) { return eval(D); };\n';
  const vmFile = path.join(root,'vm.js');
  fs.writeFileSync(vmFile,vm);
  const vmHash = sha(vm);
  const first = vm.indexOf('eval(D)');
  const source='0,(function(x){return x+1})';
  const codeHash=sha(source);
  const makeCapture = (name, htmlHash) => {
    const observed = path.join(root,name);
    fs.mkdirSync(path.join(observed,'raw'),{recursive:true});
    fs.mkdirSync(path.join(observed,'readable'));
    fs.writeFileSync(path.join(observed,'README.md'),'# Standalone observed data\n');
    fs.writeFileSync(path.join(observed,'raw',codeHash+'.txt'),source);
    fs.writeFileSync(path.join(observed,'readable',codeHash+'.js'),'0, (function (x) { return x+1; });\n');
    const manifest={
      schemaVersion:1,evidenceKind:'execution-observed',
      htmlSha256:htmlHash,vmSha256:vmHash,
      evalSite:{start:first,end:first+7},
      truncated:false,eventCount:2,uniqueSourceCount:1,
      entries:[{
        sha256:codeHash,utf16Length:source.length,
        rawFile:'raw/'+codeHash+'.txt',
        readableFile:'readable/'+codeHash+'.js',
        readableStatus:'formatted',firstEvent:0,occurrences:2,
        returned:2,threw:0,returnedTypes:{function:2},thrownTypes:{},
      }],
    };
    fs.writeFileSync(path.join(observed,'manifest.json'),JSON.stringify(manifest));
    return {observed,manifest};
  };
  return {root,staticTree,vmFile,vmHash,codeHash,helper,
    captureA:makeCapture('capture-a','a'.repeat(64)),
    captureB:makeCapture('capture-b','b'.repeat(64))};
};
const run = (stat, dest, ...captureArgs) =>
  spawnSync(process.execPath,[script,stat,dest,...captureArgs],{encoding:'utf8'});

test('creates independently labeled combined navigation and preserves static content',()=>{
  const f=fixture();
  try {
    const out=path.join(f.root,'combined');
    const result=run(f.staticTree,out,f.captureA.observed,f.vmFile,
      f.captureB.observed,f.vmFile);
    assert.equal(result.status,0,result.stderr);
    const stats=JSON.parse(result.stdout);
    assert.equal(stats.captures,2);
    assert.equal(stats.staticCandidateFiles,2);
    assert.equal(stats.observedDistinctSources,2);
    for(const file of ['reconstruction.json','lexical-context/helpers/oU.js']){
      assert.equal(fs.readFileSync(path.join(f.staticTree,file),'utf8'),
        fs.readFileSync(path.join(out,file),'utf8'));
    }
    assert.match(fs.readFileSync(path.join(out,'README.md'),'utf8'),
      /runtime-observed\/README.md/);
    assert.match(fs.readFileSync(path.join(out,'lexical-context/README.md'),'utf8'),
      /oU.js.runtime-evidence.md/);
    const base=path.join(out,'runtime-observed','vm-'+f.vmHash,'eval-'+
      f.captureA.manifest.evalSite.start+'-'+f.captureA.manifest.evalSite.end);
    for(const [htmlHash,cat] of [['a'.repeat(64),'capture-a'],['b'.repeat(64),'capture-b']]){
      const capture=path.join(base,'capture-'+htmlHash);
      const origin=JSON.parse(fs.readFileSync(path.join(capture,'origin.json'),'utf8'));
      assert.equal(origin.evidence,'execution-observed, not universally proven static source');
      assert.equal(origin.staticSourceTextCandidates.length,2);
      assert.equal(origin.staticSourceTextCandidates[0].relation,'source-text-match-only');
      assert.equal(origin.site.expression,'eval(D)');
      assert.match(fs.readFileSync(path.join(capture,'README.md'),'utf8'),
        /Execution-observed source/);
      assert.match(fs.readFileSync(path.join(capture,'origin.md'),'utf8'),
        /lexical-context\/helpers\/oU.js/);
      const detail=fs.readFileSync(path.join(capture,'entries',f.codeHash+'.md'),'utf8');
      assert.match(detail,/Original verified callsite/);
      assert.equal(fs.readFileSync(path.join(capture,'raw',f.codeHash+'.txt'),'utf8'),
        '0,(function(x){return x+1})');
      assert.ok(fs.existsSync(path.join(capture,'OBSERVED-INDEX.md')));
    }
    assert.equal(JSON.parse(fs.readFileSync(path.join(out,'reconstruction.json'),'utf8')).count,1);
    assert.notEqual(run(f.staticTree,out,f.captureA.observed,f.vmFile).status,0,
      'must not overwrite prior output');
  } finally {fs.rmSync(f.root,{recursive:true,force:true});}
});

test('rejects source hashes, duplicate provenance, and symlinks without leaving output',()=>{
  const f=fixture();
  try{
    const duplicate=path.join(f.root,'duplicate');
    assert.notEqual(run(f.staticTree,duplicate,f.captureA.observed,f.vmFile,
      f.captureA.observed,f.vmFile).status,0);
    assert.equal(fs.existsSync(duplicate),false);
    const wrong=path.join(f.root,'wrong');
    fs.writeFileSync(f.vmFile,'a different VM');
    const mismatch=run(f.staticTree,wrong,f.captureA.observed,f.vmFile);
    assert.notEqual(mismatch.status,0);
    assert.match(mismatch.stderr,/VM SHA-256 mismatch/);
    assert.equal(fs.existsSync(wrong),false);
    fs.writeFileSync(f.vmFile,'const wrapped = function(D) { return eval(D); };\n');
    const code=path.join(f.captureA.observed,'raw',f.codeHash+'.txt');
    fs.writeFileSync(code,'tampered raw expression');
    const malformed=path.join(f.root,'bad');
    const modified=run(f.staticTree,malformed,f.captureA.observed,f.vmFile);
    assert.notEqual(modified.status,0);
    assert.match(modified.stderr,/hash\/length mismatch/);
    assert.equal(fs.existsSync(malformed),false);
    const side=path.join(f.staticTree,'lexical-context','helpers','bad.js');
    fs.symlinkSync('/etc/hosts',side);
    const symlinkResult=run(f.staticTree,path.join(f.root,'symlink'),f.captureB.observed,f.vmFile);
    assert.notEqual(symlinkResult.status,0);
    assert.match(symlinkResult.stderr,/Symlink refused/);
    assert.equal(fs.existsSync(path.join(f.root,'symlink')),false);
  } finally {fs.rmSync(f.root,{recursive:true,force:true});}
});
