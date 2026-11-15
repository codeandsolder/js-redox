import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';

const linker=path.resolve(import.meta.dirname,'../scripts/link-runtime-source-tree.mjs');
const sha=v=>crypto.createHash('sha256').update(v).digest('hex');
const build=()=>{
  const root=fs.mkdtempSync(path.join(import.meta.dirname,'.runtime-link-test-'));
  const staticTree=path.join(root,'static');
  fs.mkdirSync(path.join(staticTree,'lexical-context','helpers'),{recursive:true});
  fs.writeFileSync(path.join(staticTree,'README.md'),'# Static\n');
  fs.writeFileSync(path.join(staticTree,'lexical-context','README.md'),'# Lexical\n');
  fs.writeFileSync(path.join(staticTree,'reconstruction.json'),'{"static":true}\n');
  const helper='const oU = function(D){return eval(D);};\n';
  fs.writeFileSync(path.join(staticTree,'lexical-context','helpers','oU.js'),helper);
  fs.writeFileSync(path.join(staticTree,'lexical-context','original.js'),'var oU=function(D){return eval(D)};\n');

  const outer='const runner=(0,eval)(payload);\n';
  const inner='const oU=function(D){return eval(D);}\n';
  const outerFile=path.join(root,'outer.js'),innerFile=path.join(root,'inner.js');
  fs.writeFileSync(outerFile,outer);fs.writeFileSync(innerFile,inner);
  const outerSite={start:outer.indexOf('(0,eval)('),end:outer.indexOf('(0,eval)(')+9,expression:'(0,eval)('};
  const innerSite={start:inner.indexOf('eval(D)'),end:inner.indexOf('eval(D)')+7,expression:'eval(D)'};
  const observedSource='0,(function(x){return x+1})';
  const codeHash=sha(observedSource);
  const makeCapture=(name,htmlSha)=>{
    const dir=path.join(root,name);
    fs.mkdirSync(path.join(dir,'raw'),{recursive:true});
    fs.mkdirSync(path.join(dir,'readable'));
    fs.writeFileSync(path.join(dir,'README.md'),'# Raw index\n');
    fs.writeFileSync(path.join(dir,'raw',codeHash+'.txt'),observedSource);
    fs.writeFileSync(path.join(dir,'readable',codeHash+'.js'),observedSource+';\n');
    const manifest={
      schemaVersion:2,
      htmlSha256:htmlSha,
      sourceProvenance:{
        outerLoader:{sha256:sha(outer),indirectEvalSite:outerSite,decodedBy:'observed-first-indirect-eval'},
        innerExecutable:{sha256:sha(inner),evalSite:innerSite,strippedLeadingNewlineCodeUnits:17},
      },
      eventCount:2,uniqueSourceCount:1,truncated:false,
      entries:[{
        sha256:codeHash,utf16Length:observedSource.length,
        rawFile:'raw/'+codeHash+'.txt',
        readableFile:'readable/'+codeHash+'.js',
        readableStatus:'formatted',firstEvent:0,occurrences:2,
        returned:2,threw:0,returnedTypes:{function:2},thrownTypes:{},
      }],
    };
    fs.writeFileSync(path.join(dir,'manifest.json'),JSON.stringify(manifest));
    return dir;
  };
  const probe=path.join(root,'ast-probe.cjs');
  fs.writeFileSync(probe,[
    '#!/usr/bin/env node',
    'const fs=require("node:fs"),path=require("node:path");',
    'const [source,start,end,root]=process.argv.slice(2);',
    'const s=fs.readFileSync(source,"utf8");',
    'if(s.slice(Number(start),Number(end))!=="eval(D)")process.exit(3);',
    'const files=["lexical-context/helpers/oU.js","lexical-context/original.js"];',
    'console.log(JSON.stringify({schema:"js-redox/ast-site-probe/v1",',
    'original:{startUtf16:Number(start),endUtf16:Number(end),site:{argument_is_bound_to_nearest_parameter:true,eval_is_unresolved:true}},',
    'matches:files.map(p=>({path:p,relation:"ast-lexical-structure-match",',
    'site:{start:fs.readFileSync(path.join(root,p),"utf8").indexOf("eval(D)"),end:fs.readFileSync(path.join(root,p),"utf8").indexOf("eval(D)")+7,line:1,frames:[]}})),parseFailures:[]}));',
  ].join('\n'));
  fs.chmodSync(probe,0o755);
  const a=makeCapture('capture-a','a'.repeat(64));
  const b=makeCapture('capture-b','b'.repeat(64));
  const run=(dest,...captures)=>spawnSync(process.execPath,
    [linker,staticTree,dest,probe,...captures.flatMap(dir=>[dir,outerFile,innerFile])],
    {encoding:'utf8'});
  return {root,staticTree,outerFile,innerFile,innerSite,outerSite,codeHash,a,b,run};
};
const dispose=f=>fs.rmSync(f.root,{recursive:true,force:true});

test('two captures, dual hash roots, verified AST candidates and untouched static JS',()=>{
  const f=build();
  try{
    const out=path.join(f.root,'combined');
    const run=f.run(out,f.a,f.b);
    assert.equal(run.status,0,run.stderr);
    const stats=JSON.parse(run.stdout);
    assert.equal(stats.captures,2);
    assert.equal(stats.staticAstCandidateFiles,2);
    const index=JSON.parse(fs.readFileSync(path.join(out,'runtime-observed/index.json'),'utf8'));
    assert.equal(index.schema,'js-redox/linked-runtime-source-tree/v2');
    assert.equal(index.captures.length,2);
    assert.equal(index.captures[0].staticAstMatches,2);
    for(const file of ['reconstruction.json','lexical-context/helpers/oU.js',
      'lexical-context/original.js']){
      assert.deepEqual(fs.readFileSync(path.join(f.staticTree,file)),
        fs.readFileSync(path.join(out,file)));
    }
    for(const html of ['a'.repeat(64),'b'.repeat(64)]){
      const relative=path.join('runtime-observed','loader-'+sha(fs.readFileSync(f.outerFile)),
        'inner-'+sha(fs.readFileSync(f.innerFile)),
        'eval-'+f.innerSite.start+'-'+f.innerSite.end,
        'capture-'+html);
      const dir=path.join(out,relative);
      const origin=JSON.parse(fs.readFileSync(path.join(dir,'origin.json'),'utf8'));
      assert.equal(origin.schema,'js-redox/runtime-origin/v2');
      assert.equal(origin.outerLoader.indirectEvalSite.start,f.outerSite.start);
      assert.equal(origin.innerExecutable.evalSite.start,f.innerSite.start);
      assert.equal(origin.staticAstStructuralMatches.length,2);
      assert.equal(origin.staticAstStructuralMatches[0].relation,'ast-lexical-structure-match');
      assert.match(fs.readFileSync(path.join(dir,'origin.md'),'utf8'),/OXC AST/);
      assert.deepEqual(fs.readFileSync(path.join(dir,'raw',f.codeHash+'.txt')),
        Buffer.from('0,(function(x){return x+1})'));
      assert.ok(fs.existsSync(path.join(dir,'entries',f.codeHash+'.md')));
    }
    assert.match(fs.readFileSync(path.join(out,'lexical-context/helpers/oU.js.runtime-evidence.md'),'utf8'),
      /OXC structural lexical-site match/);
    assert.notEqual(f.run(out,f.a).status,0,'overwriting existing output must fail');
  } finally{dispose(f);}
});

test('rejects v1, duplicates, source tampering and symlinks atomically',()=>{
  const f=build();
  try{
    const tryRun=(name,...dirs)=>f.run(path.join(f.root,name),...dirs);
    let failure=tryRun('dup',f.a,f.a);
    assert.notEqual(failure.status,0);
    assert.match(failure.stderr,/Duplicate capture provenance/);
    assert.ok(!fs.existsSync(path.join(f.root,'dup')));

    const file=path.join(f.a,'manifest.json');
    const original=fs.readFileSync(file,'utf8');
    const old=JSON.parse(original);old.schemaVersion=1;
    fs.writeFileSync(file,JSON.stringify(old));
    failure=tryRun('v1',f.a);assert.notEqual(failure.status,0);
    assert.match(failure.stderr,/dual-layer v2/);
    fs.writeFileSync(file,original);

    fs.writeFileSync(f.innerFile,'tampered');
    failure=tryRun('wrong-inner',f.a);assert.notEqual(failure.status,0);
    assert.match(failure.stderr,/Inner executable SHA-256 mismatch/);
    fs.writeFileSync(f.innerFile,'const oU=function(D){return eval(D);}\n');

    fs.writeFileSync(path.join(f.a,'raw',f.codeHash+'.txt'),'tampered');
    failure=tryRun('wrong-raw',f.a);assert.notEqual(failure.status,0);
    assert.match(failure.stderr,/hash\/length mismatch/);
    assert.ok(!fs.existsSync(path.join(f.root,'wrong-raw')));

    fs.symlinkSync('/etc/hosts',path.join(f.staticTree,'lexical-context/helpers/bad.js'));
    failure=tryRun('symlink',f.b);assert.notEqual(failure.status,0);
    assert.match(failure.stderr,/Symlink refused/);
    assert.ok(!fs.existsSync(path.join(f.root,'symlink')));
  }finally{dispose(f);}
});
