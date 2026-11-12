import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';

const project = path.resolve(import.meta.dirname, '..');
const runner = path.join(project, 'scripts/capture-vm-eval.mjs');
const exporter = path.join(project, 'scripts/export-runtime-eval.mjs');
const sha256 = value => crypto.createHash('sha256').update(value).digest('hex');
const run = (script, args) =>
  spawnSync(process.execPath, [script, ...args], {encoding:'utf8', timeout:25000});

test('generic VM captures decoded executable eval without changing original source', () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'jsredox-generic-eval-'));
  try {
    const inner = "var worker = function(D) { return eval(D + ' + 1'); };";
    const evalExpression = "eval(D + ' + 1')";
    const argumentExpression = "D + ' + 1'";
    const innerEvalStart = inner.indexOf(evalExpression);
    const innerArgStart = inner.indexOf(argumentExpression);
    // The outer VM genuinely evaluates a separately decoded string layer.
    const outer = 'var packed = ' + JSON.stringify('\n' + inner) +
      ';\n(0,eval)(packed);';
    const outerStart = outer.indexOf('(0,eval)(');
    const entry = [
      "if (worker('1') !== 2) throw Error('first return changed');",
      "if (worker('1') !== 2) throw Error('second return changed');",
      "try { worker('missingVar'); throw Error('expected eval to throw'); }",
      "catch (e) { if (!(e instanceof ReferenceError)) throw e; }",
    ].join('\n');
    fs.writeFileSync(path.join(root, 'outer.js'), outer);
    fs.writeFileSync(path.join(root, 'inner.js'), inner);
    fs.writeFileSync(path.join(root, 'entry.js'), entry);
    const cfg = {
      outerFile:'outer.js', innerFile:'inner.js', entryFile:'entry.js',
      identityFile:'entry.js',
      outerSite:{start:outerStart,end:outerStart + '(0,eval)('.length,
        expression:'(0,eval)('},
      evalSite:{start:innerEvalStart,end:innerEvalStart + evalExpression.length,
        expression:evalExpression},
      firstArgumentSite:{start:innerArgStart,end:innerArgStart + argumentExpression.length,
        expression:argumentExpression},
    };
    const configFile = path.join(root, 'config.json');
    fs.writeFileSync(configFile, JSON.stringify(cfg));
    const captured = path.join(root, 'captured');
    const first = run(runner, [configFile, captured]);
    assert.equal(first.status, 0, first.stderr);
    const summary = JSON.parse(first.stdout);
    assert.equal(summary.events, 3);
    assert.equal(summary.unique, 2);
    const report = JSON.parse(fs.readFileSync(path.join(captured, 'report.json')));
    assert.equal(report.ok, true);
    assert.equal(report.dynamicCodeEvents.length,3);
    assert.deepEqual(report.dynamicCodeEvents.map(e=>e.outcome),
      ['return','return','throw']);
    assert.equal(report.dynamicCodeEvents[2].thrownType,'unknown');
    assert.equal(report.sourceProvenance.outerLoader.sha256, sha256(outer));
    assert.equal(report.sourceProvenance.innerExecutable.sha256, sha256(inner));
    assert.equal(report.sourceProvenance.innerExecutable.strippedLeadingNewlineCodeUnits,1);
    assert.equal(report.sourceProvenance.innerExecutable.evalSite.expression,evalExpression);
    assert.equal(fs.readFileSync(path.join(captured,'inner.js'),'utf8'),inner);
    assert.equal(fs.readFileSync(path.join(captured,'outer.js'),'utf8'),outer);
    assert.equal(fs.readFileSync(path.join(captured, 'sources',
      'eval-'+sha256('1 + 1')+'.js'),'utf8'), '1 + 1');
    assert.notEqual(run(runner,[configFile,captured]).status,0,
      'existing captures must not be overwritten');

    const stub = path.join(root, 'formatter.cjs');
    fs.writeFileSync(stub, [
      '#!/usr/bin/env node',
      'const fs=require("node:fs");',
      'const s=fs.readFileSync(process.argv[3],"utf8");',
      'fs.writeFileSync(process.argv[4],s+String.fromCharCode(59,10));',
    ].join('\n'));
    fs.chmodSync(stub,0o755);
    const exported = path.join(root,'exported');
    const result = run(exporter, [path.join(captured,'report.json'),
      path.join(captured,'sources'), exported, stub]);
    assert.equal(result.status,0,result.stderr);
    const manifest = JSON.parse(fs.readFileSync(path.join(exported,'manifest.json'),'utf8'));
    assert.equal(manifest.schemaVersion,2);
    assert.equal(manifest.eventCount,3);
    assert.equal(manifest.uniqueSourceCount,2);
    assert.equal(manifest.sourceProvenance.innerExecutable.evalSite.expression,evalExpression);
    assert.equal(manifest.environment,'generic synchronous Node VM replay');
    assert.equal(manifest.identityKind,'provided-file');
    assert.deepEqual(manifest.entries.map(e=>e.occurrences),[2,1]);
    assert.equal(manifest.entries[0].returned,2);
    assert.equal(manifest.entries[1].threw,1);
    assert.equal(manifest.entries[0].readableStatus,'formatted');
    assert.equal(fs.readFileSync(path.join(exported,'raw',
      sha256('1 + 1')+'.txt'),'utf8'), '1 + 1');
  } finally {
    fs.rmSync(root,{recursive:true,force:true});
  }
});

test('invalid original callsites and conflicting decoded sources publish nothing', () => {
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-generic-invalid-'));
  try {
    const inner='var worker = D => eval(D);';
    const outer='var encoded = ' + JSON.stringify(inner) + '; (0,eval)(encoded);';
    fs.writeFileSync(path.join(root,'outer.js'),outer);
    fs.writeFileSync(path.join(root,'entry.js'),"worker('1+1');");
    fs.writeFileSync(path.join(root,'inner.js'),inner+'//tampered');
    const base={
      outerFile:'outer.js', innerFile:'inner.js', entryFile:'entry.js',
      outerSite:{start:outer.indexOf('(0,eval)('),
        end:outer.indexOf('(0,eval)(')+9,expression:'(0,eval)('},
      evalSite:{start:inner.indexOf('eval(D)'),
        end:inner.indexOf('eval(D)')+7,expression:'eval(D)'},
      firstArgumentSite:{start:inner.indexOf('eval(D)')+5,
        end:inner.indexOf('eval(D)')+6,expression:'D'},
    };
    const config=path.join(root,'config.json'),out=path.join(root,'out');
    fs.writeFileSync(config,JSON.stringify(base));
    let failed=run(runner,[config,out]);
    assert.notEqual(failed.status,0);
    assert.match(failed.stderr,/byte-identical/);
    assert.equal(fs.existsSync(out),false);
    assert.equal(fs.readdirSync(root).filter(n=>n.startsWith('.jsredox-observed-')).length,0);

    fs.writeFileSync(path.join(root,'inner.js'),inner);
    const wrong={...base,evalSite:{...base.evalSite,start:0,end:7}};
    fs.writeFileSync(config,JSON.stringify(wrong));
    failed=run(runner,[config,out]);
    assert.notEqual(failed.status,0);
    assert.match(failed.stderr,/Source site/);
    assert.equal(fs.existsSync(out),false);
  } finally {
    fs.rmSync(root,{recursive:true,force:true});
  }
});

test('unique source snippets locate UTF-16 sites and preserve extra argument effects', () => {
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-generic-extra-'));
  try {
    const inner="var marker='🦀'; var side=0; var worker=D=>eval(D + ' + 2',side++);";
    const outer='var packed='+JSON.stringify(inner)+'; (0,eval)(packed);';
    fs.writeFileSync(path.join(root,'outer.js'),outer);
    fs.writeFileSync(path.join(root,'inner.js'),inner);
    fs.writeFileSync(path.join(root,'entry.js'),
      "if(worker('3')!==5 || side!==1) throw Error('eval semantics changed');");
    const cfg={
      outerFile:'outer.js',innerFile:'inner.js',entryFile:'entry.js',
      evalExpression:"eval(D + ' + 2',side++)",
      firstArgumentExpression:"D + ' + 2'",
    };
    const config=path.join(root,'config.json'),out=path.join(root,'out');
    fs.writeFileSync(config,JSON.stringify(cfg));
    const first=run(runner,[config,out]);
    assert.equal(first.status,0,first.stderr);
    const report=JSON.parse(fs.readFileSync(path.join(out,'report.json'),'utf8'));
    assert.equal(report.dynamicCodeEvents.length,1);
    assert.equal(report.dynamicCodeEvents[0].outcome,'return');
    assert.equal(report.dynamicCodeEvents[0].resultType,'number');
    assert.equal(fs.readFileSync(path.join(out,'sources',
      'eval-'+sha256('3 + 2')+'.js'),'utf8'),'3 + 2');
    const span=report.sourceProvenance.innerExecutable.evalSite;
    assert.equal(inner.slice(span.start,span.end),cfg.evalExpression);
    assert.equal(span.start,inner.indexOf(cfg.evalExpression));
    assert.ok(Buffer.byteLength(inner.slice(0,span.start))>span.start,
      'UTF-16 offsets must not be mistaken for byte positions');

    // A text locator may never silently select one of two equal candidates.
    const invalid={...cfg,evalExpression:'eval'};
    fs.writeFileSync(config,JSON.stringify(invalid));
    const failure=run(runner,[config,path.join(root,'bad')]);
    assert.notEqual(failure.status,0);
    assert.match(failure.stderr,/unique|direct eval/);
  } finally {
    fs.rmSync(root,{recursive:true,force:true});
  }
});

test('binary capture identities are hashed byte-for-byte', () => {
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-binary-identity-'));
  try {
    const inner='var worker=D=>eval(D);';
    const outer='var packed='+JSON.stringify(inner)+'; (0,eval)(packed);';
    const identity=Buffer.from([0,255,254,1,2,3,4]);
    fs.writeFileSync(path.join(root,'outer.js'),outer);
    fs.writeFileSync(path.join(root,'entry.js'),"worker('7*6');");
    fs.writeFileSync(path.join(root,'identity.bin'),identity);
    const config={outerFile:'outer.js',entryFile:'entry.js',
      identityFile:'identity.bin',evalExpression:'eval(D)',
      firstArgumentExpression:'D'};
    fs.writeFileSync(path.join(root,'config.json'),JSON.stringify(config));
    const out=path.join(root,'out');
    const result=run(runner,[path.join(root,'config.json'),out]);
    assert.equal(result.status,0,result.stderr);
    const report=JSON.parse(fs.readFileSync(path.join(out,'report.json'),'utf8'));
    assert.equal(report.htmlSha256,sha256(identity));
    assert.equal(report.identityKind,'provided-file');
  } finally {fs.rmSync(root,{recursive:true,force:true});}
});

test('throws during later eval arguments cannot be misreported as executed source',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'jsredox-eval-order-'));
  try {
    const inner="var worker=D=>eval(D,fail());";
    const outer='var packed='+JSON.stringify(inner)+'; (0,eval)(packed);';
    fs.writeFileSync(path.join(root,'outer.js'),outer);
    fs.writeFileSync(path.join(root,'entry.js'),
      "function fail(){throw Error('argument failed')} try{worker('2+2')}catch(e){}");
    const config={
      outerFile:'outer.js',entryFile:'entry.js',
      evalExpression:'eval(D,fail())',firstArgumentExpression:'D',
    };
    fs.writeFileSync(path.join(root,'config.json'),JSON.stringify(config));
    const dest=path.join(root,'out');
    const result=run(runner,[path.join(root,'config.json'),dest]);
    assert.notEqual(result.status,0);
    assert.match(result.stderr,/before eval was invoked/);
    assert.equal(fs.existsSync(dest),false);
  } finally{fs.rmSync(root,{recursive:true,force:true});}
});
