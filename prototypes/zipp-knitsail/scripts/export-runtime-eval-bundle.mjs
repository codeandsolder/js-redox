#!/usr/bin/env node
// Export one whole execution, retaining separate AST-verified site witnesses.
import fs from 'node:fs';
import path from 'node:path';
import {spawnSync} from 'node:child_process';

const [captureDir,outDir,formatter] = process.argv.slice(2);
if (!captureDir || !outDir || !formatter) {
  throw Error('Usage: export-runtime-eval-bundle.mjs CAPTURE_DIR OUTPUT_DIR FORMATTER');
}
const readJSON=file=>JSON.parse(fs.readFileSync(file,'utf8'));
const capture=readJSON(path.join(captureDir,'bundle.json'));
if (capture.schemaVersion!==1 || capture.kind!=='direct-eval-capture-bundle' ||
    !Array.isArray(capture.sites) || !Array.isArray(capture.captures)) {
  throw Error('Invalid original direct-eval capture bundle');
}
const validHash=x=>typeof x==='string' && /^[0-9a-f]{64}$/u.test(x);
if (!validHash(capture.executableSha256) || !validHash(capture.captureSha256)) {
  throw Error('Invalid executable or capture identity hash');
}
const sourceDir=path.join(captureDir,'sources');
const destination=path.resolve(outDir);
if (fs.existsSync(destination)) throw Error('Destination already exists');
fs.mkdirSync(path.dirname(destination),{recursive:true});
const stage=fs.mkdtempSync(path.join(path.dirname(destination),'.jsredox-bundle-'));
try {
  let last=-1;
  for (const [position,c] of capture.captures.entries()) {
    if (!Number.isSafeInteger(c.siteIndex) || c.siteIndex<=last ||
        c.directory!=='site-'+String(c.siteIndex).padStart(4,'0') ||
        !Number.isSafeInteger(c.eventCount) || c.eventCount<1) {
      throw Error('Invalid/unsorted bundle capture site at '+position);
    }
    last=c.siteIndex;
    const selected=capture.sites[c.siteIndex];
    if (!selected || selected.siteIndex!==c.siteIndex ||
        selected.eventCount!==c.eventCount ||
        JSON.stringify(selected.evalSite)!==JSON.stringify(c.evalSite)) {
      throw Error('Bundle capture does not agree with configured site');
    }
    const report=readJSON(path.join(captureDir,c.directory,'report.json'));
    if (report.captureSiteIndex!==c.siteIndex ||
        report.captureSha256!==capture.captureSha256 ||
        report.sourceProvenance?.executable?.sha256!==capture.executableSha256 ||
        JSON.stringify(report.sourceProvenance?.executable?.evalSite)!==
          JSON.stringify(c.evalSite) ||
        report.dynamicCodeEvents?.length!==c.eventCount) {
      throw Error('Site event report disagrees with bundle');
    }
    const child=spawnSync(process.execPath,[
      new URL('./export-runtime-eval.mjs', import.meta.url).pathname,
      path.join(captureDir,c.directory,'report.json'),
      sourceDir,path.join(stage,c.directory),formatter,
    ],{encoding:'utf8',timeout:120000,maxBuffer:1024*1024});
    if (child.status!==0) {
      throw Error('Exporting site '+c.siteIndex+' failed: '+
        (child.stderr||child.stdout||child.error?.message||'unknown').slice(0,900));
    }
  }
  const exported={
    schemaVersion:1,kind:'direct-eval-export-bundle',
    executableSha256:capture.executableSha256,
    captureSha256:capture.captureSha256,
    sites:capture.sites,
    captures:capture.captures,
  };
  fs.writeFileSync(path.join(stage,'bundle.json'),JSON.stringify(exported,null,2)+'\n');
  fs.writeFileSync(path.join(stage,'execution.json'),
    fs.readFileSync(path.join(captureDir,'report.json')));
  if (fs.existsSync(destination)) throw Error('Destination appeared during export');
  fs.renameSync(stage,destination);
  console.log(JSON.stringify({
    output:destination,sites:capture.sites.length,
    observedSites:capture.captures.length,
  }));
} catch(error) {
  fs.rmSync(stage,{recursive:true,force:true});
  throw error;
}
