#!/usr/bin/env node
// Single-stage execution-observed source producer; original executable
// bytes are the source of the AST and SHA-256 witness, never instrumentation.
import fs from 'node:fs';
import path from 'node:path';
import vm from 'node:vm';
import {
  sha256, readSource, instrumentEvalSites, createObserver, contextGlobals,
} from './eval-capture-core.mjs';

const [configFile, outputDirectory] = process.argv.slice(2);
if (!configFile || !outputDirectory) {
  throw Error('Usage: capture-direct-eval.mjs CONFIG.json OUTPUT_DIR');
}
const root=path.dirname(path.resolve(configFile));
const config=JSON.parse(fs.readFileSync(configFile,'utf8'));
const source=readSource(root, config.sourceFile);
const entry=config.entryFile ? readSource(root, config.entryFile) : null;
const identity=config.identityFile ?
  fs.readFileSync(path.resolve(root,config.identityFile)) : source.bytes;
const timeoutMs=config.timeoutMs ?? 10000;
if (!Number.isSafeInteger(timeoutMs) || timeoutMs < 1) {
  throw Error('timeoutMs must be a positive integer');
}
const destination=path.resolve(outputDirectory);
if (fs.existsSync(destination)) throw Error('Output already exists: '+destination);
fs.mkdirSync(path.dirname(destination),{recursive:true});
const stage=fs.mkdtempSync(path.join(path.dirname(destination),'.jsredox-direct-'));
try {
  const context=vm.createContext(contextGlobals(config.globals));
  const observer=createObserver(context,source.bytes,path.join(stage,'sources'),
    config.maxEvents ?? 10000);
  const instrumented=instrumentEvalSites(source.text,config.sites,observer.hooks);
  new vm.Script(instrumented.code,{filename:'instrumented-direct.js'});
  // Don't alter the original JS file, and don't run an injected wrapper:
  // eval() stays a direct call in the same lexical function and scope.
  vm.runInContext(instrumented.code,context,{filename:'instrumented-direct.js',
    timeout:timeoutMs});
  if (entry) vm.runInContext(entry.text,context,{filename:'entry.js',timeout:timeoutMs});
  const result=observer.finish(instrumented.sites.map(site=>site.hasAdditionalArgs));
  const sourceSha256=sha256(source.bytes);
  const captureSha256=sha256(identity);
  const bySite=instrumented.sites.map(({siteIndex,hasAdditionalArgs,...site})=>({
    siteIndex, site, events:result.events.filter(event=>event.siteIndex===siteIndex),
  }));
  const report={
    schemaVersion:4,
    ok:true, captureSha256,
    identityKind:config.identityFile?'provided-file':'executable',
    sourceProvenance:{
      kind:'direct-executable-multi',
      executable:{sha256:sourceSha256,evalSites:bySite.map(item=>item.site)},
    },
    environment:'generic synchronous Node VM direct source',
    dynamicCodeEvents:result.events,
    dynamicTruncated:result.truncated,
    skippedNonString:result.skippedNonString,
  };
  const captures=[];
  for (const item of bySite) {
    // A selected but unexecuted site is explicitly listed in the bundle
    // summary, not misrepresented as observed source evidence.
    if (!item.events.length) continue;
    const dir='site-'+String(item.siteIndex).padStart(4,'0');
    fs.mkdirSync(path.join(stage,dir));
    const siteReport={
      schemaVersion:3, ok:true, captureSha256,
      captureSessionSha256:sha256(sourceSha256 + ':' + sha256(entry?.bytes ?? Buffer.alloc(0))),
      captureSiteIndex:item.siteIndex,
      identityKind:report.identityKind,
      sourceProvenance:{
        kind:'direct-executable',
        executable:{sha256:sourceSha256,evalSite:item.site},
      },
      environment:report.environment,
      dynamicCodeEvents:item.events.map((event,index)=>({
        ...event, globalEventIndex:event.index, index,
      })),
      dynamicTruncated:result.truncated,
      skippedNonString:0,
    };
    fs.writeFileSync(path.join(stage,dir,'report.json'),
      JSON.stringify(siteReport,null,2)+'\n');
    captures.push({siteIndex:item.siteIndex, directory:dir,
      evalSite:item.site,eventCount:item.events.length});
  }
  fs.writeFileSync(path.join(stage,'bundle.json'),JSON.stringify({
    schemaVersion:1,
    kind:'direct-eval-capture-bundle',
    executableSha256:sourceSha256,
    captureSha256,
    sites:bySite.map(item=>({
      siteIndex:item.siteIndex,evalSite:item.site,eventCount:item.events.length,
    })),
    captures,
  },null,2)+'\n');
  fs.writeFileSync(path.join(stage,'executable.js'),source.bytes);
  fs.writeFileSync(path.join(stage,'report.json'),JSON.stringify(report,null,2)+'\n');
  if (fs.existsSync(destination)) throw Error('Output appeared during capture');
  fs.renameSync(stage,destination);
  console.log(JSON.stringify({
    output:destination,events:result.events.length,unique:result.unique,
    truncated:result.truncated,skippedNonString:result.skippedNonString,
    executableSha256:sourceSha256,
    sites:bySite.length,observedSites:captures.length,
  }));
} catch(error) {
  fs.rmSync(stage,{recursive:true,force:true});
  throw error;
}
