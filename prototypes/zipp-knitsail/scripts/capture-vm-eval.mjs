#!/usr/bin/env node
// Capture one precisely located direct-eval site in arbitrary synchronous
// two-layer Node VM scripts. The original VM is retained byte-for-byte;
// instrumentation runs only in an ephemeral executable copy.
import fs from 'node:fs';
import path from 'node:path';
import vm from 'node:vm';
import {sha256,readSource,uniqueSite,verifySite,instrumentEval,createObserver,contextGlobals} from './eval-capture-core.mjs';

const [configFile, outputDirectory] = process.argv.slice(2);
if (!configFile || !outputDirectory) {
  throw Error('Usage: capture-vm-eval.mjs CONFIG.json OUTPUT_DIR');
}
const configPath = path.resolve(configFile);
const config = JSON.parse(fs.readFileSync(configPath, 'utf8'));
const configDir = path.dirname(configPath);
const read = filename => readSource(configDir, filename);
const outer = read(config.outerFile);
const entry = read(config.entryFile);
// Capture identity bytes may be binary (e.g. an archived HTML response).
// Only executable JS layers must decode as canonical UTF-8.
const identityBytes = config.identityFile ?
  fs.readFileSync(path.resolve(configDir, config.identityFile)) : outer.bytes;
const expectedInner = config.innerFile ? read(config.innerFile) : null;
const outerSite = config.outerSite ??
  uniqueSite(outer.text, '(0,eval)(', 'outer loader');
verifySite(outer.text, outerSite, '(0,eval)(');
const maxEvents = config.maxEvents ?? 10000;
const timeoutMs = config.timeoutMs ?? 10000;
if (!Number.isSafeInteger(maxEvents) || maxEvents < 1 ||
    !Number.isSafeInteger(timeoutMs) || timeoutMs < 1) {
  throw Error('maxEvents and timeoutMs must be positive integers');
}
const output = path.resolve(outputDirectory);
if (fs.existsSync(output)) throw Error('Output already exists: ' + output);
fs.mkdirSync(path.dirname(output), {recursive:true});
const staging = fs.mkdtempSync(path.join(path.dirname(output), '.jsredox-observed-'));
try {
  const sourceDir = path.join(staging, 'sources');
  fs.mkdirSync(sourceDir);
  const context = vm.createContext(contextGlobals(config.globals));
  const builtinEval = vm.runInContext('eval', context);
  const observation = createObserver(context, outer.bytes, sourceDir, maxEvents);
  let extraEvalArguments = false;
  const report = {
    ok:false, htmlSha256:sha256(identityBytes), outerVmSha256:sha256(outer.bytes),
    sourceProvenance:null, dynamicCodeEvents:observation.events, dynamicTruncated:false,
    environment:'generic synchronous Node VM replay', skippedNonString:0,
    identityKind:config.identityFile ? 'provided-file' : 'outer-loader',
  };
  let decodedCount = 0;
  context.eval = function(source) {
    if (++decodedCount !== 1 || typeof source !== 'string') {
      throw Error('Expected one decoded executable string at first outer indirect eval');
    }
    context.eval = builtinEval;
    const prefixLength = (source.match(/^\n*/u) ?? [''])[0].length;
    const inner = source.slice(prefixLength);
    if (expectedInner && !Buffer.from(inner, 'utf8').equals(expectedInner.bytes)) {
      throw Error('Decoded inner VM is not byte-identical to innerFile');
    }
    const instrumentedSite = instrumentEval(inner, config, observation.hooks);
    extraEvalArguments = instrumentedSite.hasAdditionalArgs;
    new vm.Script(instrumentedSite.code, {filename:'instrumented-executable.js'});
    const site = instrumentedSite.site;
    const innerBytes = Buffer.from(inner, 'utf8');
    if (innerBytes.toString('utf8') !== inner) throw Error('Inner VM has unpaired surrogate');
    fs.writeFileSync(path.join(staging, 'inner.js'), innerBytes);
    report.sourceProvenance = {
      outerLoader: {
        sha256:sha256(outer.bytes), decodedBy:'observed-first-indirect-eval',
        indirectEvalSite:outerSite,
      },
      innerExecutable: {
        sha256:sha256(innerBytes), evalSite:site,
        strippedLeadingNewlineCodeUnits:prefixLength,
      },
    };
    return Reflect.apply(builtinEval, undefined, ['\n'.repeat(prefixLength) + instrumentedSite.code]);
  };
  try {
    vm.runInContext(outer.text, context, {filename:'outer.js', timeout:timeoutMs});
    vm.runInContext(entry.text, context, {filename:'entry.js', timeout:timeoutMs});
  } finally {
    context.eval = builtinEval;
  }
  if (decodedCount !== 1 || !report.sourceProvenance) {
    throw Error('Outer loader did not supply exactly one decoded executable');
  }
  const results = observation.finish(extraEvalArguments);
  report.ok = true;
  report.skippedNonString = results.skippedNonString;
  report.dynamicTruncated = results.truncated;
  fs.writeFileSync(path.join(staging, 'outer.js'), outer.bytes);
  fs.writeFileSync(path.join(staging, 'report.json'), JSON.stringify(report, null, 2) + '\n');
  if (fs.existsSync(output)) throw Error('Output appeared during capture: ' + output);
  fs.renameSync(staging, output);
  console.log(JSON.stringify({
    output, events:results.events.length, unique:results.unique,
    truncated:results.truncated, skippedNonString:results.skippedNonString,
    originalInnerSha256:report.sourceProvenance.innerExecutable.sha256,
  }));
} catch (error) {
  fs.rmSync(staging, {recursive:true, force:true});
  throw error;
}
