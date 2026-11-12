#!/usr/bin/env node
// Capture one precisely located direct-eval site in arbitrary synchronous
// two-layer Node VM scripts. The original VM is retained byte-for-byte;
// instrumentation runs only in an ephemeral executable copy.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import vm from 'node:vm';

const [configFile, outputDirectory] = process.argv.slice(2);
if (!configFile || !outputDirectory) {
  throw Error('Usage: capture-vm-eval.mjs CONFIG.json OUTPUT_DIR');
}
const sha256 = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const configPath = path.resolve(configFile);
const config = JSON.parse(fs.readFileSync(configPath, 'utf8'));
const configDir = path.dirname(configPath);
const read = file => {
  if (typeof file !== 'string' || !file) throw Error('Expected a source path in config');
  const bytes = fs.readFileSync(path.resolve(configDir, file));
  const text = new TextDecoder('utf-8', {fatal:true}).decode(bytes);
  if (!Buffer.from(text, 'utf8').equals(bytes)) throw Error('Noncanonical UTF-8 source: ' + file);
  return {bytes, text};
};
const outer = read(config.outerFile);
const entry = read(config.entryFile);
// Capture identity bytes may be binary (e.g. an archived HTML response).
// Only executable JS layers must decode as canonical UTF-8.
const identityBytes = config.identityFile ?
  fs.readFileSync(path.resolve(configDir, config.identityFile)) : outer.bytes;
const expectedInner = config.innerFile ? read(config.innerFile) : null;
const siteCheck = (code, site, expected) => {
  if (!site || !Number.isSafeInteger(site.start) || !Number.isSafeInteger(site.end) ||
      site.start < 0 || site.end <= site.start ||
      typeof site.expression !== 'string' || !site.expression ||
      code.slice(site.start, site.end) !== site.expression ||
      (expected !== undefined && site.expression !== expected)) {
    throw Error('Source site does not match original UTF-16 coordinates');
  }
};
// Exact snippets can be supplied instead of hand-counted UTF-16 offsets.
// Require uniqueness: this is a locator, NOT AST/semantic proof. The native
// importer independently validates the original executable eval node.
const uniqueSite = (code, expression, context) => {
  if (typeof expression !== 'string' || !expression) {
    throw Error('Expected a nonempty source expression for ' + context);
  }
  const first = code.indexOf(expression);
  if (first < 0 || code.indexOf(expression, first + 1) !== -1) {
    throw Error('Source expression must be unique in ' + context);
  }
  return {start:first, end:first + expression.length, expression};
};
const outerSite = config.outerSite ??
  uniqueSite(outer.text, '(0,eval)(', 'outer loader');
siteCheck(outer.text, outerSite, '(0,eval)(');
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
  const events = [];
  const pending = [];
  let truncated = false;
  let skippedNonString = 0;
  let overlaps = 0;
  let extraEvalArguments = false;
  const report = {
    ok:false, htmlSha256:sha256(identityBytes), outerVmSha256:sha256(outer.bytes),
    sourceProvenance:null, dynamicCodeEvents:events, dynamicTruncated:false,
    environment:'generic synchronous Node VM replay', skippedNonString:0,
    identityKind:config.identityFile ? 'provided-file' : 'outer-loader',
  };

  // The first decoded indirect-eval string is the executable inner source.
  // Restore the native eval binding before running the instrumented inner VM.
  const contextGlobals = config.globals ?? {};
  if (!contextGlobals || Array.isArray(contextGlobals) ||
      typeof contextGlobals !== 'object' || Object.hasOwn(contextGlobals, 'eval')) {
    throw Error('globals must be a JSON object without an eval override');
  }
  const context = vm.createContext({...contextGlobals, console, Buffer});
  const builtinEval = vm.runInContext('eval', context);
  const hookBase = '__jsredox_eval_' + sha256(outer.bytes).slice(0,20);
  const argName = hookBase + '_arg';
  const returnName = hookBase + '_return';
  const store = new Map();
  context[argName] = function(value) {
    if (typeof value !== 'string') {
      skippedNonString++;
      pending.push(null);
      return value;
    }
    if (pending.some(index => index !== null)) overlaps++;
    if (events.length >= maxEvents) {
      truncated = true;
      pending.push(null);
      return value;
    }
    // JS strings containing isolated UTF-16 surrogates have no lossless UTF-8
    // representation. Do not silently replace those code units in evidence.
    const bytes = Buffer.from(value, 'utf8');
    if (bytes.toString('utf8') !== value) {
      throw Error('Unpaired surrogate cannot be exported losslessly as UTF-8 source');
    }
    const digest = sha256(bytes);
    const previous = store.get(digest);
    if (previous && previous !== value) throw Error('SHA-256 collision in observed sources');
    store.set(digest, value);
    const target = path.join(sourceDir, 'eval-' + digest + '.js');
    if (!fs.existsSync(target)) fs.writeFileSync(target, bytes, {flag:'wx'});
    const index = events.length;
    events.push({index, type:'string', sha256:digest, length:value.length,
      outcome:'throw', thrownType:'unknown'});
    pending.push(index);
    return value;
  };
  context[returnName] = function(value) {
    const index = pending.pop();
    if (index !== null && index !== undefined) {
      const event = events[index];
      event.outcome = 'return';
      event.resultType = typeof value;
      delete event.thrownType;
    }
    return value;
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
    if (inner.includes(argName) || inner.includes(returnName)) {
      throw Error('Observer hook name conflicts with original executable');
    }
    const site = config.evalSite ??
      uniqueSite(inner, config.evalExpression, 'decoded executable');
    siteCheck(inner, site);
    if (!/^eval\s*\([\s\S]*\)$/u.test(site.expression)) {
      throw Error('Configured executable site must be a nonoptional direct eval call');
    }
    const first = config.firstArgumentSite ?? (() => {
      const text = site.expression;
      const offset = uniqueSite(text, config.firstArgumentExpression,
        'direct eval expression');
      return {start:site.start + offset.start,
        end:site.start + offset.end, expression:offset.expression};
    })();
    if (!first || !Number.isSafeInteger(first.start) || !Number.isSafeInteger(first.end) ||
        first.start < site.start + 5 || first.end > site.end - 1 ||
        first.start >= first.end ||
        inner.slice(first.start, first.end) !== first.expression ||
        typeof first.expression !== 'string' ||
        first.expression.trimStart().startsWith('...')) {
      throw Error('Invalid first nonspread eval argument interval');
    }
    // Only insert hooks at caller-provided, exact UTF-16 boundaries. The
    // native importer independently confirms the original site is an AST
    // direct-eval expression; never use this instrumented copy as source proof.
    const originalCall = inner.slice(site.start, site.end);
    const relativeStart = first.start - site.start;
    const relativeEnd = first.end - site.start;
    // A later call argument can throw *before* the eval itself is invoked.
    // Success proves invocation; missing return does not. Flag this case
    // rather than misreporting an unevaluated first operand as executed code.
    extraEvalArguments = originalCall.slice(relativeEnd, -1).trim().startsWith(',');
    const modifiedCall = returnName + '(' +
      originalCall.slice(0, relativeStart) + argName + '(' +
      first.expression + ')' + originalCall.slice(relativeEnd) + ')';
    const instrumented = inner.slice(0, site.start) +
      modifiedCall + inner.slice(site.end);
    new vm.Script(instrumented, {filename:'instrumented-executable.js'});
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
    return Reflect.apply(builtinEval, undefined, ['\n'.repeat(prefixLength) + instrumented]);
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
  if (overlaps) throw Error('Nested/reentrant eval return attribution is ambiguous; refusing capture');
  if (extraEvalArguments && pending.some(index => index !== null)) {
    throw Error('A later eval argument may have thrown before eval was invoked; refusing ambiguous capture');
  }
  if (events.length === 0) throw Error('No string eval operands were observed');
  report.ok = true;
  report.skippedNonString = skippedNonString;
  report.dynamicTruncated = truncated;
  fs.writeFileSync(path.join(staging, 'outer.js'), outer.bytes);
  fs.writeFileSync(path.join(staging, 'report.json'), JSON.stringify(report, null, 2) + '\n');
  if (fs.existsSync(output)) throw Error('Output appeared during capture: ' + output);
  fs.renameSync(staging, output);
  console.log(JSON.stringify({
    output, events:events.length, unique:store.size,
    truncated, skippedNonString,
    originalInnerSha256:report.sourceProvenance.innerExecutable.sha256,
  }));
} catch (error) {
  fs.rmSync(staging, {recursive:true, force:true});
  throw error;
}
