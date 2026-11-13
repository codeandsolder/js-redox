#!/usr/bin/env node
// Import execution-observed eval operands into a separate, provenance-marked
// analyst tree. Never conflate these fragments with static recovery or
// silently discard code that cannot parse as a standalone JavaScript script.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';

const [reportFile, capturedSourceDir, outputDirectory, deobfuscator] = process.argv.slice(2);
if (!reportFile || !capturedSourceDir || !outputDirectory || !deobfuscator) {
  throw Error('Usage: export-runtime-eval.mjs REPORT.json CAPTURED_SOURCE_DIR OUTPUT_DIR DEOBFUSCATE_SAFE_BINARY');
}
const hex64 = /^[0-9a-f]{64}$/;
const report = JSON.parse(fs.readFileSync(reportFile, 'utf8'));
const provenance=report.sourceProvenance;
const isDirect=report.schemaVersion===3 && provenance?.kind==='direct-executable';
const loader=provenance?.outerLoader;
const executable=isDirect?provenance?.executable:provenance?.innerExecutable;
const outerSite=loader?.indirectEvalSite;
const innerSite=executable?.evalSite;
const validSite=(site,expression)=>
  site && Number.isSafeInteger(site.start) && Number.isSafeInteger(site.end) &&
  site.start>=0 && site.end-site.start===site.expression?.length &&
  typeof site.expression==='string' && site.expression.length>0 &&
  (expression===undefined || site.expression===expression);
const directValid=isDirect &&
  hex64.test(report.captureSha256) &&
  hex64.test(executable?.sha256) &&
  validSite(innerSite) &&
  /^eval\s*\([\s\S]*\)$/u.test(innerSite.expression);
const layeredValid=report.schemaVersion===undefined &&
  hex64.test(report.htmlSha256) && hex64.test(report.outerVmSha256) &&
  hex64.test(loader?.sha256) && hex64.test(executable?.sha256) &&
  report.outerVmSha256===loader.sha256 &&
  loader.decodedBy==='observed-first-indirect-eval' &&
  validSite(outerSite,'(0,eval)(') && validSite(innerSite) &&
  /^eval\s*\([\s\S]*\)$/u.test(innerSite.expression) &&
  Number.isSafeInteger(executable.strippedLeadingNewlineCodeUnits) &&
  executable.strippedLeadingNewlineCodeUnits>=0;
if ((!directValid && !layeredValid) || !Array.isArray(report.dynamicCodeEvents)) {
  throw Error('Missing or invalid direct executable / dual-layer source provenance');
}
const output = path.resolve(outputDirectory);
if (fs.existsSync(output)) throw Error('Output already exists: ' + output);
fs.mkdirSync(path.dirname(output), {recursive: true});
const staging = output + '.tmp-' + process.pid;
if (fs.existsSync(staging)) throw Error('Staging path exists: ' + staging);
fs.mkdirSync(path.join(staging, 'raw'), {recursive: true});
fs.mkdirSync(path.join(staging, 'readable'), {recursive: true});

try {
  const groups = new Map();
  const events = report.dynamicCodeEvents;
  for (const [position, event] of events.entries()) {
    if (!event || event.index !== position ||
        (event.outcome !== 'return' && event.outcome !== 'throw')) {
      throw Error('Invalid event at position ' + position);
    }
    if (event.type !== 'string') {
      throw Error('Non-string events must be counted separately from source events');
    }
    if (!hex64.test(event.sha256) ||
        !Number.isSafeInteger(event.length) || event.length < 0) {
      throw Error('Invalid source hash or length at event ' + position);
    }
    const hasGlobal = Number.isSafeInteger(event.globalEventIndex) &&
      event.globalEventIndex >= 0;
    if (event.globalEventIndex !== undefined && !hasGlobal) {
      throw Error('Invalid global event index at local event ' + position);
    }
    const known = groups.get(event.sha256) ?? {
      sha256: event.sha256, utf16Length: event.length,
      firstEvent: position, occurrences: 0, returned: 0, threw: 0,
      returnedTypes: {}, thrownTypes: {},
      ...(hasGlobal ? {globalEventIndices:[]} : {}),
    };
    if (hasGlobal !== ('globalEventIndices' in known)) {
      throw Error('Inconsistent global event index presence for ' + event.sha256);
    }
    if (hasGlobal) {
      const previous = known.globalEventIndices.at(-1);
      if (previous !== undefined && event.globalEventIndex <= previous) {
        throw Error('Global event indices must increase within each source');
      }
      known.globalEventIndices.push(event.globalEventIndex);
    }
    if (known.utf16Length !== event.length) {
      throw Error('Conflicting decoded string lengths for ' + event.sha256);
    }
    known.occurrences++;
    if (event.outcome === 'return') {
      known.returned++;
      const kind = event.resultType ?? 'unknown';
      known.returnedTypes[kind] = (known.returnedTypes[kind] ?? 0) + 1;
    } else {
      known.threw++;
      const kind = event.thrownType ?? 'unknown';
      known.thrownTypes[kind] = (known.thrownTypes[kind] ?? 0) + 1;
    }
    groups.set(event.sha256, known);
  }
  // Global indices identify the interleaving of identical source strings
  // across independently exported callsites of the same execution session.
  const globallyIndexed = events.filter(e=>e.globalEventIndex !== undefined);
  if (globallyIndexed.length && globallyIndexed.length !== events.length) {
    throw Error('Partially indexed multi-site capture is not valid');
  }
  if (globallyIndexed.length &&
      new Set(globallyIndexed.map(e=>e.globalEventIndex)).size !== globallyIndexed.length) {
    throw Error('Duplicate global event index in one site export');
  }
  const entries = [];
  for (const entry of groups.values()) {
    const sourceFile = path.join(capturedSourceDir, 'eval-' + entry.sha256 + '.js');
    const source = fs.readFileSync(sourceFile);
    const actualHash = crypto.createHash('sha256').update(source).digest('hex');
    if (actualHash !== entry.sha256) {
      throw Error('Captured source hash mismatch: ' + entry.sha256);
    }
    const text = source.toString('utf8');
    if (text.length !== entry.utf16Length) {
      throw Error('Captured source JS length mismatch: ' + entry.sha256);
    }
    const rawName = entry.sha256 + '.txt';
    fs.copyFileSync(sourceFile, path.join(staging, 'raw', rawName));
    entry.rawFile = 'raw/' + rawName;
    const readableName = entry.sha256 + '.js';
    const formattedPath = path.join(staging, 'readable', readableName);
    const result = spawnSync(deobfuscator, ['source', sourceFile, formattedPath, '--format-output'], {
      encoding:'utf8', timeout:20_000, maxBuffer:1024*1024,
    });
    if (result.error) throw result.error;
    if (result.status === 0 && fs.existsSync(formattedPath)) {
      entry.readableFile = 'readable/' + readableName;
      entry.readableStatus = 'formatted';
    } else if (result.status !== 0 &&
      (result.stderr + result.stdout).includes('parse-failure')) {
      entry.readableFile = null;
      entry.readableStatus = 'standalone-parse-rejected';
      fs.rmSync(formattedPath, {force:true});
    } else {
      throw Error('Formatting failed for ' + entry.sha256 +
        ': ' + (result.stderr || result.stdout || result.status).slice(0,400));
    }
    entries.push(entry);
  }
  const metadata = {
    schemaVersion:isDirect?3:2,
    evidenceKind:'execution-observed, not universal static proof',
    environment:report.environment ?? 'execution-observed Node VM source',
    identityKind:report.identityKind ?? 'archived-html',
    ...(isDirect ? {captureSha256:report.captureSha256} : {htmlSha256:report.htmlSha256}),
    sourceProvenance: provenance,
    truncated: report.dynamicTruncated === true,
    eventCount: events.length,
    uniqueSourceCount: entries.length,
    entries,
  };
  fs.writeFileSync(path.join(staging, 'manifest.json'), JSON.stringify(metadata, null, 2) + '\n');
  const callableOutcomes = entries.filter(x=>x.returnedTypes.function > 0 && x.readableFile);
  const lines = [
    '# Execution-observed dynamic source tree',
    '',
    'These are dynamic eval input strings observed during ONE execution capture.',
    'It is not a proof that these snippets are universal, and standalone parsing',
    'does not imply that an eval string can run outside its original lexical scope.',
    '',
    'Capture identity SHA-256: ' + (isDirect ? report.captureSha256 : report.htmlSha256),
    'Capture environment: ' + (report.environment ?? 'unspecified'),
    ...(isDirect ? [
      'Original direct executable SHA-256: ' + executable.sha256,
    ] : [
      'Original outer loader SHA-256: ' + loader.sha256,
      'Original inner executable SHA-256: ' + executable.sha256,
      'Loader indirect eval offset: ' + outerSite.start + '..' + outerSite.end,
    ]),
    'Executable direct eval offset: ' + innerSite.start + '..' + innerSite.end,
    'String eval operands observed: ' + events.length,
    'Other input types skipped by capture: ' + (report.skippedNonString ?? 0),
    'Unique string operands: ' + entries.length,
    'Event buffer truncated: ' + (report.dynamicTruncated === true),
    '',
    '## Eval strings returning callable values',
    '',
  ];
  for (const entry of callableOutcomes) {
    lines.push('- [' + entry.sha256.slice(0,16) + '](' + entry.readableFile +
      ') — ' + entry.utf16Length + ' source units; observed ' +
      entry.occurrences + ' time(s)');
  }
  lines.push('', 'A callable result may be a lexical identifier lookup, not a newly',
    'generated function definition. Other operands, including failing evals,',
    'are accounted for in manifest.json; exact bytes live in raw/.',
    'Only sources accepted by the standalone formatter appear in readable/.', '');
  fs.writeFileSync(path.join(staging, 'README.md'), lines.join('\n'));
  fs.renameSync(staging, output);
  console.log(JSON.stringify({
    events:events.length, unique:entries.length, formatted:entries.filter(e=>e.readableFile).length,
    callableResults:callableOutcomes.length, truncated:metadata.truncated,
    output,
  }));
} catch (error) {
  fs.rmSync(staging, {recursive:true, force:true});
  throw error;
}
