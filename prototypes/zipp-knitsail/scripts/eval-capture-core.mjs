// Shared execution-observed eval instrumentation for original JS source.
// The producer locates sites textually; the native importer validates the
// executable AST and the original, unmodified source independently.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';

export const sha256 = bytes => crypto.createHash('sha256').update(bytes).digest('hex');

export function readSource(root, filename) {
  if (typeof filename !== 'string' || !filename) throw Error('Expected source path');
  const bytes = fs.readFileSync(path.resolve(root, filename));
  const text = new TextDecoder('utf-8', {fatal:true}).decode(bytes);
  if (!Buffer.from(text, 'utf8').equals(bytes)) {
    throw Error('Noncanonical UTF-8 source: ' + filename);
  }
  return {bytes, text};
}

export function uniqueSite(code, expression, context) {
  if (typeof expression !== 'string' || !expression) {
    throw Error('Expected nonempty source expression for ' + context);
  }
  const first = code.indexOf(expression);
  if (first < 0 || code.indexOf(expression, first + 1) !== -1) {
    throw Error('Source expression must occur exactly once in ' + context);
  }
  return {start:first, end:first + expression.length, expression};
}

export function verifySite(code, site, expected) {
  if (!site || !Number.isSafeInteger(site.start) ||
      !Number.isSafeInteger(site.end) || site.start < 0 ||
      site.end <= site.start || typeof site.expression !== 'string' ||
      !site.expression || code.slice(site.start, site.end) !== site.expression ||
      (expected !== undefined && site.expression !== expected)) {
    throw Error('Source site does not match original UTF-16 coordinates');
  }
}

export function instrumentEval(code, config, names, siteIndex=0) {
  const site = config.evalSite ?? uniqueSite(code, config.evalExpression, 'executable');
  verifySite(code, site);
  // Text checks restrict obvious mismatches; full AST proof belongs to the
  // Rust/OXC importer and never uses the modified executable as an input.
  if (!/^eval\s*\([\s\S]*\)$/u.test(site.expression)) {
    throw Error('Configured site must be a nonoptional direct eval call');
  }
  const first = config.firstArgumentSite ?? (() => {
    const relative = uniqueSite(site.expression, config.firstArgumentExpression, 'eval arguments');
    return {start:site.start + relative.start, end:site.start + relative.end,
      expression:relative.expression};
  })();
  if (!Number.isSafeInteger(first.start) || !Number.isSafeInteger(first.end) ||
      first.start < site.start + 5 || first.end > site.end - 1 ||
      first.start >= first.end || typeof first.expression !== 'string' ||
      code.slice(first.start, first.end) !== first.expression ||
      first.expression.trimStart().startsWith('...')) {
    throw Error('Invalid first nonspread eval argument interval');
  }
  const originalCall = code.slice(site.start, site.end);
  const relativeStart = first.start - site.start;
  const relativeEnd = first.end - site.start;
  const hasAdditionalArgs = originalCall.slice(relativeEnd, -1).trim().startsWith(',');
  for (const name of [names.arg, names.result]) {
    if (code.includes(name)) throw Error('Observer hook name conflicts with original executable');
  }
  const newCall = names.result + '(' + siteIndex + ',' +
    originalCall.slice(0, relativeStart) + names.arg + '(' + siteIndex + ',' +
    first.expression + ')' + originalCall.slice(relativeEnd) + ')';
  return {
    code:code.slice(0, site.start) + newCall + code.slice(site.end),
    site, hasAdditionalArgs,
  };
}

export function instrumentEvalSites(code, configs, names) {
  if (!Array.isArray(configs) || configs.length === 0) {
    throw Error('sites must be a nonempty array of eval-site configurations');
  }
  const replacements = configs.map((siteConfig, siteIndex) => {
    const modified = instrumentEval(code, siteConfig, names, siteIndex);
    return {
      siteIndex, site:modified.site,
      hasAdditionalArgs:modified.hasAdditionalArgs,
      replacement:modified.code.slice(
        modified.site.start,
        modified.code.length - (code.length - modified.site.end)),
    };
  });
  const sorted = [...replacements].sort((a,b) => a.site.start-b.site.start);
  for (let i=1;i<sorted.length;i++) {
    if (sorted[i].site.start < sorted[i-1].site.end) {
      throw Error('Eval sites must have distinct, nonoverlapping source intervals');
    }
  }
  let instrumented=code;
  for (const site of sorted.reverse()) {
    instrumented=instrumented.slice(0,site.site.start)+site.replacement+
      instrumented.slice(site.site.end);
  }
  return {
    code:instrumented,
    sites:replacements.map(({siteIndex,site,hasAdditionalArgs})=>
      ({siteIndex,...site,hasAdditionalArgs})),
  };
}

export function createObserver(context, originalSource, destination, maxEvents=10000) {
  if (!Number.isSafeInteger(maxEvents) || maxEvents < 1) {
    throw Error('maxEvents must be a positive integer');
  }
  fs.mkdirSync(destination, {recursive:true});
  const events = [];
  const pending = [];
  const unique = new Map();
  const hooks = {
    arg:'__jsredox_eval_' + sha256(originalSource).slice(0,20) + '_arg',
    result:'__jsredox_eval_' + sha256(originalSource).slice(0,20) + '_return',
  };
  let truncated = false;
  let skippedNonString = 0;
  let overlap = false;
  context[hooks.arg] = (siteIndex,value) => {
    if (!Number.isSafeInteger(siteIndex) || siteIndex < 0) {
      throw Error('Invalid instrumented site index');
    }
    if (typeof value !== 'string') {
      skippedNonString++;
      pending.push({siteIndex,index:null});
      return value;
    }
    if (pending.some(p => p.index !== null)) overlap = true;
    if (events.length >= maxEvents) {
      truncated = true;
      pending.push({siteIndex,index:null});
      return value;
    }
    const bytes = Buffer.from(value, 'utf8');
    if (bytes.toString('utf8') !== value) {
      throw Error('Unpaired surrogate cannot be recorded losslessly as UTF-8');
    }
    const hash = sha256(bytes);
    const previous = unique.get(hash);
    if (previous !== undefined && previous !== value) {
      throw Error('SHA-256 collision in observed eval sources');
    }
    unique.set(hash,value);
    const file = path.join(destination,'eval-' + hash + '.js');
    if (!fs.existsSync(file)) fs.writeFileSync(file,bytes,{flag:'wx'});
    const index = events.length;
    // Throws cannot be typed from a simple result wrapper without moving
    // the original eval into a different lexical scope.
    events.push({index, siteIndex, type:'string', sha256:hash, length:value.length,
      outcome:'throw',thrownType:'unknown'});
    pending.push({siteIndex,index});
    return value;
  };
  context[hooks.result] = (siteIndex,value) => {
    const completed = pending.pop();
    if (!completed || completed.siteIndex !== siteIndex) {
      throw Error('Eval invocation/result attribution mismatch');
    }
    if (completed.index !== null) {
      const event=events[completed.index];
      event.outcome='return';
      event.resultType=typeof value;
      delete event.thrownType;
    }
    return value;
  };
  return {
    hooks, events,
    finish(additionalArgsBySite=[]) {
      if (overlap) throw Error('Nested or reentrant eval attribution is ambiguous');
      const extra = typeof additionalArgsBySite === 'boolean' ?
        [additionalArgsBySite] : additionalArgsBySite;
      if (pending.some(({siteIndex,index}) => index !== null && extra[siteIndex])) {
        throw Error('A later eval argument may have thrown before eval was invoked');
      }
      if (!events.length) throw Error('No string eval operands were observed');
      return {events, unique:unique.size, truncated, skippedNonString};
    },
  };
}

export function contextGlobals(globals) {
  if (globals === undefined) return {console,Buffer};
  if (!globals || Array.isArray(globals) || typeof globals !== 'object' ||
      Object.hasOwn(globals,'eval')) {
    throw Error('globals must be a JSON object without eval override');
  }
  return {...globals,console,Buffer};
}
