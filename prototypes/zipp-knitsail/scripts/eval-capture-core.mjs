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

export function instrumentEval(code, config, names, siteIndex=0, astVerified=false) {
  const site = config.evalSite ?? uniqueSite(code, config.evalExpression, 'executable');
  verifySite(code, site);
  // Only explicit/manual sites need this narrow textual preflight. In the
  // automatic path OXC has already verified the *original* unresolved eval
  // identifier, optionality, and exact source hash. Re-running a naive regex
  // here wrongly rejects true direct calls such as ((eval))(x) or eval/*c*/(x).
  if (!astVerified && !/^eval\s*\([\s\S]*\)$/u.test(site.expression)) {
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
    site, firstArgumentSite:first, hasAdditionalArgs,
  };
}

export function instrumentEvalSites(code, configs, names, astVerified=false) {
  if (!Array.isArray(configs) || configs.length === 0) {
    throw Error('sites must be a nonempty array of eval-site configurations');
  }
  const sites = configs.map((cfg,siteIndex) => ({
    siteIndex, ...instrumentEval(code,cfg,names,siteIndex,astVerified),
  }));
  // Every configured site is identified by its original UTF-16 interval.
  const ids = new Set(sites.map(({site})=>site.start+':'+site.end));
  if (ids.size !== sites.length) {
    throw Error('Duplicate eval callsites with identical original source intervals');
  }
  const wrappers = sites.flatMap(({siteIndex,site,firstArgumentSite})=>[
    {start:site.start,end:site.end,kind:'result',
      open:names.result+'('+siteIndex+',',close:')'},
    {start:firstArgumentSite.start,end:firstArgumentSite.end,kind:'arg',
      open:names.arg+'('+siteIndex+',',close:')'},
  ]);
  // Valid AST spans are nested or disjoint, never partially overlapping.
  for (const [i,a] of wrappers.entries()) {
    for (const b of wrappers.slice(i+1)) {
      const crosses=(a.start<b.start && b.start<a.end && a.end<b.end) ||
        (b.start<a.start && a.start<b.end && b.end<a.end);
      if (crosses) throw Error('Eval and argument source intervals must be nested or disjoint');
    }
  }
  const positions=new Map();
  for (const wrapper of wrappers) {
    if (!positions.has(wrapper.start)) positions.set(wrapper.start,[]);
    if (!positions.has(wrapper.end)) positions.set(wrapper.end,[]);
    positions.get(wrapper.start).push({...wrapper,opening:true});
    positions.get(wrapper.end).push({...wrapper,opening:false});
  }
  let cursor=0;
  let instrumented='';
  for(const [offset,items] of [...positions.entries()].sort((a,b)=>a[0]-b[0])) {
    instrumented+=code.slice(cursor,offset);
    // Close innermost-to-outermost, then open outermost-to-innermost.
    // Equal spans occur when an outer call's argument is an inner call:
    // the outer argument wrapper must surround the inner result wrapper.
    items.sort((a,b)=>{
      if(a.opening!==b.opening) return a.opening?1:-1;
      const sizeA=a.end-a.start,sizeB=b.end-b.start;
      if(sizeA!==sizeB) return a.opening?sizeB-sizeA:sizeA-sizeB;
      if(a.kind!==b.kind) {
        return a.opening ? (a.kind==='arg'?-1:1) :
          (a.kind==='result'?-1:1);
      }
      return a.siteIndex-b.siteIndex;
    });
    instrumented+=items.map(item=>item.opening?item.open:item.close).join('');
    cursor=offset;
  }
  instrumented+=code.slice(cursor);
  return {
    code:instrumented,
    sites:sites.map(({siteIndex,site,hasAdditionalArgs})=>
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
