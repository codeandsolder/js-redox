#!/usr/bin/env node
// Non-destructive overlay for execution-observed JavaScript sources.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';

const [staticDir, destination, astProbeBinary, ...args] = process.argv.slice(2);
if (!staticDir || !destination || !astProbeBinary || args.length < 3 || args.length % 3) {
  throw Error('Usage: link-runtime-source-tree.mjs STATIC_TREE OUT_TREE AST_PROBE_BIN OBSERVED_TREE OUTER_LOADER_JS INNER_EXECUTABLE_JS [OBSERVED_TREE OUTER_LOADER_JS INNER_EXECUTABLE_JS ...]');
}
const source = path.resolve(staticDir), output = path.resolve(destination);
const astProbe = path.resolve(astProbeBinary);
if (!fs.statSync(astProbe).isFile()) throw Error('AST probe binary not found');
const pairs = Array.from({length:args.length/3},(_,i)=>({
  observed:path.resolve(args[i*3]),
  outer:path.resolve(args[i*3+1]),
  inner:path.resolve(args[i*3+2]),
}));
const hash = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const sha64 = /^[a-f0-9]{64}$/;
const contains = (dir, other) => dir===other || dir.startsWith(other+path.sep);
const link = (from,to) => path.posix.relative(path.posix.dirname(from),to);
function write(p,body) {
  fs.mkdirSync(path.dirname(p),{recursive:true});
  fs.writeFileSync(p,body.endsWith('\n')?body:body+'\n');
}
function copyNoSymlinks(from,to) {
  fs.cpSync(from,to,{recursive:true,filter(p){
    if(fs.lstatSync(p).isSymbolicLink()) throw Error('Symlink refused: '+p);
    return true;
  }});
}
function listJs(root) {
  const result=[];
  function walk(dir,relative){
    for(const entry of fs.readdirSync(dir,{withFileTypes:true})){
      const sub=path.posix.join(relative,entry.name), p=path.join(dir,entry.name);
      if(entry.isSymbolicLink()) throw Error('Static tree symlink: '+sub);
      if(entry.isDirectory()) walk(p,sub);
      else if(entry.isFile() && sub.endsWith('.js')) result.push({file:sub,text:fs.readFileSync(p,'utf8')});
    }
  }
  walk(root,'');
  return result.sort((a,b)=>a.file.localeCompare(b.file));
}
function structuralMatches(pair, site) {
  const result=spawnSync(astProbe,
    [pair.inner,String(site.start),String(site.end),source],
    {encoding:'utf8',timeout:60_000,maxBuffer:16*1024*1024});
  if (result.error || result.status!==0) {
    throw Error('OXC AST probe failed: ' +
      (result.error?.message || result.stderr || result.status).slice(0,1000));
  }
  const proof=JSON.parse(result.stdout);
  if (proof.schema!=='js-redox/ast-site-probe/v1' ||
      proof.original?.startUtf16!==site.start ||
      proof.original?.endUtf16!==site.end ||
      proof.original?.site?.argument_is_bound_to_nearest_parameter!==true ||
      proof.original?.site?.eval_is_unresolved!==true ||
      !Array.isArray(proof.matches) || !Array.isArray(proof.parseFailures) ||
      proof.parseFailures.length!==0) {
    throw Error('AST probe returned invalid, incomplete or mismatched structural evidence');
  }
  const seen=new Set();
  return proof.matches.map(match=>{
    if (match.relation!=='ast-lexical-structure-match' ||
        typeof match.path!=='string' || path.posix.isAbsolute(match.path) ||
        !match.path.endsWith('.js') || match.path.split('/').includes('..') ||
        !Number.isSafeInteger(match.site?.line) || match.site.line<1) {
      throw Error('AST probe returned invalid candidate path or location');
    }
    const absolute=path.resolve(source,match.path);
    if (!absolute.startsWith(source+path.sep) || !fs.statSync(absolute).isFile()) {
      throw Error('AST candidate escaped source tree');
    }
    const key=match.path+':'+match.site.start+':'+match.site.end;
    if(seen.has(key)) throw Error('AST probe returned duplicate candidate');
    seen.add(key);
    return {path:match.path,line:match.site.line,
      byteSpan:{start:match.site.start,end:match.site.end},
      relation:'ast-lexical-structure-match',
      lexicalFrames:match.site.frames.map(frame=>({
        binding:frame.binding,params:frame.params
      })),
    };
  });
}
// The input tree fingerprint is taken *before* navigation documentation is
// added to the copied tree. It identifies the precise static snapshot used.
function fingerprint(root) {
  const files=[];
  function walk(dir, prefix) {
    for (const entry of fs.readdirSync(dir,{withFileTypes:true})) {
      const relative=path.posix.join(prefix,entry.name);
      const abs=path.join(dir,entry.name);
      if (entry.isSymbolicLink()) throw Error('Static tree symlink: '+relative);
      if (entry.isDirectory()) walk(abs,relative);
      else if (entry.isFile()) files.push(relative);
    }
  }
  walk(root,'');
  const digest=crypto.createHash('sha256');
  for(const relative of files.sort()){
    digest.update(relative);
    digest.update(String.fromCharCode(0));
    digest.update(hash(fs.readFileSync(path.join(root,relative))));
    digest.update(String.fromCharCode(10));
  }
  return {sha256:digest.digest('hex'),files:files.length};
}
const stage=output+'.tmp-'+process.pid;
if(fs.existsSync(output)||fs.existsSync(stage)) throw Error('Refusing to overwrite output');
if(!fs.existsSync(path.join(source,'README.md'))) throw Error('Missing static tree README');
if(fs.existsSync(path.join(source,'runtime-observed'))) throw Error('Static tree already has observations');
for(const input of [source,...pairs.flatMap(p=>[p.observed,p.outer,p.inner])]){
  if(contains(output,input)||contains(input,output)) throw Error('Output overlaps input');
}
try{
  copyNoSymlinks(source,stage);
  const staticInputSnapshot=fingerprint(stage);
  const backlink=new Map(), captures=[], locations=new Set();
  for(const pair of pairs){
    const m=JSON.parse(fs.readFileSync(path.join(pair.observed,'manifest.json'),'utf8'));
    const p=m.sourceProvenance;
    const outer=p?.outerLoader,inner=p?.innerExecutable;
    if(m.schemaVersion!==2 || !sha64.test(m.htmlSha256) ||
      !sha64.test(outer?.sha256) || !sha64.test(inner?.sha256) ||
      outer.decodedBy!=='observed-first-indirect-eval' ||
      !Array.isArray(m.entries) || m.uniqueSourceCount!==m.entries.length ||
      !Number.isSafeInteger(m.eventCount) || m.eventCount<0) {
      throw Error('Required dual-layer v2 source manifest is invalid');
    }
    const outerCode=fs.readFileSync(pair.outer);
    const innerCode=fs.readFileSync(pair.inner);
    if(hash(outerCode)!==outer.sha256) throw Error('Outer loader SHA-256 mismatch');
    if(hash(innerCode)!==inner.sha256) throw Error('Inner executable SHA-256 mismatch');
    const loader=outerCode.toString('utf8'),vm=innerCode.toString('utf8');
    const outerSite=outer.indirectEvalSite??{},site=inner.evalSite??{};
    const validSite=(value,text,code)=>
      Number.isSafeInteger(value.start) &&
      Number.isSafeInteger(value.end) && value.start>=0 &&
      value.end<=code.length && value.end>value.start &&
      value.expression===text && code.slice(value.start,value.end)===text;
    if(!validSite(outerSite,'(0,eval)(',loader) ||
       !validSite(site,'eval(D)',vm) ||
       !Number.isSafeInteger(inner.strippedLeadingNewlineCodeUnits) ||
       inner.strippedLeadingNewlineCodeUnits<0) {
      throw Error('Invalid dual-layer loader/inner executable source coordinates');
    }
    const matches=structuralMatches(pair,site);
    if(matches.length===0) throw Error('No AST-backed source-tree match for the executable eval site');
    const relative=path.posix.join('runtime-observed','loader-'+outer.sha256,
      'inner-'+inner.sha256,'eval-'+site.start+'-'+site.end,
      'capture-'+m.htmlSha256);
    if(locations.has(relative)) throw Error('Duplicate capture provenance');
    locations.add(relative);
    const dir=path.join(stage,relative);
    copyNoSymlinks(pair.observed,dir);
    const origin=path.posix.join(relative,'origin.md');
    const captureReadme=path.posix.join(relative,'README.md');
    write(path.join(dir,'origin.json'),JSON.stringify({
      schema:'js-redox/runtime-origin/v2',
      evidence:'execution-observed; AST-lexical callsite match, not universal equivalence',
      htmlSha256:m.htmlSha256,
      outerLoader:outer,
      innerExecutable:inner,
      staticAstStructuralMatches:matches,
      eventCount:m.eventCount,uniqueSourceCount:m.uniqueSourceCount,
      truncated:m.truncated===true,
    },null,2));
    const links=[
      '# Executable inner VM direct-eval callsite','',
      'Execution-observed source; matched AST lexical sites do NOT prove',
      'whole-function equivalence or universal reachability.','',
      '- HTML capture SHA-256: '+m.htmlSha256,
      '- Outer loader SHA-256: '+outer.sha256,
      '- Outer loader indirect eval source offset: '+outerSite.start+'..'+outerSite.end,
      '- Inner executable VM SHA-256: '+inner.sha256,
      '- Inner executable direct eval source offset: '+site.start+'..'+site.end,
      '- Leading newline units stripped to normalize the decoded VM: '+
        inner.strippedLeadingNewlineCodeUnits,'',
      '## Outer loader invocation','',
      '~~~javascript',outerSite.expression,'~~~','',
      '## Decoded executable direct eval','',
      '~~~javascript',site.expression,'~~~','',
      '## OXC AST + semantic lexical callsite matches','',
    ];
    for(const match of matches){
      links.push('- ['+match.path+']('+link(origin,match.path)+') (line '+
        match.line+', verified nested AST/binding structure; not a whole-function equivalence proof)');
      const refs=backlink.get(match.path)??[];
      refs.push({origin,line:match.line});
      backlink.set(match.path,refs);
    }
    write(path.join(stage,origin),links.join('\n'));
    const callable=[],others=[];
    for(const e of m.entries){
      if(!sha64.test(e.sha256)||!Number.isSafeInteger(e.utf16Length)||
        e.utf16Length<0||e.rawFile!=='raw/'+e.sha256+'.txt'||
        (e.readableFile!==null&&e.readableFile!=='readable/'+e.sha256+'.js')){
        throw Error('Invalid observed source entry paths');
      }
      const raw=fs.readFileSync(path.join(dir,e.rawFile));
      if(hash(raw)!==e.sha256||raw.toString('utf8').length!==e.utf16Length){
        throw Error('Observed source hash/length mismatch: '+e.sha256);
      }
      if(e.readableFile&&!fs.statSync(path.join(dir,e.readableFile)).isFile()){
        throw Error('Missing readable file: '+e.sha256);
      }
      const page=path.posix.join(relative,'entries',e.sha256+'.md');
      const rawPath=path.posix.join(relative,e.rawFile);
      const readablePath=e.readableFile?path.posix.join(relative,e.readableFile):null;
      write(path.join(stage,page),[
        '# Runtime-observed eval input '+e.sha256.slice(0,16),'',
        'Execution-conditional evidence; not a universal static rewrite.','',
        '- [Original verified callsite]('+link(page,origin)+')',
        '- [Exact raw operand]('+link(page,rawPath)+')',
        ...(readablePath?['- [Readable presentation]('+link(page,readablePath)+')']:
          ['- Standalone formatting status: '+e.readableStatus]),
        '- SHA-256: '+e.sha256,
        '- UTF-16 code units: '+e.utf16Length,
        '- First event index: '+e.firstEvent,
        '- Occurrences: '+e.occurrences,
        '- Returns: '+e.returned+'; throws: '+e.threw,
        '- Return types: '+JSON.stringify(e.returnedTypes),
        '- Thrown types: '+JSON.stringify(e.thrownTypes),'',
        'A formatted expression may still require the original lexical scope.','',
      ].join('\n'));
      const row='- ['+e.sha256.slice(0,16)+']('+link(captureReadme,page)+
        ') — '+e.utf16Length+' code units; '+e.occurrences+' call(s)'+
        (readablePath?' ([readable]('+link(captureReadme,readablePath)+'))':' (raw only)');
      if((e.returnedTypes?.function??0)>0) callable.push(row);
      else others.push(row);
    }
    fs.renameSync(path.join(dir,'README.md'),path.join(dir,'OBSERVED-INDEX.md'));
    write(path.join(dir,'README.md'),[
      '# Captured dynamic JavaScript','',
      'Execution-observed source from one modeled browser replay, not an',
      'independent module and not universally proven static source.','',
      '- [Verified original callsite and lexical candidates](origin.md)',
      '- [Machine-readable origin](origin.json)',
      '- [Original observation manifest](manifest.json)',
      '- [Original exporter index](OBSERVED-INDEX.md)','',
      'Eval calls: '+m.eventCount+'; distinct operands: '+m.uniqueSourceCount+
      '; truncated: '+(m.truncated===true),'',
      '## Eval strings returning callable values','',
      'A callable result can also be a lexical lookup, not a new function definition.','',
      ...callable,'','## Other eval operands, including failures','',...others,'',
    ].join('\n'));
    captures.push({outerLoaderSha256:outer.sha256,innerExecutableSha256:inner.sha256,
      htmlSha256:m.htmlSha256,site:{start:site.start,end:site.end},
      loaderSite:{start:outerSite.start,end:outerSite.end},
      directory:relative,calls:m.eventCount,sources:m.uniqueSourceCount,
      truncated:m.truncated===true,staticAstMatches:matches.length});
  }
  for(const [original,refs] of backlink){
    const sidecar=original+'.runtime-evidence.md';
    write(path.join(stage,sidecar),[
      '# Runtime AST source observations related to '+path.posix.basename(original),'',
      'OXC structural lexical-site match; this does not prove whole-function equivalence.',
      'The JavaScript source file is unchanged.','',
      ...refs.map(r=>'- Line '+r.line+': [observed source and origin]('+
        link(sidecar,r.origin)+')'), '',
    ].join('\n'));
  }
  const index='runtime-observed/README.md';
  write(path.join(stage,index),[
    '# Execution-observed source tree','',
    'Separate execution evidence, not universal static source recovery.','',
    ...captures.map(c=>'- [outer '+c.outerLoaderSha256.slice(0,12)+
      ' / inner '+c.innerExecutableSha256.slice(0,12)+' / executable site '+
      c.site.start+'..'+c.site.end+' / HTML '+c.htmlSha256.slice(0,12)+']('+
      link(index,c.directory+'/README.md')+') — '+c.calls+
      ' evals, '+c.sources+' distinct strings'+(c.truncated?' (truncated)':'')),
    '',
  ].join('\n'));
  write(path.join(stage,'runtime-observed/index.json'),JSON.stringify({
    schema:'js-redox/linked-runtime-source-tree/v2',
    staticJavaScriptAndReconstructionUnmodified:true,
    staticInputSnapshot,captures,
  },null,2));
  fs.appendFileSync(path.join(stage,'README.md'),
    '\n## Execution-observed generated source\n\n'+
    '[Browse separate runtime sources and their original callsites](runtime-observed/README.md). '+
    'These are not universal static transformations.\n');
  const lex=path.join(stage,'lexical-context/README.md');
  if(fs.existsSync(lex)&&backlink.size){
    fs.appendFileSync(lex,'\n## Runtime-observed source-text candidates\n\n'+
      'These links do not alter the original helper sources.\n\n'+
      [...backlink.keys()].sort().map(p=>'- ['+p+']('+
        link('lexical-context/README.md',p+'.runtime-evidence.md')+')').join('\n')+'\n');
  }
  fs.renameSync(stage,output);
  console.log(JSON.stringify({output,captures:captures.length,
    staticAstCandidateFiles:backlink.size,
    observedDistinctSources:captures.reduce((n,c)=>n+c.sources,0)}));
}catch(e){
  fs.rmSync(stage,{recursive:true,force:true});
  throw e;
}
