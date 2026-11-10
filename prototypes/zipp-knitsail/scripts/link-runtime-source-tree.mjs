#!/usr/bin/env node
// Non-destructive overlay for execution-observed JavaScript sources.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';

const [staticDir, destination, ...args] = process.argv.slice(2);
if (!staticDir || !destination || args.length < 2 || args.length % 2) {
  throw Error('Usage: link-runtime-source-tree.mjs STATIC_TREE OUT_TREE OBSERVED_TREE ORIGINAL_VM [OBSERVED_TREE ORIGINAL_VM ...]');
}
const source = path.resolve(staticDir), output = path.resolve(destination);
const pairs = Array.from({length:args.length/2},(_,i)=>({
  observed:path.resolve(args[i*2]), vm:path.resolve(args[i*2+1]),
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
function anchorsFor(files,siteText) {
  const tokens=siteText.match(/[A-Za-z_$][\w$]*|\d+(?:\.\d+)?|[^\s]/gu);
  if(!tokens?.length) throw Error('Empty callsite');
  const escape = s => [...s].map(c=>'\\.^$*+?()[]{}|'.includes(c)?'\\'+c:c).join('');
  const regex=new RegExp(tokens.map(escape).join('\\s*'),'gu');
  const matches=[];
  for(const item of files) for(const match of item.text.matchAll(regex)){
    matches.push({path:item.file,
      line:1+(item.text.slice(0,match.index).match(/\n/g)?.length??0),
      relation:'source-text-match-only'});
  }
  return matches;
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
    digest.update('\\0');
    digest.update(hash(fs.readFileSync(path.join(root,relative))));
    digest.update('\\n');
  }
  return {sha256:digest.digest('hex'),files:files.length};
}
const stage=output+'.tmp-'+process.pid;
if(fs.existsSync(output)||fs.existsSync(stage)) throw Error('Refusing to overwrite output');
if(!fs.existsSync(path.join(source,'README.md'))) throw Error('Missing static tree README');
if(fs.existsSync(path.join(source,'runtime-observed'))) throw Error('Static tree already has observations');
for(const input of [source,...pairs.flatMap(p=>[p.observed,p.vm])]){
  if(contains(output,input)||contains(input,output)) throw Error('Output overlaps input');
}
try{
  copyNoSymlinks(source,stage);
  const staticInputSnapshot=fingerprint(stage);
  const staticFiles=listJs(stage), backlink=new Map(), captures=[], locations=new Set();
  for(const pair of pairs){
    const m=JSON.parse(fs.readFileSync(path.join(pair.observed,'manifest.json'),'utf8'));
    if(m.schemaVersion!==1||!sha64.test(m.vmSha256)||!sha64.test(m.htmlSha256)||
      !Array.isArray(m.entries)||m.uniqueSourceCount!==m.entries.length||
      !Number.isSafeInteger(m.eventCount)||m.eventCount<0){
      throw Error('Invalid observed manifest');
    }
    const vmBytes=fs.readFileSync(pair.vm);
    if(hash(vmBytes)!==m.vmSha256) throw Error('VM SHA-256 mismatch');
    const vm=vmBytes.toString('utf8'),site=m.evalSite??{};
    if(!Number.isSafeInteger(site.start)||!Number.isSafeInteger(site.end)||
      site.start<0||site.end<=site.start||site.end>vm.length){
      throw Error('Invalid original source interval');
    }
    const siteText=vm.slice(site.start,site.end), matches=anchorsFor(staticFiles,siteText);
    const relative=path.posix.join('runtime-observed','vm-'+m.vmSha256,
      'eval-'+site.start+'-'+site.end,'capture-'+m.htmlSha256);
    if(locations.has(relative)) throw Error('Duplicate capture provenance');
    locations.add(relative);
    const dir=path.join(stage,relative);
    copyNoSymlinks(pair.observed,dir);
    const origin=path.posix.join(relative,'origin.md');
    const captureReadme=path.posix.join(relative,'README.md');
    write(path.join(dir,'origin.json'),JSON.stringify({
      schema:'js-redox/runtime-origin/v1',
      evidence:'execution-observed, not universally proven static source',
      vmSha256:m.vmSha256,htmlSha256:m.htmlSha256,site:{...site,expression:siteText},
      staticSourceTextCandidates:matches,
      eventCount:m.eventCount,uniqueSourceCount:m.uniqueSourceCount,truncated:m.truncated===true,
    },null,2));
    const links=[
      '# Original VM callsite','',
      'Execution-observed. Static source code is not altered.','',
      '- VM SHA-256: '+m.vmSha256,
      '- HTML capture SHA-256: '+m.htmlSha256,
      '- Original JavaScript UTF-16 interval: '+site.start+'..'+site.end,'',
      '~~~javascript',siteText,'~~~','',
      '## Text-matching static lexical locations','',
    ];
    if(!matches.length) links.push('No candidates found; not a proof of absence.');
    for(const match of matches){
      links.push('- ['+match.path+']('+link(origin,match.path)+') (line '+
        match.line+', textual match only; lexical identity not independently proven)');
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
    captures.push({vmSha256:m.vmSha256,htmlSha256:m.htmlSha256,
      site:{start:site.start,end:site.end},directory:relative,
      calls:m.eventCount,sources:m.uniqueSourceCount,
      truncated:m.truncated===true,staticTextMatches:matches.length});
  }
  for(const [original,refs] of backlink){
    const sidecar=original+'.runtime-evidence.md';
    write(path.join(stage,sidecar),[
      '# Runtime source observations related to '+path.posix.basename(original),'',
      'Textual callsite candidates only; this does not prove lexical identity.',
      'The JavaScript source file is unchanged.','',
      ...refs.map(r=>'- Line '+r.line+': [observed source and origin]('+
        link(sidecar,r.origin)+')'), '',
    ].join('\n'));
  }
  const index='runtime-observed/README.md';
  write(path.join(stage,index),[
    '# Execution-observed source tree','',
    'Separate execution evidence, not universal static source recovery.','',
    ...captures.map(c=>'- [VM '+c.vmSha256.slice(0,12)+' / site '+
      c.site.start+'..'+c.site.end+' / HTML '+c.htmlSha256.slice(0,12)+']('+
      link(index,c.directory+'/README.md')+') — '+c.calls+
      ' evals, '+c.sources+' distinct strings'+(c.truncated?' (truncated)':'')),
    '',
  ].join('\n'));
  write(path.join(stage,'runtime-observed/index.json'),JSON.stringify({
    schema:'js-redox/linked-runtime-source-tree/v1',
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
    staticCandidateFiles:backlink.size,
    observedDistinctSources:captures.reduce((n,c)=>n+c.sources,0)}));
}catch(e){
  fs.rmSync(stage,{recursive:true,force:true});
  throw e;
}
