import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {correlateZippEvalSites} from '../scripts/link-zipp-eval-sites.mjs';

const digest=(b)=>createHash('sha256').update(b).digest('hex');
const source="const crab='🦀';\r\nfunction f(D){return eval(eval(D));}\r\nfunction dormant(E){return eval(E);}\u2028";
const bytes=Buffer.from(source);
const sha=digest(bytes);
function callSite(expression,occurrence=0){
  let start=-1;
  for(let i=0;i<=occurrence;i++)start=source.indexOf(expression,start+1);
  assert.notEqual(start,-1);
  return {start,end:start+expression.length,expression};
}
function candidate(expression,arg,occurrence=0){
  const evalSite=callSite(expression,occurrence);
  const argStart=source.indexOf(arg,evalSite.start);
  assert.ok(argStart>=evalSite.start && argStart+arg.length<=evalSite.end);
  return {evalSite,firstArgumentSite:{start:argStart,
    end:argStart+arg.length,expression:arg}};
}
const outer=candidate('eval(eval(D))','eval(D)');
const inner=candidate('eval(D)','D');
const dormant=candidate('eval(E)','E');
const inventory={schemaVersion:1,sourceSha256:sha,sites:[outer,inner,dormant],unsupported:[]};
function loc(span){
  const prefix=source.slice(0,span.start);
  const lines=prefix.split(/\r\n|\r|\n|\u2028|\u2029/);
  return {line:lines.length,column:lines.at(-1).length+1};
}
function event(index,kind,bytes,span,origin='initial-program'){
  return {index,kind,sourceHex:Buffer.from(bytes).toString('hex'),
    caller:span?{functionId:1,instructionIp:index+8,origin,...loc(span)}:null};
}
const original=[
  event(0,'direct-eval','"40+2"',inner.evalSite),
  event(1,'direct-eval','40+2',outer.evalSite),
  event(2,'direct-eval','"40+2"',inner.evalSite),
  event(3,'direct-eval','2+2',outer.evalSite,'runtime-installed'),
  event(4,'indirect-or-host','3+7',outer.evalSite),
  event(5,'function-constructor','return 4;',null),
];
const observer={schemaVersion:1,engine:'zipp',sourceSha256:sha,
  truncated:false,execution:{initial:{ok:true}},events:original};

test('correlates nested direct eval, repeated cached calls and Unicode line positions',()=>{
  const report=correlateZippEvalSites(bytes,inventory,observer);
  assert.deepEqual(report.summary,
    {total:6,matched:3,ambiguous:0,unmatched:0,unavailable:3});
  assert.deepEqual(report.events.slice(0,3).map(e=>e.correlation.inventoryIndex),
    [1,0,1]);
  for(const item of report.events.slice(0,3)){
    assert.equal(item.correlation.sourceProvenance.executableSha256,sha);
    assert.equal(item.correlation.sourceProvenance.kind,'initial-program-direct-eval-callsite');
  }
  assert.equal(report.events[3].correlation.reason,'runtime-installed-caller');
  assert.equal(report.events[4].correlation.reason,'not-a-direct-eval');
  assert.equal(report.events[5].correlation.reason,'not-a-direct-eval');
  assert.equal(report.observerTruncated,false);
});

test('does not confuse a later source with an original one despite identical location',()=>{
  const later={...original[0],caller:{...original[0].caller,origin:'runtime-installed'}};
  const report=correlateZippEvalSites(bytes,inventory,
    {...observer,events:[later]});
  assert.equal(report.events[0].correlation.status,'unavailable');
  assert.equal(report.events[0].correlation.reason,'runtime-installed-caller');
});

test('refuses mismatched OXC and ZIPP exact original SHA-256',()=>{
  assert.throws(()=>correlateZippEvalSites(bytes,{...inventory,sourceSha256:'0'.repeat(64)},observer),/OXC inventory SHA-256/);
  assert.throws(()=>correlateZippEvalSites(bytes,inventory,{...observer,sourceSha256:'0'.repeat(64)}),/ZIPP observer SHA-256/);
  assert.throws(()=>correlateZippEvalSites(Buffer.from(source+' '),inventory,observer),/SHA-256/);
});

test('refuses malformed or forged AST spans and argument ranges',()=>{
  const bad={...outer,evalSite:{...outer.evalSite,expression:'eval(1)'}};
  assert.throws(()=>correlateZippEvalSites(bytes,{...inventory,sites:[bad]},observer),/Malformed OXC evalSite/);
  const swapped={...inner,firstArgumentSite:{...inner.firstArgumentSite,start:0}};
  assert.throws(()=>correlateZippEvalSites(bytes,{...inventory,sites:[swapped]},observer),/Malformed OXC firstArgumentSite/);
  const surrogate={...inner,evalSite:{...inner.evalSite,start:source.indexOf('🦀')+1}};
  assert.throws(()=>correlateZippEvalSites(bytes,{...inventory,sites:[surrogate]},observer),/Malformed OXC evalSite/);
});

test('ambiguous positions are never silently assigned to the first candidate',()=>{
  const duplicate={...inventory,sites:[inner,inner]};
  const report=correlateZippEvalSites(bytes,duplicate,
    {...observer,events:[original[0]]});
  assert.deepEqual(report.summary,
    {total:1,matched:0,ambiguous:1,unmatched:0,unavailable:0});
  assert.equal(report.events[0].correlation.candidateCount,2);
});

test('unsupported direct eval is reported without pretending to be captured',()=>{
  const src="function f(){eval();}";
  const b=Buffer.from(src),s=digest(b);
  const idx=src.indexOf('eval()');
  const inv={schemaVersion:1,sourceSha256:s,sites:[],
    unsupported:[{evalSite:{start:idx,end:idx+6,expression:'eval()'},reason:'missing first argument'}]};
  const evt={schemaVersion:1,engine:'zipp',sourceSha256:s,truncated:false,
    events:[event(0,'direct-eval','2+2',null)]};
  // An unavailable caller is not invented from inventory alone.
  assert.equal(correlateZippEvalSites(b,inv,evt).events[0].correlation.reason,'caller-unavailable');
  const caller={...original[0].caller,functionId:0,line:1,column:idx+1};
  const correlated=correlateZippEvalSites(b,inv,
    {...evt,events:[{...evt.events[0],caller}]});
  assert.equal(correlated.events[0].correlation.reason,'unsupported-original-ast-site');
});

test('missing callsite, malformed event and truncation stay explicit',()=>{
  const missing={...original[0],caller:{...original[0].caller,column:9999}};
  const report=correlateZippEvalSites(bytes,inventory,
    {...observer,truncated:true,events:[missing]});
  assert.equal(report.observerTruncated,true);
  assert.equal(report.events[0].correlation.reason,'no-original-ast-site');
  assert.throws(()=>correlateZippEvalSites(bytes,inventory,
    {...observer,events:[{...original[0],sourceHex:'ed a0 80'}]}),/Invalid ZIPP event/);
  assert.throws(()=>correlateZippEvalSites(bytes,inventory,
    {...observer,events:[{...original[0],index:5}]}),/Invalid ZIPP event/);
});

test('preserves raw WTF-8 dynamic code bytes without requiring UTF-8 decode',()=>{
  const raw={...original[0],sourceHex:'eda080'};
  const report=correlateZippEvalSites(bytes,inventory,
    {...observer,events:[raw]});
  assert.equal(report.events[0].sourceSha256,digest(Buffer.from([0xed,0xa0,0x80])));
  assert.equal(report.events[0].sourceByteLength,3);
  assert.equal(report.summary.matched,1);
});

test('BOM, CRLF and ECMAScript Unicode line breaks keep exact UTF-16 source positions',()=>{
  const code="\uFEFFconst crab='🦀';\r\nconst a=eval('1');\u2028const b=eval('2');";
  const b=Buffer.from(code),h=digest(b);
  const first=code.indexOf("eval('1')"),second=code.indexOf("eval('2')");
  const inv={schemaVersion:1,sourceSha256:h,unsupported:[],
    sites:[
      {evalSite:{start:first,end:first+9,expression:"eval('1')"},
        firstArgumentSite:{start:first+5,end:first+8,expression:"'1'"}},
      {evalSite:{start:second,end:second+9,expression:"eval('2')"},
        firstArgumentSite:{start:second+5,end:second+8,expression:"'2'"}},
    ]};
  const make=(index,value,line,column)=>({index,kind:'direct-eval',
    sourceHex:Buffer.from(value).toString('hex'),
    caller:{functionId:0,instructionIp:index+1,origin:'initial-program',
      line,column}});
  const z={schemaVersion:1,engine:'zipp',sourceSha256:h,truncated:false,
    events:[make(0,'1',2,9),make(1,'2',3,9)]};
  const result=correlateZippEvalSites(b,inv,z);
  assert.deepEqual(result.events.map(e=>e.correlation.status),['matched','matched']);
  assert.deepEqual(result.events.map(e=>e.correlation.inventoryIndex),[0,1]);
});

test('invalid original UTF-8 is refused, not silently replaced',()=>{
  assert.throws(()=>correlateZippEvalSites(Buffer.from([0xff]),inventory,observer),/UTF-8|encoded data/);
});
