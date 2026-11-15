#!/usr/bin/env node
// Correlate ZIPP's native direct-eval events with OXC's exact-source AST
// inventory. Neither input is an importer witness by itself.
import fs from 'node:fs';
import {createHash} from 'node:crypto';
import {pathToFileURL} from 'node:url';

const hash=(bytes)=>createHash('sha256').update(bytes).digest('hex');
const integer=(value)=>Number.isSafeInteger(value) && value>=0;
function validUtf16Boundary(text,offset){
  if(offset<=0 || offset>=text.length) return true;
  const before=text.charCodeAt(offset-1),after=text.charCodeAt(offset);
  return !(before>=0xD800 && before<=0xDBFF && after>=0xDC00 && after<=0xDFFF);
}

function sourceIndex(text){
  const starts=[0];
  for(let i=0;i<text.length;i++){
    const ch=text[i];
    if(ch==='\n' || ch==='\u2028' || ch==='\u2029' ||
      (ch==='\r' && text[i+1]!=='\n')) starts.push(i+1);
  }
  return function position(offset) {
    let low=0,high=starts.length;
    while(low<high){
      const mid=(low+high)>>>1;
      if(starts[mid]<=offset)low=mid+1;else high=mid;
    }
    const line=low;
    return {line,column:offset-starts[line-1]+1};
  };
}

function checkSite(source,record,unsupported){
  const site=record?.evalSite;
  if(!site || !integer(site.start) || !integer(site.end) ||
    site.start>=site.end || site.end>source.length ||
    !validUtf16Boundary(source,site.start) ||
    !validUtf16Boundary(source,site.end) ||
    source.slice(site.start,site.end)!==site.expression){
    throw Error('Malformed OXC evalSite: span/expression does not match original UTF-16 source');
  }
  if(!unsupported){
    const arg=record.firstArgumentSite;
    if(!arg || !integer(arg.start) || !integer(arg.end) ||
      arg.start>=arg.end || arg.start<site.start || arg.end>site.end ||
      !validUtf16Boundary(source,arg.start) ||
      !validUtf16Boundary(source,arg.end) ||
      source.slice(arg.start,arg.end)!==arg.expression){
      throw Error('Malformed OXC firstArgumentSite');
    }
  }
  return site;
}

function verifySha(value,expected,label){
  if(value!==expected)throw Error(label+' SHA-256 does not match original executable bytes');
}

export function correlateZippEvalSites(originalBytes,inventory,capture){
  const bytes=Buffer.from(originalBytes);
  const source=new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(bytes);
  const sourceSha256=hash(bytes);
  if(inventory?.schemaVersion!==1 || !Array.isArray(inventory.sites) ||
    !Array.isArray(inventory.unsupported))throw Error('Invalid OXC inventory schema');
  verifySha(inventory.sourceSha256,sourceSha256,'OXC inventory');
  if(capture?.schemaVersion!==2 || capture.engine!=='zipp' ||
    !Array.isArray(capture.events) || typeof capture.truncated!=='boolean'){
    throw Error('Invalid ZIPP observer schema');
  }
  verifySha(capture.sourceSha256,sourceSha256,'ZIPP observer');
  const at=sourceIndex(source);
  const positions=new Map();
  function add(record,index,unsupported){
    const site=checkSite(source,record,unsupported);
    const {line,column}=at(site.start);
    const key=line+':'+column;
    const candidates=positions.get(key)??[];
    candidates.push({index,site,firstArgumentSite:record.firstArgumentSite??null,
      unsupported});
    positions.set(key,candidates);
  }
  inventory.sites.forEach((record,index)=>add(record,index,false));
  inventory.unsupported.forEach((record,index)=>add(record,index,true));
  const events=capture.events.map((event,index)=>{
    if(event?.index!==index || !['direct-eval','indirect-or-host','function-constructor'].includes(event.kind) ||
      typeof event.sourceHex!=='string' || !/^(?:[0-9a-f]{2})*$/.test(event.sourceHex) ||
      (event.caller!=null && (typeof event.caller!=='object' ||
        !integer(event.caller.functionId) || !integer(event.caller.instructionIp) ||
        !Number.isSafeInteger(event.caller.line) ||
        !Number.isSafeInteger(event.caller.column)))){
      throw Error('Invalid ZIPP event at index '+index);
    }
    // Outcome is an independent completion of *this compiler attempt*.
    // It does not encode the exact returned JS value or the thrown value.
    // null means the observation was taken while the attempt was in flight.
    const resultOutcome=event.outcome;
    if(resultOutcome!==null &&
      (!resultOutcome || typeof resultOutcome!=='object' ||
        !['returned','threw'].includes(resultOutcome.status) ||
        (resultOutcome.status==='returned' &&
          !['number','string','boolean','undefined','object','function','symbol','bigint']
            .includes(resultOutcome.type)) ||
        (resultOutcome.status==='threw' &&
          Object.hasOwn(resultOutcome,'type')))){
      throw Error('Invalid ZIPP attempt outcome at index '+index);
    }
    const content=Buffer.from(event.sourceHex,'hex');
    const result={index,kind:event.kind,sourceSha256:hash(content),
      sourceByteLength:content.length,caller:event.caller??null,
      outcome:resultOutcome};
    if(event.kind!=='direct-eval'){
      result.correlation={status:'unavailable',reason:'not-a-direct-eval'};
    }else if(event.caller===null || event.caller===undefined){
      result.correlation={status:'unavailable',reason:'caller-unavailable'};
    }else if(event.caller.origin!=='initial-program'){
      if(event.caller.origin!=='runtime-installed'){
        throw Error('Unknown ZIPP caller origin at index '+index);
      }
      result.correlation={status:'unavailable',reason:'runtime-installed-caller'};
    }else if(event.caller.line<1 || event.caller.column<1){
      result.correlation={status:'unmatched',reason:'invalid-caller-position'};
    }else{
      const candidates=positions.get(event.caller.line+':'+event.caller.column)??[];
      if(candidates.length===0){
        result.correlation={status:'unmatched',reason:'no-original-ast-site'};
      }else if(candidates.length!==1){
        result.correlation={status:'ambiguous',candidateCount:candidates.length};
      }else if(candidates[0].unsupported){
        result.correlation={status:'unavailable',reason:'unsupported-original-ast-site'};
      }else{
        const candidate=candidates[0];
        result.correlation={status:'matched',inventoryIndex:candidate.index,
          sourceProvenance:{kind:'initial-program-direct-eval-callsite',
            executableSha256:sourceSha256,evalSite:candidate.site,
            firstArgumentSite:candidate.firstArgumentSite,
            functionId:event.caller.functionId,
            instructionIp:event.caller.instructionIp}};
      }
    }
    return result;
  });
  return {
    schemaVersion:2,kind:'zipp-source-correlation',
    executableSha256:sourceSha256,
    observerTruncated:capture.truncated,
    execution:capture.execution??null,
    summary:{
      total:events.length,
      matched:events.filter(e=>e.correlation.status==='matched').length,
      ambiguous:events.filter(e=>e.correlation.status==='ambiguous').length,
      unmatched:events.filter(e=>e.correlation.status==='unmatched').length,
      unavailable:events.filter(e=>e.correlation.status==='unavailable').length,
      returned:events.filter(e=>e.outcome?.status==='returned').length,
      threw:events.filter(e=>e.outcome?.status==='threw').length,
      pending:events.filter(e=>e.outcome===null).length,
    },
    events,
  };
}

function main(){
  if(process.argv.length!==5) {
    throw Error('Usage: node link-zipp-eval-sites.mjs ORIGINAL.js OXC-INVENTORY.json ZIPP-OBSERVATION.json');
  }
  const [sourceFile,inventoryFile,observerFile]=process.argv.slice(2);
  const result=correlateZippEvalSites(
    fs.readFileSync(sourceFile),
    JSON.parse(fs.readFileSync(inventoryFile,'utf8')),
    JSON.parse(fs.readFileSync(observerFile,'utf8')),
  );
  process.stdout.write(JSON.stringify(result,null,2)+'\n');
}

if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href){
  try{main();}catch(error){console.error('link-zipp-eval-sites: '+error.message);process.exitCode=1;}
}
