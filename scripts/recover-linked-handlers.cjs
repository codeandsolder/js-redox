#!/usr/bin/env node
const fs=require('node:fs');
const path=require('node:path');
const os=require('node:os');
const cp=require('node:child_process');
const acorn=require('../third_party/js-virtualizer/node_modules/acorn');

const reportPath=process.argv[2];
if(!reportPath) throw new Error('usage: recover-linked-handlers.cjs report.jsonl [--file substring]');
function arg(name,def=''){const i=process.argv.indexOf(name);return i>=0?process.argv[i+1]:def;}
const fileFilter=arg('--file','');

function parseFunctionSpan(id){
  const m=/^fn@([0-9a-f]+)-([0-9a-f]+)$/.exec(id);
  if(!m)return null;
  return [parseInt(m[1],16),parseInt(m[2],16)];
}
function lhsId(n){return n&&n.type==='Identifier'?n.name:null;}
function inferFlags(fnSource, selector, allowedMasks){
  const wrapped='('+fnSource+')';
  const ast=acorn.parse(wrapped,{ecmaVersion:'latest',sourceType:'script'});
  const aliases=new Map(), constants=new Map(), flags=new Map();
  // The Rust report's selector_masks are useful hints but may be incomplete when
  // a bit is decoded in a sibling control-state of the same fetch closure.
  // Discover any power-of-two dependency that can be traced back to the opcode.
  const allowed=new Set(allowedMasks);
  for(let bit=1;bit>0 && bit<=0x40000000;bit*=2) allowed.add(bit);

  function resolveOrigin(n,seen=new Set()){
    if(!n)return null;
    if(n.type==='Identifier'){
      if(n.name===selector)return selector;
      if(seen.has(n.name))return null;
      seen.add(n.name);
      const a=aliases.get(n.name);
      return a?resolveOrigin({type:'Identifier',name:a},seen):null;
    }
    if(n.type==='AssignmentExpression'&&n.operator==='=')return resolveOrigin(n.right,seen);
    if(n.type==='ParenthesizedExpression')return resolveOrigin(n.expression,seen);
    return null;
  }
  function num(n){
    if(!n)return null;
    if(n.type==='Literal'&&typeof n.value==='number'&&Number.isInteger(n.value))return n.value;
    if(n.type==='Identifier'&&constants.has(n.name))return constants.get(n.name);
    if(n.type==='AssignmentExpression'&&n.operator==='=')return num(n.right);
    if(n.type==='ParenthesizedExpression')return num(n.expression);
    return null;
  }
  function deps(n,out=new Set()){
    if(!n)return out;
    if(n.type==='BinaryExpression'&&n.operator==='&'){
      const ln=num(n.left), rn=num(n.right);
      const lo=resolveOrigin(n.left), ro=resolveOrigin(n.right);
      if(rn!==null&&lo===selector&&allowed.has(rn))out.add(rn);
      if(ln!==null&&ro===selector&&allowed.has(ln))out.add(ln);
      deps(n.left,out); deps(n.right,out); return out;
    }
    if(n.type==='UnaryExpression'){deps(n.argument,out);return out;}
    if(n.type==='AssignmentExpression'){deps(n.right,out);return out;}
    if(n.type==='SequenceExpression'){for(const x of n.expressions)deps(x,out);return out;}
    if(n.type==='LogicalExpression'||n.type==='BinaryExpression'){deps(n.left,out);deps(n.right,out);return out;}
    if(n.type==='ConditionalExpression'){deps(n.test,out);deps(n.consequent,out);deps(n.alternate,out);return out;}
    return out;
  }
  function visit(n){
    if(!n||typeof n!=='object')return;
    if(n.type==='AssignmentExpression'&&n.operator==='='){
      visit(n.right);
      const id=lhsId(n.left);
      if(id){
        const origin=resolveOrigin(n.right);
        const val=num(n.right);
        if(origin)aliases.set(id,origin); else aliases.delete(id);
        if(val!==null)constants.set(id,val); else constants.delete(id);
        const ds=[...deps(n.right)];
        if(ds.length===1&&allowed.has(ds[0]))flags.set(ds[0],id);
      }
      return;
    }
    if(n.type==='SequenceExpression'){for(const x of n.expressions)visit(x);return;}
    if(n.type==='BinaryExpression'||n.type==='LogicalExpression'){visit(n.left);visit(n.right);return;}
    if(n.type==='UnaryExpression'||n.type==='UpdateExpression'){visit(n.argument);return;}
    if(n.type==='ConditionalExpression'){visit(n.test);visit(n.consequent);visit(n.alternate);return;}
    if(n.type==='CallExpression'){visit(n.callee);for(const a of n.arguments)visit(a);return;}
    for(const v of Object.values(n)){
      if(Array.isArray(v))for(const x of v)visit(x);
      else if(v&&typeof v==='object'&&v.type)visit(v);
    }
  }
  visit(ast);
  return Object.fromEntries([...flags.entries()].sort((a,b)=>a[0]-b[0]));
}

const lines=fs.readFileSync(reportPath,'utf8').split(/\r?\n/).filter(Boolean);
const reports=lines.map(x=>JSON.parse(x)).filter(r=>!fileFilter||r.file.includes(fileFilter));
const output=[];

for(const report of reports){
  const source=fs.readFileSync(report.file,'utf8');
  const funcs=new Map(report.functions.map(f=>[f.id,f]));
  const builders=new Map(report.push_builders.map(b=>[b.start,b]));
  const stateMachines=report.state_machines||[];

  for(const dec of report.decoder_candidates||[]){
    if(dec.builder_start==null||!dec.selector_var||!(dec.selector_masks||[]).length)continue;
    const span=parseFunctionSpan(dec.function_id); if(!span)continue;
    const ds=span[0], de=span[1];
    const childSource=source.slice(ds,de);
    let flagMap;
    try{flagMap=inferFlags(childSource,dec.selector_var,dec.selector_masks);}
    catch(e){output.push({file:report.file,decoder:dec.function_id,status:'flag-parse-error',error:String(e)});continue;}
    const reportMasks=dec.selector_masks.slice().sort((a,b)=>a-b);
    const masks=Object.keys(flagMap).map(Number).filter(Number.isFinite).sort((a,b)=>a-b);
    if(!masks.length || reportMasks.some(m=>!flagMap[m])){
      output.push({file:report.file,decoder:dec.function_id,status:'missing-flags',flags:flagMap,masks,reportMasks});
      continue;
    }

    const containingFuncs=report.functions.filter(f=>f.start<=ds&&f.end>=de);
    const containingIds=new Set(containingFuncs.map(f=>f.id));
    let sms=stateMachines.filter(sm=>containingIds.has(sm.function_id)&&sm.shift!=null&&sm.switch_cases>=3);
    const after=sms.filter(sm=>sm.start>=de);
    if(after.length)sms=after;
    if(!sms.length){
      output.push({file:report.file,decoder:dec.function_id,status:'no-handler-state-machine',flags:flagMap});
      continue;
    }
    sms.sort((a,b)=>{
      const fa=funcs.get(a.function_id), fb=funcs.get(b.function_id);
      const sa=(fa.end-fa.start), sb=(fb.end-fb.start);
      return sa-sb || (a.end-a.start)-(b.end-b.start) || a.start-b.start;
    });
    const sm=sms[0];
    const parent=funcs.get(sm.function_id);
    if(!parent){
      output.push({file:report.file,decoder:dec.function_id,status:'missing-parent'});
      continue;
    }

    const builder=builders.get(dec.builder_start);
    if(!builder)continue;
    const observed=[...new Set(builder.values.filter((_,i)=>i%dec.width===0).filter(x=>x!==null))].sort((a,b)=>a-b);
    if(!observed.length)continue;
    const lo=Math.min(...observed), hi=Math.max(...observed);

    const tmpBase=fs.mkdtempSync(path.join(os.tmpdir(),'jsvm-'));
    const parentFile=path.join(tmpBase,'parent.js');
    const pathFile=path.join(tmpBase,'paths.json');
    const normFile=path.join(tmpBase,'norm.json');
    fs.writeFileSync(parentFile,'('+source.slice(parent.start,parent.end)+');\n');

    const flagSpec=masks.map(m=>flagMap[m]+'='+m).join(',');
    const recoverArgs=[
      path.join(__dirname,'recover-flattened-handlers.cjs'),parentFile,
      '--state',sm.state_var,'--mask',String(sm.mask),'--shift',String(sm.shift),
      '--flags',flagSpec,'--opcodes',lo+'-'+hi
    ];
    let pathsJson;
    try{pathsJson=cp.execFileSync(process.execPath,recoverArgs,{encoding:'utf8',maxBuffer:20*1024*1024,timeout:120000});}
    catch(e){
      output.push({file:report.file,decoder:dec.function_id,status:'recover-error',error:String(e.stderr||e)});
      try{fs.rmSync(tmpBase,{recursive:true,force:true});}catch{}
      continue;
    }
    fs.writeFileSync(pathFile,pathsJson);

    const mapping=[];
    for(const [off,v] of Object.entries(dec.operand_vars||{})){
      if(Number(off)>0)mapping.push(v+'=op'+off);
    }
    mapping.push(dec.ip+'=ip',dec.selector_var+'=opcode');
    for(const m of masks)mapping.push(flagMap[m]+'=flag'+m);

    let normJson;
    try{
      normJson=cp.execFileSync(process.execPath,[
        path.join(__dirname,'normalize-handler-paths.cjs'),pathFile,'--map',mapping.join(',')
      ],{encoding:'utf8',maxBuffer:30*1024*1024,timeout:120000});
    }catch(e){
      output.push({file:report.file,decoder:dec.function_id,status:'normalize-error',error:String(e.stderr||e)});
      try{fs.rmSync(tmpBase,{recursive:true,force:true});}catch{}
      continue;
    }
    fs.writeFileSync(normFile,normJson);
    const norm=JSON.parse(normJson);
    const handlers=norm.out.filter(x=>observed.includes(x.opcode));

    output.push({
      file:report.file,
      decoder:dec.function_id,
      status:'ok',
      parent:parent.id,
      state_machine:{state:sm.state_var,init:sm.init_state,mask:sm.mask,shift:sm.shift,cases:sm.switch_cases,start:sm.start,end:sm.end},
      selector:dec.selector_var,
      flags:flagMap,
      operands:dec.operand_vars,
      ip:dec.ip,
      width:dec.width,
      observed_opcodes:observed,
      handlers
    });

    try{fs.rmSync(tmpBase,{recursive:true,force:true});}catch{}
  }
}
console.log(JSON.stringify(output,null,2));
