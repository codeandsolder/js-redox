#!/usr/bin/env node
const fs = require('node:fs');
const acorn = require('../third_party/js-virtualizer/node_modules/acorn');
const escodegen = require('../third_party/js-virtualizer/node_modules/escodegen');

function arg(name, def=null) {
  const i = process.argv.indexOf(name);
  return i >= 0 ? process.argv[i+1] : def;
}
const input = process.argv[2];
if (!input) throw new Error('usage: recover-flattened-handlers.cjs <wrapped.js> --state k --mask 7 --shift 3 --flags V=1,C=2,D=4,A=8 --opcodes 0-13');
const stateName = arg('--state');
const mask = Number(arg('--mask'));
const shift = Number(arg('--shift'));
const flagSpec = arg('--flags','');
const opcodeRange = arg('--opcodes','0-15');
const flags = Object.fromEntries(flagSpec.split(',').filter(Boolean).map(x => {
  const [k,v] = x.split('=');
  return [k, Number(v)];
}));
const [opLo, opHi] = opcodeRange.split('-').map(Number);

const source = fs.readFileSync(input,'utf8');
const ast = acorn.parse(source,{ecmaVersion:'latest',sourceType:'script',ranges:true});

function code(node) {
  if (!node) return '';
  return source.slice(node.start,node.end).replace(/\s+/g,' ').trim();
}

function findStateMachine(node) {
  let found = null;
  function walk(n) {
    if (!n || typeof n !== 'object' || found) return;
    if (n.type === 'ForStatement') {
      let initName = null, initValue = null;
      if (n.init?.type === 'VariableDeclaration') {
        for (const d of n.init.declarations) {
          if (d.id.type==='Identifier' && d.id.name===stateName && d.init?.type==='Literal' && typeof d.init.value==='number') {
            initName=d.id.name; initValue=d.init.value;
          }
        }
      }
      if (initName) {
        const sw = n.body?.body?.find?.(x=>x.type==='SwitchStatement' && code(x.discriminant).includes(stateName));
        if (sw) found={loop:n,sw,initValue};
      }
    }
    for (const v of Object.values(n)) {
      if (Array.isArray(v)) for (const x of v) walk(x);
      else if (v && typeof v==='object' && v.type) walk(v);
    }
  }
  walk(node);
  return found;
}

const machine = findStateMachine(ast);
if (!machine) throw new Error('state machine not found');

function unknown(reason) { return {known:false,reason}; }
function known(value) { return {known:true,value}; }

function evalExpr(n, env) {
  if (!n) return unknown('missing');
  switch (n.type) {
    case 'Literal': return known(n.value);
    case 'Identifier':
      if (n.name === 'undefined') return known(undefined);
      return Object.prototype.hasOwnProperty.call(env,n.name) ? known(env[n.name]) : unknown(n.name);
    case 'UnaryExpression': {
      const a=evalExpr(n.argument,env); if(!a.known)return a;
      switch(n.operator){
        case '!': return known(!a.value);
        case '~': return known(~a.value);
        case '+': return known(+a.value);
        case '-': return known(-a.value);
        case 'void': return known(undefined);
        case 'typeof': return known(typeof a.value);
        default:return unknown('unary '+n.operator);
      }
    }
    case 'BinaryExpression': {
      const l=evalExpr(n.left,env), r=evalExpr(n.right,env); if(!l.known||!r.known)return unknown('binary');
      switch(n.operator){
        case '==': return known(l.value==r.value); case '===': return known(l.value===r.value);
        case '!=': return known(l.value!=r.value); case '!==': return known(l.value!==r.value);
        case '<': return known(l.value<r.value); case '<=': return known(l.value<=r.value);
        case '>': return known(l.value>r.value); case '>=': return known(l.value>=r.value);
        case '&': return known(l.value&r.value); case '|': return known(l.value|r.value);
        case '^': return known(l.value^r.value); case '<<': return known(l.value<<r.value);
        case '>>': return known(l.value>>r.value); case '>>>': return known(l.value>>>r.value);
        case '+': return known(l.value+r.value); case '-': return known(l.value-r.value);
        case '*': return known(l.value*r.value); case '/': return known(l.value/r.value);
        case '%': return known(l.value%r.value);
        default:return unknown('bin '+n.operator);
      }
    }
    case 'LogicalExpression': {
      const l=evalExpr(n.left,env); if(!l.known)return l;
      if(n.operator==='&&') return l.value ? evalExpr(n.right,env) : known(l.value);
      if(n.operator==='||') return l.value ? known(l.value) : evalExpr(n.right,env);
      return unknown('logical '+n.operator);
    }
    case 'ConditionalExpression': {
      const t=evalExpr(n.test,env); if(!t.known)return unknown('ternary');
      return evalExpr(t.value?n.consequent:n.alternate,env);
    }
    case 'AssignmentExpression': {
      if(n.operator==='=' && n.left.type==='Identifier'){
        const v=evalExpr(n.right,env);
        if(v.known){env[n.left.name]=v.value; return v;}
      }
      return unknown('assignment');
    }
    case 'SequenceExpression': {
      let last=known(undefined);
      for(const e of n.expressions) last=evalExpr(e,env);
      return last;
    }
  }
  return unknown(n.type);
}

function makeCtx(opcode,state) {
  const env={[stateName]:state};
  for(const [name,bit] of Object.entries(flags)) env[name]=(opcode & bit)!==0 ? bit : 0;
  env.__opcode=opcode;
  return {env,nextState:null,terminal:null,fragments:[],unknown:[]};
}

function processExpr(n,ctx) {
  if (!n || ctx.terminal) return;
  if (n.type==='SequenceExpression') { for(const e of n.expressions) processExpr(e,ctx); return; }
  if (n.type==='ConditionalExpression') {
    const t=evalExpr(n.test,ctx.env);
    if(t.known) processExpr(t.value?n.consequent:n.alternate,ctx);
    else { ctx.unknown.push('condition '+code(n.test)); ctx.fragments.push(code(n)); }
    return;
  }
  if (n.type==='LogicalExpression') {
    const t=evalExpr(n.left,ctx.env);
    if(t.known) {
      if((n.operator==='&&' && t.value)||(n.operator==='||' && !t.value)) processExpr(n.right,ctx);
    } else ctx.fragments.push(code(n));
    return;
  }
  if (n.type==='AssignmentExpression' && n.left.type==='Identifier') {
    if (n.left.name===stateName && n.operator==='=') {
      const v=evalExpr(n.right,ctx.env);
      if(v.known){ctx.nextState=v.value; ctx.env[stateName]=v.value;}
      else ctx.unknown.push('next-state '+code(n.right));
      return;
    }
    const v=evalExpr(n.right,ctx.env);
    if(v.known) ctx.env[n.left.name]=v.value;
    else ctx.fragments.push(code(n));
    return;
  }
  if (n.type==='CallExpression' && n.callee.type==='Identifier' && n.arguments[0]?.type==='FunctionExpression') {
    processStmt(n.arguments[0].body,ctx); return;
  }
  // Preserve semantic operations; do not execute calls/member writes.
  ctx.fragments.push(code(n));
}

function processStmt(n,ctx) {
  if (!n || ctx.terminal) return;
  switch(n.type){
    case 'BlockStatement': for(const s of n.body){processStmt(s,ctx); if(ctx.terminal)break;} return;
    case 'ExpressionStatement': processExpr(n.expression,ctx); return;
    case 'IfStatement': {
      const t=evalExpr(n.test,ctx.env);
      if(t.known) processStmt(t.value?n.consequent:n.alternate,ctx);
      else {ctx.unknown.push('if '+code(n.test)); ctx.fragments.push(code(n));}
      return;
    }
    case 'VariableDeclaration':
      for(const d of n.declarations){
        if(d.id.type==='Identifier' && d.init){
          const v=evalExpr(d.init,ctx.env);
          if(v.known) ctx.env[d.id.name]=v.value;
        }
      }
      return;
    case 'ReturnStatement': ctx.terminal='return '+code(n.argument); return;
    case 'ThrowStatement': ctx.terminal='throw '+code(n.argument); return;
    case 'BreakStatement': return;
    case 'TryStatement':
      // Nested VM/exception machinery is semantic payload. Keep it opaque,
      // but continue after it so a following state assignment is still seen.
      ctx.fragments.push(code(n));
      return;
    case 'ForStatement':
    case 'WhileStatement':
      ctx.fragments.push(code(n));
      return;
    default: ctx.fragments.push(code(n)); return;
  }
}

function selectedCaseForState(state) {
  const selector=state & mask;
  return machine.sw.cases.find(c => {
    if (!c.test) return false;
    const v=evalExpr(c.test,{});
    return v.known && v.value===selector;
  });
}

function runOpcode(opcode) {
  let state=machine.initValue;
  const path=[];
  const allFragments=[];
  const unknown=[];
  for(let step=0;step<64;step++){
    if(state===undefined){return {opcode,path,fragments:allFragments,unknown,terminal:'state=undefined'};}
    const c=selectedCaseForState(state);
    if(!c) return {opcode,path,fragments:allFragments,unknown:[...unknown,'no case for state '+state],terminal:'stuck'};
    const ctx=makeCtx(opcode,state);
    // selector vars are commonly assigned once per loop: e.g. b = mask & state >> shift.
    for(const [name] of Object.entries(flags)) ctx.env[name]=(opcode & flags[name]) ? flags[name] : 0;
    // Discover selector identifiers in the loop body by evaluating declarations against state.
    const body=machine.loop.body.body;
    for(const stmt of body){
      if(stmt.type==='VariableDeclaration'){
        for(const d of stmt.declarations){
          if(d.id.type==='Identifier' && d.init){
            const env={...ctx.env,[stateName]:state};
            const v=evalExpr(d.init,env);
            if(v.known) ctx.env[d.id.name]=v.value;
          }
        }
      }
    }
    // Explicit common selector if not materialized by the declaration scan.
    ctx.env.__selector=(state>>shift)&mask;
    processStmt({type:'BlockStatement',body:c.consequent},ctx);
    path.push({state,case:state&mask,selector:(state>>shift)&mask,next:ctx.nextState,terminal:ctx.terminal,fragments:[...ctx.fragments]});
    allFragments.push(...ctx.fragments);
    unknown.push(...ctx.unknown);
    if(ctx.terminal) return {opcode,path,fragments:allFragments,unknown,terminal:ctx.terminal};
    if(ctx.nextState===null) return {opcode,path,fragments:allFragments,unknown:[...unknown,'no next state from '+state],terminal:'stuck'};
    state=ctx.nextState;
  }
  return {opcode,path,fragments:allFragments,unknown:[...unknown,'step limit'],terminal:'limit'};
}

const results=[];
for(let op=opLo;op<=opHi;op++) results.push(runOpcode(op));
console.log(JSON.stringify({state:stateName,mask,shift,init:machine.initValue,flags,results},null,2));
