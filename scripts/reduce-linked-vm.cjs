#!/usr/bin/env node
const fs = require('node:fs');
const path = require('node:path');
const acorn = require('../third_party/js-virtualizer/node_modules/acorn');
const escodegen = require('../third_party/js-virtualizer/node_modules/escodegen');

const UNKNOWN = Symbol('unknown');
class Sym {
  constructor(name) { this.name = name; }
  toString() { return this.name; }
}
const isSym = v => v instanceof Sym;
const isForkSignal = v => v && typeof v === 'object' && Array.isArray(v.__stateFork);

function code(n) {
  return escodegen.generate(n, {format:{compact:true,semicolons:false}});
}
function parseExprFunction(raw) {
  const ast=acorn.parse('('+raw+')',{ecmaVersion:'latest',sourceType:'script'});
  return ast.body[0].expression;
}
function parseFor(raw) {
  const ast=acorn.parse('function __sm(){'+raw+'}',{ecmaVersion:'latest',sourceType:'script'});
  const fn=ast.body[0];
  return fn.body.body.find(x=>x.type==='ForStatement');
}
function parseFnId(id) {
  const m=/^fn@([0-9a-f]+)-([0-9a-f]+)$/i.exec(id);
  if (!m) throw new Error('bad fn id '+id);
  return [parseInt(m[1],16),parseInt(m[2],16)];
}
function truthy(v) {
  if (v===UNKNOWN || isSym(v)) return UNKNOWN;
  return !!v;
}

function computedDecoderValue(node, env, dec, opcode) {
  if (node.type !== 'ComputedMemberExpression') return UNKNOWN;
  if (node.object.type !== 'Identifier' || node.object.name !== dec.object) return UNKNOWN;
  const idx=node.property;
  // Acorn ESTree uses .property for computed member.
  if (idx.type==='AssignmentExpression' && idx.operator==='=' &&
      idx.left.type==='Identifier' && dec.base && idx.left.name===dec.base) {
    // base = width * ip
    if (idx.right.type==='BinaryExpression' && idx.right.operator==='*') {
      const a=idx.right.left,b=idx.right.right;
      const width=(a.type==='Literal'?a.value:b.type==='Literal'?b.value:null);
      const ip=(a.type==='Identifier'?a.name:b.type==='Identifier'?b.name:null);
      if (Number(width)===Number(dec.width) && ip===dec.ip) {
        env[dec.base]=new Sym('pc');
        return opcode;
      }
    }
  }
  if (idx.type==='BinaryExpression' && idx.operator==='+' && dec.base) {
    let off=null;
    if (idx.left.type==='Identifier' && idx.left.name===dec.base && idx.right.type==='Literal') off=Number(idx.right.value);
    if (idx.right.type==='Identifier' && idx.right.name===dec.base && idx.left.type==='Literal') off=Number(idx.left.value);
    if (off!==null && off>=1 && off<dec.width) return new Sym('operand'+off);
  }
  return UNKNOWN;
}

function evalExpr(n, env, effects, ctx={}) {
  if (!n) return undefined;
  switch (n.type) {
    case 'Literal': return n.value;
    case 'Identifier':
      return Object.prototype.hasOwnProperty.call(env,n.name)?env[n.name]:UNKNOWN;
    case 'ParenthesizedExpression':
      return evalExpr(n.expression,env,effects,ctx);
    case 'ComputedMemberExpression': {
      if (ctx.decoder) {
        const v=computedDecoderValue(n,env,ctx.decoder,ctx.opcode);
        if (v!==UNKNOWN) return v;
      }
      return UNKNOWN;
    }
    case 'UnaryExpression': {
      const a=evalExpr(n.argument,env,effects,ctx);
      if (a===UNKNOWN || isSym(a)) return UNKNOWN;
      switch(n.operator){
        case 'void': return undefined;
        case '!': return !a;
        case '~': return ~a;
        case '+': return +a;
        case '-': return -a;
        case 'typeof': return typeof a;
        default:return UNKNOWN;
      }
    }
    case 'BinaryExpression':
    case 'LogicalExpression': {
      if (n.type==='LogicalExpression') {
        const l=evalExpr(n.left,env,effects,ctx);
        const lt=truthy(l);
        if (lt===UNKNOWN) return UNKNOWN;
        if (n.operator==='&&') return lt?evalExpr(n.right,env,effects,ctx):l;
        if (n.operator==='||') return lt?l:evalExpr(n.right,env,effects,ctx);
        return UNKNOWN;
      }
      const l=evalExpr(n.left,env,effects,ctx), r=evalExpr(n.right,env,effects,ctx);
      if (l===UNKNOWN || r===UNKNOWN || isSym(l) || isSym(r)) return UNKNOWN;
      switch(n.operator){
        case '==':return l==r; case '!=':return l!=r; case '===':return l===r; case '!==':return l!==r;
        case '<':return l<r; case '<=':return l<=r; case '>':return l>r; case '>=':return l>=r;
        case '&':return l&r; case '|':return l|r; case '^':return l^r;
        case '>>':return l>>r; case '>>>':return l>>>r; case '<<':return l<<r;
        case '+':return l+r; case '-':return l-r; case '*':return l*r; case '/':return l/r; case '%':return l%r;
        default:return UNKNOWN;
      }
    }
    case 'ConditionalExpression': {
      const t=truthy(evalExpr(n.test,env,effects,ctx));
      if (t===UNKNOWN) return UNKNOWN;
      return evalExpr(t?n.consequent:n.alternate,env,effects,ctx);
    }
    case 'SequenceExpression': {
      let v;
      for(const e of n.expressions) {
        v=evalExpr(e,env,effects,ctx);
        if(isForkSignal(v))return v;
      }
      return v;
    }
    case 'AssignmentExpression': {
      if (n.left.type==='Identifier') {
        const name=n.left.name;
        if(name===ctx.stateVar && n.operator==='=' && n.right.type==='ConditionalExpression'){
          const test=truthy(evalExpr(n.right.test,env,effects,ctx));
          if(test===UNKNOWN){
            const yes=evalExpr(n.right.consequent,cloneEnv(env),null,ctx);
            const no=evalExpr(n.right.alternate,cloneEnv(env),null,ctx);
            if(yes!==UNKNOWN && no!==UNKNOWN && !isSym(yes) && !isSym(no)){
              return {__stateFork:[
                {guard:code(n.right.test),value:yes},
                {guard:'!('+code(n.right.test)+')',value:no},
              ]};
            }
          }
        }
        const rhs=evalExpr(n.right,env,effects,ctx);
        if(isForkSignal(rhs))return rhs;
        if(rhs!==UNKNOWN){
          if(n.operator==='=')env[name]=rhs;
          else if(n.operator==='+=' && typeof env[name]==='number' && typeof rhs==='number')env[name]+=rhs;
          else if(n.operator==='-=' && typeof env[name]==='number' && typeof rhs==='number')env[name]-=rhs;
          else { if(effects)effects.push(code(n)); return UNKNOWN; }
          if(effects && !ctx.structural?.has(name))effects.push(code(n));
          return env[name];
        }
      }
      if(effects)effects.push(code(n));
      return UNKNOWN;
    }
    case 'UpdateExpression': {
      if(n.argument.type==='Identifier' && typeof env[n.argument.name]==='number'){
        const name=n.argument.name,old=env[name];
        env[name]+=n.operator==='++'?1:-1;
        if(effects && !ctx.structural?.has(name))effects.push(code(n));
        return n.prefix?env[name]:old;
      }
      if(effects)effects.push(code(n));
      return UNKNOWN;
    }
    default:
      if(effects)effects.push(code(n));
      return UNKNOWN;
  }
}

function deriveDecoderEnv(fnAst, dec, opcode, maxPos=Infinity) {
  const env={};
  if (dec.selector_var) env[dec.selector_var]=opcode;
  const assignments=[];
  function walk(n){
    if(!n||typeof n!=='object')return;
    if(typeof n.start==='number' && n.start>=maxPos)return;
    if(n.type==='AssignmentExpression')assignments.push(n);
    for(const v of Object.values(n)){
      if(Array.isArray(v))for(const x of v)walk(x);
      else if(v&&typeof v==='object'&&v.type)walk(v);
    }
  }
  walk(fnAst.body);

  // A few passes allow temporaries like n/u to feed later bit assignments.
  for(let pass=0;pass<4;pass++){
    let changed=false;
    for(const a of assignments){
      if(a.left.type!=='Identifier')continue;
      const name=a.left.name;
      const before=env[name];
      const v=evalExpr(a.right,env,null,{decoder:dec,opcode});
      if(v!==UNKNOWN){
        if(a.operator==='=')env[name]=v;
        else if(a.operator==='+=' && typeof env[name]==='number'&&typeof v==='number')env[name]+=v;
        else continue;
        if(env[name]!==before)changed=true;
      }
    }
    if(!changed)break;
  }
  return env;
}

function unwrapDispatchCall(stmt){
  if(stmt?.type!=='ExpressionStatement')return null;
  const e=stmt.expression;
  if(e?.type!=='CallExpression'||!e.arguments?.length)return null;
  const fn=e.arguments[0];
  if(fn?.type!=='FunctionExpression'&&fn?.type!=='ArrowFunctionExpression')return null;
  return fn.body?.type==='BlockStatement'?fn.body.body:null;
}


function cloneEnv(env) {
  return {...env};
}

function detectStateFork(expr, env, effects, ctx) {
  if (!expr) return null;
  if (expr.type === 'SequenceExpression') {
    for (const e of expr.expressions) {
      const f = detectStateFork(e, env, effects, ctx);
      if (f) return f;
      // Evaluate preceding sequence elements so guards can depend on their assignments.
      evalExpr(e, env, effects, ctx);
    }
    return null;
  }
  if (expr.type !== 'AssignmentExpression' || expr.operator !== '=' ||
      expr.left.type !== 'Identifier' || expr.left.name !== ctx.stateVar ||
      expr.right.type !== 'ConditionalExpression') {
    return null;
  }

  const testExpr = expr.right.test;
  const test = truthy(evalExpr(testExpr, env, effects, ctx));
  if (test !== UNKNOWN) return null;

  const yes = evalExpr(expr.right.consequent, cloneEnv(env), null, ctx);
  const no = evalExpr(expr.right.alternate, cloneEnv(env), null, ctx);
  if (yes === UNKNOWN || no === UNKNOWN || isSym(yes) || isSym(no)) return null;

  return {
    fork: [
      {guard: code(testExpr), value: yes},
      {guard: '!(' + code(testExpr) + ')', value: no},
    ]
  };
}

function execStmt(stmt,env,effects,ctx){
  switch(stmt.type){
    case 'BlockStatement':
      for(const s of stmt.body){const r=execStmt(s,env,effects,ctx);if(r?.stop)return r;} return {};
    case 'ExpressionStatement': {
      const fork=detectStateFork(stmt.expression,env,effects,ctx);
      if(fork)return fork;
      const value=evalExpr(stmt.expression,env,effects,ctx);
      if(isForkSignal(value))return {fork:value.__stateFork};
      return {};
    }
    case 'IfStatement': {
      const t=truthy(evalExpr(stmt.test,env,effects,ctx));
      if(t===UNKNOWN){effects.push(code(stmt));return {stop:true,unknown:true};}
      const branch=t?stmt.consequent:stmt.alternate;
      return branch?execStmt(branch,env,effects,ctx):{};
    }
    case 'ThrowStatement': effects.push('throw '+code(stmt.argument)); return {stop:true,thrown:true};
    case 'ReturnStatement': effects.push('return '+(stmt.argument?code(stmt.argument):'')); return {stop:true,returned:true};
    case 'TryStatement': effects.push(code(stmt)); return {};
    case 'FunctionDeclaration': effects.push(code(stmt)); return {};
    case 'VariableDeclaration':
      for(const d of stmt.declarations){
        if(d.id.type==='Identifier'&&d.init){
          const v=evalExpr(d.init,env,effects,ctx);
          if(v!==UNKNOWN)env[d.id.name]=v; else effects.push(code(d));
        }
      }
      return {};
    case 'BreakStatement': return {stop:true,break:true};
    default: effects.push(code(stmt)); return {};
  }
}

function reduceStateMachine(raw,sm,initialEnv,opcode){
  const loop=parseFor(raw);
  if(!loop)throw new Error('state loop parse failed');
  const sw=loop.body.body.find(x=>x.type==='SwitchStatement');
  if(!sw)throw new Error('switch missing');
  const caseMap=new Map();
  for(const c of sw.cases)if(c.test?.type==='Literal')caseMap.set(Number(c.test.value),c.consequent);

  const initial={
    env:{...initialEnv,[sm.state_var]:sm.init_state},
    effects:[],
    states:[],
    guards:[],
    iterations:0,
  };
  const queue=[initial],done=[];
  const structural=new Set([sm.state_var,sm.selector_var].filter(Boolean));

  while(queue.length){
    const path=queue.shift();
    let forked=false;

    while(path.iterations<128 && path.env[sm.state_var]!==undefined){
      path.iterations++;
      const state=path.env[sm.state_var];
      if(typeof state!=='number')break;
      const sel=sm.shift==null?undefined:((state>>sm.shift)&sm.mask);
      if(sm.selector_var)path.env[sm.selector_var]=sel;
      const c=state&sm.mask;
      path.states.push(state);
      const cons=caseMap.get(c);
      if(!cons)break;

      let body=cons;
      const unwrapped=cons.length?unwrapDispatchCall(cons[0]):null;
      if(unwrapped)body=unwrapped;
      const before=path.env[sm.state_var];
      let terminal=null;

      for(const stmt of body){
        if(stmt.type==='BreakStatement')break;
        const rr=execStmt(stmt,path.env,path.effects,{structural,stateVar:sm.state_var});
        if(rr?.fork){
          for(const choice of rr.fork){
            const child={
              env:cloneEnv(path.env),
              effects:[...path.effects],
              states:[...path.states],
              guards:[...path.guards,choice.guard],
              iterations:path.iterations,
            };
            child.env[sm.state_var]=choice.value;
            queue.push(child);
          }
          forked=true;
          terminal={forked:true};
          break;
        }
        if(rr?.unknown||rr?.thrown||rr?.returned){
          terminal=rr;
          break;
        }
      }

      if(forked)break;
      if(terminal){
        path.terminal=terminal;
        break;
      }
      if(path.env[sm.state_var]===before){
        path.effects.push('[no-state-change]');
        break;
      }
    }

    if(!forked)done.push(path);
  }

  return {paths:done};
}

function containers(report,start,end){
  return report.functions
    .filter(f=>f.start<=start&&f.end>=end)
    .sort((a,b)=>(a.end-a.start)-(b.end-b.start));
}

function chooseSemanticMachine(report,dec){
  const [ds,de]=parseFnId(dec.function_id);
  for(const f of containers(report,ds,de).slice(1)){
    const sms=report.state_machines
      .filter(sm=>sm.function_id===f.id&&sm.start>de)
      .sort((a,b)=>a.start-b.start);
    if(sms.length)return {parent:f,sm:sms[0]};
  }
  return null;
}

function observedOpcodes(report,dec){
  const b=report.push_builders.find(x=>x.start===dec.builder_start);
  if(!b)return [];
  const width=dec.width,ops=new Set();
  for(let i=0;i<b.values.length;i+=width){
    const v=b.values[i];
    if(Number.isInteger(v))ops.add(v);
  }
  return [...ops].sort((a,b)=>a-b);
}

function main(){
  const argv=process.argv.slice(2);
  if(argv.length<1){
    console.error('usage: reduce-linked-vm.cjs <scan.jsonl> [function-id]');
    process.exit(2);
  }
  const wanted=argv[1];
  for(const line of fs.readFileSync(argv[0],'utf8').trim().split(/\n+/)){
    const report=JSON.parse(line);
    const source=fs.readFileSync(report.file,'utf8');
    for(const dec of report.decoder_candidates||[]){
      if(!dec.builder_var||!dec.selector_var)continue;
      if(wanted&&dec.function_id!==wanted)continue;
      const choice=chooseSemanticMachine(report,dec);
      if(!choice)continue;
      const [ps,pe]=parseFnId(choice.parent.id);
      const parentFn=parseExprFunction(source.slice(ps,pe));
      const sm=choice.sm;
      const smRaw=source.slice(sm.start,sm.end);
      const preHandlerLimit=sm.start-ps;
      const ops=observedOpcodes(report,dec);
      const rows=[];
      for(const op of ops){
        const env=deriveDecoderEnv(parentFn,dec,op,preHandlerLimit);
        const reduced=reduceStateMachine(smRaw,sm,env,op);
        const paths=reduced.paths.map(p=>({
          guards:p.guards,
          states:p.states,
          effects:p.effects,
          terminal:p.terminal||null,
        }));
        const row={
          opcode:op,
          derived_env:Object.fromEntries(Object.entries(env).filter(([k,v])=>typeof v!=='object'&&v!==UNKNOWN)),
          paths,
        };
        if(paths.length===1){
          row.states=paths[0].states;
          row.effects=paths[0].effects;
        }
        rows.push(row);
      }
      console.log(JSON.stringify({
        file:report.file,
        decoder:dec.function_id,
        parent:choice.parent.id,
        state_machine:{
          function_id:sm.function_id,
          state_var:sm.state_var,
          init_state:sm.init_state,
          mask:sm.mask,
          shift:sm.shift,
          selector_var:sm.selector_var,
          span:[sm.start,sm.end],
        },
        opcodes:rows,
      }));
    }
  }
}
main();
