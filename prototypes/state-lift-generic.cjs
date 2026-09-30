const fs = require('fs');
const acorn = require('/srv/scratch/js_devirtualization/third_party/js-virtualizer/node_modules/acorn');

const file = process.argv[2];
const wantedState = process.argv[3];
const wantedInit = Number(process.argv[4]);
const flagSpec = process.argv[5] || '';
const flagMap = new Map(
  flagSpec.split(',').filter(Boolean).map(part => {
    const [name,mask] = part.split('=');
    return [name, Number(mask)];
  })
);
if (!wantedState || !Number.isFinite(wantedInit) || !flagMap.size) {
  throw new Error('usage: state-lift-generic.cjs <file> <stateVar> <init> A=1,B=2,...');
}
const src = fs.readFileSync(file, 'utf8');
const ast = acorn.parse(src, {ecmaVersion:'latest', sourceType:'script'});

function text(n){ return src.slice(n.start,n.end).replace(/\s+/g,' ').trim(); }
function walk(n, fn){
  if (!n || typeof n !== 'object') return;
  fn(n);
  for (const [k,v] of Object.entries(n)) {
    if (k==='start'||k==='end'||k==='loc') continue;
    if (Array.isArray(v)) for (const x of v) walk(x,fn);
    else if (v && typeof v==='object' && v.type) walk(v,fn);
  }
}
function literalNum(n){
  return n && n.type==='Literal' && typeof n.value==='number' ? n.value : null;
}
function initStateFor(n){
  if (n.type!=='ForStatement' || !n.init || n.init.type!=='VariableDeclaration') return null;
  for (const d of n.init.declarations) {
    if (d.id.type==='Identifier' && d.init && literalNum(d.init)!==null)
      return {name:d.id.name,value:d.init.value};
  }
  return null;
}
const machines=[];
walk(ast,n=>{ const i=initStateFor(n); if(i) machines.push({node:n,...i}); });
const m=machines.find(x=>x.name===wantedState && x.value===wantedInit);
if(!m) throw new Error(wantedState + '=' + wantedInit + ' state machine not found');

let selectorName=null, selectorMask=null, selectorShift=null, switchMask=null, sw=null;
for(const st of m.node.body.body){
  if(st.type==='VariableDeclaration'){
    for(const d of st.declarations){
      if(!d.init||d.id.type!=='Identifier') continue;
      // mask & (state >> shift), either operand order.
      const e=d.init;
      if(e.type==='BinaryExpression' && e.operator==='&'){
        const pairs=[[e.left,e.right],[e.right,e.left]];
        for(const [a,b] of pairs){
          const mask=literalNum(a);
          if(mask===null||!b||b.type!=='BinaryExpression'||b.operator!=='>>') continue;
          if(b.left.type==='Identifier'&&b.left.name===m.name&&literalNum(b.right)!==null){
            selectorName=d.id.name; selectorMask=mask; selectorShift=b.right.value;
          }
        }
      }
    }
  } else if(st.type==='SwitchStatement'){
    const e=st.discriminant;
    if(e.type==='BinaryExpression'&&e.operator==='&'){
      const pairs=[[e.left,e.right],[e.right,e.left]];
      for(const [a,b] of pairs){
        const mask=literalNum(a);
        if(mask!==null && b.type==='Identifier'&&b.name===m.name){
          switchMask=mask; sw=st;
        }
      }
    }
  }
}
if(!sw) throw new Error('state switch not found');
console.error('machine', {state:m.name, init:m.value, selectorName, selectorMask, selectorShift, switchMask, cases:sw.cases.length});

const cases=new Map();
for(const c of sw.cases){
  const v=c.test ? literalNum(c.test):'default';
  cases.set(v,c.consequent);
}

function known(value){ return {known:true,value}; }
const UNKNOWN={known:false,value:undefined};

function evalExpr(n,env){
  if(!n) return UNKNOWN;
  switch(n.type){
    case 'Literal': return known(n.value);
    case 'Identifier': return env.has(n.name)?known(env.get(n.name)):UNKNOWN;
    case 'UnaryExpression':{
      if(n.operator==='void') return known(undefined);
      const a=evalExpr(n.argument,env); if(!a.known)return UNKNOWN;
      switch(n.operator){case '!':return known(!a.value);case '~':return known(~a.value);case '+':return known(+a.value);case '-':return known(-a.value);case 'typeof':return known(typeof a.value);}
      return UNKNOWN;
    }
    case 'BinaryExpression':{
      const a=evalExpr(n.left,env),b=evalExpr(n.right,env);if(!a.known||!b.known)return UNKNOWN;
      switch(n.operator){
        case '==':return known(a.value==b.value);case '===':return known(a.value===b.value);
        case '!=':return known(a.value!=b.value);case '!==':return known(a.value!==b.value);
        case '<':return known(a.value<b.value);case '<=':return known(a.value<=b.value);case '>':return known(a.value>b.value);case '>=':return known(a.value>=b.value);
        case '&':return known(a.value&b.value);case '|':return known(a.value|b.value);case '^':return known(a.value^b.value);
        case '>>':return known(a.value>>b.value);case '>>>':return known(a.value>>>b.value);case '<<':return known(a.value<<b.value);
        case '+':return known(a.value+b.value);case '-':return known(a.value-b.value);case '*':return known(a.value*b.value);
        case '/':return known(a.value/b.value);case '%':return known(a.value%b.value);
      } return UNKNOWN;
    }
    case 'LogicalExpression':{
      const a=evalExpr(n.left,env);if(!a.known)return UNKNOWN;
      if(n.operator==='&&') return a.value?evalExpr(n.right,env):known(a.value);
      if(n.operator==='||') return a.value?known(a.value):evalExpr(n.right,env);
      if(n.operator==='??') return a.value!=null?known(a.value):evalExpr(n.right,env);
      return UNKNOWN;
    }
    case 'AssignmentExpression':{
      if(n.operator!=='=' || n.left.type!=='Identifier') return UNKNOWN;
      const v=evalExpr(n.right,env); if(!v.known)return UNKNOWN;
      env.set(n.left.name,v.value);
      return v;
    }
    case 'ConditionalExpression':{
      const t=evalExpr(n.test,env);if(!t.known)return UNKNOWN;
      return evalExpr(t.value?n.consequent:n.alternate,env);
    }
    default:return UNKNOWN;
  }
}

function assignedIdent(left){
  return left && left.type==='Identifier'?left.name:null;
}
function execExpr(n,env,stateVar,sem){
  if(!n)return {terminal:false};
  if(n.type==='SequenceExpression'){
    for(const e of n.expressions){ const r=execExpr(e,env,stateVar,sem); if(r.terminal)return r; }
    return {terminal:false};
  }
  if(n.type==='ConditionalExpression'){
    const t=evalExpr(n.test,env);
    if(!t.known) {
      // Runtime-data-dependent choice: preserve the operation but do not let it
      // block state-machine lifting. A subsequent explicit state assignment
      // still determines control flow.
      sem.push(text(n));
      return {terminal:false};
    }
    return execExpr(t.value?n.consequent:n.alternate,env,stateVar,sem);
  }
  if(n.type==='LogicalExpression'){
    const a=evalExpr(n.left,env);
    if(!a.known) { sem.push(text(n)); return {terminal:false}; }
    if(n.operator==='&&'){ if(a.value)return execExpr(n.right,env,stateVar,sem); return {terminal:false}; }
    if(n.operator==='||'){ if(!a.value)return execExpr(n.right,env,stateVar,sem); return {terminal:false}; }
  }
  if(n.type==='AssignmentExpression'){
    const id=assignedIdent(n.left);
    if(id===stateVar){
      const v=evalExpr(n.right,env);
      if(!v.known) throw new Error('unknown state rhs: '+text(n.right));
      env.set(stateVar,v.value);
      return {terminal:v.value===undefined};
    }
    // Preserve semantic effects, but propagate known simple assignments because
    // a later predicate may depend on them.
    const v=evalExpr(n.right,env);
    if(id&&v.known) env.set(id,v.value);
    sem.push(text(n));
    return {terminal:false};
  }
  if(n.type==='CallExpression' && n.arguments[0] && (n.arguments[0].type==='FunctionExpression'||n.arguments[0].type==='ArrowFunctionExpression')){
    return execStatements(n.arguments[0].body.body,env,stateVar,sem);
  }
  sem.push(text(n));
  return {terminal:false};
}

function execStatement(st,env,stateVar,sem){
  switch(st.type){
    case 'ExpressionStatement':return execExpr(st.expression,env,stateVar,sem);
    case 'BlockStatement':return execStatements(st.body,env,stateVar,sem);
    case 'IfStatement':{
      const t=evalExpr(st.test,env);
      if(!t.known) throw new Error('unknown if: '+text(st.test));
      if(t.value) return execStatement(st.consequent,env,stateVar,sem);
      if(st.alternate) return execStatement(st.alternate,env,stateVar,sem);
      return {terminal:false};
    }
    case 'VariableDeclaration':
      for(const d of st.declarations){
        if(d.id.type==='Identifier'&&d.init){
          const v=evalExpr(d.init,env);if(v.known)env.set(d.id.name,v.value);
        }
      } return {terminal:false};
    case 'ThrowStatement':sem.push('throw '+text(st.argument));return {terminal:true,kind:'throw'};
    case 'ReturnStatement':sem.push('return '+(st.argument?text(st.argument):''));return {terminal:true,kind:'return'};
    case 'TryStatement':
    case 'ForStatement':
    case 'WhileStatement':
    case 'FunctionDeclaration':
      // Nested semantic machinery belongs to the opcode operation, not this
      // dispatcher. Preserve it as opaque source and continue.
      sem.push(text(st)); return {terminal:false};
    case 'BreakStatement': return {terminal:false};
    default: sem.push(text(st)); return {terminal:false};
  }
}
function execStatements(stmts,env,stateVar,sem){
  for(const st of stmts){ const r=execStatement(st,env,stateVar,sem); if(r.terminal)return r; }
  return {terminal:false};
}

function signature(sem){
  return sem.map(s=>s.replace(/\s+/g,' ').trim()).join(' ; ');
}
function runOpcode(op){
  const env=new Map([[m.name,m.value]]);
  for (const [name,mask] of flagMap) env.set(name, op & mask);
  const sem=[];
  const trace=[];
  for(let steps=0;steps<64;steps++){
    const state=env.get(m.name);
    if(state===undefined) return {op,trace,sem,terminal:'undefined'};
    const selector=(state>>selectorShift)&selectorMask;
    env.set(selectorName,selector);
    const caseNo=state&switchMask;
    trace.push(state);
    const body=cases.get(caseNo);
    if(!body) throw new Error('missing case '+caseNo+' state '+state);
    const before=env.get(m.name);
    const r=execStatements(body,env,m.name,sem);
    if(r.terminal)return {op,trace,sem,terminal:r.kind||'undefined'};
    const after=env.get(m.name);
    if(after===before) return {op,trace,sem,terminal:'no-transition'};
  }
  return {op,trace,sem,terminal:'step-limit'};
}

const groups=new Map();
let selectorDomainMask = 0;
for (const mask of flagMap.values()) selectorDomainMask |= mask;
for(let op=0;op<=selectorDomainMask;op++){
  try{
    const r=runOpcode(op);
    const sig=signature(r.sem);
    if(!groups.has(sig))groups.set(sig,[]);
    groups.get(sig).push(op);
    console.log(JSON.stringify({op,trace:r.trace,terminal:r.terminal,semantics:r.sem}));
  }catch(e){
    console.log(JSON.stringify({op,error:e.message}));
  }
}
console.log('GROUPS');
for(const [sig,ops] of groups)console.log(JSON.stringify({ops,signature:sig}));
