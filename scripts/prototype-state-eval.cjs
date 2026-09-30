const fs = require('node:fs');
const parser = require('../third_party/js-virtualizer/node_modules/@babel/parser');
const generate = require('../third_party/js-virtualizer/node_modules/@babel/generator').default;

function code(n) { return generate(n, {compact:true, comments:false}).code; }
const UNKNOWN = Symbol('unknown');

function unwrapValue(node, env) {
  if (!node) return UNKNOWN;
  switch (node.type) {
    case 'NumericLiteral': return node.value;
    case 'BooleanLiteral': return node.value;
    case 'NullLiteral': return null;
    case 'Identifier':
      if (node.name === 'undefined') return undefined;
      return env.has(node.name) ? env.get(node.name) : UNKNOWN;
    case 'ParenthesizedExpression': return unwrapValue(node.expression, env);
    case 'AssignmentExpression': {
      if (node.operator !== '=') return UNKNOWN;
      const v = unwrapValue(node.right, env);
      if (node.left.type === 'Identifier' && v !== UNKNOWN) env.set(node.left.name, v);
      return v;
    }
    case 'UnaryExpression': {
      const a = unwrapValue(node.argument, env);
      if (node.operator === 'void') return undefined;
      if (a === UNKNOWN) return UNKNOWN;
      if (node.operator === '!') return !a;
      if (node.operator === '+') return +a;
      if (node.operator === '-') return -a;
      if (node.operator === '~') return ~a;
      return UNKNOWN;
    }
    case 'BinaryExpression': {
      const a = unwrapValue(node.left, env), b = unwrapValue(node.right, env);
      if (a === UNKNOWN || b === UNKNOWN) return UNKNOWN;
      switch (node.operator) {
        case '==': return a == b; // intentional JS semantics
        case '===': return a === b;
        case '!=': return a != b;
        case '!==': return a !== b;
        case '<': return a < b;
        case '<=': return a <= b;
        case '>': return a > b;
        case '>=': return a >= b;
        case '&': return a & b;
        case '|': return a | b;
        case '^': return a ^ b;
        case '<<': return a << b;
        case '>>': return a >> b;
        case '>>>': return a >>> b;
        case '+': return a + b;
        case '-': return a - b;
        case '*': return a * b;
        case '/': return a / b;
        case '%': return a % b;
      }
      return UNKNOWN;
    }
    case 'LogicalExpression': {
      const a = unwrapValue(node.left, env);
      if (a === UNKNOWN) return UNKNOWN;
      if (node.operator === '&&') return a ? unwrapValue(node.right, env) : a;
      if (node.operator === '||') return a ? a : unwrapValue(node.right, env);
      if (node.operator === '??') return a == null ? unwrapValue(node.right, env) : a;
      return UNKNOWN;
    }
    case 'ConditionalExpression': {
      const t = unwrapValue(node.test, env);
      if (t === UNKNOWN) return UNKNOWN;
      return unwrapValue(t ? node.consequent : node.alternate, env);
    }
  }
  return UNKNOWN;
}

function evalNode(node, env, stateVar, semantic, opts={}) {
  if (!node) return;
  switch (node.type) {
    case 'BlockStatement':
      for (const s of node.body) {
        evalNode(s, env, stateVar, semantic, opts);
        if (env.has('__terminal')) break;
      }
      return;
    case 'ExpressionStatement': return evalNode(node.expression, env, stateVar, semantic, opts);
    case 'SequenceExpression': for (const e of node.expressions) evalNode(e, env, stateVar, semantic, opts); return;
    case 'ConditionalExpression': {
      const t = unwrapValue(node.test, env);
      if (t === UNKNOWN) { semantic.push('UNKNOWN_COND:'+code(node.test)); return; }
      return evalNode(t ? node.consequent : node.alternate, env, stateVar, semantic, opts);
    }
    case 'LogicalExpression': {
      const left = unwrapValue(node.left, env);
      if (left === UNKNOWN) { semantic.push('UNKNOWN_LOGIC:'+code(node.left)); return; }
      if (node.operator === '&&') { if (left) return evalNode(node.right, env, stateVar, semantic, opts); return; }
      if (node.operator === '||') { if (!left) return evalNode(node.right, env, stateVar, semantic, opts); return; }
      if (node.operator === '??') { if (left == null) return evalNode(node.right, env, stateVar, semantic, opts); return; }
      semantic.push('UNKNOWN_LOGIC_OP:'+node.operator); return;
    }
    case 'IfStatement': {
      const t = unwrapValue(node.test, env);
      if (t === UNKNOWN) { semantic.push('UNKNOWN_IF:'+code(node.test)); return; }
      return evalNode(t ? node.consequent : node.alternate, env, stateVar, semantic, opts);
    }
    case 'AssignmentExpression': {
      if (node.operator === '=' && node.left.type === 'Identifier') {
        const name=node.left.name;
        const v=unwrapValue(node.right, env);
        if (name === stateVar) {
          if (v === UNKNOWN) semantic.push('UNKNOWN_STATE:'+code(node));
          else env.set(name,v);
          return;
        }
        // Track known control values, but preserve non-control assignments as semantics.
        if (v !== UNKNOWN && (opts.controlVars?.has(name))) { env.set(name,v); return; }
      }
      semantic.push(code(node));
      return;
    }
    case 'CallExpression': {
      // Protector callback wrapper i(function(){...}, this)
      if (node.arguments?.[0]?.type === 'FunctionExpression' || node.arguments?.[0]?.type === 'ArrowFunctionExpression') {
        return evalNode(node.arguments[0].body, env, stateVar, semantic, opts);
      }
      semantic.push(code(node)); return;
    }
    case 'TryStatement': semantic.push('TRY:'+code(node)); return;
    case 'ThrowStatement': semantic.push('THROW:'+code(node.argument)); env.set('__terminal','throw'); return;
    case 'ReturnStatement': semantic.push('RETURN:'+(node.argument?code(node.argument):'')); env.set('__terminal','return'); return;
    case 'VariableDeclaration': {
      for (const d of node.declarations) {
        if (d.id.type==='Identifier' && d.init) {
          const v=unwrapValue(d.init,env);
          if (v!==UNKNOWN) env.set(d.id.name,v);
        }
      }
      return;
    }
    case 'BreakStatement': return;
    default: semantic.push('OPAQUE:'+code(node)); return;
  }
}

function findInnerStateMachine(fn, bitVars) {
  let best=null;
  function countBitRefs(n) {
    let c=0;
    function walk(x, isRoot=false) {
      if (!x || typeof x!=='object') return;
      // Do not let an outer flattened loop inherit signal from a nested VM.
      if (!isRoot && ['ForStatement','WhileStatement','DoWhileStatement'].includes(x.type)) return;
      if (x.type==='Identifier' && bitVars.has(x.name)) c++;
      for (const [k,v] of Object.entries(x)) {
        if (['loc','start','end'].includes(k)) continue;
        if (Array.isArray(v)) for (const y of v) walk(y,false);
        else if (v && typeof v==='object' && v.type) walk(v,false);
      }
    }
    walk(n,true); return c;
  }
  function walk(n, depth=0) {
    if (!n || typeof n!=='object') return;
    if (n.type==='ForStatement' && n.body?.type==='BlockStatement') {
      const sw=n.body.body.find(x=>x.type==='SwitchStatement');
      if (sw && sw.cases.length>=2) {
        const refs=countBitRefs(n.body);
        const score=refs*100 + depth*2 + sw.cases.length;
        if (!best || score>best.score) best={loop:n,sw,score,refs,depth};
      }
    }
    for (const [k,v] of Object.entries(n)) {
      if (['loc','start','end'].includes(k)) continue;
      if (Array.isArray(v)) for (const x of v) walk(x,depth+1);
      else if (v && typeof v==='object' && v.type) walk(v,depth+1);
    }
  }
  walk(fn.body);
  return best;
}

function parseStateMachine(sm) {
  const init=sm.loop.init;
  if (init?.type!=='VariableDeclaration' || init.declarations.length!==1) throw new Error('unsupported loop init');
  const d=init.declarations[0];
  if (d.id.type!=='Identifier' || d.init?.type!=='NumericLiteral') throw new Error('unsupported state init');
  const stateVar=d.id.name, initState=d.init.value;

  // Find selector declaration in loop body: var ..., w = MASK & state >> SHIFT
  let selectorVar=null, lowMask=null, shift=null;
  for (const stmt of sm.loop.body.body) {
    if (stmt.type!=='VariableDeclaration') continue;
    for (const dec of stmt.declarations) {
      if (dec.id.type!=='Identifier' || !dec.init) continue;
      const src=code(dec.init);
      const m=src.match(/^(\d+)&([A-Za-z_$][\w$]*)>>(\d+)$/);
      if (m && m[2]===stateVar) { selectorVar=dec.id.name; lowMask=Number(m[1]); shift=Number(m[3]); }
    }
  }
  if (!selectorVar) throw new Error('selector declaration not found');
  const cases=new Map();
  for (const c of sm.sw.cases) {
    if (c.test?.type==='NumericLiteral') cases.set(c.test.value,c.consequent);
  }
  return {stateVar,initState,selectorVar,lowMask,shift,cases};
}

function deriveBitVars(fetchSource) {
  const ast=parser.parse('const __fetch='+fetchSource+';', {sourceType:'script'});
  const fn=ast.program.body[0].declarations[0].init;
  const envAlias=new Map();
  const candidates=new Map(); // source selector -> Map(mask -> destination var)

  function add(root, mask, lhs) {
    if (!root || !Number.isInteger(mask) || mask<=0 || (mask & (mask-1))!==0) return;
    if (!candidates.has(root)) candidates.set(root,new Map());
    candidates.get(root).set(mask,lhs);
  }
  function idOf(x) {
    if (!x) return null;
    if (x.type==='Identifier') return envAlias.get(x.name)||x.name;
    if (x.type==='AssignmentExpression' && x.operator==='=' && x.left.type==='Identifier') {
      const root=idOf(x.right);
      if (root) envAlias.set(x.left.name,root);
      return root;
    }
    return null;
  }
  function numOf(x) {
    if (!x) return null;
    if (x.type==='NumericLiteral') return x.value;
    if (x.type==='AssignmentExpression' && x.operator==='=' && x.right.type==='NumericLiteral') return x.right.value;
    return null;
  }
  function process(n) {
    if (!n) return;
    if (n.type==='SequenceExpression') { for (const e of n.expressions) process(e); return; }
    if (n.type==='ConditionalExpression') { process(n.consequent); process(n.alternate); return; }
    if (n.type==='ExpressionStatement') return process(n.expression);
    if (n.type==='BlockStatement') { for (const s of n.body) process(s); return; }
    if (n.type==='AssignmentExpression' && n.operator==='=' && n.left.type==='Identifier') {
      const lhs=n.left.name;
      if (n.right.type==='Identifier') envAlias.set(lhs, envAlias.get(n.right.name)||n.right.name);
      if (n.right.type==='BinaryExpression' && n.right.operator==='&') {
        let root=idOf(n.right.left), mask=numOf(n.right.right);
        if (!root) { root=idOf(n.right.right); mask=numOf(n.right.left); }
        add(root,mask,lhs);
      }
      process(n.right);
      return;
    }
    for (const [k,v] of Object.entries(n)) {
      if (['loc','start','end'].includes(k)) continue;
      if (Array.isArray(v)) for (const x of v) if (x?.type) process(x);
      else if (v?.type) process(v);
    }
  }
  process(fn.body);

  let selector=null, bits=new Map();
  for (const [root,map] of candidates) {
    const score=[...map.keys()].filter(x=>x<=128).length;
    if (!selector || score>bits.size) { selector=root; bits=map; }
  }
  return {selector,bits};
}

function routeOpcode(machine, bits, opcode, maxSteps=64) {
  const env=new Map();
  env.set(machine.stateVar,machine.initState);
  const controlVars=new Set([machine.selectorVar,...bits.values()]);
  for (const [mask,name] of bits) env.set(name, (opcode & mask) ? mask : 0);
  const semantic=[], trace=[];
  for (let step=0;step<maxSteps;step++) {
    const k=env.get(machine.stateVar);
    if (k===undefined) return {trace,semantic,terminal:'exit'};
    if (typeof k!=='number') return {trace,semantic,terminal:'unknown-state'};
    const low=k & machine.lowMask;
    const sel=(k >> machine.shift) & machine.lowMask;
    env.set(machine.selectorVar,sel);
    trace.push(k);
    const body=machine.cases.get(low);
    if (!body) return {trace,semantic,terminal:'missing-case-'+low};
    const before=k;
    for (const stmt of body) evalNode(stmt,env,machine.stateVar,semantic,{controlVars});
    if (env.has('__terminal')) return {trace,semantic,terminal:env.get('__terminal')};
    const after=env.get(machine.stateVar);
    if (after===before) return {trace,semantic,terminal:'stalled'};
  }
  return {trace,semantic,terminal:'step-limit'};
}

const [,, parentPath, fetchPath, maxOp='19'] = process.argv;
if (!parentPath || !fetchPath) {
  console.error('usage: prototype-state-eval.cjs <parent.js> <fetch.js> [max-opcode]'); process.exit(2);
}
const parentRaw=fs.readFileSync(parentPath,'utf8');
const parentAst=parser.parse('const __parent='+parentRaw+';', {sourceType:'script'});
const parentFn=parentAst.program.body[0].declarations[0].init;
const fetchRaw=fs.readFileSync(fetchPath,'utf8');
const bitInfo=deriveBitVars(fetchRaw);
const selector=bitInfo.selector;
const bits=bitInfo.bits;
if (!selector || bits.size < 2) throw new Error('opcode selector bits not recovered');
const smChoice=findInnerStateMachine(parentFn, new Set(bits.values()));
const sm=parseStateMachine(smChoice);
console.log('machine', {stateVar:sm.stateVar,initState:sm.initState,selectorVar:sm.selectorVar,lowMask:sm.lowMask,shift:sm.shift,bitRefs:smChoice.refs,depth:smChoice.depth});
console.log('opcode selector', selector);
console.log('opcode bits', Object.fromEntries([...bits].map(([k,v])=>[k,v])));
for (let op=0; op<=Number(maxOp); op++) {
  const r=routeOpcode(sm,bits,op);
  console.log(JSON.stringify({op,trace:r.trace,terminal:r.terminal,semantic:r.semantic}));
}
