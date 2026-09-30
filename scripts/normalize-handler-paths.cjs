#!/usr/bin/env node
const fs=require('node:fs');
const crypto=require('node:crypto');
const acorn=require('../third_party/js-virtualizer/node_modules/acorn');
const escodegen=require('../third_party/js-virtualizer/node_modules/escodegen');

const input=process.argv[2];
if(!input) throw new Error('usage: normalize-handler-paths.cjs paths.json --map a=b,c=d');
function arg(name,def=''){const i=process.argv.indexOf(name);return i>=0?process.argv[i+1]:def;}
const fixed=Object.fromEntries(arg('--map','').split(',').filter(Boolean).map(x=>x.split('=')));
const data=JSON.parse(fs.readFileSync(input,'utf8'));

function isIdentifierKey(parent,node){
  if(!parent)return false;
  if(parent.type==='MemberExpression' && parent.property===node && !parent.computed)return true;
  if((parent.type==='Property'||parent.type==='MethodDefinition') && parent.key===node && !parent.computed && !parent.shorthand)return true;
  if(parent.type==='LabeledStatement' && parent.label===node)return true;
  if((parent.type==='BreakStatement'||parent.type==='ContinueStatement') && parent.label===node)return true;
  return false;
}

function boundNames(fn){
  const out=new Set();
  if(fn.id?.name)out.add(fn.id.name);
  for(const p of fn.params||[]) if(p.type==='Identifier')out.add(p.name);
  function scan(n){
    if(!n||typeof n!=='object')return;
    if(n!==fn && /Function(Expression|Declaration)$/.test(n.type))return;
    if(n.type==='ArrowFunctionExpression' && n!==fn)return;
    if(n.type==='VariableDeclarator' && n.id?.type==='Identifier')out.add(n.id.name);
    if(n.type==='FunctionDeclaration' && n.id?.name)out.add(n.id.name);
    for(const v of Object.values(n)){
      if(Array.isArray(v))for(const x of v)scan(x);
      else if(v&&typeof v==='object'&&v.type)scan(v);
    }
  }
  scan(fn.body);
  return out;
}

function normalizeText(text,globalState,mode){
  if(!text)return '';
  let wrapped='function __h(){\n'+text+';\n}';
  let ast;
  try{ast=acorn.parse(wrapped,{ecmaVersion:'latest',sourceType:'script'});}
  catch(e){
    wrapped='function __h(){\nvoid ('+text+');\n}';
    ast=acorn.parse(wrapped,{ecmaVersion:'latest',sourceType:'script'});
  }
  const root=ast.body[0];
  const scopes=[];

  function shadowed(name){
    return scopes.some(s=>s.has(name));
  }
  function canonical(name){
    if(Object.prototype.hasOwnProperty.call(fixed,name) && !shadowed(name)) return fixed[name];
    if(name==='__h')return name;
    if(['undefined','NaN','Infinity'].includes(name))return name;
    if(mode==='shape')return 'v';
    const key=scopes.length+':'+name;
    if(!globalState.has(key))globalState.set(key,'v'+globalState.size);
    return globalState.get(key);
  }

  function walk(node,parent=null,isSyntheticRoot=false){
    if(!node||typeof node!=='object')return;
    const isFn=['FunctionDeclaration','FunctionExpression','ArrowFunctionExpression'].includes(node.type);
    if(isFn){
      // The synthetic wrapper exists only for parsing. Its free references are
      // the real handler's outer variables, so don't treat wrapper locals as a
      // new lexical boundary unless they are explicitly declared by fragment code.
      const bindings=boundNames(node);
      bindings.delete('__h');
      scopes.push(bindings);
    }

    if(node.type==='Identifier' && !isIdentifierKey(parent,node)){
      node.name=canonical(node.name);
    } else {
      for(const [k,v] of Object.entries(node)){
        if(k==='start'||k==='end'||k==='loc'||k==='range')continue;
        if(Array.isArray(v))for(const x of v)walk(x,node,false);
        else if(v&&typeof v==='object'&&v.type)walk(v,node,false);
      }
    }

    if(isFn)scopes.pop();
  }
  walk(root,null,true);
  return root.body.body.map(s=>escodegen.generate(s,{format:{compact:true,semicolons:false,parentheses:true}})).join(';');
}

function signature(s){return crypto.createHash('sha256').update(s).digest('hex').slice(0,16);}

const out=[];
for(const res of data.results){
  function build(mode){
    const state=new Map(), chunks=[];
    for(const step of res.path)for(const f of step.fragments)chunks.push(normalizeText(f,state,mode));
    let terminal='';
    if(res.terminal && !['state=undefined','stuck','limit'].includes(res.terminal)){
      terminal=normalizeText(res.terminal.replace(/^(throw|return)\s+/,''),state,mode);
      terminal=(res.terminal.startsWith('throw')?'throw:':'return:')+terminal;
    }
    return [...chunks,terminal].filter(Boolean).join('||');
  }
  const semantic=build('exact');
  const shape=build('shape');
  out.push({
    opcode:res.opcode,
    states:res.path.map(x=>x.state),
    semantic,
    signature:signature(semantic),
    shape_semantic:shape,
    shape_signature:signature(shape),
    unknown:res.unknown
  });
}
console.log(JSON.stringify({input,fixed,out},null,2));
