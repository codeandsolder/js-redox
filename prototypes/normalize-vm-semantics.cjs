const fs=require('fs');
const acorn=require('/srv/scratch/js_devirtualization/third_party/js-virtualizer/node_modules/acorn');

const lines=fs.readFileSync(process.argv[2],'utf8').split(/\n/).filter(Boolean);
const rows=[];
for(const line of lines){
  if(line==='GROUPS')break;
  try{const x=JSON.parse(line); if(x.op!==undefined && x.semantics)rows.push(x);}catch{}
}

function key(x){return JSON.stringify(x);}
function cloneNode(n){return n;}

function makeCanon(aliasableAssignments){
  const aliases=new Map();
  const ids=new Map();
  let next=0;
  const resolving=new Set();

  function cid(name){
    if(!ids.has(name))ids.set(name,'v'+(next++));
    return ids.get(name);
  }
  function resolveId(name){
    if(!aliases.has(name)||resolving.has(name))return ['id',cid(name)];
    resolving.add(name);
    const out=canonExpr(aliases.get(name),false);
    resolving.delete(name);
    return out;
  }
  function canonGeneric(n){
    if(n===null||n===undefined)return null;
    if(Array.isArray(n))return n.map(canonGeneric);
    if(typeof n!=='object')return n;
    if(n.type==='Identifier')return ['id',cid(n.name)];
    if(n.type==='Literal')return ['lit',n.value];
    const out=['node',n.type];
    const skip=new Set(['type','start','end','raw','loc']);
    for(const k of Object.keys(n).sort()){
      if(skip.has(k))continue;
      // Noncomputed property/member keys are semantic names; regular binding
      // identifiers are handled recursively/anonymized.
      out.push([k,canonGeneric(n[k])]);
    }
    return out;
  }
  function canonExpr(n,top=true){
    if(!n)return ['null'];
    switch(n.type){
      case 'Identifier':return resolveId(n.name);
      case 'Literal':return ['lit',n.value];
      case 'ArrayExpression':return ['array',...n.elements.map(e=>canonExpr(e,false))];
      case 'ObjectExpression':return ['object',...n.properties.map(p=>canonGeneric(p))];
      case 'UnaryExpression':{
        const a=canonExpr(n.argument,false);
        if(n.operator==='~' && Array.isArray(a) && a[0]==='un' && a[1]==='~')return a[2];
        return ['un',n.operator,a];
      }
      case 'BinaryExpression':{
        let a=canonExpr(n.left,false),b=canonExpr(n.right,false);
        if(['&','|','^'].includes(n.operator)){
          if(key(a)===key(b) && ['&','|'].includes(n.operator))return a;
          if(key(a)>key(b))[a,b]=[b,a];
        }
        return ['bin',n.operator,a,b];
      }
      case 'LogicalExpression':
        return ['logic',n.operator,canonExpr(n.left,false),canonExpr(n.right,false)];
      case 'ConditionalExpression':
        return ['cond',canonExpr(n.test,false),canonExpr(n.consequent,false),canonExpr(n.alternate,false)];
      case 'MemberExpression':{
        let obj=canonExpr(n.object,false);
        let prop;
        if(n.computed){
          // Assignment-in-index patterns are protector temporaries; canonicalize
          // to the assigned value while retaining alias for subsequent uses.
          if(n.property.type==='AssignmentExpression' && n.property.operator==='=' && n.property.left.type==='Identifier'){
            aliases.set(n.property.left.name,n.property.right);
            prop=canonExpr(n.property.right,false);
          }else prop=canonExpr(n.property,false);
        }else prop=['prop',n.property.name];
        return ['member',obj,prop,!!n.computed];
      }
      case 'CallExpression':
        return ['call',canonExpr(n.callee,false),...n.arguments.map(a=>canonExpr(a,false))];
      case 'NewExpression':
        return ['new',canonExpr(n.callee,false),...n.arguments.map(a=>canonExpr(a,false))];
      case 'AssignmentExpression':{
        if(n.left.type==='Identifier' && n.operator==='=' && aliasableAssignments.has(n)){
          aliases.set(n.left.name,n.right);
          if(top)return null;
          return canonExpr(n.right,false);
        }
        return ['assign',n.operator,canonExpr(n.left,false),canonExpr(n.right,false)];
      }
      case 'UpdateExpression':
        return ['update',n.operator,canonExpr(n.argument,false),n.prefix];
      case 'SequenceExpression':{
        const out=[];
        for(const e of n.expressions){
          const c=canonExpr(e,true); if(c)out.push(c);
        }
        return out.length===1?out[0]:['seq',...out];
      }
      case 'FunctionExpression':
      case 'ArrowFunctionExpression':
        return ['function',n.params.length,canonGeneric(n.body)];
      default:return canonGeneric(n);
    }
  }
  function processProgram(prog){
    const out=[];
    for(const st of prog.body){
      if(st.type==='ExpressionStatement'){
        const c=canonExpr(st.expression,true);if(c)out.push(c);
      }else if(st.type==='ThrowStatement'){
        out.push(['throw',canonExpr(st.argument,false)]);
      }else if(st.type==='ReturnStatement'){
        out.push(['return',st.argument?canonExpr(st.argument,false):null]);
      }else{
        out.push(['stmt',st.type,canonGeneric(st)]);
      }
    }
    return out;
  }
  return {processProgram};
}

function flattenSemanticNodes(programs){
  const nodes=[];
  for(const p of programs){
    for(const st of p.body){
      if(st.type==='ExpressionStatement'){
        if(st.expression.type==='SequenceExpression'){
          for(const e of st.expression.expressions)nodes.push({kind:'expr',node:e});
        }else{
          nodes.push({kind:'expr',node:st.expression});
        }
      }else nodes.push({kind:'stmt',node:st});
    }
  }
  return nodes;
}
function collectReads(n,out,parent=null,keyName=null){
  if(!n||typeof n!=='object')return;
  if(Array.isArray(n)){for(const x of n)collectReads(x,out,parent,keyName);return;}
  if(n.type==='Identifier'){
    const isWrite =
      (parent?.type==='AssignmentExpression' && keyName==='left') ||
      (parent?.type==='VariableDeclarator' && keyName==='id') ||
      ((parent?.type==='FunctionExpression'||parent?.type==='ArrowFunctionExpression'||parent?.type==='FunctionDeclaration') && keyName==='params') ||
      (parent?.type==='MemberExpression' && keyName==='property' && !parent.computed);
    if(!isWrite)out.add(n.name);
    return;
  }
  for(const [k,v] of Object.entries(n)){
    if(['start','end','loc','raw'].includes(k))continue;
    if(v&&typeof v==='object')collectReads(v,out,n,k);
  }
}
function topAssignment(n){
  if(n?.type==='AssignmentExpression' && n.operator==='=' && n.left.type==='Identifier')return n;
  return null;
}
function aliasableFor(nodes){
  const future=new Set();
  const out=new WeakSet();
  for(let i=nodes.length-1;i>=0;i--){
    const n=nodes[i].kind==='expr'?nodes[i].node:nodes[i].node;
    const a=nodes[i].kind==='expr'?topAssignment(n):null;
    if(a && future.has(a.left.name))out.add(a);
    const reads=new Set();collectReads(n,reads);
    for(const x of reads)future.add(x);
  }
  return out;
}

const groups=new Map();
for(const row of rows){
  const programs=[];
  const rawFailures=[];
  for(const snippet of row.semantics){
    let p;
    try{p=acorn.parse(snippet,{ecmaVersion:'latest'});}
    catch(e){
      try{p=acorn.parse('('+snippet+')',{ecmaVersion:'latest'});}
      catch(e2){rawFailures.push(snippet);continue;}
    }
    programs.push(p);
  }
  const nodes=flattenSemanticNodes(programs);
  const c=makeCanon(aliasableFor(nodes));
  const normalized=[];
  for(const p of programs)normalized.push(...c.processProgram(p));
  for(const raw of rawFailures)normalized.push(['raw',raw]);
  const sig=key(normalized);
  if(!groups.has(sig))groups.set(sig,[]);
  groups.get(sig).push(row.op);
  console.log(JSON.stringify({op:row.op,signature:normalized}));
}
console.log('GROUPS');
for(const [sig,ops] of groups)console.log(JSON.stringify({ops,signature:JSON.parse(sig)}));
