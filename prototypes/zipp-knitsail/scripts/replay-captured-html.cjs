const fs = require('fs');
const {createHash} = require('node:crypto');
const vm = require('vm');
const { performance } = require('perf_hooks');

const htmlPath = process.argv[2];
if (!htmlPath) throw new Error('Usage: node replay-captured-html.cjs archived.html');
const htmlBytes = fs.readFileSync(htmlPath);
const htmlSha256 = createHash('sha256').update(htmlBytes).digest('hex');
const html = htmlBytes.toString('utf8');
if (process.env.KNITSAIL_HTML_SHA256 && process.env.KNITSAIL_HTML_SHA256 !== htmlSha256) throw Error('Captured HTML identity mismatch');

const scripts = [...html.matchAll(/<script([^>]*)>([\s\S]*?)<\/script>/gi)].map(m => m[2]);
const wrapper = scripts.find(s => /var g=['"]knitsail['"]/.test(s) && /challenge_version/.test(s));
if (!wrapper) throw new Error('Knitsail wrapper not found');
// This match is the source-literal TEXT (escape sequences remain); do not
// compare it directly with the runtime string passed to knitsail.a.
const payloadMatch = wrapper.match(/var p='([^']+)'/);
const payloadPrefix = payloadMatch ? payloadMatch[1].slice(0, 3) : null;
const handlerRe = payloadPrefix ? new RegExp('\\.' + payloadPrefix + '_\\s*=') : null;
const vmScript = handlerRe ? scripts.find(s => handlerRe.test(s) && /knitsail/.test(s)) : null;
if (!vmScript) throw new Error('Knitsail VM handler not found for prefix ' + payloadPrefix);
const vmSha256 = createHash('sha256').update(vmScript).digest('hex');
// Optional private, exact original VM output for source-offset verification.
// Written before the in-memory instrumentation transforms the executable copy.
if (process.env.KNITSAIL_VM_SOURCE_OUT) {
  fs.writeFileSync(process.env.KNITSAIL_VM_SOURCE_OUT, vmScript);
}


// Optional *site-specific* direct-eval witness. The original source string
// and its sha stay untouched in the report; only the in-memory execution
// copy is instrumented, preserving the syntactically direct eval call.
const dynamicDir = process.env.KNITSAIL_DYNAMIC_DIR || null;
const dynamicCodeEvents = [];
const pendingEval = [];
let dynamicTruncated = false;
let dynamicEvalSite = null;
let runtimeVmScript = vmScript;
const dynamicMaxEvents = Number(process.env.KNITSAIL_DYNAMIC_MAX_EVENTS || '10000');
if (!Number.isSafeInteger(dynamicMaxEvents) || dynamicMaxEvents < 0) {
  throw Error('KNITSAIL_DYNAMIC_MAX_EVENTS must be a nonnegative integer');
}
if (dynamicDir) {
  const evalExpression = 'eval(D)';
  const originalCall = 'return ' + evalExpression;
  if (vmScript.split(originalCall).length !== 2) {
    throw Error('Expected unique original Knitsail eval site');
  }
  const start = vmScript.indexOf(originalCall) + 'return '.length;
  dynamicEvalSite = { start, end: start + evalExpression.length };
  const replacement = [
    'try {',
    'return __knitsail_capture_eval_result(eval(__knitsail_capture_eval_arg(D)));',
    '} catch (__knitsail_capture_error) {',
    '__knitsail_capture_eval_throw(__knitsail_capture_error);',
    'throw __knitsail_capture_error;',
    '}'
  ].join(' ');
  runtimeVmScript = vmScript.replace(originalCall, replacement);
  fs.mkdirSync(dynamicDir, {recursive:true});
}

const eidMatch = wrapper.match(/var eid='([^']*)'/);
const eid = eidMatch ? eidMatch[1] : 'unknown';
const baseHref = process.env.KS_HREF || 'https://www.google.com/search?q=rust+async+tokio&hl=en&gl=us';
const configuredUa = process.env.KS_UA || 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/100.0.4896.127 Safari/537.36';
const configuredPlatform = process.env.KS_PLATFORM || 'Win32';
const configuredHc = Number(process.env.KS_HC || 8);
const configuredMemory = Number(process.env.KS_MEMORY || 8);

let cookieValue = '';
let replacedUrl = null;
let beaconUrls = [];
let accesses = [];
const once = new Set();
function note(s) {
  if (!once.has(s)) {
    once.add(s); accesses.push(s);
    if (accesses.length < 200) console.error('ACCESS', s);
  }
}

function Event(type, init={}) { this.type=type; Object.assign(this, init); }
function CustomEvent(type, init={}) { Event.call(this,type,init); }
const listeners = new Map();
const eventTarget = {
  addEventListener(type, cb){ note('window.addEventListener:'+type); (listeners.get(type)||listeners.set(type,[]).get(type)).push(cb); },
  removeEventListener(type, cb){ note('window.removeEventListener:'+type); },
  dispatchEvent(ev){ for(const cb of listeners.get(ev?.type)||[]) try{cb.call(this,ev)}catch{} return true; },
};

const locationObj = {
  href: baseHref,
  search: '?q=rust+async+tokio&hl=en&gl=us',
  protocol:'https:', hostname:'www.google.com', host:'www.google.com', pathname:'/search',
  replace(v){ replacedUrl=String(v); this.href=replacedUrl; console.error('REPLACE',new URL(replacedUrl,baseHref).origin); },
  assign(v){ replacedUrl=String(v); this.href=replacedUrl; console.error('ASSIGN',new URL(replacedUrl,baseHref).origin); },
  toString(){ return this.href; }
};

const documentListeners = new Map();
const document = {
  readyState:'complete', hidden:false, visibilityState:'visible',
  referrer:'', URL:baseHref, location:locationObj,
  documentElement:{clientWidth:1365,clientHeight:768},
  body:{clientWidth:1365,clientHeight:768,appendChild(){},removeChild(){}},
  get cookie(){ return cookieValue; },
  set cookie(v){ cookieValue = cookieValue ? cookieValue+'; '+String(v) : String(v); console.error('COOKIE_SET',String(v).length); },
  addEventListener(type,cb){ note('document.addEventListener:'+type); (documentListeners.get(type)||documentListeners.set(type,[]).get(type)).push(cb); },
  removeEventListener(type,cb){ note('document.removeEventListener:'+type); },
  dispatchEvent(ev){ for(const cb of documentListeners.get(ev?.type)||[]) try{cb.call(this,ev)}catch{} return true; },
  createEvent(type){ return {type,initEvent(t){this.type=t},initCustomEvent(t){this.type=t}}; },
  createElement(tag){
    note('document.createElement:'+tag);
    const el={
      tagName:String(tag).toUpperCase(), style:{}, classList:{contains(){return false},add(){},remove(){}},
      appendChild(){},removeChild(){},remove(){},setAttribute(k,v){this[k]=v},getAttribute(k){return this[k]??null},
      addEventListener(){},removeEventListener(){},dispatchEvent(){return true},
      getContext(){return null;},
    };
    if (tag === 'a') {
      let h=''; Object.defineProperty(el,'href',{get(){return h},set(v){h=String(v)}});
    }
    return el;
  },
  getElementsByTagName(){return[]}, querySelector(){return null}, querySelectorAll(){return[]},
};

const navBase={
  userAgent:configuredUa,
  platform:configuredPlatform, language:'en-US', languages:['en-US','en'], hardwareConcurrency:configuredHc, deviceMemory:configuredMemory,
  cookieEnabled:true,onLine:true,webdriver:false,maxTouchPoints:0,plugins:[],mimeTypes:[],
  sendBeacon(url){ beaconUrls.push(String(url)); console.error('BEACON',String(url).slice(0,300)); return true; },
};
const navigator = new Proxy(navBase,{get(t,p,r){note('navigator.'+String(p));return Reflect.get(t,p,r)},has(t,p){note('navigator.has:'+String(p));return Reflect.has(t,p)}});

const storage = new Map();
const mkStorage = name => ({
  getItem(k){note(name+'.getItem');return storage.get(name+':'+k)??null},
  setItem(k,v){note(name+'.setItem');storage.set(name+':'+k,String(v))},
  removeItem(k){storage.delete(name+':'+k)},clear(){},
});

function Image(){ Object.defineProperty(this,'src',{set(v){note('Image.src');}}); }

const google={
  timers:{load:{e:{},t:{start:Date.now()},m:{},sgls:-1}},
  c:{e(){},},
  tick(){},
  log(){},
  sn:'web',
  kEI:eid,
};

const ctx={
  console, performance, navigator, document, location:locationObj,
  screen:{width:1365,height:768,availWidth:1365,availHeight:728,colorDepth:24,pixelDepth:24},
  innerWidth:1365,innerHeight:768,outerWidth:1365,outerHeight:768,devicePixelRatio:1,
  localStorage:mkStorage('localStorage'),sessionStorage:mkStorage('sessionStorage'),
  setTimeout,clearTimeout,setInterval,clearInterval,setImmediate,clearImmediate,queueMicrotask,
  requestIdleCallback:cb=>setTimeout(()=>cb({didTimeout:false,timeRemaining:()=>50}),0),
  cancelIdleCallback:clearTimeout,
  TextEncoder,TextDecoder,Uint8Array,Uint16Array,Uint32Array,Int8Array,Int16Array,Int32Array,ArrayBuffer,DataView,Blob,
  URL,URLSearchParams,Promise,Map,Set,WeakMap,WeakSet,Symbol,Reflect,Proxy,
  Date,Math,JSON,RegExp,Error,TypeError,Object,Array,String,Number,Boolean,
  parseInt,parseFloat,isNaN,encodeURIComponent,decodeURIComponent,encodeURI,decodeURI,
  atob:s=>Buffer.from(s,'base64').toString('binary'),
  btoa:s=>Buffer.from(s,'binary').toString('base64'),
  crypto:require('crypto').webcrypto,
  trustedTypes:undefined,Image,Event,CustomEvent,XMLHttpRequest:function(){note('XMLHttpRequest')},
  google,
  ...eventTarget,
};
ctx.window=ctx;ctx.self=ctx;ctx.globalThis=ctx;ctx.global=ctx;ctx.top=ctx;ctx.parent=ctx;
ctx.getComputedStyle=()=>({});

if (dynamicDir) {
  ctx.__knitsail_capture_eval_arg = value => {
    if (dynamicCodeEvents.length >= dynamicMaxEvents) {
      dynamicTruncated = true;
      pendingEval.push(null);
      return value;
    }
    const isString = typeof value === 'string';
    const sha256 = isString ? createHash('sha256').update(value).digest('hex') : null;
    const index = dynamicCodeEvents.length;
    dynamicCodeEvents.push({
      index, type:typeof value, length:isString ? value.length : null,
      sha256, outcome:null
    });
    pendingEval.push(index);
    if (isString) {
      const filename = require('node:path').join(dynamicDir, 'eval-' + sha256 + '.js');
      if (!fs.existsSync(filename)) fs.writeFileSync(filename, value);
    }
    return value;
  };
  ctx.__knitsail_capture_eval_result = value => {
    const index = pendingEval.pop();
    if (index !== null && index !== undefined) {
      dynamicCodeEvents[index].outcome = 'return';
      dynamicCodeEvents[index].resultType = typeof value;
    }
    return value;
  };
  ctx.__knitsail_capture_eval_throw = error => {
    const index = pendingEval.pop();
    if (index !== null && index !== undefined) {
      dynamicCodeEvents[index].outcome = 'throw';
      dynamicCodeEvents[index].thrownType = typeof error;
    }
    return error;
  };
}
vm.createContext(ctx);
const entryCalls = [];
const outerCalls = [];
let currentOuterFirst;
let fatal=null;
try {
  vm.runInContext(runtimeVmScript,ctx,{filename:'live-knitsail-vm.js',timeout:10000});
  console.error('VM_LOADED',Object.keys(ctx.knitsail||{}));
  const {createHash} = require('node:crypto');
  const sha256 = value => createHash('sha256').update(value).digest('hex');

  const originalA = ctx.knitsail.a;
  if (typeof originalA !== 'function') throw Error('Missing knitsail.a');
  ctx.knitsail.a = function(...args) {
    currentOuterFirst = args[0];
    outerCalls.push({
      argument_count: args.length,
      first_type: typeof args[0],
      first_length: args[0]?.length ?? null,
      dispatch_prefix: typeof args[0] === 'string' ? args[0].slice(0, 3) : null,
    });
    return Reflect.apply(originalA, this, args);
  };

  // Mirrors the real dispatch: AV[Q.substring(0,3) + '_'](Q.substring(3),...).
  const entryName = payloadPrefix + '_';
  const originalEntry = ctx.knitsail[entryName];
  if (typeof originalEntry !== 'function') throw Error('Missing dispatch target: '+entryName);
  ctx.knitsail[entryName] = function(...args) {
    const H = args[0];
    const event = {
      function: entryName,
      call_index: entryCalls.length,
      argument_count: args.length,
      first_type: typeof H,
      first_length: H?.length ?? null,
      first_sha256: typeof H === 'string' ? sha256(H) : null,
      equals_a_first_slice_3: typeof H === 'string' && H === currentOuterFirst?.slice(3),
      short_input_branch: H?.length < 2,
      remaining_types: args.slice(1).map(a => Array.isArray(a) ? 'array' : typeof a),
    };
    entryCalls.push(event);
    if (process.env.KNITSAIL_CAPTURE_H_PATH) {
      fs.writeFileSync(process.env.KNITSAIL_CAPTURE_H_PATH, JSON.stringify({value: H}) + '\n');
    }
    console.error('API_CALL_WITNESS ' + JSON.stringify(event));
    return Reflect.apply(originalEntry, this, args);
  };

  vm.runInContext(wrapper,ctx,{filename:'live-knitsail-wrapper.js',timeout:10000});
} catch(e) {
  fatal=e; console.error('FATAL',e && e.stack || e);
}

setTimeout(()=>{
  const sgCookie=(cookieValue.match(/(?:^|;\s*)SG_SS=([^;]+)/)||[])[1]||null;
  const sgUrl=replacedUrl ? (new URL(replacedUrl,baseHref).searchParams.get('sg_ss')) : null;
  const value=sgCookie||sgUrl;
  console.log(JSON.stringify({
    ok:!!value,fatal:fatal?String(fatal):null,htmlSha256,vmSha256,
    source:value?(sgCookie?'cookie':'url'):null,
    valueLength:value?value.length:null,
    startsStar:value?decodeURIComponent(value).startsWith('*'):false,
    entryCalls, outerCalls, dynamicEvalSite, dynamicCodeEvents, dynamicTruncated,
    // Redact challenge token, query/session IDs and request effects from report.
    cookiePresent:!!cookieValue,requestChanged:!!replacedUrl,beaconCount:beaconUrls.length,accesses
  },null,2));
},Number(process.env.KS_DELAY_MS || 250));
