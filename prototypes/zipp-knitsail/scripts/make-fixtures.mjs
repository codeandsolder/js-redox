import fs from 'node:fs';
import crypto from 'node:crypto';
import path from 'node:path';

const work = path.resolve(import.meta.dirname, '..');
const originalPath = process.env.KNITSAIL_ORIGINAL ?? '/home/jan/projects/js-redox/work/knitsail-devirt-20261105/embedded/embedded-4148a06d2aa37711.js';
const recoveredPath = process.env.KNITSAIL_RECOVERED ?? '/home/jan/projects/js-redox-readable-20261105/work/reconstruction-20261105/exception-sensitive-dispatch-20261109/knitsail-scc-c555f75-source-tree/key-208.js';
const original = fs.readFileSync(originalPath);
const sha = crypto.createHash('sha256').update(original).digest('hex');
const expected = 'd016538d95a679e1604c8e6f4c1fa5d78ff3d729eace6c832e54a10b550b4a98';
if (sha !== expected) throw new Error('Source identity mismatch: ' + sha);
const functionBody = original.subarray(28591, 29605).toString('utf8');
const recovered = fs.readFileSync(recoveredPath, 'utf8');
if (!functionBody.startsWith('function(P,K,c,a,k,') || !functionBody.endsWith('}')) throw new Error('Raw span mismatch');
if (!recovered.includes('const capturedHandler = function(')) throw new Error('Recovered source mismatch');
const prelude = `
const T = 'push', JM = 'length', r = 'toString', YX = 0;
const E = {origin: 'Knitsail'}, m = {}, u = {};
const events = [];
let report;
function O(source, code) {
  events.push(['O', code]);
  switch(code) {
    case 24: return {ctx:'Knitsail'};
    case 16: return 42;
    case 9: return {computed: source};
    case 13: return {decoded: source};
    case 26: return 137;
    default: throw new Error('unexpected O code '+code);
  }
}
function t(_e, seed) { events.push(['t', seed]); return function() { events.push(['token']); return seed + 1; }; }
function V(_m, code) { events.push(['V', code]); return 41; }
function AM(P) { const b = P.bytes[P.offset++]; events.push(['AM', b ?? null]); if (b === undefined) throw new Error('exhausted input'); return b; }
function y(_c, code, _p, fn) { events.push(['y',code]); const target = {}; fn(target); report = target; }
function pack(fields) {
  const bits=[];
  for (const [value, width] of fields) for(let i=0;i<width;i++) bits.push((value >> i) & 1);
  const bytes = Array.from({length:Math.ceil(bits.length/8)},(_,j)=>Array.from({length:8},(_,b)=>bits[j*8+b]??0).reduce((v,bit,i)=>v|(bit<<i),0));
  return {bytes,offset:0};
}
function execute(label, fields) {
  events.length=0; m.D=undefined; report=undefined;
  const P=pack(fields);
  capturedHandler(P);
  return {label, bytes:P.bytes, readBytes:P.offset, report, decoded:m.D, events:events.slice()};
}
`;
const tail = `
const outputs=[
  execute('one-literal-one-reference', [[0,3],[2,5],[1,1],[0,1],[2,2]]),
  execute('two-references-one-literal', [[1,3],[3,5],[0,1],[1,1],[0,1],[0,1],[1,1]]),
];
console.log('RESULT:'+JSON.stringify(outputs));
`;
for (const [name, impl] of [
  ['raw-208.js', 'const capturedHandler = (' + functionBody + ');\n'],
  ['recovered-208.js', recovered + '\n'],
]) {
  fs.writeFileSync(path.join(work,'inputs',name), prelude+'\n'+impl+'\n'+tail);
}
fs.writeFileSync(path.join(work,'inputs','manifest.json'),JSON.stringify({source_sha256:sha,raw_span:[28591,29605],raw_function_bytes:Buffer.byteLength(functionBody),recovered_source_bytes:Buffer.byteLength(recovered),fixture:'Knitsail handler 208'},null,2)+'\n');
console.log('Generated exact-origin Knitsail handler 208 fixtures:', sha, functionBody.length, recovered.length);
