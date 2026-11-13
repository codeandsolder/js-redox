import fs from 'node:fs';
import crypto from 'node:crypto';
import path from 'node:path';

const root = path.resolve(import.meta.dirname, '..');
const originalPath = process.env.KNITSAIL_ORIGINAL ??
  '/home/jan/projects/js-redox/work/knitsail-devirt-20261105/embedded/embedded-4148a06d2aa37711.js';
const original = fs.readFileSync(originalPath);
const sha = crypto.createHash('sha256').update(original).digest('hex');
if (sha !== 'd016538d95a679e1604c8e6f4c1fa5d78ff3d729eace6c832e54a10b550b4a98') {
  throw new Error('Unexpected original Knitsail source SHA: ' + sha);
}
const body = original.subarray(27625, 27860).toString('utf8');
if (!body.startsWith('function(P,K,c,a,k,D,A,h,e){for(e=44;') || !body.endsWith('}')) {
  throw new Error('Handler 164 original byte span changed');
}
const variants = [['normal', 'healthy'], ['short', 'x']];
if (process.env.KNITSAIL_H_INPUT) {
  const captured = JSON.parse(fs.readFileSync(process.env.KNITSAIL_H_INPUT, 'utf8'));
  if (typeof captured.value !== 'string') throw Error('Archived caller H missing or non-string');
  variants.push(['archived', captured.value]);
}
for (const [variant, H] of variants) {
  // This is the actual oU branch predicate, selectively isolated.
  // The surrounding oU DOM/browser initializer is NOT executed here.
  const code = `
const H = ${JSON.stringify(H)};
let T = 'push', JM = 'length';
if (H.length < 2) { T = H; JM = H; }
const E = {}, n = {}, G = {}, writes = [], event = [];
const payload = {byte: 0};
function O(P, n) { event.push(['O',n]); return 24; }
function M(a,b,c) {
  event.push(['M',a,b]);
  if (a === 32 && b === 127) return 2;
  if (a === 36 && b === 127) return event.filter(x=>x[0]==='M' && x[1]===36).length - 1;
  throw Error('unexpected M');
}
function t(P, seed) { event.push(['t',seed]); return [10,20,30]; }
function x(G,D,K) { writes.push([D,K.slice()]); }
const capturedHandler = (${body});
let status = 'ok';
try { capturedHandler(payload); } catch (err) { status = err.name; }
console.log('RESULT:' + JSON.stringify({H_length:H.length,status,writes,event}));
`;
  const file = path.join(root, 'inputs', 'raw-164-' + variant + '.js');
  fs.writeFileSync(file, code);
  const output = (await import('node:child_process')).execFileSync('node', [file], {encoding:'utf8'});
  process.stdout.write(variant + ' ' + output);
}
