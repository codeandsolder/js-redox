import fs from 'node:fs';
import path from 'node:path';
const root = path.resolve(import.meta.dirname, '..');
for (const variant of ['raw', 'recovered']) {
  const input = path.join(root, 'inputs', variant + '-208.js');
  const output = path.join(root, 'inputs', variant + '-208-warm.js');
  const body = fs.readFileSync(input, 'utf8');
  const anchor = 'const outputs=[';
  if (!body.includes(anchor)) throw new Error('Fixture anchor not found');
  const warm = 'for (let i = 0; i < 1600; i++) execute("warm", [[0,3],[2,5],[1,1],[0,1],[2,2]]);\n';
  fs.writeFileSync(output, body.replace(anchor, warm + anchor));
}
