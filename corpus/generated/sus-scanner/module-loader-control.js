const modules = {
  101(module, exports) { exports.value = 1; },
  202(module, exports) { exports.value = 2; },
  303(module, exports) { exports.value = 3; },
  404(module, exports) { exports.value = 4; },
};
const cache = {};
function r(id) {
  if (cache[id]) return cache[id].exports;
  const module = cache[id] = { exports: {} };
  modules[id](module, module.exports, r);
  return module.exports;
}
r.d = (exports, definition) => {
  for (const key in definition) {
    if (!Object.prototype.hasOwnProperty.call(exports, key)) {
      Object.defineProperty(exports, key, { enumerable: true, get: definition[key] });
    }
  }
};
r.r = exports => Object.defineProperty(exports, "__esModule", { value: true });
const a = r(101);
const b = r(202);
const c = r(303);
const d = r(404);
globalThis.bundleResult = [a.value, b.value, c.value, d.value];
