// Minimal regression: with ZIPP_OPT=1 ZIPP_NO_OPT_TIER_UP=1, debug Tier O panics
// in codegen/opt/build.rs at debug_assert!(preds.is_empty(), "the entry has no predecessor").
function f(n) {
  while (n > 0) n--;
  return n;
}

let sum = 0;
for (let i = 0; i < 1600; i++) sum += f(3);
console.log('RESULT:' + sum);
