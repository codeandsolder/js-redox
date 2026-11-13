let coercions = 0;
const obj = {answer: 41, tick(x) { return this.answer + x; }};
const key = {toString() { coercions++; return 'answer'; }};
const k2 = {toString() { coercions++; return 'tick'; }};
const a = obj[key];
obj[key] = a + 1;
const b = obj[k2](1);
console.log('RESULT:' + JSON.stringify({a,b,coercions,answer:obj.answer}));
