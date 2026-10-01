const aliased = {
  text: "must-stay",
  less: function(a, b) { return a < b; },
  invoke: function(fn, value) { return fn(value); }
};
const alias = aliased;
console.log(alias.text, alias.less(1, 2), alias.invoke(x => x + 1, 4));

const mutated = {
  text: "before",
  less: function(a, b) { return a < b; },
  invoke: function(fn, value) { return fn(value); }
};
mutated.text = "after";
console.log(mutated.text, mutated.less(2, 3), mutated.invoke(x => x * 2, 5));
