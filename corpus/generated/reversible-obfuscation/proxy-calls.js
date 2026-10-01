const proxy = {
  invoke2: function(fn, a, b) {
    return fn(a, b);
  },
  invoke0: function(fn) {
    return fn();
  }
};

const arrowProxy = {
  invoke1: (fn, value) => fn(value),
  equal: (a, b) => a === b
};

function add(a, b) {
  return a + b;
}

const holder = {
  marker: "holder",
  method: function() {
    return this === holder ? "bound" : "detached";
  }
};

console.log(proxy.invoke2(add, 20, 22));
console.log(proxy.invoke0(holder.method));
console.log(arrowProxy.invoke1(x => x * 3, 14));
console.log(arrowProxy.equal(6, 6));
