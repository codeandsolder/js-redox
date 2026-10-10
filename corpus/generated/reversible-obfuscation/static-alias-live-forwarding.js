const fakeRoot = {
  Array: function FakeArray() {},
  Object,
};

fakeRoot.Array.prototype.push = function push() {
  return "push";
};

function getArray(root) {
  return root.Array;
}

function helper(root, resolver, source, selector, alias) {
  var r = [arguments];
  var owner;
  owner = (1, r[0][1])(r[0][0]);
  var target;
  target = [owner, owner.prototype][r[0][3]];
  if (target.hasOwnProperty(r[0][4]) && target[r[0][4]] === target[r[0][2]]) {
    return;
  }
  target[r[0][4]] = target[r[0][2]];
  var descriptor = {};
  descriptor.set = function(value) {
    target[r[0][2]] = value;
  };
  descriptor.get = function() {
    return typeof target[r[0][2]] == "undefined" ? undefined : target[r[0][2]];
  };
  var method;
  method = "define";
  method += "Property";
  r[0][0].Object[method](target, r[0][4], descriptor);
}

var install = function(resolver, source, selector, alias) {
  var q = [arguments];
  helper(fakeRoot, q[0][0], q[0][1], q[0][2], q[0][3]);
};

// The real installer can early-return when an equal own alias already exists.
// That proves the helper's forwarding path without proving this invocation installs it.
fakeRoot.Array.prototype.f2AA = fakeRoot.Array.prototype.push;
install(getArray, "push", 1, "f2AA");
const preservedDataAlias = fakeRoot.Array.prototype.f2AA;
fakeRoot.Array.prototype.push = function replacementPush() {
  return "replacement";
};
console.log(
  fakeRoot.Array.prototype.f2AA === preservedDataAlias,
  fakeRoot.Array.prototype.f2AA !== fakeRoot.Array.prototype.push,
);
