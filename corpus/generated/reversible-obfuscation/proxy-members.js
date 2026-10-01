var helpers = {
  get: function (obj) {
    return obj.value;
  },
  at: function (obj, key) {
    return obj[key];
  },
  arrowGet: (obj) => obj.value,
  arrowAt: (obj, key) => obj[key]
};

var argCalls = 0;
var getterCalls = 0;
var target = {
  get value() {
    getterCalls += 1;
    return 9;
  },
  a: 5
};

function makeTarget() {
  argCalls += 1;
  return target;
}

function makeKey() {
  argCalls += 1;
  return "a";
}

console.log(
  helpers.get(makeTarget()),
  helpers.at(makeTarget(), makeKey()),
  helpers.arrowGet(makeTarget()),
  helpers.arrowAt(makeTarget(), makeKey()),
  argCalls,
  getterCalls
);
