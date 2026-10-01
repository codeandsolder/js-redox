var helpers = {
  text: "visible",
  answer: 40 + 2,
  yes: !0,
  nothing: null,
  missing: void 0,
  not: function (value) { return !value; },
  neg: function (value) { return -value; },
  bitnot: function (value) { return ~value; },
  discard: function (value) { return void value; }
};

var sideEffects = 0;
function bump() {
  sideEffects += 1;
  return 7;
}

console.log(
  helpers.text,
  helpers.answer,
  helpers["yes"],
  helpers.nothing,
  helpers.missing,
  helpers.not(0),
  helpers.neg(3),
  helpers.bitnot(1),
  helpers.discard(bump()),
  sideEffects
);
