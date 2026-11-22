(function () {
  function p() {
    const values = ["first", "one"];
    p = function () {
      return values;
    };
    return p();
  }
  function d(i) {
    i = i - 10;
    const values = p();
    let value = values[i];
    return value;
  }
  console.log(d(10));
})();

(function () {
  function p() {
    const values = ["second", "two"];
    p = function () {
      return values;
    };
    return p();
  }
  function d(i) {
    i = i - 20;
    const values = p();
    let value = values[i];
    return value;
  }
  console.log(d(20));
})();
