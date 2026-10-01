function p() {
  var table = ["first", "second"];
  p = function () {
    return table;
  };
  return p();
}

function d(index) {
  index = index - 10;
  const table = p();
  let value = table[index];
  return value;
}

let alias = d;
alias = function () {
  return "rebound";
};

console.log(alias(10));
