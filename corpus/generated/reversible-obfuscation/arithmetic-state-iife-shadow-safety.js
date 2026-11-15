function run(value) {
  var out = "";
  for (var state = 2; state !== 9;) {
    switch (state) {
      case 2: state = 0; break;
      case 0:
        !function() { var state = 1; out += value ? "T" : "F"; }();
        state = 1;
        break;
      case 1: state = 9; break;
    }
  }
  return out;
}
console.log(run(true), run(false));
