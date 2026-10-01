function run(flag) {
  let out = "";
  for (var state = 1; void 0 !== state;) {
    var low = 3 & state;
    switch (low) {
      case 0:
        out += "B";
        state = void 0;
        break;
      case 1:
        out += "A";
        state = flag ? 0 : 2;
        break;
      case 2:
        out += "C";
        state = void 0;
        break;
    }
  }
  return out;
}
console.log(run(true), run(false));
