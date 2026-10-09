function run(a, b) {
  var state = 2;
  var out = "";
  for (; state !== 11;) {
    switch (state) {
      case 2:
        state = a ? 3 : 5;
        break;
      case 3:
        state = b ? 7 : 9;
        break;
      case 5:
        out += "F";
        state = 11;
        break;
      case 7:
        out += "T";
        state = 11;
        break;
      case 9:
        out += "t";
        state = 11;
        break;
    }
  }
  return out;
}
console.log(run(true, true), run(true, false), run(false, true));
