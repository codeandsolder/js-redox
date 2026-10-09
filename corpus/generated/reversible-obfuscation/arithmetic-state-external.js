function run() {
  var state = 2;
  var out = "";
  for (; state !== 5;) {
    switch (state) {
      case 2:
        out += "A";
        state = 4;
        break;
      case 4:
        out += "B";
        state = 5;
        break;
    }
  }
  return out;
}
console.log(run());
