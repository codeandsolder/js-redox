function run() {
  var state = 2;
  var out = "";
  for (; state !== 4;) {
    switch (state) {
      case 2:
        try {
          state = 3;
          out += "A";
        } finally {
          out += "F";
        }
        break;
      case 3:
        out += "B";
        state = 4;
        break;
    }
  }
  return out;
}
console.log(run());
