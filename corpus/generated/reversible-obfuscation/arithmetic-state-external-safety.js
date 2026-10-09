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
  // The terminal state is observable, so the loop cannot be replaced unless
  // the replacement also preserves that state mutation.
  return out + ":" + state;
}
console.log(run());
