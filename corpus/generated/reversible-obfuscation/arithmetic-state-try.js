function maybeThrow(flag) {
  if (flag) throw new Error("boom");
}

function run(flag) {
  var state = 2;
  var out = "";
  for (; state !== 4;) {
    switch (state) {
      case 2:
        try {
          out += "A";
          maybeThrow(flag);
        } catch (error) {
          out += "C";
        }
        state = 3;
        break;
      case 3:
        out += "B";
        state = 4;
        break;
    }
  }
  return out;
}
console.log(run(false), run(true));
