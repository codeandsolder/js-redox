var calls = 0;
function choose(flag) {
  calls++;
  return flag;
}

function run(flag) {
  var state = 2;
  var out = "";
  for (; state !== 9;) {
    switch (state) {
      case 2:
        out += "A";
        state = choose(flag) ? 3 : 5;
        break;
      case 3:
        out += "T";
        state = 9;
        break;
      case 5:
        out += "F";
        state = 7;
        break;
      case 7:
        out += "!";
        state = 9;
        break;
    }
  }
  return out;
}
console.log(run(true), run(false), calls);
