function run(value) {
  let out = "";
  for (var state = 2; void 0 !== state;) {
    var low = 3 & state, high = 3 & (state >> 2);
    switch (low) {
      case 0:
        !function() {
          switch (high) {
            case 0:
              flag = value === 0;
              state = 1;
              break;
          }
        }();
        break;
      case 1:
        state = flag ? 3 : void 0;
        break;
      case 2:
        var flag = false;
        state = 0;
        break;
      case 3:
        out = "zero";
        state = void 0;
        break;
    }
  }
  return out;
}
console.log(run(0), run(1));
