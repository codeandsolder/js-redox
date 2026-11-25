"use strict";
let out = "";
for (let state = 6; void 0 !== state;) {
  let low = 7 & state, shifted = state >> 3, high = 7 & shifted;
  switch (low) {
    case 0:
      !function() {
        switch (high) {
          case 0:
            out += "D";
            state = void 0;
            break;
          case 2:
            out += "C";
            state = 0;
            break;
        }
      }();
      break;
    case 1:
      out += "B";
      state = 16;
      break;
    case 6:
      out += "A";
      state = 1;
      break;
  }
}
console.log(out);
