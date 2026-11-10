// Two functions with identical semantics; the first uses an artificial numeric state loop.
function flattened(input) {
  let state = 87;
  let result = 0;
  while (state !== 14) {
    if (state === 87) {
      result = input + 1;
      state = 71;
    } else if (state === 71) {
      result = result * 2;
      state = 14;
    } else {
      throw Error("bad state " + state);
    }
  }
  return result;
}

function structured(input) {
  const result = input + 1;
  return result * 2;
}

let checksum1 = 0;
let checksum2 = 0;
for (let i = 0; i < 1600; i++) {
  checksum1 += flattened(i);
  checksum2 += structured(i);
}
console.log('CHECK:' + checksum1 + '/' + checksum2);
