function sideEffect() {
  globalThis.orderedSwitchSafety = (globalThis.orderedSwitchSafety || 0) + 1;
  return 0;
}

const out = [];
for (var order = "0|1".split("|"), index = 0, extra = sideEffect(); 1;) {
  switch (order[index++]) {
    case "0":
      out.push("A");
      continue;
    case "1":
      out.push("B");
      continue;
  }
  break;
}
void extra;
console.log(out.join(""));
