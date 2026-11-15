function run() {
  var state = 2, out = "";
  for (; state !== 5;) {
    switch (state) {
      case 2:
        var regs = ["ZERO", "ONE"];
        regs[true] = "TRUE";
        regs[false] = "FALSE";
        regs[null] = "NULL";
        regs["01"] = "PADDED";
        regs["1.0"] = "DECIMAL";
        state = 3;
        break;
      case 3:
        out = [regs[0], regs[1], regs[true], regs[false],
          regs[null], regs["01"], regs["1.0"]].join(":");
        state = 5;
        break;
    }
  }
  return out;
}
console.log(run());
