function install(target, name, flag, alias) {
  return target + ":" + name + ":" + flag + ":" + alias;
}

function run(root) {
  var state = 2;
  var out = "";
  for (; state !== 5;) {
    switch (state) {
      case 2:
        var regs = [arguments];
        regs[1] = "t";
        regs[2] = "2";
        regs[3] = "AA";
        regs[4] = 1;
        var peek = function () {
          return regs[0][0];
        };
        state = 3;
        break;
      case 3:
        regs[5] = regs[1];
        regs[5] += regs[2];
        regs[5] += regs[3];
        state = 4;
        break;
      case 4:
        void peek;
        out = install("RegExp", "test", regs[4], regs[5]);
        state = 5;
        break;
    }
  }
  return out + ":" + (root === globalThis);
}
console.log(run(globalThis));
