function run() {
  var state = 2;
  var out = "";
  for (; state !== 4;) {
    switch (state) {
      case 2:
        var regs = [];
        regs[1] = "A";
        var mutate = function () {
          regs[1] = "B";
        };
        state = 3;
        break;
      case 3:
        mutate();
        out = regs[1];
        state = 4;
        break;
    }
  }
  return out;
}
console.log(run());

function runShadow() {
  var state = 2;
  var out = "";
  for (; state !== 4;) {
    switch (state) {
      case 2:
        var regs = [];
        regs[1] = "A";
        var escaped = regs;
        function nested() {
          var regs = [];
          regs[1] = "nested";
          return regs[1];
        }
        void nested;
        state = 3;
        break;
      case 3:
        escaped[1] = "B";
        out = regs[1];
        state = 4;
        break;
    }
  }
  return out;
}
console.log(runShadow());
