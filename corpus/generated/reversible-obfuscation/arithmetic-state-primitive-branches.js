function runString(flag) {
  var state = 2;
  var out = "";
  for (; state !== 9;) {
    switch (state) {
      case 2:
        out += "A";
        state = flag ? "3" : 5;
        break;
      case 3:
        out += "WRONG_NUMBER";
        state = 9;
        break;
      case "3":
        out += "STRING";
        state = 9;
        break;
      case 5:
        out += "F";
        state = 9;
        break;
    }
  }
  return out;
}

function runBoolean(flag) {
  var state = 2;
  var out = "";
  for (; state !== 9;) {
    switch (state) {
      case 2:
        out += "A";
        state = flag ? true : 5;
        break;
      case 1:
        out += "WRONG_NUMBER";
        state = 9;
        break;
      case true:
        out += "BOOLEAN";
        state = 9;
        break;
      case 5:
        out += "F";
        state = 9;
        break;
    }
  }
  return out;
}

function runNull(flag) {
  var state = 2;
  var out = "";
  for (; state !== 9;) {
    switch (state) {
      case 2:
        out += "A";
        state = flag ? null : 5;
        break;
      case 0:
        out += "WRONG_NUMBER";
        state = 9;
        break;
      case null:
        out += "NULL";
        state = 9;
        break;
      case 5:
        out += "F";
        state = 9;
        break;
    }
  }
  return out;
}

function runUndefined(flag) {
  var state = 2;
  var out = "";
  for (; state !== 9;) {
    switch (state) {
      case 2:
        out += "A";
        state = flag ? void 0 : 5;
        break;
      case 0:
        out += "WRONG_NUMBER";
        state = 9;
        break;
      case 5:
        out += "F";
        state = 9;
        break;
      default:
        out += "DEFAULT";
        state = 9;
        break;
    }
  }
  return out;
}

function runDirectUndefined() {
  var state = 2;
  var out = "";
  for (; state !== 9;) {
    switch (state) {
      case 2:
        out += "A";
        state = void 0;
        break;
      default:
        out += "DIRECT";
        state = 9;
        break;
    }
  }
  return out;
}

console.log(
  runString(true), runString(false),
  runBoolean(true), runBoolean(false),
  runNull(true), runNull(false),
  runUndefined(true), runUndefined(false),
  runDirectUndefined(),
);
