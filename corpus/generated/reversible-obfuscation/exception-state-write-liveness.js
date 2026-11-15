function makeTarget(shouldThrow) {
  return Object.defineProperty({}, "value", {
    get() {
      if (shouldThrow) throw Error("expected");
      return true;
    }
  });
}
function safe(shouldThrow) {
  let state = 1;
  while (true) try {
    if (state === 1) {
      state = 73;
      if (makeTarget(shouldThrow).value) state = 2;
      else state = 3;
    } else if (state === 2) return "safe-yes";
    else if (state === 3) return "safe-no";
  } catch (error) { return "safe-caught"; }
}
function catchReads(shouldThrow) {
  let state = 1;
  while (true) try {
    if (state === 1) {
      state = 73;
      if (makeTarget(shouldThrow).value) state = 2;
      else state = 3;
    } else if (state === 2) return "read-yes";
    else if (state === 3) return "read-no";
  } catch (error) { return "catch-read:" + state; }
}
function catchReplaces(shouldThrow) {
  let state = 1;
  while (true) try {
    if (state === 1) {
      state = 73;
      if (makeTarget(shouldThrow).value) state = 2;
      else state = 3;
    } else if (state === 2) return "replace-yes";
    else if (state === 3) return "replace-no";
    else if (state === 4) return "replace-resumed";
  } catch (error) { state = 4; }
}
function catchImplicitlyRetries(shouldThrow) {
  let state = 1;
  while (true) try {
    if (state === 1) {
      state = 73;
      if (makeTarget(shouldThrow).value) state = 2;
      else state = 3;
    } else if (state === 73) return "implicit-retry-73";
    else if (state === 2) return "implicit-yes";
    else if (state === 3) return "implicit-no";
  } catch (error) { /* resume current state */ }
}
function capturedState() {
  let state = 1;
  let seen = [];
  const observe = () => { seen.push(state); return true; };
  while (true) try {
    if (state === 1) {
      state = 73;
      if (observe()) state = 2;
      else state = 3;
    } else if (state === 2) return seen;
    else if (state === 3) return seen;
  } catch (error) { throw error; }
}
function liveBranch() {
  let state = 1;
  while (true) try {
    if (state === 1) {
      state = 73;
      if (state === 73) state = 2;
      else state = 3;
    } else if (state === 2) return "branch-yes";
    else if (state === 3) return "branch-no";
  } catch (error) { throw error; }
}
function mappedArgument(state) {
  const seen = [];
  while (true) try {
    if (state === 1) {
      state = 73;
      seen.push(arguments[0]);
      state = 2;
    } else if (state === 2) return seen;
  } catch (error) { throw error; }
}
for (const shouldThrow of [false, true]) {
  console.log(safe(shouldThrow), catchReads(shouldThrow),
    catchReplaces(shouldThrow), catchImplicitlyRetries(shouldThrow));
}
console.log(JSON.stringify(capturedState()), liveBranch(), JSON.stringify(mappedArgument(1)));
