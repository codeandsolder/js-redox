// Catch-resume transitions must remain reachable even if no normal
// transition enters the recovery state. Unreachable cases can be removed
// without moving state effects across try/catch or a loop condition.
function recover(mode, log) {
    let state = 1;
    let recovery = 0;
    while (true) try {
        if (state == 99) {
            log.push("UNREACHABLE");
            return "dead";
        } else if (state == 1) {
            log.push("start");
            state = mode === "throw" ? 2 : 4;
        } else if (state == 2) {
            recovery = 1;
            log.push("enter-throwing-state");
            throw Error("expected");
        } else if (state == 3) {
            log.push("resumed");
            state = 4;
        } else if (state == 4) {
            log.push("end");
            return log.length;
        }
    } catch (error) {
        log.push("catch", error.message);
        if (recovery == 1) {
            state = 3;
            recovery = 0;
        } else throw error;
    }
}
for (const mode of ["throw", "normal"]) {
    const log = [];
    console.log(JSON.stringify([mode, recover(mode, log), log]));
}

// Dead-case destructuring declarations must still shadow outer bindings.
const shadowed = "outer";
function preservedHoists() {
    let state = 1;
    while (true) try {
        if (state == 99) {
            var {shadowed, spare} = {shadowed: "inner", spare: 42};
            state = 2;
        } else if (state == 1) {
            return [typeof shadowed, typeof spare];
        }
    } catch (error) { throw error; }
}
console.log(JSON.stringify(["hoisted-bindings", preservedHoists()]));
