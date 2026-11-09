
// Pure allocated literals are truthy and cannot invoke user code.
function inertGuard() {
    let counter = 0;
    const seen = [];
    while (!["", null, 1, false, [2], {}, /x/, void 0] == 0) {
        seen.push(++counter);
        if (counter === 2) break;
    }
    return seen;
}
// Array elements still execute on every loop test.
function effectfulGuard() {
    const seen = [];
    let index = 0;
    while (![seen.push("test"), ++index] == 0) {
        seen.push("body");
        if (index === 2) break;
    }
    return seen;
}
function spreadGuard() {
    const seen = [];
    const iterable = {
        [Symbol.iterator]() {
            seen.push("iterator");
            return [1][Symbol.iterator]();
        }
    };
    let index = 0;
    while (![...iterable] == 0) {
        seen.push(++index);
        if (index === 2) break;
    }
    return seen;
}
function tdzGuard() {
    try {
        while (![later] == 0) { break; }
    } catch (error) {
        return error.name;
    }
    let later = "ready";
    return later;
}
console.log(JSON.stringify([inertGuard(), effectfulGuard(), spreadGuard(), tdzGuard()]));
