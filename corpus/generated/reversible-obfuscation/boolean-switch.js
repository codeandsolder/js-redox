
// Boolean-valued switches are ordinary two-way control flow, but their
// labels, selection order, fallthrough and side effects must remain intact.
function run(value, out) {
    switch (!(value === 3)) {
        case false:
            out.push("equal");
            break;
        case true:
            out.push("not-equal");
            (function(label) { out.push(label); })("callback");
            break;
    }
    switch (!(value === 5)) {
        case true:
            out.push("before-fallthrough");
        case false:
            out.push("after-fallthrough");
            break;
    }
    switch (!(value === 7)) {
        default:
            out.push("default");
            break;
        case false:
            out.push("seven");
            break;
    }
    return out;
}
function selectedOnce(value, out) {
    switch (!(out.push("test"), value === 2)) {
        case true:
            out.push("other");
            break;
        case false:
            out.push("two");
            break;
    }
    return out;
}
for (const value of [2, 3, 5, 7, null]) {
    console.log(JSON.stringify([value, run(value, []), selectedOnce(value, [])]));
}


function dynamicCase(flag, log) {
    switch (!flag) {
        case true:
            log.push("first");
            break;
        case (log.push("evaluated"), true == []):
            log.push("dynamic");
            break;
        case false:
            log.push("fallback");
            break;
    }
    return log;
}
function fallthrough(flag, log) {
    switch (!flag) {
        case true:
            log.push("first");
        case (log.push("skipped-label-on-fallthrough"), true == []):
            log.push("body-after-fallthrough");
            break;
        default:
            log.push("default");
    }
    return log;
}
function dynamicNonBoolean(flag, log) {
    switch (!flag) {
        case false:
            log.push("known");
            break;
        case (log.push("tested"), 17):
            log.push("number");
            break;
        default:
            log.push("default");
    }
    return log;
}
function dynamicLabelsAfterKnown(flag, log) {
    switch (!flag) {
        case true:
            log.push("known");
            break;
        case (log.push("first-test"), "wrong"):
            log.push("wrong");
            break;
        case (log.push("second-test"), false):
            log.push("false");
            break;
        default:
            log.push("default");
    }
    return log;
}
for (const value of [false, true]) {
    for (const f of [dynamicCase, fallthrough, dynamicNonBoolean, dynamicLabelsAfterKnown]) {
        const observed = f(value, []);
        console.log(JSON.stringify([f.name, value, observed]));
    }
}
const originalToString = Array.prototype.toString;
try {
    Array.prototype.toString = function() { return "1"; };
    console.log(JSON.stringify(["monkeypatched", dynamicCase(true, [])]));
} finally {
    Array.prototype.toString = originalToString;
}


function knownEffectful(flag, log) {
    switch (!(flag === 1)) {
        case 0 == ![log.push("array-element")]:
            log.push("known-true");
            break;
        case false:
            log.push("known-false");
            break;
    }
    return log;
}
function knownWithDefault(flag, log) {
    switch (!flag) {
        default:
            log.push("default");
            break;
        case (log.push("before-array"), 0 == ![log.push("in-array")]):
            log.push("true");
            break;
        case false:
            log.push("false");
            break;
    }
    return log;
}
function knownWithSpread(flag, log, throwOnIteration) {
    const iterable = { [Symbol.iterator]() {
        log.push("iterator");
        if (throwOnIteration) { throw Error("iterator failed"); }
        return [1, 2][Symbol.iterator]();
    } };
    try {
        switch (!flag) {
            case 0 == ![...iterable]:
                log.push("known");
                break;
            case false:
                log.push("other");
                break;
        }
    } catch (e) {
        log.push(e.message);
    }
    return log;
}
for (const value of [false, true]) {
    console.log(JSON.stringify(["knownEffectful", value, knownEffectful(value, [])]));
    console.log(JSON.stringify(["knownWithDefault", value, knownWithDefault(value, [])]));
    for (const throwOnIteration of [false, true]) {
        console.log(JSON.stringify(["knownWithSpread", value, throwOnIteration, knownWithSpread(value, [], throwOnIteration)]));
    }
}


function signedZeroCase(flag, events) {
    switch (!flag) {
        case 1 / (flag ? 0 : -0) === 1 / 0:
            events.push("positive");
            break;
        case false:
            events.push("false");
            break;
    }
    return events;
}
for (const flag of [false, true]) {
    console.log(JSON.stringify(["signed-zero", flag, signedZeroCase(flag, [])]));
}
