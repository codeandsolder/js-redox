
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
