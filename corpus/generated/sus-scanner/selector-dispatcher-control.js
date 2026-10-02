function choose(mode, value) {
    if (mode === 0) return value + 1;
    if (mode === 1) return value - 1;
    return value;
}

function compactDispatcher(mode, value) {
    if (mode === 0) return value + 1;
    if (mode === 1) return value - 1;
    if (mode === 2) return value * 2;
    if (mode === 3) return value / 2;
    if (mode === 4) return value | 0;
    if (mode === 5) return value >>> 0;
    return value;
}

function readableSwitch(mode, value) {
    switch (mode) {
        case 0:
            return value + 1;
        case 1:
            return value - 1;
        case 2:
            return value * 2;
        case 3:
            return value / 2;
        default:
            return value;
    }
}

console.log(choose(0, 4), compactDispatcher(3, 8), readableSwitch(2, 5));
