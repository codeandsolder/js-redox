function hashStep(left, right) {
    return (left ^ right) >>> 0;
}

function average(left, right) {
    return (left + right) / 2;
}

console.log(hashStep(1, 2), average(3, 5));
