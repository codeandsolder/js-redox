function dispatch(selector, left, right) {
    if (selector === 0) return left + right;
    if (selector === 1) return left ^ right;
    if (selector === 2) return left * right;
    if (selector === 3) return left | right;
    if (selector === 4) return left & right;
    if (selector === 5) return left << right;
    if (selector === 6) return left >>> right;
    if (selector === 7) return left - right;
    return 99;
}

console.log(dispatch(0, 2, 3), dispatch(4, 7, 3));
