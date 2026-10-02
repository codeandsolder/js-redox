function a0(t, n) {
    return -4 * (n & t) - 8 * (n & ~t) + 4 * n + 5 * ~(n & t) - 5 * ~(n | t) - 6 * ~(n | ~t);
}

function b1(t, n) {
    return 13 * (t & n) + 11 * (t & ~n) - 11 * t - ~(t & ~n) + ~(t | n) + 2 * ~(t | ~n);
}

function c2(t, n) {
    return 7 * (t & n) + 6 * (t & ~n) + (t ^ n) - 6 * t - ~(t | ~n);
}

function d3(t, n) {
    return 3 * (n & t) + 2 * (n & ~t) - ~(n & ~n) + 12 * ~(n | t) + 13 * ~(n | ~t) - 11 * ~n;
}

console.log(a0(1, 2), b1(3, 4), c2(5, 6), d3(7, 8));
