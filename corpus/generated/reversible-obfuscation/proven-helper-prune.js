(function () {
    function pruneMe(t, n) {
        return -4 * (n & t) - 8 * (n & ~t) + 4 * n + 5 * ~(n & t) - 5 * ~(n | t) - 6 * ~(n | ~t);
    }

    function keepMe(t, n) {
        return 13 * (t & n) + 11 * (t & ~n) - 11 * t - ~(t & ~n) + ~(t | n) + 2 * ~(t | ~n);
    }

    const dynamic = Number(process.env.JSVM_PRUNE_PROBE ?? "7");
    console.log(pruneMe(3, 5), keepMe(dynamic, 11));
})();
