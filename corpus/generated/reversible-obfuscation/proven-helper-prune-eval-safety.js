(function () {
    function hiddenHelper(t, n) {
        return -4 * (n & t) - 8 * (n & ~t) + 4 * n + 5 * ~(n & t) - 5 * ~(n | t) - 6 * ~(n | ~t);
    }

    console.log(eval("hiddenHelper")(3, 5));
})();
