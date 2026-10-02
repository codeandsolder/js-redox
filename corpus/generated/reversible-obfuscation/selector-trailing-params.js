(function () {
    var sideEffects = 0;

    function bump(value) {
        sideEffects += 1;
        return value;
    }

    function dispatch(selector, left, p2, p3, p4, p5, p6, p7, p8, p9) {
        if (selector === 7) return left | 0;
        if (selector === 8) return p8 + 1;
        if (selector === 9) return p9 + 1;
        if (selector === 10) return left ^ p2;
        return -1;
    }

    console.log(
        dispatch(7, 42, 2, 3, 4, 5, 6, 7, 8, bump(9)),
        sideEffects,
        dispatch(8, 1, 2, 3, 4, 5, 6, 7, 11, bump(12)),
        sideEffects
    );
})();
