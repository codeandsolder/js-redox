(function () {
    var alias = 42;
    function dispatch(selector, left, right) {
        if (selector === 0) return left + right;
        if (selector === 2) return left * right;
        if (selector === alias) return left - right;
        if (selector !== 7) {
            if (selector === 1) return left ^ right;
            if (selector === 3) return left | right;
        }
        return selector === 4 ? left & right : selector === 5 ? left << right : 99;
    }

    var sideEffects = 0;
    function bump(value) {
        sideEffects += 1;
        return value;
    }

    console.log(
        dispatch(0, bump(2), bump(3)),
        sideEffects,
        dispatch(2, 4, 5),
        dispatch(1, 6, 3),
        dispatch(3, 4, 1),
        dispatch(4, 7, 3),
        dispatch(5, 2, 3),
        dispatch(7, 9, 8),
        dispatch(42, 9, 4)
    );

    function ambiguous(selector, value) {
        if (selector === overlap) return value + 1;
        if (selector === 1) return value + 2;
        return value + 3;
    }
    console.log(ambiguous(1, 4));
    var overlap = 1;
    console.log(ambiguous(1, 4));
})();
