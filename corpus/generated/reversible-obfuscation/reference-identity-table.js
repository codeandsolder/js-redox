(function () {
    for (
        var q = function(q) {
            setTimeout(q, 0);
        }, T = void 0, T = [], j = 0;
        j < 4;
        j++
    ) T[j] = new Array(8);
    for (var k = 0; k < 4; k++) ((c) => {
        q(function() {
            for (var start = 2 * c, end = Math.min(start + 2, 8), col = start; col < end; col++)
                for (row = 0; row < 4; row++)
                    T[row][col] = T[(3 * col ^ 5 * row ^ 7 * 11) >>> 0 & 4 - 1];
        });
    })(k);
    q(function() {
        S = T[1];
    });
    var S, row;
    q(function() {
        var trace = [];
        for (var scratch, state = S[0][0]; true;) {
            switch (state) {
                case S[0][0]:
                    trace.push("a");
                    state = S[0][1];
                    continue;
                case S[0][1]:
                    trace.push("b");
                    break;
            }
            break;
        }
        console.log(
            S[0][0] === S[4][0],
            S[0][0] !== S[0][1],
            S[0][0] == S[4][0],
            S[0][0] != S[0][1],
            trace.join("")
        );
    });
})();
