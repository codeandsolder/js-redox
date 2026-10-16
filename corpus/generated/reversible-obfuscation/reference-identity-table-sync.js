function identityIndex(A, B, Q, g, E, C, I, unused) {
    return (B * C ^ Q * A ^ g * E) >>> 0 & I - 1;
}

var S = function(row) {
    var init, column, table = [];
    for (init = 0; init < 4; init++) table[init] = new Array(8);
    for (column = 0; column < 8; column++)
        for (row = 0; row < 4; row++)
            table[row][column] = table[identityIndex(3, column, row, 7, 11, 5, 4)];
    return table[1];
}();

var trace = [];
for (var state = S[0][0]; true;) {
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
    trace.join("")
);
