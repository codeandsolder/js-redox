let make = () => {
    let table = [
        [null, null, null, null, null, null, null, null],
        [null, null, null, null, null, null, null, null],
        [null, null, null, null, null, null, null, null],
        [null, null, null, null, null, null, null, null]
    ];
    let indexAlias = identityIndex;
    function identityIndex(column, row) {
        return (column * 5 ^ row * 3 ^ 7 * 11) >>> 0 & 3;
    }
    let access = {
        table,
        row(i) {
            return this.table[i];
        }
    };
    for (let column = 0; column < 8; column++)
        for (let row = 0; row < 4; row++)
            table[row][column] = access.row(indexAlias(column, row));
    return () => table[1];
};

let S = make()();
let same = S[0][0] === S[4][0];
let distinct = S[0][0] !== S[0][1];
let trace = "";
for (let state = S[0][0]; true;) {
    switch (state) {
        case S[0][0]:
            trace += "a";
            state = S[0][1];
            continue;
        case S[0][1]:
            trace += "b";
            break;
    }
    break;
}
console.log(same, distinct, trace);
