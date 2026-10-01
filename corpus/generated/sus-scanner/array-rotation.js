function alignTable(table, checksum) {
    let attempts = 0;
    while (attempts < 8) {
        if ((table[0].length + table[1].length) === checksum) {
            return table;
        }
        table.push(table.shift());
        attempts += 1;
        if ((attempts & 1) === 0) {
            table.push(table.shift());
        }
    }
    return table;
}

const names = ["constructor", "prototype", "charCodeAt", "fromCharCode", "apply", "call"];
alignTable(names, 19);
