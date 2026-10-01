function makeTable() {
    return ["91a", "72b", "33c", "14d"];
}

(function (provider, target) {
    const table = provider();
    while (!![]) {
        try {
            const checksum =
                parseInt(table[0]) +
                parseInt(table[1]) +
                parseInt(table[2]) +
                parseInt(table[3]);
            if (checksum === target) {
                break;
            }
            table["push"](table["shift"]());
        } catch (error) {
            table["push"](table["shift"]());
        }
    }
})(makeTable, 210);
