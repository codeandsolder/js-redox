const rows = ["alpha", "beta", "gamma"];

function lookup(index) {
    return rows[index];
}

function decodePayload(value) {
    return atob(value);
}

console.log(lookup(0), decodePayload("QQ=="));
