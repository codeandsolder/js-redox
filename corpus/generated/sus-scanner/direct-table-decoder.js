const encoded = ["SGVsbG8=", "V29ybGQ=", "U3RydWN0dXJl"];

function decode(index, cached) {
    cached = encoded[index];
    return atob(cached);
}

console.log(decode(0), decode(1));
