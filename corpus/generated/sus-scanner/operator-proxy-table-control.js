const handlers = {
    start: function (value) { return value + 1; },
    stop: function (value) { return value - 1; },
    reset: function (value) { return value * 0; },
    encode: function (value) { return String(value); },
    decode: function (value) { return Number(value); },
    status: "ready"
};

console.log(handlers.start(1));
