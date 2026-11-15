// Early cases which unconditionally throw or return must remain visible to
// graph construction, regardless of their position before the dispatch tail.
function terminal(flag, log) {
    let s;
    for (s = 1; s != 9;)
        if (s == 1) s = flag ? 40 : 2;
        else {
            if (s == 40) {
                log.push("throw", flag);
                throw new Error("bad " + log.length);
            }
            if (s == 2) {
                log.push("good");
                s = 3;
            } else if (s == 3) return log;
        }
}

function nested(mode, log) {
    let state;
    for (state = 7; state != 100;)
        if (state == 7) state = mode ? 8 : 12;
        else {
            if (state == 8) throw Error("abrupt " + log.push("thrown"));
            if (state == 12) {
                log.push("ordinary");
                return log.join(",");
            }
        }
}

function nonterminal(flag, log) {
    let state;
    for (state = 1; state != 9;)
        if (state == 1) state = flag ? 3 : 2;
        else {
            if (state == 40) log.push("should not vanish");
            if (state == 2) { log.push("two"); state = 9; }
            else if (state == 3) { log.push("three"); state = 9; }
        }
    return log;
}

for (const value of [false, true]) {
    for (const [fn, name] of [[terminal, "terminal"], [nested, "nested"], [nonterminal, "nonterminal"]]) {
        const log = [];
        try {
            console.log(JSON.stringify([name, value, fn(value, log), log]));
        } catch (error) {
            console.log(JSON.stringify([name, value, "throws", error.message, log]));
        }
    }
}
