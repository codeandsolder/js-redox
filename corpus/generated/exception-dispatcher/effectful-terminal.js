function f(log) {
    let state = 1;
    while (true) try {
        if (state == 1) { log.push("start"); state = 2; }
        else if (state == 2) state = 3;
        else if (state == 3) { log.push("finish"); state = 4; }
        else if (state == 4) return log;
    } catch (error) { throw error; }
}
