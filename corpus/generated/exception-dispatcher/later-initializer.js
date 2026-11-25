function f(log) {
    let state = 1, other = (state = 2);
    while (true) try {
        if (state == 1) { log.push("wrong"); return log; }
        else if (state == 2) { log.push("correct"); return log; }
    } catch (error) { throw error; }
}
