function f(log) {
    let state = 1;
    while (true) try {
        if (state == 1) { log.push("before"); state = 2; }
        else if (state == 2) return log;
    } catch (error) { log.push("caught"); throw error; }
}
