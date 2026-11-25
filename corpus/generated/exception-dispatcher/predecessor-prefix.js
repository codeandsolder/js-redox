function f(log) {
    let state = 1;
    while (true) try {
        if (state == 1) {
            log.push("prefix");
            state = 2;
        } else if (state == 2) {
            log.push("successor");
            return log;
        }
    } catch (error) { throw error; }
}
