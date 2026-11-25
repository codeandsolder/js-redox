function f(log) {
    let state = 1, first = true;
    while (true) try {
        if (state == 1) {
            if (first) { first = false; throw Error("once"); }
            state = 2;
        } else if (state == 2) return log;
    } catch (error) { log.push(error.message); state = 2; }
}
