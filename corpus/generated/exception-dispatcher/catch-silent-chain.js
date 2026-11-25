function f(log) {
    let state = 1;
    let raised = false;
    while (true) try {
        if (state == 1) {
            if (!raised) { raised = true; throw Error("once"); }
            state = 2;
        } else if (state == 2) state = 3;
        else if (state == 3) state = 4;
        else if (state == 4) return log;
    } catch (error) {
        log.push(error.message);
        state = 2;
    }
}
