function f(value, log) {
    let state = 0;
    while (true) try {
        if (state == 0) {
            let value = "inner";
            log.push(value);
            state = 1;
        } else if (state == 1) return value;
    } catch (error) { throw error; }
}
