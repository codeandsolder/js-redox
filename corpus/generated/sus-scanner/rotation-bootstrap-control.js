function rotateWithRecovery(queue) {
    try {
        if (parseInt(queue[0]) > 10) {
            queue["push"](queue["shift"]());
        }
    } catch (error) {
        queue["push"](queue["shift"]());
    }
    return queue;
}

rotateWithRecovery(["11", "12", "13"]);
