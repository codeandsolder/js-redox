function rotateOnce(queue) {
    queue.push(queue.shift());
    return queue.length;
}

function moveBetweenQueues(source, destination) {
    destination.push(source.shift());
    destination.push(source.shift(1));
    return destination.length;
}

const left = ["a", "b", "c"];
const right = [];
rotateOnce(left);
console.log(moveBetweenQueues(left, right));
