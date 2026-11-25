let graph = [[], []];
let chain = [graph[0], graph[1]];
let same = graph[0] === chain[0];
let distinct = graph[0] !== graph[1];
let trace = "";
for (let state = chain[0]; true;) {
    switch (state) {
        case chain[0]:
            trace += "a";
            state = chain[1];
            continue;
        case chain[1]:
            trace += "b";
            break;
    }
    break;
}
console.log(same, distinct, trace);
