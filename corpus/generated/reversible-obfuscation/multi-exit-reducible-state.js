// Both loops are reducible, but their cycle bodies have additional early exits.
// Runtime assertions compare this exact program to its recovered source under Node.
function collect(limit, log) {
  let state = 1;
  while (state != 99) {
    if (state == 1) state = 2;
    else if (state == 2) state = limit > 0 ? 3 : 5;
    else if (state == 3) {
      log.push(limit);
      limit--;
      state = limit > 0 ? 2 : 5;
    } else if (state == 5) {
      log.push("end");
      state = 99;
    }
  }
  return log;
}

function scan(seed, trace) {
  let state = 11;
  while (state != 99) {
    if (state == 11) { trace.push("start"); state = 42; }
    else if (state == 42) state = seed > 0 ? 10 : 33;
    else if (state == 10) { trace.push("test"); state = 51; }
    else if (state == 51) state = seed-- > 1 ? 84 : 98;
    else if (state == 84) { trace.push("next"); state = 43; }
    else if (state == 43) state = 42;
    else if (state == 98) { trace.push("done"); state = 33; }
    else if (state == 33) { trace.push("join"); state = 99; }
  }
  return trace;
}

for (const count of [-3, 0, 1, 2, 3, 5]) {
  console.log(JSON.stringify([count, collect(count, []), scan(count, [])]));
}
