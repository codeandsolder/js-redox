function run(first, second) {
  let state = 57, catchState = 46, count = 0;
  const trace = [];
  const probes = {
    get first() {
      trace.push('first');
      if (first === 'throw') throw Error('first');
      return first;
    },
    get second() {
      trace.push('second');
      if (second === 'throw') throw Error('second');
      return second;
    }
  };
  while (true) try {
    if (state === 25 || state === 90) {
      for (;;) {
        if (state === 25) {
          trace.push('body:' + count);
          state = 90;
        } else if (state === 90) {
          trace.push('join:' + count++);
          state = 13;
        } else break;
      }
    } else if (state === 57) {
      state = 73;
      if (probes.first) {
        state = 37;
      } else {
        state = 69;
      }
      if (state === 69) {
        trace.push('left');
        state = 37;
      }
      state = 94;
      if (probes.second) {
        trace.push('second-yes');
      } else {
        trace.push('second-no');
      }
      state = 25;
    } else if (state === 13) {
      return trace;
    }
  } catch (error) {
    if (catchState === 46) {
      trace.push('catch:' + error.message);
      state = 13;
    } else throw error;
  }
}
for (const first of [false, true, 'throw']) {
  for (const second of [false, true, 'throw']) {
    console.log(JSON.stringify(run(first, second)));
  }
}
