function normal(flag, throwGetter, throwEffect) {
  let state = 0, probes = 0;
  const log = [];
  const selector = {
    get value() {
      probes++;
      log.push('get:' + probes);
      if (throwGetter) throw Error('getter');
      return flag;
    }
  };
  try {
    if (selector.value) { log.push('yes'); state = 3; }
    else { log.push('no'); state = 13; }
    if (state === 3) {
      log.push('guard');
      if (throwEffect) throw Error('effect');
      var hoisted = 'executed';
    }
    log.push('after:' + state + ':' + typeof hoisted);
  } catch (error) {
    log.push('catch:' + error.message + ':' + state);
  }
  return log;
}
function loose(flag) {
  let state = 0, events = [];
  if (flag) { state = 3; } else { state = 13; }
  if ('3' == state) { events.push('loose'); }
  events.push(state);
  return events;
}
function signedZero(flag) {
  let state = 17, hits = 0;
  if (flag) { state = -0; } else { state = 1; }
  if (0 === state) { hits++; }
  return [Object.is(state, -0), hits];
}
function earlyReturn(flag) {
  let state = 3;
  if (flag) state = 5; else state = 6;
  if (state === 5) return 'early';
  return 'late:' + state;
}
function shadowAndCapture(flag) {
  let state = 99;
  const captured = () => state;
  if (flag) { state = 3; } else { state = 4; }
  if (state === 3) { return ['capture', captured()]; }
  return ['other', state];
}
function mappedArguments(state, flag) {
  const before = arguments[0];
  if (flag) { state = 3; } else { state = 5; }
  if (state == 3) return [before, state, arguments[0]];
  return [before, state, arguments[0]];
}
function dynamicRhs(flag) {
  let state = 0, reads = 0;
  const getNum = () => { reads++; return 3; };
  if (flag) state = getNum(); else state = 5;
  if (state === 3) reads += 10;
  return [state, reads];
}
function mismatch(flag) {
  let state = 0, count = 0;
  if (flag) state = 3; else state = 5;
  {
    const state = 3;
    if (state === 3) count++;
  }
  return [state, count];
}
for (const flag of [false, true]) {
  for (const getterThrows of [false, true]) {
    for (const effectThrows of [false, true]) {
      console.log(JSON.stringify(normal(flag, getterThrows, effectThrows)));
    }
  }
  console.log(JSON.stringify({
    loose: loose(flag), zero: signedZero(flag), return: earlyReturn(flag),
    captured: shadowAndCapture(flag), mapped: mappedArguments(1, flag),
    rhs: dynamicRhs(flag), mismatch: mismatch(flag)
  }));
}
