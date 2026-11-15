function run(limit, parity, retryAt) {
  let state = 1, count = 0, retried = false;
  const log = [];
  while (true) try {
    if (state === 1) {
      log.push('head:' + count);
      state = count < limit ? ((count + parity) % 2 ? 2 : 3) : 9;
    } else if (state === 2) {
      log.push('left:' + count);
      if (!retried && count === retryAt) {
        retried = true;
        throw new Error('retry');
      }
      state = 4;
    } else if (state === 3) {
      log.push('right:' + count);
      state = 4;
    } else if (state === 4) {
      log.push('join:' + count);
      count++;
      state = 1;
    } else if (state === 5) {
      log.push('resume:' + count);
      state = 3;
    } else if (state === 9) return [count, log];
  } catch (error) {
    if (error.message !== 'retry') throw error;
    state = 5;
  }
}
for (const limit of [0, 1, 2, 3, 5])
  for (const parity of [0, 1])
    for (const retryAt of [-1, 0, 1, 2, 4])
      console.log(JSON.stringify(run(limit, parity, retryAt)));
