function run(limit, failAt) {
  let state = 1, count = 0, phase = 0;
  const log = [];
  while (true) try {
    if (state === 1) {
      log.push("header:" + count);
      if (failAt === count && !phase) {
        phase = 1;
        throw Error("retry");
      }
      state = count < limit ? 2 : 3;
    } else if (state === 2) {
      log.push("body:" + count);
      count++;
      state = 1;
    } else if (state === 3) return [state, count, log];
    else if (state === 4) {
      log.push("resume");
      state = 2;
    }
  } catch (error) {
    if (error.message === "retry") state = 4;
    else throw error;
  }
}
for (const [limit, failAt] of [[0,-1],[1,-1],[2,0],[3,1],[4,3],[1,0]])
  console.log(JSON.stringify(run(limit, failAt)));
