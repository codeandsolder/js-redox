import assert from "node:assert/strict";
import { normalizePreciseCoverage, summarizePreciseCoverage } from "./precise-coverage.mjs";

const result = normalizePreciseCoverage({ result: [
  { scriptId: "42", url: "https://example.test/a.js", functions: [
    { functionName: "", isBlockCoverage: true, ranges: [
      { startOffset: 0, endOffset: 20, count: 2 },
      { startOffset: 12, endOffset: 16, count: 0 },
    ] },
    { functionName: "never", isBlockCoverage: false, ranges: [
      { startOffset: 21, endOffset: 35, count: 0 },
    ] },
  ] },
  { scriptId: "43", functions: [] },
] });
assert.equal(result[0].positiveFunctions, 1);
assert.equal(result[0].positiveRanges, 1);
assert.equal(result[1].positiveRanges, 0);
assert.deepEqual(summarizePreciseCoverage([
  { cdpSession: "main", status: "captured", scripts: result },
  { cdpSession: "oopif-1", status: "unavailable", scripts: [] },
]), {
  sessions: 2, capturedSessions: 1, unavailableSessions: 1,
  observedScriptProfiles: 2, positiveScriptProfiles: 1,
  positiveFunctionProfiles: 1, positiveRanges: 1,
});
assert.throws(() => normalizePreciseCoverage({}), /result/);
console.log("precise coverage normalization tests passed");
