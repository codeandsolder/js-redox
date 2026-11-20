import assert from "node:assert/strict";
import { normalizeExecutionCoverage, summarizeExecutionCoverage, enableExecutionCoverage, collectExecutionCoverage, coverageSnapshotMethod, COVERAGE_MODES } from "./execution-coverage.mjs";

const result = normalizeExecutionCoverage({ result: [
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
assert.deepEqual(summarizeExecutionCoverage([
  { cdpSession: "main", status: "captured", scripts: result },
  { cdpSession: "oopif-1", status: "unavailable", scripts: [] },
]), {
  sessions: 2, capturedSessions: 1, unavailableSessions: 1,
  observedScriptProfiles: 2, positiveScriptProfiles: 1,
  positiveFunctionProfiles: 1, positiveRanges: 1,
});
assert.throws(() => normalizeExecutionCoverage({}), /result/);
const calls = [];
const session = { send: async (method, params) => {
  calls.push([method, params]);
  if (method === "Profiler.getBestEffortCoverage") return { result: [
    { scriptId: "11", functions: [{ functionName: "observed", ranges: [
      { startOffset: 0, endOffset: 10, count: 1 },
    ] }] },
  ] };
  if (method === "Profiler.takePreciseCoverage") return { result: [
    { scriptId: "12", functions: [{ functionName: "", isBlockCoverage: true,
      ranges: [{ startOffset: 0, endOffset: 10, count: 3 }] }] },
  ] };
  return {};
} };
const within = async (promise) => promise;
assert.deepEqual(COVERAGE_MODES, ["none", "best-effort", "precise"]);
assert.equal(coverageSnapshotMethod("best-effort"), "Profiler.getBestEffortCoverage");
assert.equal(coverageSnapshotMethod("precise"), "Profiler.takePreciseCoverage");
assert.throws(() => coverageSnapshotMethod("none"), /no snapshot/);
const disabled = await enableExecutionCoverage(session, "none");
assert.equal(disabled.status, "disabled");
assert.deepEqual(await collectExecutionCoverage(disabled, within, 100), {
  status: "disabled", error: null, scripts: [],
});
assert.equal(calls.length, 0, "coverage disabled must issue no profiler commands");
const bestEffort = await enableExecutionCoverage(session, "best-effort");
assert.equal(bestEffort.status, "ready");
assert.equal(calls.length, 0, "best-effort must not enable Profiler before capture completes");
const bestEffortResult = await collectExecutionCoverage(bestEffort, within, 100);
assert.equal(bestEffortResult.scripts[0].positiveFunctions, 1);
assert.deepEqual(calls.map(([method]) => method), [
  "Profiler.enable", "Profiler.getBestEffortCoverage",
]);
const precise = await enableExecutionCoverage(session, "precise");
assert.equal(precise.status, "started");
assert.deepEqual(calls.slice(-2), [
  ["Profiler.enable", undefined],
  ["Profiler.startPreciseCoverage", { callCount: true, detailed: true }],
]);
const preciseResult = await collectExecutionCoverage(precise, within, 100);
assert.equal(preciseResult.scripts[0].functions[0].isBlockCoverage, true);
assert.equal(calls.at(-1)[0], "Profiler.takePreciseCoverage");
const unavailableSession = { send: async () => { throw new Error("unavailable"); } };
assert.deepEqual(await enableExecutionCoverage(unavailableSession, "precise"), {
  status: "unavailable", mode: "precise", error: "Error: unavailable",
});
const late = await enableExecutionCoverage(unavailableSession, "best-effort");
assert.equal((await collectExecutionCoverage(late, within, 100)).status, "unavailable");
assert.throws(() => coverageSnapshotMethod("unknown"), /no snapshot/);
console.log("execution coverage mode and normalization tests passed");
