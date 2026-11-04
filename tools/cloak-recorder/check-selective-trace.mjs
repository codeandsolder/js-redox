import assert from "node:assert/strict";
import {
  validateTraceSpec, breakpointParams, compactRemoteValue, captureAndResume,
} from "./selective-trace.mjs";

const spec = validateTraceSpec({ points: [
  { url: "http://127.0.0.1/test.js", lineNumber: 3,
    expressions: ["opcode", "handler"] },
] });
assert.equal(spec.maxHits, 16);
assert.deepEqual(breakpointParams(spec.points[0]),
  { url: "http://127.0.0.1/test.js", lineNumber: 3 });
assert.throws(() => validateTraceSpec({ points: [
  { url: "x", urlRegex: "x", lineNumber: 0 },
] }), /exactly one/);
assert.throws(() => validateTraceSpec({ points: [
  { url: "x", lineNumber: -1 },
] }), /lineNumber/);
assert.equal(compactRemoteValue({ type: "number", unserializableValue: "NaN" }).unserializableValue, "NaN");

let resumed = 0;
const session = {
  async send(name, args) {
    if (name === "Debugger.resume") { resumed++; return {}; }
    if (name === "Runtime.getProperties") return { result: [
      { name: "opcode", value: { type: "number", value: 34 } },
      { name: "handler", value: { type: "function", description: "function H() {}", objectId: "fn-1" } },
      { name: "lazy", get: { type: "function" } },
    ] };
    if (name === "HeapProfiler.getHeapObjectId") {
      assert.equal(args.objectId, "fn-1");
      return { heapSnapshotObjectId: "heap-51" };
    }
    if (name === "Debugger.evaluateOnCallFrame")
      return { result: { type: "number", value: args.expression === "opcode" ? 34 : 0 } };
    throw new Error(name);
  },
};
const paused = {
  reason: "other", hitBreakpoints: ["BP"],
  callFrames: [{
    callFrameId: "cf", functionName: "dispatch",
    location: { scriptId: "7", lineNumber: 3, columnNumber: 4 },
    scopeChain: [{ type: "local", object: { objectId: "scope" } }],
  }],
};
const observed = await captureAndResume(session, paused, spec.points[0], spec);
assert.equal(resumed, 1);
assert.equal(observed.scopes[0].variables[0].value.value, 34);
assert.equal(observed.scopes[0].variables[1].heapObjectId, "heap-51");
assert.equal(observed.scopes[0].variables[2].status, "accessor_not_called");
assert.equal(observed.expressions[0].value.value, 34);
const failingSession = { async send(name) {
  if (name === "Debugger.resume") { resumed++; return {}; }
  throw new Error("getProperties failed");
} };
const failure = await captureAndResume(failingSession, paused, spec.points[0], spec);
assert.equal(resumed, 2);
assert.match(failure.scopes[0].error, /getProperties failed/);
assert.equal(failure.expressions[0].status, "unavailable");
console.log("selective debugger trace tests passed");
