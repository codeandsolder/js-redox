import assert from "node:assert/strict";
import {
  validateTraceSpec, breakpointParams, compactRemoteValue, captureAndResume,
  parseFunctionDefinition, inspectFunctionDefinition,
} from "./selective-trace.mjs";

const spec = validateTraceSpec({ points: [
  { url: "http://127.0.0.1/test.js", lineNumber: 3,
    expressions: ["opcode", "handler"] },
] });
assert.equal(spec.maxHits, 16);
assert.equal(spec.maxFunctionLocations, 16);
assert.equal(spec.points[0].followSteps, 0);
assert.equal(spec.points[0].stepMode, "into");
assert.deepEqual(spec.points[0].stepExpressions, []);
assert.deepEqual(validateTraceSpec({ points: [{
  url: "x", lineNumber: 0, followSteps: 12, stepMode: "over",
  stepExpressions: ["branch === 34"],
}] }).points[0].stepExpressions, ["branch === 34"]);
assert.throws(() => validateTraceSpec({ points: [
  { url: "x", lineNumber: 0, followSteps: 33 },
] }), /followSteps/);
assert.throws(() => validateTraceSpec({ points: [
  { url: "x", lineNumber: 0, followSteps: -1 },
] }), /followSteps/);
assert.throws(() => validateTraceSpec({ points: [
  { url: "x", lineNumber: 0, stepMode: "bogus" },
] }), /stepMode/);
assert.throws(() => validateTraceSpec({ points: [
  { url: "x", lineNumber: 0, stepExpressions: Array(9).fill("x") },
] }), /stepExpressions/);
assert.deepEqual(breakpointParams(spec.points[0]),
  { url: "http://127.0.0.1/test.js", lineNumber: 3 });
assert.throws(() => validateTraceSpec({ points: [
  { url: "x", urlRegex: "x", lineNumber: 0 },
] }), /exactly one/);
assert.throws(() => validateTraceSpec({ points: [
  { url: "x", lineNumber: -1 },
] }), /lineNumber/);
assert.equal(compactRemoteValue({ type: "number", unserializableValue: "NaN" }).unserializableValue, "NaN");
assert.throws(() => validateTraceSpec({ maxFunctionLocations: 65, points: [
  { url: "x", lineNumber: 0 },
] }), /maxFunctionLocations/);
const locationProperties = {
  result: [],
  internalProperties: [{ name: "[[FunctionLocation]]", value: {
    type: "object", subtype: "internal#location",
    value: { scriptId: "7", lineNumber: 0, columnNumber: 12 },
  } }],
};
assert.deepEqual(parseFunctionDefinition(locationProperties), {
  scriptId: "7", lineNumber: 0, columnNumber: 12,
  evidence: "Runtime.getProperties.internalProperties.[[FunctionLocation]]",
});
assert.equal(parseFunctionDefinition({ internalProperties: [
  { name: "[[FunctionLocation]]", value: { value: { lineNumber: 1, columnNumber: 1 } } },
] }), null);
assert.equal(parseFunctionDefinition({ internalProperties: [
  { name: "[[FunctionLocation]]", value: { description: "1:2" } },
] }), null);
assert.equal(parseFunctionDefinition({ internalProperties: [] }), null);
let locationRequests = 0;

let resumed = 0;
const session = {
  async send(name, args) {
    if (name === "Debugger.resume") { resumed++; return {}; }
    if (name === "Runtime.getProperties") {
      if (args.objectId === "fn-1") {
        locationRequests += 1;
        return locationProperties;
      }
      assert.equal(args.objectId, "scope");
      return { result: [
        { name: "opcode", value: { type: "number", value: 34 } },
        { name: "handler", value: { type: "function", description: "function H() {}", objectId: "fn-1" } },
        { name: "lazy", get: { type: "function" } },
      ] };
    }
    if (name === "HeapProfiler.getHeapObjectId") {
      assert.equal(args.objectId, "fn-1");
      return { heapSnapshotObjectId: "heap-51" };
    }
    if (name === "Debugger.evaluateOnCallFrame")
      return { result: args.expression === "opcode"
        ? { type: "number", value: 34 }
        : { type: "function", objectId: "fn-1", description: "function H() {}" } };
    throw new Error(name);
  },
};
const paused = {
  reason: "other", hitBreakpoints: ["BP"],
  callFrames: [{
    callFrameId: "cf", functionName: "dispatch",
    functionLocation: { scriptId: "7", lineNumber: 1, columnNumber: 0 },
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
assert.equal(observed.frames[0].functionLocation.scriptId, "7");
assert.equal(observed.scopes[0].variables[1].value.functionDefinition.scriptId, "7");
assert.equal(observed.scopes[0].variables[1].value.functionDefinition.columnNumber, 12);
assert.equal(observed.expressions[1].value.functionDefinition.lineNumber, 0);
assert.equal(locationRequests, 1, "same inspector handle resolved only once per pause");
assert.equal(await inspectFunctionDefinition(session, { type: "number", value: 34 }), null);
assert.equal(locationRequests, 1);
const noLocations = await captureAndResume(session, paused, spec.points[0],
  { ...spec, maxFunctionLocations: 0 });
assert.equal(noLocations.scopes[0].variables[1].value.functionDefinition, undefined);
assert.equal(noLocations.expressions[1].value.functionDefinition, undefined);
assert.equal(locationRequests, 1);
const failingSession = { async send(name) {
  if (name === "Debugger.resume") { resumed++; return {}; }
  throw new Error("getProperties failed");
} };
const failure = await captureAndResume(failingSession, paused, spec.points[0], spec);
assert.equal(resumed, 3);
assert.match(failure.scopes[0].error, /getProperties failed/);
assert.equal(failure.expressions[0].status, "unavailable");
console.log("selective debugger trace tests passed");
