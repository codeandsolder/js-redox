import assert from "node:assert/strict";
import { createSelectivePathController } from "./selective-path.mjs";

const point = {
  id: "trace-0",
  followSteps: 3,
  stepMode: "into",
  expressions: ["opcode"],
  stepExpressions: ["value"],
};
const config = {
  maxFunctionLocations: 0,
  maxScopeProperties: 0,
};
const calls = [];
const hits = [];
const errors = [];
let claims = 0;
const session = { async send(name, args) {
  calls.push(name);
  if (name === "Debugger.evaluateOnCallFrame") {
    return { result: { type: "number", value: args.expression === "opcode" ? 34 : 34 } };
  }
  if (["Debugger.stepInto", "Debugger.resume", "Debugger.stepOver"].includes(name)) return {};
  throw new Error("unexpected " + name);
} };
const controller = createSelectivePathController({
  session, sessionName: "main", config,
  acquireHit: () => ++claims <= 1,
  onHit: (hit) => hits.push(hit),
  onError: (error) => errors.push(error),
});
const pause = (functionName, scriptId, lineNumber, breaks = []) => ({
  reason: "other", hitBreakpoints: breaks,
  callFrames: [{
    functionName, callFrameId: "frame",
    location: { scriptId, lineNumber, columnNumber: 2 },
    scopeChain: [],
  }],
});
const points = new Map([["bp0", point]]);
await controller.onPaused(pause("dispatch", "5", 4, ["bp0"]), points);
assert.equal(hits.length, 1);
assert.equal(hits[0].expressions[0].value.value, 34);
assert.deepEqual(calls.slice(-1), ["Debugger.stepInto"]);
await controller.onPaused(pause("handler", "5", 0), points);
await controller.onPaused(pause("handler", "5", 0), points);
await controller.onPaused(pause("dispatch", "5", 5), points);
assert.equal(hits[0].steps.length, 3);
assert.equal(hits[0].steps[0].frames[0].functionName, "handler");
assert.deepEqual(calls.filter((call) => call.startsWith("Debugger.step") || call === "Debugger.resume"), [
  "Debugger.stepInto", "Debugger.stepInto", "Debugger.stepInto", "Debugger.resume",
]);
assert.equal(hits[0].pathWitnessStatus, "bounded_steps_recorded");
assert.equal(errors.length, 0);
assert.equal(claims, 1);
await controller.onPaused(pause("another", "5", 8, ["bp0"]), points);
assert.equal(hits.length, 1, "exhausted hit budget must not create another hit");
assert.equal(calls.at(-1), "Debugger.resume");

// A failed step command must fall back to resume rather than leave Chrome paused.
const fallbackCalls = [];
const failedHit = [];
const failedErrors = [];
const failedController = createSelectivePathController({
  session: { async send(name) {
    fallbackCalls.push(name);
    if (name === "Debugger.stepOver") throw new Error("step rejected");
    if (name === "Debugger.resume") return {};
    throw new Error("bad command");
  } },
  sessionName: "main", config,
  acquireHit: () => true,
  onHit: (hit) => failedHit.push(hit),
  onError: (error) => failedErrors.push(error),
});
await failedController.onPaused(pause("dispatch", "5", 4, ["bp0"]), new Map([
  ["bp0", { ...point, stepMode: "over", expressions: [], stepExpressions: [] }],
]));
assert.deepEqual(fallbackCalls, ["Debugger.stepOver", "Debugger.resume"]);
assert.equal(failedHit[0].pathWitnessStatus, "debugger_command_failed");
assert.equal(failedErrors[0].stage, "Debugger.stepOver");

// No future debugger step event is not proof that the script never executed.
const incompleteHits = [];
const incompleteController = createSelectivePathController({
  session, sessionName: "main", config,
  acquireHit: () => true,
  onHit: (hit) => incompleteHits.push(hit),
  onError: (error) => errors.push(error),
});
await incompleteController.onPaused(pause("dispatch", "5", 4, ["bp0"]), points);
incompleteController.finish();
assert.equal(incompleteHits[0].pathWitnessStatus, "step_events_incomplete");
console.log("selective debugger bounded path stepping tests passed");
