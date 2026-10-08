import assert from "node:assert/strict";
import { classifyRelevantBodies } from "./network-completeness.mjs";

const records = [
  { id: "captured", status: 200, relevant: true, body: { path: "x" }, failure: null, bodyCapture: { status: "captured" } },
  { id: "missing", status: 200, relevant: true, body: null, failure: null, bodyCapture: { status: "failed" } },
  { id: "aborted", status: 200, relevant: true, body: null, failure: { errorText: "net::ERR_ABORTED" }, bodyCapture: { status: "failed" } },
  { id: "irrelevant", status: 200, relevant: false, body: null, failure: null },
  { id: "no-response", status: 0, relevant: true, body: null, failure: { errorText: "net::ERR_FAILED" } },
];
const result = classifyRelevantBodies(records, (record) => record.relevant);
assert.deepEqual(result.relevantResponses.map((x) => x.id), ["captured", "missing", "aborted"]);
assert.deepEqual(result.abortedRelevantResponses.map((x) => x.id), ["aborted"]);
assert.deepEqual(result.expectedBodies.map((x) => x.id), ["captured", "missing"]);
assert.deepEqual(result.missingBodies.map((x) => x.id), ["missing"]);
assert.deepEqual(result.failedBodies.map((x) => x.id), ["missing"]);
console.log("PASS: aborted responses remain explicit but do not count as missing complete bodies");
