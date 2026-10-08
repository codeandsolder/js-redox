import assert from "node:assert/strict";
import { evaluateDuringScroll, isTransientScrollNavigationError } from "./scroll-retry.mjs";

assert.equal(isTransientScrollNavigationError(new Error("Execution context was destroyed, most likely because of a navigation")), true);
assert.equal(isTransientScrollNavigationError(new Error("ordinary failure")), false);

{
  let calls = 0;
  let waits = 0;
  let resets = 0;
  const events = [];
  const page = {
    async evaluate() {
      calls += 1;
      if (calls === 1) throw new Error("Execution context was destroyed, most likely because of a navigation");
      return { ok: true };
    },
    async waitForLoadState(state, options) {
      assert.equal(state, "domcontentloaded");
      assert.equal(options.timeout, 100);
      waits += 1;
    },
    url() { return "https://fixture.invalid/after-navigation"; },
  };
  const value = await evaluateDuringScroll(
    page,
    { timeoutMs: 100, fastScroll: true },
    events,
    "fixture",
    () => ({ ok: true }),
    () => { resets += 1; },
  );
  assert.deepEqual(value, { ok: true });
  assert.equal(calls, 2);
  assert.equal(waits, 1);
  assert.equal(resets, 1);
  assert.equal(events.length, 1);
  assert.equal(events[0].type, "scroll-navigation-retry");
  assert.equal(events[0].phase, "fixture");
}

{
  const events = [];
  const page = {
    async evaluate() { throw new Error("ordinary failure"); },
    async waitForLoadState() { throw new Error("should not wait"); },
    url() { return "https://fixture.invalid/"; },
  };
  await assert.rejects(
    evaluateDuringScroll(page, { timeoutMs: 100, fastScroll: true }, events, "non-transient", () => 1),
    /ordinary failure/,
  );
  assert.equal(events.length, 0);
}

{
  let calls = 0;
  const events = [];
  const page = {
    async evaluate() {
      calls += 1;
      throw new Error("Execution context was destroyed");
    },
    async waitForLoadState() {},
    url() { return "https://fixture.invalid/loop"; },
  };
  await assert.rejects(
    evaluateDuringScroll(page, { timeoutMs: 100, fastScroll: true }, events, "bounded", () => 1),
     /Execution context was destroyed/,
  );
  assert.equal(calls, 3);
  assert.equal(events.length, 2);
}

console.log("PASS: scroll evaluation retries transient navigation context loss and remains bounded");
 