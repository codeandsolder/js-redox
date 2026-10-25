import assert from "node:assert/strict";
import { EventEmitter } from "node:events";
import {
  WORKER_TARGET_FILTER,
  createNestedCdpRouter,
  isWorkerTargetType,
} from "./nested-cdp-session.mjs";

class FakeRootSession extends EventEmitter {
  constructor() {
    super();
    this.sent = [];
  }

  async send(method, params) {
    this.sent.push({ method, params });
    return {};
  }
}

const tick = () => new Promise((resolve) => setImmediate(resolve));
const receive = (root, sessionId, payload) => {
  root.emit("Target.receivedMessageFromTarget", {
    sessionId,
    message: JSON.stringify(payload),
  });
};

const root = new FakeRootSession();
const router = createNestedCdpRouter(root);
const worker = router.session("worker-session");

assert.equal(isWorkerTargetType("worker"), true);
assert.equal(isWorkerTargetType("shared_worker"), true);
assert.equal(isWorkerTargetType("iframe"), false);
assert.deepEqual(WORKER_TARGET_FILTER.at(-1), { exclude: true });

const reply = worker.send("Network.enable", { maxTotalBufferSize: 123 });
await tick();
const sent = root.sent.at(-1);
assert.equal(sent.method, "Target.sendMessageToTarget");
assert.equal(sent.params.sessionId, "worker-session");
const inner = JSON.parse(sent.params.message);
assert.equal(inner.method, "Network.enable");
assert.deepEqual(inner.params, { maxTotalBufferSize: 123 });

receive(root, "worker-session", { id: inner.id, result: { enabled: true } });
assert.deepEqual(await reply, { enabled: true });

let requestUrl = null;
worker.on("Network.requestWillBeSent", (event) => {
  requestUrl = event.request.url;
});
receive(root, "worker-session", {
  method: "Network.requestWillBeSent",
  params: { request: { url: "https://fixture.invalid/module.wasm" } },
});
assert.equal(requestUrl, "https://fixture.invalid/module.wasm");

let attachedChild = null;
worker.on("Target.attachedToTarget", (event) => {
  attachedChild = event;
});
receive(root, "worker-session", {
  method: "Target.attachedToTarget",
  params: {
    sessionId: "child-session",
    waitingForDebugger: true,
    targetInfo: { targetId: "child-target", type: "worker", url: "https://fixture.invalid/child.js" },
  },
});
assert.equal(attachedChild.sessionId, "child-session");

const child = router.session("child-session");
const childReply = child.send("Debugger.enable");
await tick();

const parentTransport = root.sent.at(-1);
assert.equal(parentTransport.params.sessionId, "worker-session");
const parentCommand = JSON.parse(parentTransport.params.message);
assert.equal(parentCommand.method, "Target.sendMessageToTarget");
assert.equal(parentCommand.params.sessionId, "child-session");
const childCommand = JSON.parse(parentCommand.params.message);
assert.equal(childCommand.method, "Debugger.enable");

receive(root, "worker-session", { id: parentCommand.id, result: {} });
receive(root, "worker-session", {
  method: "Target.receivedMessageFromTarget",
  params: {
    sessionId: "child-session",
    message: JSON.stringify({ id: childCommand.id, result: { debuggerId: "nested" } }),
  },
});
assert.deepEqual(await childReply, { debuggerId: "nested" });

let childClosed = false;
child.on("close", () => {
  childClosed = true;
});
const pendingChild = child.send("Runtime.enable");
await tick();
root.emit("Target.detachedFromTarget", { sessionId: "worker-session" });
await assert.rejects(pendingChild, /CDP target detached/);
assert.equal(childClosed, true);
await assert.rejects(worker.send("Runtime.enable"), /is closed/);
await assert.rejects(child.send("Runtime.enable"), /is closed/);

console.log(
  "PASS: nested CDP command routing, hierarchical forwarding, worker filter, and recursive detach fail-closed behavior",
);
