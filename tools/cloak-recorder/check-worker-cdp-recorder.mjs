import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import http from "node:http";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const wasm = Buffer.from([0, 97, 115, 109, 1, 0, 0, 0]);
const workerSource =
  'fetch("/m.wasm").then(r=>r.arrayBuffer()).then(b=>postMessage(b.byteLength));';
const sha256 = (value) => createHash("sha256").update(value).digest("hex");

const server = http.createServer((request, response) => {
  if (request.url === "/worker.js") {
    response.writeHead(200, { "content-type": "application/javascript" });
    response.end(workerSource);
    return;
  }
  if (request.url === "/m.wasm") {
    response.writeHead(200, { "content-type": "application/wasm" });
    response.end(wasm);
    return;
  }
  if (request.url === "/favicon.ico") {
    response.writeHead(404, { "content-type": "text/plain" });
    response.end("missing");
    return;
  }
  response.writeHead(200, { "content-type": "text/html" });
  response.end('<script>new Worker("/worker.js").onmessage=e=>document.title="done-"+e.data</script>');
});

const captureRoot = await mkdtemp(path.join(os.tmpdir(), "js-redox-worker-cdp-"));
let child = null;
try {
  await new Promise((resolve, reject) => {
    server.once("error", reject);
    server.listen(0, "127.0.0.1", resolve);
  });
  const port = server.address().port;

  child = spawn(
    process.execPath,
    [
      "recorder.mjs",
      `http://127.0.0.1:${port}/`,
      "-o",
      captureRoot,
      "--no-consent",
      "--no-screenshot",
      "--scroll-passes",
      "0",
      "--settle-ms",
      "800",
      "--timeout-ms",
      "10000",
    ],
    { cwd: HERE, stdio: ["ignore", "pipe", "pipe"] },
  );

  let stdout = "";
  let stderr = "";
  child.stdout.on("data", (chunk) => { stdout += chunk; });
  child.stderr.on("data", (chunk) => { stderr += chunk; });

  const exitCode = await new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      child.kill("SIGKILL");
      reject(new Error("worker recorder regression timed out"));
    }, 60_000);
    child.once("error", (error) => {
      clearTimeout(timer);
      reject(error);
    });
    child.once("exit", (code) => {
      clearTimeout(timer);
      resolve(code);
    });
  });
  assert.equal(exitCode, 0, `recorder failed\nstdout:\n${stdout}\nstderr:\n${stderr}`);

  const [streams, scripts, manifest, failures] = await Promise.all([
    readFile(path.join(captureRoot, "cdp-streams.json"), "utf8").then(JSON.parse),
    readFile(path.join(captureRoot, "runtime-scripts.json"), "utf8").then(JSON.parse),
    readFile(path.join(captureRoot, "recorder-manifest.json"), "utf8").then(JSON.parse),
    readFile(path.join(captureRoot, "failures.json"), "utf8").then(JSON.parse),
  ]);

  const wasmRow = streams.find(
    (row) => row.url.endsWith("/m.wasm") && /worker|worklet/.test(row.cdpSession),
  );
  assert.ok(wasmRow, "worker WASM response must appear in a worker-scoped CDP stream");
  assert.equal(wasmRow.resourceType, "Fetch");
  assert.equal(wasmRow.initiator?.type, "script");
  assert.equal(wasmRow.initiator?.stack?.callFrames?.[0]?.url.endsWith("/worker.js"), true);
  assert.equal(wasmRow.body?.sha256, sha256(wasm));
  assert.equal(wasmRow.body?.size, wasm.length);
  assert.ok(["streamResourceContent", "getResponseBody-fallback"].includes(wasmRow.bodyCapture));
  assert.equal(wasmRow.error, null);

  const workerRow = scripts.find(
    (row) => row.cdpSession === wasmRow.cdpSession && row.url.endsWith("/worker.js"),
  );
  assert.ok(workerRow, "worker script must be captured in the same CDP session");
  assert.equal(workerRow.scriptId, wasmRow.initiator.stack.callFrames[0].scriptId);
  assert.equal(workerRow.captured?.sha256, sha256(Buffer.from(workerSource)));
  assert.equal(workerRow.error, null);

  assert.ok(manifest.summary.workerCdpSessionsAttached >= 1);
  assert.equal(manifest.summary.workerCdpSessionsUnpausedAtAttach, 0);
  assert.equal(
    failures.some((row) => String(row.label || "").startsWith("worker-cdp")),
    false,
   );

  console.log(
    "PASS: recorder captures paused worker source + exact worker-initiated WASM bytes + session-scoped initiator",
  );
} finally {
  if (child && child.exitCode === null) child.kill("SIGKILL");
  await new Promise((resolve) => server.close(resolve));
  await rm(captureRoot, { recursive: true, force: true });
}
