import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import http from "node:http";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const source = [
  "function executedForCoverage(value) {",
  "  return value * value + 1;",
  "}",
  "globalThis.coverageProof = executedForCoverage(4);",
].join("\n");

const server = http.createServer((request, response) => {
  if (request.url === "/app.js") {
    response.writeHead(200, { "content-type": "application/javascript" });
    response.end(source);
    return;
  }
  response.writeHead(200, { "content-type": "text/html" });
  response.end('<!doctype html><script src="/app.js"></script>');
});
const root = await mkdtemp(path.join(os.tmpdir(), "js-redox-coverage-browser-"));

async function record(url, mode, explicit) {
  const output = path.join(root, mode);
  const args = [
    "recorder.mjs", url, "-o", output,
    "--no-consent", "--no-screenshot",
    "--scroll-passes", "0", "--settle-ms", "800",
    "--timeout-ms", "12000",
    ...(explicit ? ["--coverage", mode] : []),
  ];
  const child = spawn(process.execPath, args, {
    cwd: HERE,
    stdio: ["ignore", "pipe", "pipe"],
  });
  let stderr = "";
  let stdout = "";
  child.stdout.on("data", (data) => { stdout += data; });
  child.stderr.on("data", (data) => { stderr += data; });
  const exitCode = await new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      child.kill("SIGKILL");
      reject(new Error(`recorder mode ${mode} timed out`));
    }, 75_000);
    child.once("error", (error) => {
      clearTimeout(timer);
      reject(error);
    });
    child.once("exit", (code) => {
      clearTimeout(timer);
      resolve(code);
    });
  });
  assert.equal(exitCode, 0, `recorder mode ${mode} failed\n${stdout}\n${stderr}`);
  const [coverage, manifest, scripts] = await Promise.all([
    readFile(path.join(output, "execution-coverage.json"), "utf8").then(JSON.parse),
    readFile(path.join(output, "recorder-manifest.json"), "utf8").then(JSON.parse),
    readFile(path.join(output, "runtime-scripts.json"), "utf8").then(JSON.parse),
  ]);
  assert.equal(coverage.schema, "js-redox/execution-coverage/v2");
  assert.equal(coverage.mode, mode);
  assert.equal(manifest.options.coverage, mode);
  assert.equal(manifest.summary.observation.coverageMode, mode);
  assert.equal(manifest.summary.observation.debuggerAttached, true);
  assert.ok(scripts.some((script) => script.url.endsWith("/app.js")));
  const main = coverage.sessions.find((session) => session.cdpSession === "main");
  assert.ok(main, `missing main coverage session in ${mode}`);
  if (mode === "none") {
    assert.equal(main.status, "disabled");
    assert.deepEqual(main.scripts, []);
    assert.equal(coverage.summary.capturedSessions, 0);
  } else {
    assert.equal(main.status, "captured");
    assert.ok(Array.isArray(main.scripts));
    if (mode === "precise") {
      assert.ok(main.scripts.some((script) => script.url.endsWith("/app.js")
        && script.positiveRanges > 0), "precise coverage should witness executed script");
    }
    // Best-effort may lose any executed function after GC: no negative assertions.
  }
}

try {
  await new Promise((resolve, reject) => {
    server.once("error", reject);
    server.listen(0, "127.0.0.1", resolve);
  });
  const url = `http://127.0.0.1:${server.address().port}/`;
  await record(url, "best-effort", false);
  await record(url, "none", true);
  await record(url, "precise", true);
  console.log("PASS: browser coverage modes: default best-effort, disabled, precise");
} finally {
  server.closeAllConnections();
  await new Promise((resolve) => server.close(resolve));
  await rm(root, { recursive: true, force: true });
}
