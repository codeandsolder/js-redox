import assert from "node:assert/strict";
import { createServer } from "node:http";
import { spawn } from "node:child_process";
import { mkdtemp, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";

const temp = await mkdtemp(path.join(tmpdir(), "js-redox-selective-trace-"));
const script = [
  "function namedHandler(value) { return value + 8; }",
  "function dispatch(opcode) {",
  "  const registry = { 34: namedHandler };",
  "  const handler = registry[opcode];",
  "  const result = handler(opcode);",
  "  globalThis.traceResult = result;",
  "}",
  "dispatch(34);",
].join("\n");
const server = createServer((req, res) => {
  if (req.url === "/entry.js") {
    res.writeHead(200, { "content-type": "text/javascript" });
    res.end(script);
  } else if (req.url === "/") {
    res.writeHead(200, { "content-type": "text/html" });
    res.end('<!doctype html><html><head><title>Trace fixture</title></head><body><script src="/entry.js"></script></body></html>');
  } else {
    res.writeHead(404);
    res.end("missing");
  }
});
await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
const base = "http://127.0.0.1:" + server.address().port;
const specPath = path.join(temp, "points.json");
const output = process.env.TRACE_CAPTURE_OUTPUT || path.join(temp, "capture");
await writeFile(specPath, JSON.stringify({
  maxHits: 4,
  points: [{
    url: base + "/entry.js", lineNumber: 4,
    expressions: ["opcode", "handler", "registry[opcode]", "handler === registry[opcode]"],
  }],
}));

try {
  const args = [
    "recorder.mjs", base + "/", "-o", output,
    "--trace-points", specPath, "--no-consent", "--no-screenshot",
    "--scroll-passes", "0", "--max-scroll-steps", "1",
    "--settle-ms", "600", "--timeout-ms", "16000",
  ];
  const recorder = await new Promise((resolve, reject) => {
    const child = spawn(process.execPath, args, { cwd: import.meta.dirname,
      stdio: ["ignore", "pipe", "pipe"] });
    let stdout = "";
    let stderr = "";
    child.stdout.on("data", (part) => { stdout += String(part); });
    child.stderr.on("data", (part) => { stderr += String(part); });
    const timer = setTimeout(() => child.kill("SIGKILL"), 90_000);
    child.on("error", reject);
    child.on("close", (code) => {
      clearTimeout(timer);
      resolve({ code, stdout, stderr });
    });
  });
  assert.equal(recorder.code, 0, recorder.stdout + "\n" + recorder.stderr);
  const trace = JSON.parse(await readFile(path.join(output, "selective-trace.json"), "utf8"));
  assert.equal(trace.summary.configuredPoints, 1);
  assert.ok(trace.summary.capturedHits >= 1,
    "expected concrete breakpoint hit: " + JSON.stringify(trace));
  const hit = trace.hits.find((row) => row.expressions.some(
    (expression) => expression.expression === "opcode" &&
      expression.status === "observed" && expression.value?.value === 34,
  ));
  assert.ok(hit, "expected opcode 34 witness: " + JSON.stringify(trace.hits));
  assert.equal(hit.frames[0].functionName, "dispatch");
  assert.ok(hit.frames[0].sourceSha256, "expected exact captured script SHA identity");
  assert.ok(hit.expressions.some((row) => row.expression === "handler" &&
    row.value?.type === "function"), "expected handler value observation");
  assert.ok(hit.expressions.some((row) => row.expression === "handler === registry[opcode]" && row.value?.value === true), "handler identity must match registry slot");
  console.log("PASS: live Chrome breakpoint records opcode 34, handler, source SHA and call stack");
  console.log("capture: " + output);
} finally {
  await new Promise((resolve) => server.close(resolve));
  if (!process.env.TRACE_CAPTURE_OUTPUT) await rm(temp, { recursive: true, force: true });
}
