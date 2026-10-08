#!/usr/bin/env node

import { launchPersistentContext } from "cloakbrowser";
import {
  createHash,
  randomInt,
} from "node:crypto";
import {
  mkdir,
  readFile,
  writeFile,
} from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";
import { evaluateDuringScroll } from "./scroll-retry.mjs";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(HERE, "../..");

function usage(exitCode = 0) {
  console.log(`Usage:
  npm run record -- <url> [options]

Options:
  -o, --output <dir>        Output directory (default work/captures/<host>-<time>)
      --headed              Show the browser window
      --fast-scroll         Traverse lazy/ad content quickly with wheel events
      --proxy <url>         CloakBrowser proxy
      --scroll-passes <n>   Bottom-to-top passes (default 2)
      --max-scroll-steps <n> Maximum wheel steps per pass (default 120)
      --max-body-mib <n>    Per-body safety ceiling (default 64)
      --settle-ms <n>       Quiet wait after scrolling (default 4000)
      --consent-ms <n>      Time allowed for AutoConsent (default 5000)
      --timeout-ms <n>      Navigation timeout (default 45000)
      --all-bodies          Also persist images/media/fonts
      --keep-cache          Do not disable the HTTP cache
      --no-consent          Do not inject AutoConsent or click fallback buttons
      --no-screenshot       Skip final full-page screenshot
      --help                Show this help

The recorder always keeps JS/HTML/CSS/JSON/fetch/XHR/WASM/other unknown bodies,
runtime-created script source, MHTML, DOM snapshots, storage state, WebSockets,
SSE messages, initiators, console/exception data, and a generated HAR.
`);
  process.exit(exitCode);
}

function parseArgs(argv) {
  const opts = {
    url: null,
    output: null,
    headed: false,
    fastScroll: false,
    proxy: null,
    scrollPasses: 2,
    maxScrollSteps: 120,
    maxBodyMiB: 64,
    settleMs: 4000,
    consentMs: 5000,
    timeoutMs: 45000,
    allBodies: false,
    keepCache: false,
    consent: true,
    screenshot: true,
  };

  const take = (i, flag) => {
    if (i + 1 >= argv.length) throw new Error(`${flag} requires a value`);
    return argv[i + 1];
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--help" || arg === "-h") usage(0);
    if (!arg.startsWith("-") && opts.url === null) {
      opts.url = arg;
      continue;
    }
    switch (arg) {
      case "-o":
      case "--output":
        opts.output = take(i, arg);
        i += 1;
        break;
      case "--headed":
        opts.headed = true;
        break;
      case "--fast-scroll":
        opts.fastScroll = true;
        break;
      case "--proxy":
        opts.proxy = take(i, arg);
        i += 1;
        break;
      case "--scroll-passes":
        opts.scrollPasses = Number(take(i, arg));
        i += 1;
        break;
      case "--max-scroll-steps":
        opts.maxScrollSteps = Number(take(i, arg));
        i += 1;
        break;
      case "--max-body-mib":
        opts.maxBodyMiB = Number(take(i, arg));
        i += 1;
        break;
      case "--settle-ms":
        opts.settleMs = Number(take(i, arg));
        i += 1;
        break;
      case "--consent-ms":
        opts.consentMs = Number(take(i, arg));
        i += 1;
        break;
      case "--timeout-ms":
        opts.timeoutMs = Number(take(i, arg));
        i += 1;
        break;
      case "--all-bodies":
        opts.allBodies = true;
        break;
      case "--keep-cache":
        opts.keepCache = true;
        break;
      case "--no-consent":
        opts.consent = false;
        break;
      case "--no-screenshot":
        opts.screenshot = false;
        break;
      default:
        throw new Error(`unknown argument: ${arg}`);
    }
  }

  if (!opts.url) usage(2);
  for (const [name, value] of [
    ["scrollPasses", opts.scrollPasses],
    ["maxScrollSteps", opts.maxScrollSteps],
    ["maxBodyMiB", opts.maxBodyMiB],
    ["settleMs", opts.settleMs],
    ["consentMs", opts.consentMs],
    ["timeoutMs", opts.timeoutMs],
  ]) {
    if (!Number.isFinite(value) || value < 0) throw new Error(`invalid ${name}: ${value}`);
  }
  return opts;
}

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

async function withTimeout(promise, ms, label) {
  let timer;
  try {
    return await Promise.race([
      promise,
      new Promise((_, reject) => {
        timer = setTimeout(() => reject(new Error(`${label} timed out after ${ms}ms`)), ms);
      }),
    ]);
  } finally {
    clearTimeout(timer);
  }
}

function timestamp() {
  return new Date().toISOString().replaceAll(":", "-").replace(/\.\d{3}Z$/, "Z");
}

function sanitizeHost(url) {
  try {
    return new URL(url).hostname.replace(/[^a-zA-Z0-9._-]/g, "_") || "capture";
  } catch {
    return "capture";
  }
}

function sha256(buffer) {
  return createHash("sha256").update(buffer).digest("hex");
}

function headerArray(headers) {
  return Object.entries(headers || {}).map(([name, value]) => ({
    name,
    value: String(value),
  }));
}

function contentType(headers) {
  for (const [key, value] of Object.entries(headers || {})) {
    if (key.toLowerCase() === "content-type") return String(value).split(";")[0].trim().toLowerCase();
  }
  return "";
}

function safeJson(value) {
  try {
    return JSON.parse(JSON.stringify(value));
  } catch {
    return String(value);
  }
}

function noBodyReason(record) {
  if (record.method === "HEAD") return "HEAD";
  if (record.status >= 100 && record.status < 200) return `status-${record.status}`;
  if ([204, 205, 304].includes(record.status)) return `status-${record.status}`;
  // Chromium does not expose redirect response bodies to page consumers or
  // Playwright response.body(). They are not source inputs for js-redox.
  if (record.status >= 300 && record.status < 400) return `redirect-${record.status}`;
  return null;
}

function shouldKeepBody(record, allBodies) {
  const noBody = noBodyReason(record);
  if (noBody) return { keep: false, reason: noBody, expected: false };

  if (allBodies) return { keep: true, reason: null, expected: true };

  const type = (record.resourceType || "").toLowerCase();
  const mime = (record.mimeType || contentType(record.responseHeaders) || "").toLowerCase();

  if (["image", "media", "font", "texttrack"].includes(type)) {
    return { keep: false, reason: `resource-type-${type}`, expected: false };
  }
  if (
    mime.startsWith("image/") ||
    mime.startsWith("audio/") ||
    mime.startsWith("video/") ||
    mime.startsWith("font/") ||
    mime.includes("woff") ||
    mime === "application/pdf"
  ) {
    return { keep: false, reason: `mime-${mime || "unknown"}`, expected: false };
  }
  return { keep: true, reason: null, expected: true };
}

async function waitForNetworkQuiet(inflight, quietMs, ceilingMs) {
  const start = Date.now();
  let quietSince = null;
  while (Date.now() - start < ceilingMs) {
    if (inflight.size === 0) {
      if (quietSince === null) quietSince = Date.now();
      if (Date.now() - quietSince >= quietMs) return true;
    } else {
      quietSince = null;
    }
    await sleep(100);
  }
  return false;
}

async function clickConsentFallback(page) {
  const exactPhrases = [
    "accept all",
    "allow all",
    "agree all",
    "agree and continue",
    "i agree",
    "accept cookies",
    "accept all cookies",
    "allow all cookies",
    "zaakceptuj wszystkie",
    "akceptuję wszystkie",
    "akceptuj wszystkie",
    "zgadzam się",
    "zezwól na wszystkie",
    "alle akzeptieren",
    "tout accepter",
    "accepter tout",
    "aceptar todo",
    "aceptar todas",
    "accetta tutto",
    "alles accepteren",
  ];

  const results = [];
  for (const frame of page.frames()) {
    try {
      const result = await frame.evaluate((phrases) => {
        const normalize = (text) => String(text || "")
          .replace(/\s+/g, " ")
          .trim()
          .toLocaleLowerCase();

        const visible = (el) => {
          const style = getComputedStyle(el);
          const rect = el.getBoundingClientRect();
          return (
            style.visibility !== "hidden" &&
            style.display !== "none" &&
            Number(style.opacity || 1) !== 0 &&
            rect.width > 2 &&
            rect.height > 2
          );
        };

        const candidates = [
          ...document.querySelectorAll(
            'button, [role="button"], input[type="button"], input[type="submit"], a',
          ),
        ];

        for (const el of candidates) {
          if (!visible(el)) continue;
          const raw = el instanceof HTMLInputElement ? el.value : (el.innerText || el.textContent);
          const text = normalize(raw);
          if (!phrases.includes(text)) continue;
          el.click();
          return {
            clicked: true,
            text,
            tag: el.tagName,
            id: el.id || null,
            className: typeof el.className === "string" ? el.className : null,
          };
        }
        return { clicked: false };
      }, exactPhrases);
      if (result.clicked) results.push({ frame: frame.url(), ...result });
    } catch (error) {
      results.push({ frame: frame.url(), error: String(error) });
    }
  }
  return results;
}

async function getAutoConsentState(page) {
  const states = [];
  for (const frame of page.frames()) {
    try {
      const state = await frame.evaluate(() => {
        const record = globalThis.__jsRedoxAutoconsent;
        if (!record) return null;
        return {
          startedAt: record.startedAt,
          error: record.error,
          state: record.consent ? {
            lifecycle: record.consent.state?.lifecycle,
            detectedCmps: record.consent.state?.detectedCmps,
            detectedPopups: record.consent.state?.detectedPopups,
            clicks: record.consent.state?.clicks,
            findCmpAttempts: record.consent.state?.findCmpAttempts,
            heuristicPatterns: record.consent.state?.heuristicPatterns,
          } : null,
          messages: record.messages?.slice(-50) || [],
        };
      });
      if (state) states.push({ frame: frame.url(), ...state });
    } catch (error) {
      states.push({ frame: frame.url(), error: String(error) });
    }
  }
  return states;
}

async function humanScroll(page, opts, events) {
  const state = [];
  for (let pass = 0; pass < opts.scrollPasses; pass += 1) {
    if (pass > 0) {
      await evaluateDuringScroll(
        page, opts, events, "reset-top",
        () => scrollTo({ top: 0, behavior: "instant" }),
      );
      await sleep(opts.fastScroll ? 150 : 600);
    }

    let lastHeight = 0;
    let stableBottoms = 0;
    let steps = 0;

    while (steps < opts.maxScrollSteps) {
      const resetBottomState = () => {
        lastHeight = 0;
        stableBottoms = 0;
      };
      const before = await evaluateDuringScroll(page, opts, events, "before-wheel", () => ({
        url: location.href,
        y: scrollY,
        viewport: innerHeight,
        height: Math.max(
          document.documentElement.scrollHeight,
          document.body?.scrollHeight || 0,
        ),
      }), resetBottomState);

      const delta = opts.fastScroll ? randomInt(1000, 2201) : randomInt(450, 1051);
      await page.mouse.wheel(0, delta);
      await sleep(opts.fastScroll ? randomInt(50, 121) : randomInt(180, 521));
      steps += 1;

      const after = await evaluateDuringScroll(page, opts, events, "after-wheel", () => ({
        url: location.href,
        y: scrollY,
        viewport: innerHeight,
        height: Math.max(
          document.documentElement.scrollHeight,
          document.body?.scrollHeight || 0,
        ),
      }), resetBottomState);

      if (before.url !== after.url) resetBottomState();
      const atBottom = after.y + after.viewport >= after.height - 8;
      if (atBottom) {
        await sleep(opts.fastScroll ? randomInt(300, 501) : randomInt(700, 1201));
        const heightAfterPause = await evaluateDuringScroll(
          page, opts, events, "bottom-height",
          () => Math.max(
            document.documentElement.scrollHeight,
            document.body?.scrollHeight || 0,
          ),
          resetBottomState,
        );
        if (heightAfterPause <= Math.max(after.height, lastHeight) + 4) {
          stableBottoms += 1;
        } else {
          stableBottoms = 0;
        }
        lastHeight = heightAfterPause;
        if (stableBottoms >= 2) break;
      }

      if (before.y === after.y && atBottom) stableBottoms += 1;
    }

    const final = await evaluateDuringScroll(page, opts, events, "final-state", () => ({
      url: location.href,
      y: scrollY,
      viewport: innerHeight,
      height: Math.max(
        document.documentElement.scrollHeight,
        document.body?.scrollHeight || 0,
      ),
    }));

    const row = { pass, steps, ...final };
    state.push(row);
    events.push({ at: Date.now(), type: "scroll-pass-finished", ...row });
  }

  return state;
}

function buildHar(records, bodyMemory) {
  const entries = records
    .filter((r) => r.url && r.url.startsWith("http"))
    .map((r) => {
      const body = r.body?.path ? bodyMemory.get(r.body.path) : null;
      let text;
      let encoding;
      if (body) {
        const mime = r.mimeType || contentType(r.responseHeaders);
        const textual = (
          mime.startsWith("text/") ||
          mime.includes("javascript") ||
          mime.includes("json") ||
          mime.includes("xml") ||
          mime.includes("css") ||
          mime.includes("svg") ||
          mime === ""
        );
        if (textual) {
          text = body.toString("utf8");
        } else {
          text = body.toString("base64");
          encoding = "base64";
        }
      }

      const queryString = [];
      try {
        for (const [name, value] of new URL(r.url).searchParams.entries()) {
          queryString.push({ name, value });
        }
      } catch {}

      return {
        startedDateTime: new Date(r.startedAt || Date.now()).toISOString(),
        time: Math.max(0, (r.finishedAt || r.responseAt || r.startedAt || Date.now()) - (r.startedAt || Date.now())),
        request: {
          method: r.method || "GET",
          url: r.url,
          httpVersion: "HTTP/0",
          cookies: [],
          headers: headerArray(r.requestHeaders),
          queryString,
          headersSize: -1,
          bodySize: r.postBody?.size ?? -1,
          ...(r.postDataText ? {
            postData: {
              mimeType: contentType(r.requestHeaders),
              text: r.postDataText,
            },
          } : {}),
        },
        response: {
          status: r.status || 0,
          statusText: r.statusText || "",
          httpVersion: r.protocol || "HTTP/0",
          cookies: [],
          headers: headerArray(r.responseHeaders),
          content: {
            size: r.body?.size ?? 0,
            mimeType: r.mimeType || contentType(r.responseHeaders) || "application/octet-stream",
            ...(text !== undefined ? { text } : {}),
            ...(encoding ? { encoding } : {}),
          },
          redirectURL: r.responseHeaders?.location || r.responseHeaders?.Location || "",
          headersSize: -1,
          bodySize: r.body?.size ?? -1,
          _jsRedoxBody: r.body || null,
          _jsRedoxBodyCapture: r.bodyCapture || null,
        },
        cache: {},
        timings: {
          blocked: -1,
          dns: -1,
          connect: -1,
          send: 0,
          wait: Math.max(0, (r.responseAt || r.finishedAt || r.startedAt) - (r.startedAt || 0)),
          receive: Math.max(0, (r.finishedAt || r.responseAt || 0) - (r.responseAt || r.finishedAt || 0)),
          ssl: -1,
        },
        pageref: r.frameUrl || undefined,
        _resourceType: r.resourceType,
        _initiator: r.initiator || null,
        _failure: r.failure || null,
        _requestId: r.id,
      };
    });

  return {
    log: {
      version: "1.2",
      creator: {
        name: "js-redox CloakBrowser recorder",
        version: "1",
      },
      pages: [],
      entries,
    },
  };
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  const out = path.resolve(
    opts.output || path.join(ROOT, "work", "captures", `${sanitizeHost(opts.url)}-${timestamp()}`),
  );
  const profileDir = path.join(out, "profile");
  const bodiesDir = path.join(out, "bodies");
  const runtimeDir = path.join(out, "runtime-scripts");
  const framesDir = path.join(out, "frames");

  await Promise.all([
    mkdir(out, { recursive: true }),
    mkdir(profileDir, { recursive: true }),
    mkdir(bodiesDir, { recursive: true }),
    mkdir(runtimeDir, { recursive: true }),
    mkdir(framesDir, { recursive: true }),
  ]);

  const bodyMemory = new Map();
  async function writeCas(buffer, extension = "") {
    const digest = sha256(buffer);
    const rel = path.posix.join("bodies", `${digest}${extension}`);
    if (!bodyMemory.has(rel)) {
      bodyMemory.set(rel, buffer);
      await writeFile(path.join(out, rel), buffer);
    }
    return { sha256: digest, size: buffer.length, path: rel };
  }

  const failures = [];
  const events = [];
  const networkRecords = [];
  const networkByRequest = new Map();
  const inflight = new Set();
  const jobs = new Set();
  const websocketEvents = [];
  const eventSourceEvents = [];
  const runtimeEvents = [];
  const runtimeScripts = new Map();
  const streamed = new Map();
  const cdpRequests = new Map();
  let nextRequest = 1;

  const queueJob = (promise, label) => {
    const job = Promise.resolve(promise)
      .catch((error) => failures.push({ at: Date.now(), label, error: String(error?.stack || error) }))
      .finally(() => jobs.delete(job));
    jobs.add(job);
    return job;
  };

  async function drainJobs() {
    while (jobs.size) await Promise.allSettled([...jobs]);
  }

  const browserOptions = {
    userDataDir: profileDir,
    headless: !opts.headed,
    humanize: true,
    viewport: { width: 1440, height: 1000 },
    serviceWorkers: "allow",
  };
  if (opts.proxy) browserOptions.proxy = opts.proxy;

  console.log(`[recorder] output: ${out}`);
  console.log(`[recorder] launching CloakBrowser`);

  const context = await launchPersistentContext(browserOptions);
  let page = context.pages()[0] || await context.newPage();
  page.setDefaultTimeout(opts.timeoutMs);

  // Playwright-level capture is deliberately retained in addition to CDP.
  // It sees OOPIF/subframe traffic that may live on a different CDP target.
  const ensureRequestRecord = (request) => {
    let record = networkByRequest.get(request);
    if (record) return record;

    record = {
      id: `pw-${nextRequest++}`,
      startedAt: Date.now(),
      method: request.method(),
      url: request.url(),
      resourceType: request.resourceType(),
      requestHeaders: {},
      responseHeaders: {},
      status: 0,
      statusText: "",
      mimeType: "",
      protocol: "",
      frameUrl: null,
      initiator: null,
      body: null,
      bodyCapture: null,
      postBody: null,
      postDataText: null,
      finishedAt: null,
      responseAt: null,
      failure: null,
    };
    try {
      record.frameUrl = request.frame().url();
    } catch {}
    try {
      record.postDataText = request.postData();
    } catch {}
    const postBuffer = request.postDataBuffer();
    if (postBuffer) {
      queueJob((async () => {
        record.postBody = await writeCas(postBuffer);
      })(), `post-body ${record.url}`);
    }

    networkByRequest.set(request, record);
    networkRecords.push(record);
    inflight.add(record.id);
    queueJob(withTimeout(request.allHeaders(), Math.min(opts.timeoutMs, 15_000), "request headers").then((h) => { record.requestHeaders = h; }), `request-headers ${record.url}`);
    return record;
  };

  context.on("request", (request) => {
    ensureRequestRecord(request);
  });

  context.on("response", (response) => {
    const request = response.request();
    const record = ensureRequestRecord(request);
    record.responseAt = Date.now();
    record.status = response.status();
    record.statusText = response.statusText();

    queueJob((async () => {
      try {
        record.responseHeaders = await withTimeout(response.allHeaders(), Math.min(opts.timeoutMs, 15_000), "response headers");
      } catch (error) {
        failures.push({ at: Date.now(), label: `response-headers ${record.url}`, error: String(error) });
      }
      record.mimeType = contentType(record.responseHeaders);

      const policy = shouldKeepBody(record, opts.allBodies);
      if (!policy.keep) {
        record.bodyCapture = { status: "skipped", reason: policy.reason, expected: policy.expected };
        return;
      }

      try {
        const body = await withTimeout(response.body(), Math.min(opts.timeoutMs, 15_000), "response body");
        if (body.length > opts.maxBodyMiB * 1024 * 1024) {
          record.bodyCapture = {
            status: "skipped",
            reason: "body-over-limit",
            expected: true,
            observedSize: body.length,
            limitMiB: opts.maxBodyMiB,
          };
          return;
        }
        record.body = await writeCas(body);
        record.bodyCapture = { status: "captured", channel: "playwright-response-body" };
      } catch (error) {
        record.bodyCapture = {
          status: "failed",
          reason: "playwright-response-body-failed",
          expected: true,
          error: String(error),
        };
      }
    })(), `response-body ${record.url}`);
  });

  context.on("requestfinished", (request) => {
    const record = ensureRequestRecord(request);
    record.finishedAt = Date.now();
    inflight.delete(record.id);
  });

  context.on("requestfailed", (request) => {
    const record = ensureRequestRecord(request);
    record.finishedAt = Date.now();
    record.failure = request.failure();
    inflight.delete(record.id);
  });

  page.on("websocket", (ws) => {
    const socketId = `pw-ws-${websocketEvents.length + 1}`;
    websocketEvents.push({ at: Date.now(), socketId, type: "created", url: ws.url() });
    ws.on("framesent", (event) => {
      websocketEvents.push({
        at: Date.now(),
        socketId,
        type: "sent",
        opcode: typeof event.payload === "string" ? 1 : 2,
        payload: typeof event.payload === "string" ? event.payload : event.payload.toString("base64"),
        base64: typeof event.payload !== "string",
      });
    });
    ws.on("framereceived", (event) => {
      websocketEvents.push({
        at: Date.now(),
        socketId,
        type: "received",
        opcode: typeof event.payload === "string" ? 1 : 2,
        payload: typeof event.payload === "string" ? event.payload : event.payload.toString("base64"),
        base64: typeof event.payload !== "string",
      });
    });
    ws.on("socketerror", (error) => websocketEvents.push({
      at: Date.now(), socketId, type: "error", error: String(error),
    }));
    ws.on("close", () => websocketEvents.push({ at: Date.now(), socketId, type: "closed" }));
  });

  page.on("console", (message) => {
    runtimeEvents.push({
      at: Date.now(),
      type: "console",
      level: message.type(),
      text: message.text(),
      location: message.location(),
    });
  });

  page.on("pageerror", (error) => {
    runtimeEvents.push({
      at: Date.now(),
      type: "pageerror",
      error: String(error?.stack || error),
    });
  });

  page.on("worker", (worker) => {
    const row = { at: Date.now(), type: "worker-created", url: worker.url() };
    runtimeEvents.push(row);
    worker.on("close", () => runtimeEvents.push({
      at: Date.now(),
      type: "worker-closed",
      url: worker.url(),
    }));
  });

  if (opts.consent) {
    const injected = await readFile(path.join(HERE, "autoconsent.inject.js"), "utf8");
    await context.addInitScript({
      content: `${injected}\n//# sourceURL=js-redox-recorder://autoconsent.js`,
    });
  }

  const cdp = await context.newCDPSession(page);
  await Promise.all([
    cdp.send("Page.enable"),
    cdp.send("Runtime.enable"),
    cdp.send("Debugger.enable"),
    cdp.send("Log.enable"),
    cdp.send("Network.enable", {
      maxTotalBufferSize: 512 * 1024 * 1024,
      maxResourceBufferSize: 128 * 1024 * 1024,
      maxPostDataSize: 16 * 1024 * 1024,
      enableDurableMessages: true,
    }),
  ]);
  if (!opts.keepCache) await cdp.send("Network.setCacheDisabled", { cacheDisabled: true });

  cdp.on("Network.requestWillBeSent", (event) => {
    cdpRequests.set(event.requestId, {
      method: event.request.method,
      url: event.request.url,
      requestHeaders: event.request.headers,
      postData: event.request.postData || null,
      initiator: event.initiator || null,
      documentURL: event.documentURL || null,
      frameId: event.frameId || null,
      resourceType: event.type || null,
    });
  });

  // CDP streaming starts at responseReceived, before normal HAR export could evict
  // response content from Chromium's inspector cache.
  cdp.on("Network.responseReceived", (event) => {
    const request = cdpRequests.get(event.requestId) || {};
    const record = {
      requestId: event.requestId,
      url: event.response.url,
      status: event.response.status,
      mimeType: event.response.mimeType,
      resourceType: event.type,
      responseHeaders: event.response.headers,
      method: request.method || "GET",
      requestHeaders: request.requestHeaders || {},
      postData: request.postData || null,
      initiator: request.initiator || null,
      documentURL: request.documentURL || null,
      frameId: request.frameId || null,
      chunks: [],
      streamEnabled: false,
      streamStart: null,
      body: null,
      error: null,
    };
    streamed.set(event.requestId, record);

    const policy = shouldKeepBody(record, opts.allBodies);
    if (!policy.keep) {
      record.error = `skipped:${policy.reason}`;
      return;
    }

    record.streamStart = (async () => {
      try {
        const result = await withTimeout(cdp.send("Network.streamResourceContent", { requestId: event.requestId }), Math.min(opts.timeoutMs, 15_000), "streamResourceContent");
        if (result.bufferedData) record.chunks.push(Buffer.from(result.bufferedData, "base64"));
        record.streamEnabled = true;
      } catch (error) {
        record.error = `streamResourceContent:${String(error)}`;
      }
    })();
    queueJob(record.streamStart, `stream-start ${record.url}`);
  });

  cdp.on("Network.dataReceived", (event) => {
    const record = streamed.get(event.requestId);
    if (!record?.streamEnabled || !event.data) return;
    record.chunks.push(Buffer.from(event.data, "base64"));
  });

  cdp.on("Network.loadingFinished", (event) => {
    const record = streamed.get(event.requestId);
    if (!record) return;
    queueJob((async () => {
      if (record.streamStart) await record.streamStart;
      if (!record.streamEnabled) return;
      const body = Buffer.concat(record.chunks);
      if (body.length > opts.maxBodyMiB * 1024 * 1024) {
        record.error = `body-over-limit:${body.length}`;
        record.chunks = [];
        return;
      }
      record.body = await writeCas(body);
      record.chunks = [];
    })(), `stream-finish ${record.url}`);
  });

  cdp.on("Network.loadingFailed", (event) => {
    const record = streamed.get(event.requestId);
    if (record) {
      record.error = `loadingFailed:${event.errorText}`;
      record.chunks = [];
    }
  });

  cdp.on("Network.eventSourceMessageReceived", (event) => {
    eventSourceEvents.push({ at: Date.now(), ...safeJson(event) });
  });

  cdp.on("Log.entryAdded", ({ entry }) => {
    runtimeEvents.push({ at: Date.now(), type: "cdp-log", entry: safeJson(entry) });
  });

  cdp.on("Runtime.exceptionThrown", (event) => {
    runtimeEvents.push({ at: Date.now(), type: "exception", event: safeJson(event) });
  });

  cdp.on("Debugger.scriptParsed", (script) => {
    const url = script.url || "";
    if (url.startsWith("js-redox-recorder://")) return;
    const key = `${script.scriptId}:${script.hash || ""}`;
    if (runtimeScripts.has(key)) return;

    const row = {
      scriptId: script.scriptId,
      url,
      hash: script.hash || null,
      sourceMapURL: script.sourceMapURL || null,
      startLine: script.startLine,
      startColumn: script.startColumn,
      endLine: script.endLine,
      endColumn: script.endColumn,
      executionContextId: script.executionContextId,
      executionContextAuxData: safeJson(script.executionContextAuxData || null),
      stackTrace: safeJson(script.stackTrace || null),
      isModule: script.isModule,
      hasSourceURL: script.hasSourceURL,
      isLiveEdit: script.isLiveEdit || false,
      scriptLanguage: script.scriptLanguage || null,
      buildId: script.buildId || null,
      embedderName: script.embedderName || null,
      length: script.length || null,
      captured: null,
      error: null,
    };
    runtimeScripts.set(key, row);

    queueJob((async () => {
      try {
        const result = await withTimeout(cdp.send("Debugger.getScriptSource", { scriptId: script.scriptId }), Math.min(opts.timeoutMs, 15_000), "getScriptSource");
        if (typeof result.scriptSource === "string" && result.scriptSource.length > 0) {
          const buffer = Buffer.from(result.scriptSource, "utf8");
          if (buffer.length <= opts.maxBodyMiB * 1024 * 1024) {
            const digest = sha256(buffer);
            const rel = path.posix.join("runtime-scripts", `${digest}.js`);
            await writeFile(path.join(out, rel), buffer);
            row.captured = { sha256: digest, size: buffer.length, path: rel, kind: "javascript" };
          } else {
            row.error = `script-over-limit:${buffer.length}`;
          }
        } else if (script.scriptLanguage === "WebAssembly") {
          const wasm = await withTimeout(cdp.send("Debugger.getWasmBytecode", { scriptId: script.scriptId }), Math.min(opts.timeoutMs, 15_000), "getWasmBytecode");
          if (wasm.bytecode) {
            const buffer = Buffer.from(wasm.bytecode, "base64");
            const digest = sha256(buffer);
            const rel = path.posix.join("runtime-scripts", `${digest}.wasm`);
            await writeFile(path.join(out, rel), buffer);
            row.captured = { sha256: digest, size: buffer.length, path: rel, kind: "wasm" };
          }
        }
      } catch (error) {
        row.error = String(error);
      }
    })(), `script-source ${url || script.scriptId}`);
  });

  let navigationError = null;
  events.push({ at: Date.now(), type: "navigation-start", url: opts.url });
  console.log(`[recorder] navigating: ${opts.url}`);
  try {
    await page.goto(opts.url, {
      waitUntil: "domcontentloaded",
      timeout: opts.timeoutMs,
    });
  } catch (error) {
    navigationError = String(error);
    failures.push({ at: Date.now(), label: "navigation", error: navigationError });
    console.warn(`[recorder] navigation warning: ${navigationError}`);
  }
  events.push({ at: Date.now(), type: "navigation-domcontentloaded-or-timeout", url: page.url() });

  await sleep(800);

  let consent = { enabled: opts.consent, beforeFallback: [], fallbackClicks: [], afterFallback: [] };
  if (opts.consent) {
    console.log(`[recorder] allowing AutoConsent ${opts.consentMs} ms`);
    await sleep(opts.consentMs);
    consent.beforeFallback = await getAutoConsentState(page);

    const successfulAutoClick = consent.beforeFallback.some((row) =>
      ["optInSucceeded", "runningOptIn"].includes(row.state?.lifecycle) ||
      (row.state?.clicks || 0) > 0
    );

    if (!successfulAutoClick) {
      consent.fallbackClicks = await clickConsentFallback(page);
      if (consent.fallbackClicks.some((row) => row.clicked)) await sleep(1200);
    }
    consent.afterFallback = await getAutoConsentState(page);
  }

  console.log(`[recorder] scrolling to exercise lazy page/ad loading`);
  const scroll = await humanScroll(page, opts, events);

  console.log(`[recorder] waiting for network quiescence`);
  const networkQuiet = await waitForNetworkQuiet(inflight, Math.min(1500, opts.settleMs), opts.settleMs);
  await sleep(500);

  // One final bottom poke catches IntersectionObserver/ad slots that arm on the last paint.
  try {
    await page.evaluate(() => scrollTo({ top: document.documentElement.scrollHeight, behavior: "instant" }));
    await sleep(800);
  } catch {}
  await waitForNetworkQuiet(inflight, 700, 2500);

  await drainJobs();

  // Requests that intentionally remain open (streaming endpoints, long polling) are
  // represented rather than silently disappearing.
  const finishedAt = Date.now();
  for (const record of networkRecords) {
    if (!record.finishedAt) record.inflightAtFinish = true;
  }

  console.log(`[recorder] saving DOM, MHTML, state and manifests`);

  const frameRows = [];
  for (let i = 0; i < page.frames().length; i += 1) {
    const frame = page.frames()[i];
    const row = {
      index: i,
      url: frame.url(),
      name: frame.name(),
      parentUrl: frame.parentFrame()?.url() || null,
      html: null,
      storage: null,
      errors: [],
    };

    try {
      const html = await frame.content();
      const rel = path.posix.join("frames", `${String(i).padStart(3, "0")}.html`);
      await writeFile(path.join(out, rel), html);
      row.html = rel;
    } catch (error) {
      row.errors.push(`content:${String(error)}`);
    }

    try {
      row.storage = await frame.evaluate(() => {
        const dump = (storage) => {
          const result = {};
          for (let i = 0; i < storage.length; i += 1) {
            const key = storage.key(i);
            result[key] = storage.getItem(key);
          }
          return result;
        };
        return {
          origin: location.origin,
          localStorage: dump(localStorage),
          sessionStorage: dump(sessionStorage),
        };
      });
    } catch (error) {
      row.errors.push(`storage:${String(error)}`);
    }
    frameRows.push(row);
  }

  let mhtml = null;
  try {
    const snapshot = await withTimeout(cdp.send("Page.captureSnapshot", { format: "mhtml" }), Math.min(opts.timeoutMs, 15_000), "captureSnapshot");
    mhtml = "page.mhtml";
    await writeFile(path.join(out, mhtml), snapshot.data);
  } catch (error) {
    failures.push({ at: Date.now(), label: "mhtml", error: String(error) });
  }

  let screenshot = null;
  if (opts.screenshot) {
    try {
      screenshot = "page.png";
      await page.screenshot({ path: path.join(out, screenshot), fullPage: true });
    } catch (error) {
      failures.push({ at: Date.now(), label: "screenshot", error: String(error) });
    }
  }

  let storageState = null;
  try {
    storageState = await context.storageState({ indexedDB: true });
  } catch {
    storageState = await context.storageState();
  }
  await writeFile(path.join(out, "storage-state.json"), JSON.stringify(storageState, null, 2));

  await drainJobs();

  // Recover a body missed by Playwright from the independent early CDP stream,
  // but only when the exact method/status/URL key has one observed byte value.
  // This avoids silently assigning the wrong body to repeated dynamic requests.
  const responseKey = (row) => JSON.stringify([row.method || "GET", row.status, row.url]);
  const cdpBodiesByKey = new Map();
  for (const row of streamed.values()) {
    if (!row.body) continue;
    const key = responseKey(row);
    if (!cdpBodiesByKey.has(key)) cdpBodiesByKey.set(key, new Map());
    cdpBodiesByKey.get(key).set(row.body.path, row);
  }
  for (const record of networkRecords) {
    if (record.body || record.status <= 0) continue;
    const policy = shouldKeepBody(record, opts.allBodies);
    if (!policy.expected) continue;
    const variants = cdpBodiesByKey.get(responseKey(record));
    if (!variants || variants.size !== 1) continue;
    const stream = variants.values().next().value;
    record.body = stream.body;
    record.bodyCapture = {
      status: "captured",
      channel: "cdp-streamResourceContent-recovery",
      recoveredFrom: stream.requestId,
    };
  }

  const streamRows = [...streamed.values()].map((row) => ({
    requestId: row.requestId,
    url: row.url,
    status: row.status,
    mimeType: row.mimeType,
    resourceType: row.resourceType,
    responseHeaders: row.responseHeaders,
    method: row.method,
    requestHeaders: row.requestHeaders,
    postData: row.postData,
    initiator: row.initiator,
    documentURL: row.documentURL,
    frameId: row.frameId,
    body: row.body,
    error: row.error,
  }));

  const expectedBodies = networkRecords.filter((r) => shouldKeepBody(r, opts.allBodies).expected && r.status > 0);
  const missingBodies = expectedBodies.filter((r) => !r.body);
  const failedBodies = expectedBodies.filter((r) => r.bodyCapture?.status === "failed");

  const summary = {
    requests: networkRecords.length,
    responses: networkRecords.filter((r) => r.status > 0).length,
    capturedResponseBodies: networkRecords.filter((r) => r.body).length,
    expectedRelevantBodies: expectedBodies.length,
    missingRelevantBodies: missingBodies.length,
    failedRelevantBodies: failedBodies.length,
    cdpStreams: streamRows.length,
    capturedCdpStreams: streamRows.filter((r) => r.body).length,
    runtimeScriptsSeen: runtimeScripts.size,
    runtimeScriptsCaptured: [...runtimeScripts.values()].filter((r) => r.captured).length,
    websocketEvents: websocketEvents.length,
    eventSourceEvents: eventSourceEvents.length,
    frames: frameRows.length,
    networkQuiet,
  };

  await Promise.all([
    writeFile(path.join(out, "network.json"), JSON.stringify(networkRecords, null, 2)),
    writeFile(path.join(out, "cdp-streams.json"), JSON.stringify(streamRows, null, 2)),
    writeFile(path.join(out, "runtime-scripts.json"), JSON.stringify([...runtimeScripts.values()], null, 2)),
    writeFile(path.join(out, "websockets.json"), JSON.stringify(websocketEvents, null, 2)),
    writeFile(path.join(out, "eventsource.json"), JSON.stringify(eventSourceEvents, null, 2)),
    writeFile(path.join(out, "runtime-events.json"), JSON.stringify(runtimeEvents, null, 2)),
    writeFile(path.join(out, "events.json"), JSON.stringify(events, null, 2)),
    writeFile(path.join(out, "frames.json"), JSON.stringify(frameRows, null, 2)),
    writeFile(path.join(out, "failures.json"), JSON.stringify(failures, null, 2)),
    writeFile(path.join(out, "capture.har"), JSON.stringify(buildHar(networkRecords, bodyMemory))),
  ]);

  const manifest = {
    schema: "js-redox-cloak-capture/v1",
    createdAt: new Date().toISOString(),
    requestedUrl: opts.url,
    finalUrl: page.url(),
    navigationError,
    options: {
      ...opts,
      output: undefined,
      proxy: opts.proxy ? "<configured>" : null,
    },
    consent,
    scroll,
    summary,
    completeness: {
      relevantNetworkBodiesComplete: missingBodies.length === 0,
      missingRelevantBodies: missingBodies.map((r) => ({
        id: r.id,
        method: r.method,
        url: r.url,
        status: r.status,
        resourceType: r.resourceType,
        mimeType: r.mimeType,
        bodyCapture: r.bodyCapture,
        inflightAtFinish: r.inflightAtFinish || false,
      })),
      note: "Playwright response.body is the cross-frame body channel; CDP streamResourceContent is an independent early-stream channel for the main target. Runtime Debugger capture preserves eval/inline/blob-created script source when Chromium exposes it.",
    },
    artifacts: {
      har: "capture.har",
      bodies: "bodies/",
      network: "network.json",
      cdpStreams: "cdp-streams.json",
      runtimeScripts: "runtime-scripts/",
      runtimeScriptManifest: "runtime-scripts.json",
      frames: "frames/",
      frameManifest: "frames.json",
      mhtml,
      screenshot,
      storageState: "storage-state.json",
      websockets: "websockets.json",
      eventSource: "eventsource.json",
      runtimeEvents: "runtime-events.json",
      failures: "failures.json",
    },
    limitations: [
      "Runtime Debugger capture is attached to the main page target; worker-created eval source may require a worker-target session in a future revision.",
      "Bodies larger than maxBodyMiB are intentionally reported but not persisted unless the limit is increased.",
      "Image/media/font bodies are intentionally omitted unless --all-bodies is used.",
    ],
  };

  await writeFile(path.join(out, "recorder-manifest.json"), JSON.stringify(manifest, null, 2));
  await writeFile(path.join(out, "README.txt"), [
    "js-redox CloakBrowser capture",
    `requested: ${opts.url}`,
    `final: ${page.url()}`,
    `relevant body completeness: ${manifest.completeness.relevantNetworkBodiesComplete}`,
    `requests: ${summary.requests}`,
    `captured response bodies: ${summary.capturedResponseBodies}`,
    `runtime scripts captured: ${summary.runtimeScriptsCaptured}`,
    "",
    "Feed capture.har to the existing js-redox capture pipeline:",
    `uv run python scripts/capture-to-project.py ${path.relative(ROOT, path.join(out, "capture.har"))} work/capture-project`,
    "",
  ].join("\n"));

  console.log(`[recorder] summary: ${JSON.stringify(summary)}`);
  if (missingBodies.length) {
    console.warn(`[recorder] WARNING: ${missingBodies.length} relevant response body/bodies were not captured; see recorder-manifest.json`);
  } else {
    console.log(`[recorder] all eligible relevant response bodies captured`);
  }

  await context.close();
  console.log(`[recorder] done: ${out}`);
}

main().catch((error) => {
  console.error(error?.stack || error);
  process.exitCode = 1;
});
