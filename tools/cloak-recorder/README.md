# CloakBrowser capture recorder

`recorder.mjs` drives a fresh persistent CloakBrowser profile, accepts consent,
scrolls through the page to exercise lazy/ad loading, and writes a provenance-rich
capture for `js-redox`. Scrolling tolerates bounded page-initiated navigation/context
churn and records every retry instead of aborting the capture on a transient context loss.

## Run

```bash
cd tools/cloak-recorder
npm install
npm run record -- https://example.com
```

Useful options:

```bash
npm run record -- https://example.com \
  --headed \
  --scroll-passes 2 \
  --max-scroll-steps 120 \
  --max-body-mib 64 \
  -o ../../work/captures/example
```

`--all-bodies` additionally keeps images, media and fonts. `--proxy` is passed to
CloakBrowser. HTTP cache is disabled by default so a capture does not silently
depend on an old profile response.

## Consent

The build bundles DuckDuckGo `@duckduckgo/autoconsent` and its maintained rules
into an init script that exists before navigation. The recorder asks AutoConsent
for opt-in behavior because the goal is to exercise the page after advertising
consent. It enables generated rules and heuristic detection.

AutoConsent is bounded by the recorder's own timer; the capture does not wait
forever for a CMP that is absent or broken. If AutoConsent did not act, a
conservative cross-frame exact-text fallback clicks common "accept all" phrases.

## Capture channels

The recorder intentionally uses overlapping channels instead of trusting a HAR
export after the fact:

- Playwright request/response events retain request metadata and immediately
  request response bodies. This is the cross-frame/OOPIF path.
- CDP `Network.streamResourceContent` starts at `responseReceived` for the main
  target, every out-of-process iframe target, and auto-attached worker-like target,
  streaming bytes as they arrive and reducing dependence on Chromium's inspector
  response cache. If streaming loses a race with a completed binary response, a
  base64 `Network.getResponseBody` result is accepted as an exact-byte fallback;
  decoded-text fallbacks are deliberately not promoted to exact bytes. Worker
  targets enable Network before Runtime/Debugger so their first fetch retains its
  exact initiator stack.
- CDP `Debugger.scriptParsed` + `getScriptSource` retain runtime/eval/inline/blob
  JavaScript from the main page, out-of-process iframe targets, and Chromium
  worker-like targets even when it never exists as a network response.
  `scriptParsed` generation stack traces and execution-context auxiliary data are
  retained so nested `eval`/Function children can be linked back to the captured
  script that compiled them.
- WebSocket frames and SSE/EventSource messages are recorded separately.
- Final per-frame DOM, MHTML, cookies/localStorage/sessionStorage/IndexedDB state,
  console/exception data and a screenshot are retained. `frames.json` also keeps
  each frame's `document.characterSet` plus external script `src`/`charset`/`type`
  metadata so classic-script byte decoding can be reconstructed when CDP source
  capture is unavailable.
- Network bodies are content-addressed by SHA-256. The generated `capture.har`
  embeds bodies needed by the existing importer and points back to capture
  status/provenance.

By default the body policy keeps script, document, stylesheet, fetch/XHR, JSON,
WASM/octet-stream and unknown response types while omitting obvious images,
media, fonts and PDF. Every eligible response is represented in the manifest
with capture success/failure. A response that Chromium explicitly aborts after headers, or
that is still in flight when the capture window ends, is reported separately from a completed
response whose body was lost; only the latter makes the relevant-body completeness check fail.

If the top page/context/browser target closes itself after acquisition has begun, the recorder emits a `salvaged: true` partial bundle instead of discarding already captured evidence. Network/CDP/runtime/HAR/failure artifacts are drained and written normally; unavailable final-page artifacts such as frame HTML, MHTML, screenshot or storage state are represented as missing/null and the terminal-close phase is retained in `salvageReason`. Non-target-close recorder errors still fail normally.

## Feed into js-redox

```bash
uv run python scripts/capture-to-project.py \
  work/captures/example/capture.har \
  work/example-project
```

Keep raw captures under `work/` or the private corpus; do not commit real captured
site bodies to the public repository.

## Worker-target coverage

The recorder uses Chromium Target auto-attach for dedicated, shared, service and
worklet-style worker targets. First-level worker targets are attached before page
navigation and arrive paused; Network capture is enabled first, then
Debugger/Runtime, then the worker resumes. This keeps their earliest fetches, CDP
initiator stacks, and worker-local generated script source in the same
session-scoped provenance model as page/OOPIF capture.

Worker sessions also install recursive auto-attach for child workers. Chromium can
report a recursively created child as already running while that policy is being
installed; those sessions are still captured, but the manifest counts them as
`workerCdpSessionsUnpausedAtAttach` and does not claim early-event completeness for
them. Observed events remain exact evidence. Playwright response capture remains
the cross-target byte fallback when Chromium does not expose a corresponding
target/session.
