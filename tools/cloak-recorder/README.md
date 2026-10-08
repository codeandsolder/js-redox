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
  target and every out-of-process iframe target, streaming bytes as they arrive
  and reducing dependence on Chromium's inspector response cache.
- CDP `Debugger.scriptParsed` + `getScriptSource` retain runtime/eval/inline/blob
  JavaScript from the main page and out-of-process iframe targets even when it
  never exists as a network response. `scriptParsed` generation stack
  traces and execution-context auxiliary data are retained so nested `eval`/Function
  children can be linked back to the captured script that compiled them.
- WebSocket frames and SSE/EventSource messages are recorded separately.
- Final per-frame DOM, MHTML, cookies/localStorage/sessionStorage/IndexedDB state,
  console/exception data and a screenshot are retained.
- Network bodies are content-addressed by SHA-256. The generated `capture.har`
  embeds bodies needed by the existing importer and points back to capture
  status/provenance.

By default the body policy keeps script, document, stylesheet, fetch/XHR, JSON,
WASM/octet-stream and unknown response types while omitting obvious images,
media, fonts and PDF. Every eligible response is represented in the manifest
with capture success/failure. A response that Chromium explicitly aborts after headers is
reported separately from a completed response whose body was lost; only the latter makes the
relevant-body completeness check fail.

## Feed into js-redox

```bash
uv run python scripts/capture-to-project.py \
  work/captures/example/capture.har \
  work/example-project
```

Keep raw captures under `work/` or the private corpus; do not commit real captured
site bodies to the public repository.

## Known gap

The main-page and out-of-process-iframe debugger sessions capture runtime-created
scripts for page/frame targets. Dedicated/shared/service-worker target-local `eval`
source is not yet attached with its own debugger session. Their network-fetched
scripts are still captured normally. If a corpus sample proves worker-local
generated code matters, add worker-target sessions rather than pretending the
current capture is complete.
