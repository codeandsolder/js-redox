# CloakBrowser capture recorder

`recorder.mjs` drives a fresh persistent CloakBrowser profile, accepts consent,
scrolls through the page to exercise lazy/ad loading, and writes a provenance-rich
capture for `js-redox`.

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
  target and streams bytes as they arrive, reducing dependence on Chromium's
  inspector response cache.
- CDP `Debugger.scriptParsed` + `getScriptSource` retain runtime/eval/inline/blob
  JavaScript that may never exist as a network response.
- WebSocket frames and SSE/EventSource messages are recorded separately.
- Final per-frame DOM, MHTML, cookies/localStorage/sessionStorage/IndexedDB state,
  console/exception data and a screenshot are retained.
- Network bodies are content-addressed by SHA-256. The generated `capture.har`
  embeds bodies needed by the existing importer and points back to capture
  status/provenance.

By default the body policy keeps script, document, stylesheet, fetch/XHR, JSON,
WASM/octet-stream and unknown response types while omitting obvious images,
media, fonts and PDF. Every eligible response is represented in the manifest
with capture success/failure; missing relevant bodies are never silently treated
as a complete capture.

## Feed into js-redox

```bash
uv run python scripts/capture-to-project.py \
  work/captures/example/capture.har \
  work/example-project
```

Keep raw captures under `work/` or the private corpus; do not commit real captured
site bodies to the public repository.

## Known gap

The main-page debugger session captures runtime-created scripts for the page
target. Dedicated/shared/service-worker target-local `eval` source is not yet
attached with its own debugger session. Their network-fetched scripts are still
captured normally. If a corpus sample proves worker-local generated code matters,
add target auto-attach rather than pretending the current capture is complete.
