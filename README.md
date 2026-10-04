# js_devirtualization

Reusable static JavaScript VM devirtualization research and tooling.

## Layout

- `data/` — original uploaded archives.
- `corpus/taobao/` — extracted real-world Fireye / ET samples.
- `corpus/generated/` — source ↔ virtualized ground-truth pairs.
- `corpus/manifest.json` — asserted positive/negative regression corpus.
- `src/jsvm-lift/` — Rust/Oxc detector and lifter prototype.
- `scripts/` — build, benchmark, width-consensus and bytecode inspection helpers.
- `third_party/` — pinned reference implementations / corpus generators.
- `work/` — disposable derived analysis output.

## Build

The Rust code is one Cargo workspace (`jsvm-safe-core` + `jsvm-lift`) with a single root `Cargo.lock` and shared dependency-version pins. Whole-workspace correctness gates are therefore ordinary Cargo commands:

```sh
cargo fmt --all -- --check
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

For normal executable builds, use the project helper rather than raw `cargo`:

```sh
scripts/build-jsvm-lift.sh
```

It pins rustc 1.98.1, preserves the distributed sccache wrapper, derives build parallelism from live farm capacity, and publishes durable executables under `.cargo-target-nodebug/`. The helper asks Cargo for the workspace target directory rather than assuming a member-local `target/` layout.

## Regression

```sh
uv run python scripts/benchmark-jsvm-lift.py
```

The harness asserts structural VM detection for generated/real VM positives, zero confirmed dispatchers for negatives/CFF-only samples, and exact stdout equivalence for generated source/virtualized pairs.

## Suspicious-structure triage

`sus-scan` is the cheap first-pass structural scanner used to rank code before deeper recovery. General AST-level obfuscation structures live in `src/jsvm-lift/src/bin/sus-scan/structures.rs` rather than being mixed into the scoring collector.

The structure module uses small detector registries by AST node type. Detectors emit explainable `StructuralSignal` records; the main scanner owns clustering, weighting and output. New families should therefore be added as a detector plus positive/control fixtures in `corpus/generated/sus-scanner/`, without vendor-name checks.

Current structural families include same-array rotation (`x.push(x.shift())`, including literal bracket members), checksum-driven rotation bootstraps, dense operator/call proxy tables, self-disabling one-shot wrapper factories, direct literal-table decoders, tiny mixed-boolean-arithmetic helpers, and numeric selector dispatchers. Low-level evidence may deliberately remain below the standalone cluster threshold; repeated evidence or a stronger composite structure promotes the region.

Coverage is intentionally measured separately from generic suspicion scoring. On the 47-file real corpus plus 3 VM hard negatives, the simple scanner and structural scanner both cluster 49/50 files, but the structural layer names concrete obfuscation families in 17 files (16 real + the Yandex VM-negative that genuinely contains a rotation bootstrap). That named coverage is the useful metric because the families map directly onto safe deobfuscation passes such as table decoding, pure-helper evaluation, and selector specialization.

## Current pipeline

The target is a provenance-preserving **browser capture -> readable source project** pipeline, with VM devirtualization as one transformation stage rather than the whole product.

```text
HAR or browser "Webpage, Complete" capture
  ↓
capture normalization + exact raw resources/
  ↓
HTML inline-script extraction + source/source-map/module references
  ↓
document import-map normalization + scoped/bare-specifier resolution
  ↓
Oxc parse/codegen validation into readable src/
  ↓
safe static deobfuscation from exact captured bytes + formatted src/_readable/
  ↓
Webpack/Next chunk/direct-table + named global/member-loader module recovery into src/_modules/
  ↓
static generated-code recovery (Function(...) today; eval-like forms next)
  ↓
bounded recursive safe recovery + scanning of generated-code bodies
  ↓
VM/CFF detection + switch/table semantic IR
  ↓
role-normalized devirtualization where the dispatcher linkage is proven
  ↓
readable recovered modules + analysis/provenance graph
```

The directory contract is intentionally simple:

- `resources/` preserves captured response bodies or saved-page files exactly.
- `src/` contains parser-validated/readable or recovered source.
- `src/_deobfuscated/` contains semantics-preserving recovery from the exact captured JS bytes.
- `src/_readable/` is the formatted human-facing view of those safe-deobfuscated outputs.
- `src/_modules/` contains explicit Webpack/Next modules from chunk/direct-table shapes plus named factories recovered from global AMD `define("name", [...], factory)` and structurally proven member-loader calls such as `LWR.define(...)`, `Ya.define(...)`, or local `.define + .require/.loadModules` loaders.
- `src/_dynamic_deobfuscated/` contains proven safe recovery of generated-code children; exact recovered bytes remain the fallback when validation refuses a child.
- `src/_dynamic/` contains formatted analyst views of generated-code children after the selected safe stage.
- `src/_devirtualized/` contains semantic modules and pseudocode for supported direct-switch and function-table VMs.
- `analysis/` contains machine-readable provenance, import-map/module-resolution state, VM evidence and transform metadata.

This separation is important: presentation/deobfuscation passes never overwrite the original capture or make provenance ambiguous.

### Capture-to-project prototype

Build the Rust tools, then use the one-command driver:

```sh
uv run python scripts/capture-to-project.py capture.har work/capture-project
uv run python scripts/capture-to-project.py "Saved Page.html" work/saved-project
# Large captures / intentional oversubscription of content-only subprocess stages:
uv run python scripts/capture-to-project.py capture.har work/capture-project --jobs 8
```

For a normal browser **Save Page / Webpage, Complete** export, the companion `Saved Page_files/` directory is discovered automatically. `--assets-dir` can override it. Saved-page files get stable synthetic URLs for graph resolution; an original page URL from Chromium's `saved from url=(...)` marker is retained separately when available.

The driver runs capture normalization, readable-source materialization, source-map recovery, literal module/worker reference analysis, document import-map resolution, safe deobfuscation, explicit bundle-module extraction, generated-code recovery, VM triage/devirtualization, provenance-graph construction, and an analyst-facing project README. Import maps are resolved with exact, prefix and scoped mappings; multiple maps keep earlier exact definitions, and document context is propagated only through captured module imports so worker graphs do not accidentally inherit page import maps.

`har-project` remains the HAR-specific importer. `saved-page-to-manifest.py` performs the equivalent normalization for saved HTML plus its resource directory. Both converge on the same internal resource/inline-script model. The stage ordering and tool wiring live in importable `scripts/capture_pipeline.py`; `capture-to-project.py` is the supported CLI front door, while the older `har-to-project.py` is retained only as a thin HAR-only compatibility wrapper over that same core.

`materialize-har-source.py` produces the readable `src/` tree. JavaScript is parsed and regenerated by Oxc; parse failures fall back to the exact raw body and are recorded rather than silently discarded. Inline browser `<script>` blocks are classified by their HTML script type: classic/module JavaScript is executable, `importmap`/`speculationrules`/JSON MIME types are structured data, and other non-JavaScript script blocks remain inert text. Content-only work is keyed by exact SHA-256 and parallelized: identical JS bodies are formatted once and the derived result is materialized for every captured occurrence with explicit reuse provenance. Fuzzy similarity is never treated as semantic equivalence; request-specific GTM/config variants and randomized challenge code remain distinct.

`materialize-bundle-modules.py` treats Oxc spans as UTF-8 byte offsets against the exact derived JS bytes, clears and reproducibly rebuilds `src/_modules/`, keeps captured Webpack IDs or explicit named-loader module names as canonical identity, places direct Webpack tables under `module-table-NN/`, global AMD factories under `amd-modules/`, and member-loader factories under `member-named-modules/`. Bundle inventory is also exact-content keyed, so duplicate safe-deobfuscated bodies are parsed once. Extracted module wrappers are formatted in parallel from provenance-neutral templates; exact duplicate templates share one formatter invocation, then each output receives its own parent/span provenance line. `bundle-unpack` accepts bare or parenthesized Webpack function/arrow wrappers, global named AMD `define("name", [deps...], factory)` calls, and structurally module-like member calls such as Salesforce LWR, Yandex `Ya.define`, and Amazon APS. Unresolved global member loaders are keyed by their stable global path; resolved local objects remain conservative and need loader evidence (`define` with `require`/`requirejs`, or `define` with `loadModules` and multiple named factories). Dependency arrays are authoritative; `require`/`exports`/`module` pseudo-dependencies are mapped to their actual factory parameters before scope-aware export collection, so parameter renaming does not lose exports and shadowed nested bindings do not invent edges. DOM registries such as `customElements.define(...)` do not match because they lack the required dependency/factory module shape. Named exports and static `module.exports` writes are carried into `analysis/bundles.json`, provenance-graph nodes, module-file headers, and the generated `src/_modules/README.md` navigation index. Cross-bundle graph resolution also keeps embedded direct object module tables in their private namespace: a direct table wholly inside the source module is excluded as a candidate for that source module's outer-loader dependency, while nested JSONP chunk registrations remain eligible.

Safe deobfuscation resolves ambiguous JavaScript as browser Script vs ES Module from syntax/semantic validation before rewriting, then pins that resolved source mode across all iterations; CommonJS is only a fallback for genuinely CJS-only syntax. This avoids rejecting valid classic-script patterns such as duplicate top-level function declarations merely because they are invalid under module strictness. Classic scripts containing `with` still fail closed before any semantic rewrite because identifier resolution inside `with` is environment-dependent; they can continue through the separately proven string-recovery stage instead.

The string-recovery CLI likewise reads and writes explicit UTF-8 bytes rather than newline-normalizing text I/O, so unchanged CRLF captures remain byte-identical and hash/provenance validation stays exact.

`scan-har-project.py` prefers a proven safe-deobfuscated view for captured units while retaining the captured file as provenance. Static `Function(...)` payloads become bounded recursive code units: each exact recovered child is passed through the same safe string-recovery + deob stack, hash/provenance validated, and scanned from the furthest proven-safe result. Static string recovery includes the existing Base64/RC4 families plus a strict rotated-Base91 scaffold. The expensive Base91 array/scope proof is entered only when the source contains the necessary quoted 91-character / 91-unique-symbol alphabet; ordinary large application bundles therefore skip it in a linear preflight. Base91 recovery proves the rotation and decoder arithmetic, tracks lexical scope (including constructor, quoted/computed method and block-arrow scopes), tolerates uniquely provable affine/CFF hiding of its constants, and can solve control-flow-flattened constant lookups only when their exact Base91 semantic positions uniquely determine the hidden table state; it rewrites only ASCII-safe decoded strings. Proven read-only literal `const` tables may then expose numeric string fragments while dynamic reads are preserved; mutation, aliasing or escaping rejects the table. Recovery is iterated to a bounded fixed point so a first pass can expose a method name such as `run` and a later pass can safely discover a decoder local to that method. This is enough to recover independently randomized js-confuser/js-virtualizer outputs while the later semantic deobfuscator still correctly refuses sloppy-mode `with` regions. Supported direct-switch VMs are lifted with `switch-ir`; linked function-table VMs use `table-ir`. Large unlinked handler tables remain explicit VM candidates only when they are handler-dense (at least 75% function entries) and also have runtime-indexed calls from a loop; exact spans already proven to be Webpack module tables are excluded from candidate scoring. Base VM scanning is exact-content cached when no generated-code dumps are present, while generated-code-bearing units keep independent dump provenance. Generated child recovery is separately exact-content cached by raw child SHA: duplicate children still receive distinct occurrence paths/recovery rows/graph edges, but string recovery, safe deobfuscation and readable formatting execute once per exact body. Python recovery helpers are invoked directly with the active interpreter; timeouts are recorded as failed optional stages (exit 124) and fall back to exact bytes instead of aborting the whole project or leaving a wrapper-spawned orphan process. Unconfirmed numeric direct-switch maps remain visible in scanner JSON, but weak VM-candidate promotion now requires evidence score >=3 rather than treating every numeric switch as suspicious; this excludes codec enum/bitstream tables such as H.264 aspect-ratio parsing without changing confirmed VM thresholds.

## Useful inspection commands

After a JSON scan:

```sh
uv run python scripts/width-consensus.py work/scans/taobao.jsonl
uv run python scripts/dump-linked-bytecode.py work/scans/taobao.jsonl
```

The bytecode dumper preserves unresolved constant-decoder calls symbolically rather than inventing values.

## Ground-truth families

Current families include:

- Alibaba Fireye (real capture);
- Alibaba ET bytecode-VM build (real capture);
- sibling ET direct-CFF build as a real-world negative;
- js-virtualizer;
- heavily js-confuser-obfuscated js-virtualizer;
- js-vm-obfuscator;
- ssukka `--vm`;
- aggressive non-VM js-confuser CFF negative.

See the Notion page **JavaScript VM obfuscation & static devirtualization — current** and its implementation-log child for detailed findings and pinned third-party revisions.
