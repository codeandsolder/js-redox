# js-redox

Provenance-preserving static recovery for hostile browser JavaScript and embedded WebAssembly. The pipeline reconstructs captured source projects, applies only proof-gated semantic rewrites, recovers module/VM/WASM structure, and keeps exact captured bytes authoritative.

## Layout

- `data/` — original uploaded archives.
- `corpus/taobao/` — extracted real-world Fireye / ET samples.
- `corpus/generated/` — source ↔ virtualized ground-truth pairs.
- `corpus/manifest.json` — asserted positive/negative regression corpus.
- `src/jsvm-safe-core/` — proof-gated semantics-preserving JavaScript rewrites.
- `src/jsvm-lift/` — capture/project analysis, structural scanning, VM recovery and bundle/module tooling.
- `src/sourcemap-compose/` — `sourcemaps compose|project`, backed by the shared Rust source-map recovery implementation.
- `src/wasm-redox/` — WASM validation/readability, deep CFG/state-machine recovery and JavaScript/WASM boundary proofs.
- `scripts/` — capture pipeline, proof correlation, build, benchmark and regression helpers.
- Large unpinned-corpus acquisition, grading, catalog, and review tooling lives in [`codeandsolder/js-redox-corpus`](https://github.com/codeandsolder/js-redox-corpus); this repository keeps only engine-facing and pinned-regression tooling.
- `third_party/` — pinned reference implementations / corpus generators.
- `work/` — disposable derived analysis output.

## Build

The Rust side is one Cargo workspace with four crates: `jsvm-safe-core`, `jsvm-lift`, `sourcemap-compose`, and `wasm-redox`. It uses a single root `Cargo.lock`, shared dependency-version pins, and `rust-version = "1.99"`. Whole-workspace correctness gates are therefore ordinary Cargo commands:

```sh
cargo fmt --all -- --check
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

Workspace lints additionally deny unsafe code and Clippy's `unwrap_used`, `expect_used`, `panic`, `todo`, and `unimplemented` classes across every member and target. Detector mismatches are expected to fail closed instead of terminating analysis.

For normal executable builds, use the project helper rather than raw `cargo`:

```sh
scripts/build-jsvm-lift.sh
```

It uses the machine-pinned Rust 1.99 toolchain, requires the distributed sccache build path, derives build parallelism from live farm capacity, and publishes durable executables under `.cargo-target-nodebug/`. The helper builds the scanner/tooling plus `sourcemaps`, `wasm-redox`, and the `fresh-eval` proof helper, and asks Cargo for the workspace target directory rather than assuming a member-local `target/` layout.

### Deep lazy-cell handler provenance (on demand)

For source files whose structural scan reports a lazy-registry indirect-call candidate, run the separate Rust proof pass on the **exact original or recovered child bytes**:

```sh
.cargo-target-nodebug/debug/lazy-cell-explain path/to/embedded-child.js \
  --output work/lazy-cell-explained
```

For any JavaScript file, the standalone source-surface command lists exact original-function byte spans when called with only a path. Add one or more --function START:END arguments to inspect calls, external references, member writes, direct eval candidates, dynamic imports, and nested lexical depth for those functions. This is an opt-in and source-independent syntactic inventory, not a runtime-effects analysis; all event offsets are SHA-256-bound to the input. Usage: cargo +1.99.1 run --locked -p jsvm-lift --bin source-surface -- path/to/code.js [--function START:END].

The reusable function-surface API accepts multiple selected function spans and collects evidence in a single AST traversal (scaling with AST size and lexical nesting, rather than rescanning the source once per recovered handler). The singleton API delegates to the same code, with no separate semantics.

The analyst-facing handler project also emits a generic, source-mapped behavior inventory for every captured function: exact call expressions, member writes, potential direct eval/Function constructors, dynamic imports, nested-function depths, and external lexical references with resolved declaration identities. The per-handler evidence JSON is explicitly syntactic, not proof of executed effects. This makes exact handler-key attribution and cross-file navigation possible without executing untrusted code.

The separate research-grade `lazy-resolver-probe` example can derive *possible* phase values from proven prototype-method phase closures and check each exact handler capture against independently proven state-field, prototype-carrier, and resolver-index semantics. It is intentionally opt-in and keeps its output distinct from the source project:

```sh
cargo +1.99.1 run --locked -p jsvm-lift --example lazy-resolver-probe -- \
  path/to/embedded-child.js
```

Both tools emit a scope-aware phase-binding mutation audit. A single syntactic initialization is not taken as proof of immutability if a nested direct eval call, with statement, or later resolved write can reach the same binding. The audit does not establish when initialization executed.

Its JSON reports `conditional_phases`: `compatible_return_structure=true` means the original handler is selected **under that explicit phase premise**. It does **not** prove the phase at a particular interpreter call, registry-slot persistence, or an observed invocation. The optional final integer argument limits focused analysis to the first N independently proven handler captures; omitting it examines all.

This deliberately stays outside the fast default browser-project pipeline. Its `analysis.json` records SHA-256-bound source spans, exact constructor/receiver origin, specialized lazy-cell factory calls, original registry-install provenance, and individually proven captured handler functions. `handlers/` contains independently formatted readable views of those original function literals with a local navigation README. A proof that a wrapper **captured** a handler is not a proof that a given browser invocation **returned or executed** that handler: dynamic resolver phases, registry-slot persistence, and observed control flow remain separate obligations. An existing nonempty output directory is refused to avoid stale generated files.

## Readable JavaScript source-tree reconstruction

A browser capture is **not** required to statically reconstruct ordinary JavaScript files.
The source-tree mode recursively scans JS, MJS, and CJS files, applies AST-driven
constant recovery, nested numeric-state control-flow reconstruction (for and
adjacent-initializer while dispatch), and removal of unread dispatcher-state
writes, then writes a **navigable directory of real transformed JavaScript**.
The regular safe transform also evaluates ECMAScript abstract equality across
statically known primitive values (`null`, `undefined`, strings, numbers,
booleans), restructures constant `switch` dispatch with strict-case matching
and source-order fallthrough, and simplifies empty `if` arms without losing
the condition's side effects. Unselected switch cases with observable hoisted
or lexical bindings are retained; dynamic tests are not guessed. The numeric
state-graph reducer also handles `for (var state = initial; ...)`, state
transitions inside `var` declaration initializers, and sequential terminating
`return` cases, preserving function-scoped hoisted variables across branches.
For a nonadjacent state initializer, a direct `eval` in an unrelated sibling
callback does not block reconstruction of another callback's **own** numeric
state. That exception is proven by the exact Oxc lexical state symbol and its
owning function scope; captured ancestor state, direct eval, `with`, or mapped
`arguments` in the state-owning function remain protected.
An effect-aware primitive evaluator simplifies expressions with a known result
while preserving original calls, getters and assignments in evaluation order,
including logically dead RHS expressions; return-value comma expressions drop
inert prefixes without altering the indirect-call semantics of callee commas.
Within function bodies, discarded expression values can also be lowered to
normal statements: comma sequences become ordered statements, `&&`/`||`
become conditional branches, and ternaries become `if/else`. Dynamic tests
are evaluated once, direct/indirect calls preserve their syntax, and generated
blocks cannot accidentally introduce string directives. The original
statement is left intact at top level, where its completion value can be
observable through JavaScript `eval`. An `if ((setup(), ..., condition))`
whose `if` already occupies a statement slot in a function/block is likewise
split into ordered setup statements followed by the original final test and
branch bodies, without creating a new lexical scope. Bare nested/unbraced
`if`, loop and labelled bodies retain their original single-statement shape.
Assignment-right comma expressions are also split for lexically resolved,
stable identifier targets, retaining
operation order; dynamic/computed member targets and RHS anonymous function
or class name-inference hazards remain intact. Semantic recovery always
runs first to a fixed point, with presentation-level expression lowering only
on subsequent no-op semantic passes; this prevents cosmetic AST rewrites from
hiding decoder calls or other semantic patterns before they are recovered.
A bounded bitwise algebra pass recovers simpler 32-bit formulas from
symbol-resolved, locally established primitive Int32 assignments. It compares
linear combinations of bitwise Boolean expressions against shorter formulas
using an exhaustive per-bit identity check (not random sampling), while
rejecting possible BigInt/object coercions, direct eval, captured bindings,
intervening writes, potentially observable negative zero, and arithmetic
outside the exact JS Number range. This can turn obfuscated byte composition
into ordinary `low | high` without special-casing any provider or function.
A complementary effect-preserving algebra pass rewrites bounded affine
combinations involving complemented bitwise XOR, retaining the original
number and evaluation order of JavaScript coercions even when operand values
are objects with stateful `valueOf` methods. Proven-primitive Int32 bindings
can additionally simplify control-flow bit-mask tests; unproven return values
remain in the two-coercion form instead of making unsafe assumptions.
These passes apply to ordinary JS, not a framework or specific obfuscator.
The original source directory is not modified.

```sh
cargo +1.99.1 run --locked -p jsvm-lift --bin deobfuscate-safe -- source-tree   path/to/original-js-tree work/readable-js-tree --max-iterations 12 --format-output
```

The output preserves relative source paths and contains linked README.md
navigation plus reconstruction.json with per-file transformation counts.
The --format-output flag creates an **analyst presentation view**: it may alter
behavior in code that inspects Function#toString. Omit it when textual fidelity
matters. Unknown control-flow shapes are left intact and inputs that could not
be recovered are preserved, explicitly labeled rather than silently omitted.

This mode starts from local JavaScript sources. Acquiring HTML/script URLs
and resolving indirect dynamic imports remain separate tasks, and a static
reconstruction does not prove a particular browser execution.

## Pinned real-corpus evaluation

`corpus-eval` is the single engine-facing evaluator for pinned private/real-world JavaScript corpora. The manifest owns capture hashes and acceptance policy; the evaluator formats, safe-deobfuscates, and structurally scans each raw sample through the Rust library APIs in-process. Node is used only as an independent syntax check for generated analyst/deobfuscated source. Reference samples are hash-verified but never executed.

```sh
cargo +1.99.1 run -p jsvm-lift --bin corpus-eval -- \
  path/to/manifest.json --corpus-root /path/to/private/corpus \
  --report /path/to/report.json
```

The evaluator uses a temporary directory for syntax-check inputs and leaves only the explicitly requested report behind. Public metadata can therefore remain in Git while private sample bytes live elsewhere.

## Suspicious-structure triage

`sus-scan` is the cheap first-pass structural scanner used to rank code before deeper recovery. General AST-level obfuscation structures live in `src/jsvm-lift/src/bin/sus-scan/structures.rs` rather than being mixed into the scoring collector.

The structure module uses small detector registries by AST node type. Detectors emit explainable `StructuralSignal` records; the main scanner owns clustering, weighting and output. New families should therefore be added as a detector plus positive/control fixtures in `corpus/generated/sus-scanner/`, without vendor-name checks.

Current structural families include same-array rotation (`x.push(x.shift())`, including literal bracket members), checksum-driven rotation bootstraps, dense operator/call proxy tables, self-disabling one-shot wrapper factories, direct literal-table decoders, tiny mixed-boolean-arithmetic helpers, and numeric selector dispatchers. Low-level evidence may deliberately remain below the standalone cluster threshold; repeated evidence or a stronger composite structure promotes the region.

Coverage is intentionally measured separately from generic suspicion scoring. On the 47-file real corpus plus 3 VM hard negatives, the simple scanner and structural scanner both cluster 49/50 files, but the structural layer names concrete obfuscation families in 17 files (16 real + the Yandex VM-negative that genuinely contains a rotation bootstrap). That named coverage is the useful metric because the families map directly onto safe deobfuscation passes such as table decoding, pure-helper evaluation, and selector specialization.

## Fast analysis of a recorded browser execution

For a browser capture already processed into a project, rerun just the
observed invocation explanations and provenance graph without repeating
deobfuscation, module recovery, or VM scans:

~~~sh
.cargo-target-nodebug/debug/trace-explain path/to/recovered-project
~~~

The invocation path page contains original-source AST guard matches and
concrete, debugger-witnessed selected-arm transitions, with the raw trace
unchanged except for derived witness metadata. A recorded true/false
value alone does not prove the branch was taken: the next pause must be
verified inside the selected AST arm. Missing or ambiguous evidence is
explicitly left unresolved. The general readable tree is never
specialized away based on a single recording.

## Current pipeline

The target is a provenance-preserving **browser capture -> readable source project** pipeline, with VM devirtualization as one transformation stage rather than the whole product.

Live recorder captures can additionally include V8 precise execution coverage
per CDP target session. When available, the project emits a readable view under
src/_observed/ and joins positive execution witnesses to exact runtime script
IDs, sessions, execution contexts, source bytes, and graph nodes. Scripts with
no positive counter remain in the general source tree: zero or missing coverage
does not prove non-execution. V8 ranges use UTF-16 rather than UTF-8 offsets.


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
exact WASM extraction/dedup + readable/deep analysis + JavaScript/WASM boundary correlation
  ↓
proof-gated static browser API callsite recovery (fetch/XHR/beacon/WebSocket)
  ↓
readable recovered modules + analysis/provenance graph
```

The directory contract is intentionally simple:

- `resources/` preserves captured response bodies or saved-page files exactly.
- `src/` contains parser-validated/readable or recovered source.
- `src/_deobfuscated/` contains semantics-preserving recovery from the exact captured JS bytes.
- `src/_readable/` is the formatted human-facing view of those safe-deobfuscated outputs.
  It now recovers meaningful lexical component names from embedded constant
  `__name`, `displayName`, or `name` metadata through nested factory wrappers
  (e.g. `var v = define({__name:'Footer'})` becomes `var Footer = define(...)`).
  It additionally recovers descriptive lexical names from explicit object
  destructuring (`{footerBg: v}` → `{footerBg: footerBg}`, including defaulted
  and nested bindings) and static property-reference aliases
  (`var x = Object.create` → `var objectCreate = Object.create`). These work
  with ordinary source objects and member paths, not a framework or built-in
  whitelist. Renaming follows Oxc lexical identities and preserves shorthand
  object keys and public export names through explicit aliases. Existing
  meaningful identifiers, name collisions, reserved words and dynamic scopes
  are respected. The presentation layer also eliminates redundant aliases of
  unshadowed standard intrinsic properties, e.g. a stable
  objectCreate = Object.create binding becomes direct Object.create references.
  A formerly detached call stays detached as (0, Object.create)(...), so its
  receiver is not accidentally rebound. It rejects alias writes/redeclarations,
  exports, dynamic scope, shadowed intrinsics, direct local builtin mutations,
  and conditionally initialized aliases. This last simplification deliberately
  assumes standard intrinsic members have not been monkeypatched by other
  scripts and are ordinary native data properties: it is for source reading,
  **not a proof of cross-script runtime equivalence**. Arbitrary object
  getters/properties are not inlined. **Only this analyst view** changes;
  the proof-checked deobfuscation and captured bytes remain unchanged.
  When a captured ESM dependency exports a descriptive lexical name
  (such as `export {Footer as t}`), the same project stage also recovers that
  name in importing modules (`import {t as b}` → `import {t as Footer}`).
  It handles functions and helpers as well as components, and can recover
  descriptive public export keys when the source binding is minified (e.g.
  `export {S as createApp}`). An explicit source/forwarded identity takes
  precedence over a different public alias. This works through named
  reexports and unambiguous star barrels. It preserves ESM
  public names, import specifiers, object-property keys and export aliases,
  uses the existing captured module resolver rather than guessing URLs, and
  does not rewrite the shared formatter cache or exact deobfuscated source.
  For an individual file, use `js-format --semantic-names INPUT OUTPUT`.
- `src/_modules/` contains explicit Webpack/Next modules from chunk/direct-table shapes plus named factories recovered from global AMD `define("name", [...], factory)` and structurally proven member-loader calls such as `LWR.define(...)`, `Ya.define(...)`, or local `.define + .require/.loadModules` loaders.
- `src/_dynamic_deobfuscated/` contains proven safe recovery of generated-code children; exact recovered bytes remain the fallback when validation refuses a child.
- `src/_dynamic/` contains formatted analyst views of generated-code children after the selected safe stage.
- `src/_devirtualized/` contains semantic modules and pseudocode for supported direct-switch and function-table VMs.
- `analysis/` contains machine-readable provenance, import-map/module-resolution state, VM evidence, transform metadata, and `api-surface.json` static browser-request callsites.

This separation is important: presentation/deobfuscation passes never overwrite the original capture or make provenance ambiguous.

### Capture-to-project prototype

Build the Rust tools, then use the one-command driver:

```sh
.cargo-target-nodebug/debug/capture-project capture.har work/capture-project
.cargo-target-nodebug/debug/capture-project "Saved Page.html" work/saved-project
# No Chromium needed: fetch the HTML, linked scripts and module dependency graph with HTTP:
.cargo-target-nodebug/debug/capture-project https://example.org/ work/example-site
# Tune bounded network acquisition for large sites:
.cargo-target-nodebug/debug/capture-project https://example.org/ work/example-large --http-max-resources 512 --http-max-resource-mib 32 --http-max-total-mib 256
# Large captures / intentional oversubscription of content-only subprocess stages:
.cargo-target-nodebug/debug/capture-project capture.har work/capture-project --jobs 8
```

The URL form runs an HTTP-only acquisition using a browser-like request and a cookie jar,
follows the HTML's explicit `script src` declarations, `modulepreload` links,
inline/imported literal ES module dependencies, static worker references, and
import maps (including scoped and prefix mappings via the existing resolver).
It persists the fetched HAR in `analysis/http-capture.har` and a concise
coverage/failure report in `analysis/http-static.json` before presenting the
normal deobfuscated `src/` project. **Start in `src/ENTRYPOINTS.md`**: it links
HTML script declarations to the actual formatted/recovered JavaScript files and
follows statically resolvable imports through the captured module tree. HTML
`modulepreload` and `preload as=script` hints are included as separately labeled
roots, so page and framework chunks are discoverable even without a direct
import from an entrypoint. Preload hints do not establish actual execution.
It does **not** run JavaScript; client-generated script URLs and computed
imports may require the browser recorder. Request count and per-resource/total
response size are bounded.

For a normal browser **Save Page / Webpage, Complete** export, the companion `Saved Page_files/` directory is discovered automatically. `--assets-dir` can override it. Saved-page files get stable synthetic URLs for graph resolution; an original page URL from Chromium's `saved from url=(...)` marker is retained separately when available.

The driver runs capture normalization, readable-source materialization, source-map recovery, literal module/worker reference analysis, document import-map resolution, safe deobfuscation, explicit bundle-module extraction, generated-code recovery, VM triage/devirtualization, WASM correlation, static browser-API callsite recovery, provenance-graph construction, and an analyst-facing project README. Import maps are resolved with exact, prefix and scoped mappings; multiple maps keep earlier exact definitions, and document context is propagated only through captured module imports so worker graphs do not accidentally inherit page import maps.

`api-surface --project` analyzes the selected safe-deobfuscated source when available and otherwise the parser-validated source view. Its first contract, `capture-api-surface/v2`, is deliberately narrow: it recognizes unshadowed standard `fetch`, `navigator.sendBeacon`, and `WebSocket` plus scope-proven stable, non-escaping `XMLHttpRequest` receivers; suppresses a sink family when the same source visibly assigns, updates, or deletes an equivalent standard sink path; resolves only exact proof-gated primitive expressions and already-available immutable `const` aliases for URL or method values; and preserves unresolved argument expressions and exact source spans instead of guessing. XHR objects constructed with a standard `XMLHttpRequest` binding but subsequently passed to callbacks, stored in application state or otherwise exposed are still shown as `xhr_open_candidate` callsites, with their method and URL expressions preserved. These are distinct from verified `xhr_open` calls and do not create `api_target` graph edges even when the source contains a literal absolute URL; locally reassigned bindings and shadowed constructors are excluded. A one-argument `fetch(...)` is reported as default `GET` only when its input itself is an exact static string—a prebuilt `Request` remains method-unknown because it may already carry another method. Standard browser API semantics remain an explicit assumption on accepted callsites, including mutations not statically proven by this first contract. Relative URLs remain relative unless a real document base is proven, and only exact absolute `http`/`https`/`ws`/`wss` URLs become `api_target` edges in the source graph. Inline `fetch(..., { method: ... })` now follows ordered object-literal overwrite semantics: later exact own `method` values may override earlier spreads/dynamic keys or inherited-method ambiguity, while later spreads or dynamic computed keys make the method unknown. Object-literal prototype setters and visible direct `Object.prototype.method` mutation are treated as inherited-method ambiguity unless an exact own `method` shadows them. Exact methods are validated using Fetch/XHR method-token, forbidden-method, and legacy normalization semantics; callsites with a proven invalid/forbidden method are retained with `method_status=invalid` for provenance but do not produce `api_target` graph edges. Other RequestInit fields, non-literal options dataflow, wrapper libraries, axios/GraphQL inference, generated-code recursion, and speculative URL reconstruction are intentionally outside v2.

`capture-import` normalizes HAR files, recorder bundles, and saved HTML plus its companion resource directory into the same `capture-project/v1` contract in `capture-manifest.json`. `capture-project` is the supported Rust orchestration front door; the supported capture-to-analysis processing path is Python-free. It combines in-process Rust stages with sibling Rust tools and keeps capture-kind dispatch owned by the normalized manifest rather than duplicating importer detection.

`source-materialize` produces the readable `src/` tree. JavaScript is parsed and regenerated by Oxc; parse failures fall back to the exact raw body and are recorded rather than silently discarded. Inline browser `<script>` blocks are classified by their HTML script type: classic/module JavaScript is executable, `importmap`/`speculationrules`/JSON MIME types are structured data, and other non-JavaScript script blocks remain inert text. Content-only work is keyed by exact SHA-256 and parallelized: identical JS bodies are formatted once and the derived result is materialized for every captured occurrence with explicit reuse provenance. Fuzzy similarity is never treated as semantic equivalence; request-specific GTM/config variants and randomized challenge code remain distinct.

`bundle-materialize` treats Oxc spans as UTF-8 byte offsets against the exact derived JS bytes, clears and reproducibly rebuilds `src/_modules/`, keeps captured Webpack/Browserify IDs or explicit named-loader module names as canonical identity, places direct Webpack tables under `module-table-NN/`, Browserify tables under `browserify-modules/`, global AMD factories under `amd-modules/`, and member-loader factories under `member-named-modules/`. Bundle inventory is also exact-content keyed, so duplicate safe-deobfuscated bodies are parsed once. Extracted module wrappers are formatted in parallel from provenance-neutral templates; exact duplicate templates share one formatter invocation, then each output receives its own parent/span provenance line. `bundle-unpack` accepts bare or parenthesized Webpack function/arrow wrappers, canonical Browserify `{id: [factory, dependencyMap]}` tables with symbolic dependency maps preserved, global named AMD `define("name", [deps...], factory)` calls, and structurally module-like member calls such as Salesforce LWR, Yandex `Ya.define`, and Amazon APS. Unresolved global member loaders are keyed by their stable global path; resolved local objects remain conservative and need loader evidence (`define` with `require`/`requirejs`, or `define` with `loadModules` and multiple named factories). Dependency arrays are authoritative; `require`/`exports`/`module` pseudo-dependencies are mapped to their actual factory parameters before scope-aware export collection, so parameter renaming does not lose exports and shadowed nested bindings do not invent edges. DOM registries such as `customElements.define(...)` do not match because they lack the required dependency/factory module shape. Named exports and static `module.exports` writes are carried into `analysis/bundles.json`, provenance-graph nodes, module-file headers, and the generated `src/_modules/README.md` navigation index. Cross-bundle graph resolution also keeps embedded direct object module tables in their private namespace: a direct table wholly inside the source module is excluded as a candidate for that source module's outer-loader dependency, while nested JSONP chunk registrations remain eligible.

Safe deobfuscation resolves ambiguous JavaScript as browser Script vs ES Module from syntax/semantic validation before rewriting, then pins that resolved source mode across all iterations; CommonJS is only a fallback for genuinely CJS-only syntax. This avoids rejecting valid classic-script patterns such as duplicate top-level function declarations merely because they are invalid under module strictness. Classic scripts containing `with` fail closed before semantic rewriting or classic string-decoder recovery because identifier resolution inside `with` is environment-dependent; the pipeline preserves exact captured bytes instead of routing around that boundary with textual heuristics.

The string-recovery path likewise reads and writes explicit UTF-8 bytes rather than newline-normalizing text I/O, so unchanged CRLF captures remain byte-identical and hash/provenance validation stays exact. Classic javascript-obfuscator table, Base64/RC4, alias and rotation recovery and flattened rotated-Base91 recovery are owned by the Rust `static-string-recover` proof engine. Base91 is an independent local proof rather than an exception to safe deobfuscation: the generic deobfuscator still rejects dynamic `with`, while the Base91 stage may analyze such a file only to prove a decoder scaffold and rewrites a call only when Oxc resolves that exact decoder symbol without crossing a `with` scope. The old Python text/table/concat pass is gone; immutable string-table exposure and literal concatenation use the existing Oxc-backed Rust pass. `deobfuscate-safe source` owns the single-source proof/report contract, while `deobfuscate-safe project` owns mode-sensitive capture-project grouping, exact/readable materialization, and the `STRING_RECOVERY`/`DEOBFUSCATION` artifacts in Rust.

To refresh *only* the presentation-layer ESM names in an already materialized capture, run `deobfuscate-safe project-names path/to/project`. It reads the existing source index, deobfuscation manifest, and resolved JavaScript references, then links explicit captured export identities to the importing local bindings under `src/_readable/`. It does not fetch resources, rerun proof-oriented deobfuscation, change `src/_deobfuscated/`, or rewrite public ESM export keys. It also generates a navigable `src/ESM_SYMBOLS.md` index linking source-backed names, public export keys, and captured importing modules. Repeating it is idempotent; the underlying readable files must already contain the source-backed names produced by the local naming/formatter pass.

`capture-project` owns recursive VM scanning in Rust and prefers a proven safe-deobfuscated view for captured units while retaining the captured file as provenance. Core scanning, static string recovery, safe deobfuscation, formatting, hashing, deduplication, and artifact emission run in-process; `switch-ir` and `table-ir` remain sibling Rust stages. Static `Function(...)` payloads become bounded recursive code units: each exact recovered child is passed through the same Rust string-recovery + deob stack, hash/provenance validated, and scanned from the furthest proven-safe result. Base91 recovery is gated by an Oxc string literal containing exactly 91 unique symbols, proves an exact rotated literal-string provider and rotator binding, resolves decoder/provider/transform links by Oxc symbol identity, and accepts affine/CFF-hidden decoder constants only when their semantic positions uniquely determine the backing-array state. Rewrites are limited to ASCII-safe decoded strings and statically resolved decoder calls; references whose lookup may be intercepted by dynamic `with` are left untouched. Proven immutable literal-table reads and literal concatenations then use the shared Oxc string-exposure pass, which is itself `with`-aware. Recovery is bounded to a fixed point so one proven rewrite can expose later safe work without creating an unbounded deobfuscation loop. On the flattened-Base91 VM regression this stricter Rust path proves 408 top-level `olQJbc` calls (656 Base91 calls total) and still recovers the 74-handler opcode registry plus both confirmed function-table dispatchers, without the Python implementation's blanket dynamic-scope table substitutions. Supported direct-switch VMs are lifted with `switch-ir`; linked function-table VMs use `table-ir`. The scanner also reports `lazy_registry_indirect_calls` separately from confirmed `table_vms`: these candidates combine an exact allocation-origin handler registry, a recognized lazy registry-accessor result, and an indirect invocation reachable on a CFG path without intervening writes. They intentionally do not prove the accessor returned an installed handler, the path is feasible, or a particular call executed. Each edge retains the registry identity, source spans, local binding, and exact-key/definite-result flags, leaving real dispatcher proof and devirtualization for stronger evidence. Large unlinked handler tables remain explicit VM candidates only when they are handler-dense (at least 75% function entries) and also have runtime-indexed calls from a loop; exact spans already proven to be Webpack module tables are excluded from candidate scoring. Base VM scanning is exact-content cached when no generated-code dumps are present, while generated-code-bearing units keep independent dump provenance. Generated child recovery is separately exact-content cached by raw child SHA: duplicate children still receive distinct occurrence paths/recovery rows/graph edges, but string recovery, safe deobfuscation and readable formatting execute once per exact body. Rust classic-decoder recovery remains an independent proof stage: if the generic safe stage rejects a source, it emits an exact identity result with zero rewrites; Base91 can still proceed only under its own narrower proof and never relaxes the global deobfuscator's safety boundary. Every derived output is hash/provenance checked. Unconfirmed numeric direct-switch maps remain visible in scanner JSON, but weak VM-candidate promotion requires evidence score >=3 rather than treating every numeric switch as suspicious; this excludes codec enum/bitstream tables such as H.264 aspect-ratio parsing without changing confirmed VM thresholds.

## WebAssembly recovery

WASM is treated as another exact binary source, not as an opaque attachment. Captured and statically recoverable inline modules are content-addressed while preserving every origin; readable WAT and deeper analysis are derived artifacts. The current machine contracts are `wasm-redox/deep-v14`, `jsvm-wasm-import-semantics/v8`, and `wasm-js-boundary-correlation/v6`. Cross-language WASM/JavaScript boundary correlation is Rust-owned and runs the JavaScript semantic analyzer plus bounded fresh-state WASM evaluator in-process; the supported capture pipeline no longer shells out to a Python correlator.

`static-byte-artifacts` is the shared proof-gated byte-producer layer. Static carriers cover direct Base64 literals, standard Base64 data URLs, and bounded JSON-serialized literal data; every candidate is accepted only after full core-WebAssembly validation. Split/generated modules are recovered from semantic operations rather than protector or site identities: exact local `Uint8Array` allocation, unshadowed Base64 decoding, bounded local byte-copy loops, and exact WebAssembly sinks. Symbol resolution crossing dynamic `with`, escaping copy helpers or buffers, unknown local calls, ambiguous writes, out-of-bounds copies, and magic-prefixed but invalid modules all reject the proof. Unary IIFEs and function-valued literal dispatch containers are traversed only as structural containers around the same proof. Byte production and sink reachability are deliberately separate proof layers: materialization can preserve exact embedded modules even when the surrounding loader is not understood, while exact module identity is claimed only at independently proven sinks. `wasm-materialize` now owns capture provenance and calls both the shared static-byte producer and the `wasm-redox` library in-process instead of maintaining subprocess glue or a second Base64 extractor. Proven assembled bytes feed exact-module identity as `assembled_exact_bytes`; vendor names and corpus URLs are not transform inputs.

The JavaScript/WASM boundary is fail-closed. The correlation layer can prove exact recovered module bytes, exact import-object binding, instance/export/module-memory identity, selected typed-array copy semantics, destination alignment, and whether intervening linear-memory effects can touch the copied interval. Concrete input-word interpretation is emitted only when both byte integrity and alignment are independently proven; ambiguous host effects or unconstrained memory writes remain barriers.

Deep semantic returns and runtime boundaries carry raw structured expression IR alongside a separately derived normalized IR. Runtime-boundary discovery records exact direct SSA dependencies, but typed IR is the sole semantic expression constructor; readable strings are rendered from that IR rather than reinterpreting Waffle SSA through a parallel expression traversal. Runtime-reference leaves are keyed by exact Waffle SSA value identity, and raw + normalized leaf sets must both exactly equal the separately recorded direct runtime-dependency edges; SSA references must resolve to same-report definitions in both forms. Normalization never mutates raw provenance: it folds only closed pure i32 subtrees and applies neutral identities that preserve the nonconstant subtree, while definitions targeted by `ssa_value` references are never eliminated. Boundary correlation preserves both forms: proven copied-input loads become `source_word` leaves, while other runtime leaves retain their identity plus any transitively proven source-word provenance. Human-readable `$runtimeN`/`source_u32(...)` projections are rendered directly from the validated structured IR; the canonical display uses normalized IR while the raw-IR projection remains separately inspectable. No runtime-token regex participates in either proof or presentation.

`fresh-eval` is a bounded proof helper for closed internal `i32` computations. It can execute a sequence of internal calls in one fresh interpreter state, feed earlier proven results into later calls, and report the relevant memory accesses. Imported calls, unsupported mutable host state, ambiguous control flow, and exhausted fuel fail closed. Public synthetic fixtures exercise the complete proof boundary; private real-world corpus material is validation data rather than hard-coded names, addresses, or exceptions.

## Useful inspection commands

After a JSON scan:

```sh
.cargo-target-nodebug/debug/debug-utils width-consensus work/scans/taobao.jsonl
.cargo-target-nodebug/debug/debug-utils dump-linked-bytecode work/scans/taobao.jsonl
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

### Link extracted handlers to their original lexical helpers

The generated source tree can also include real lexical helper implementations from
the full original JavaScript, without Chromium:

~~~sh
cargo +1.99.1 run --locked -p jsvm-lift --bin deobfuscate-safe -- source-tree \
  path/to/extracted-handlers work/readable-handlers \
  --context-source path/to/original.pretty.js \
  --max-iterations 12 --format-output
~~~

The generated lexical-context/ directory contains the original enclosing
program and transformed helper source, with links from each handler to the
helper definitions it actually references. Lookup begins with unresolved
identifiers in the extracted handler and follows *exact original lexical
symbols* through dependencies. Shadowed parameters are not confused with
external helper calls, and ambiguous names are not guessed.

Helper files are navigation views, not independently runnable modules.
The original enclosing source remains available because captured variables,
later reassignments, and top-level side effects can change their behavior.

The safe static statement pass also separates a comma-expression prefix
used as the **object of a property-assignment target**, when that entire
assignment occupies a sibling statement slot inside a function or existing
block. For example, `((setup(), object).field = value)` may become
`(setup()); (object).field = value`: every prefix still performs GetValue
before the property reference is created, and the original assignment RHS,
computed property key, receiver and anonymous-function name inference stay
in their original evaluation positions. The rewrite never adds an inner
lexical block, applies to unbraced conditional/loop/label bodies or alters
script/eval completion values. Ambiguous operand comments and nested
assignments without a safe statement slot remain untouched. The
`member_object_sequence_lowering` counter records these semantic rewrites,
distinct from whitespace-only `expression-layouts/` navigation views.

An analogous `if_guard_member_prefix_lowering` pass handles a comma
sequence in a property object that is **guaranteed to be evaluated first**
within a function/block sibling `if` test. For example,
`if (((prepare(), object).length < bound)) {...}` can evaluate
`(prepare());` before the same comparison using `(object).length`.
Only the test's unconditional leftmost evaluation path is eligible:
binary/logical left operands, conditional tests, unary operands and
nonoptional property objects. Guarded branches, right operands, call
callees, computed keys, optional chains and ambiguous inter-operand
comments cannot be hoisted. The property access and branch bodies keep their
original evaluation context. In source-tree mode, captured source and the
protected executable are stored independently of rewritten helper views.

The related `if_guard_binary_left_sequence_lowering` extracts a comma
prefix which is the **entire first operand of a binary expression** in
a sibling `if` test. Unlike a comma on the comparison's right, these
effects are unconditionally evaluated before the second operand.
The original second operand, getter order and branch semantics
remain intact; only a syntactically first sequence with unambiguous
comment boundaries is eligible. This exposes initializer effects
hidden inside comparisons without guessing assigned values.

The new if_binary_rhs_effect_lifting pass recovers comma effects on the
**right** side of nested binary comparisons, where hoisting without
capturing earlier values would reorder property getters and coercions.
It captures each earlier operand through GetValue (without ToPrimitive) in
fresh block-scoped const bindings, then evaluates the comma-prefix effects
before the original comparison. Conditional/logical branches are not lifted.
A direct eval or Annex-B function declaration inside the affected if tree
blocks the rewrite because the introduced scope might be observable.
The names are unique across the complete source, and the existing inert
comma optimizer now preserves commas that suppress anonymous function,
arrow, class, and conditional-branch name inference.
All emitted source remains a separate analyst-only view; original captured
bytes and precise source-backed extracts are retained separately.

The `assignment_conditional_lowering` pass restores ordinary `if/else`
control flow from a discarded assignment statement whose right-hand side
is a nested conditional expression. The assignment target must be a
statically resolved lexical identifier without an intervening dynamic
`with` scope; member/computed targets and unresolved names are not moved.
Every selected leaf is assigned once, and all condition effects and
throwing fallbacks (including a numeric call such as `2()`) remain under
their original guards. Anonymous function, class and arrow leaves are
left intact because splitting them could introduce assignment-inferred
names. Non-sibling placements, script/eval completion and comments at
changed syntax boundaries also stay unchanged. Source-backed helper
recovery never edits the captured executable itself.

A separate `lexical-context/annotated-handlers/` tree puts confirmed helper
context **at the first direct call** in each recovered handler. For a short
original, stable, single-return function it quotes that exact return expression
next to the call; for longer helpers it links directly to the original
definition. When a recovered direct call has statically proven literal
arguments, its annotation additionally links to the already generated,
argument-specialized helper body. This applies at **every matching callsite**,
not only the first use of a helper. Helpers whose bindings are subsequently reassigned explicitly
identify the linked code as the *initial definition*, not necessarily the
function called at runtime. Semantic symbol resolution prevents annotations
on local/shadowed parameters or unrecognized call targets. These inline
comments are presentation-only and do not modify the proof-checked handler.
The `lexical-context/context.json` manifest records annotated files and call
counts.

For small, source-backed helpers, `lexical-context/expanded-handlers/` goes
further: it places the **original return expression directly into the
recovered code**, substituting formal parameters by Oxc binding identity.
The expansion requires a stable original helper, side-effect-free and
non-reassigned arguments, and no conflicting lexical captures, dynamic scope
or call-frame-dependent syntax. For shorthand object properties, the original
key is retained (for example, `{J}` becomes `{J: P}`, never `{P}`). The
special `__proto__` shorthand uses a computed key instead of invoking the
object-literal prototype setter. Free-name
collisions are checked in each callsite's actual Oxc lexical scope, so an
unrelated nested binding does not suppress otherwise valid expansion. Calls
without those proofs stay untouched.
This is an analyst projection only; the executable/proof-checked source
tree is always kept separate.

For helpers with at least eight structurally nested calls, the optional
`lexical-context/call-spines/` Markdown views identify the deepest AST call
chain, its original helper line/byte offsets, and which enclosing argument
contains each nested call. Independently, `lexical-context/expression-layouts/`
contains alternate JS source views for either deep calls **or** long
single-line assignments, sequences, comparisons, short-circuits or conditional
operands, even without a deeply nested call. These views insert only
whitespace at AST-confirmed boundaries.

For helpers with long *nested assignment* expressions, the independent
`lexical-context/assignment-outlines/` Markdown index lists the actual
assignment targets and operators, **exact assigned RHS expressions** when
short (with AST-kind/byte-length summaries for complex RHS), source-byte
locations, lexical containment inside other assignment expressions, and nearest short-circuit
or ternary guard ancestry. It keeps assignments in nested callback bodies
separate from the enclosing initializer. This is a source-backed structural
map, not an execution trace or a claim that assignments can safely be hoisted:
outer assignment targets (including free/global names such as `Hm`) are
resolved before their RHS, computed property references can be effectful,
and branch-guarded writes may not run. Original helper and captured
executable remain unchanged.
The view never hoists effects or changes binding, receiver or evaluation
order. Its syntax must parse and regenerate the exact same canonical
JavaScript; if not, the alternate view is refused. This makes
enormous registration expressions navigable without inventing an equivalent
sequence of statements. The list describes **syntax nesting**, not execution
order: short-circuit guards, argument evaluation, computed keys, callback
boundaries and JavaScript receiver identity remain governed by the linked
helper source. Captured source and executable files remain unchanged; the
layout is not suitable where Function#toString or exact source bytes matter.

The `lexical-context/binding-writes/` index adds **original lexical binding
mutation provenance** for every linked symbol that receives a resolved write.
Each report links the original declaration, exact write and operation byte
spans, assignment/update operator, and nearest enclosing function. All
lookups use Oxc symbol identity: shadowed names do not become writes to the
outer binding. Reports include writes inside deferred closures but identify
those function boundaries. Declaration initializers live in the linked
initial-definition helper, not in this reference-write table. Unknown
execution order, direct eval, dynamic scope, and external code must not be
mistaken for a proven reaching definition; the maps are navigation evidence,
not constant-propagation permission. Structured `write_sites` are also
recorded in the source-tree `context.json` helper rows, without changing the
original source, recovered helper code, or captured executable.

For mutable computed-property aliases, the `lexical-context/explained/`
views retain executable property expressions and annotate them with their
**actual** lexical string assignments and conditional overrides. For example,
`target[key /* property alias: "push"; H when (H.length < 2) truthy */]`
shows why blindly replacing `key` with `.push` would be incorrect. The
analysis resolves writes and uses by the same Oxc symbol ID (including nested
closures), so an unrelated shadowed `key` is never joined by spelling. The
`lexical-context/context.json` v2 manifest exposes each original literal,
dynamic write, condition and annotated read count for tools. These are
**alternate browsing views**; the ordinary transformed JS and original
context remain byte-for-byte unchanged, including any source-sensitive
`Function.prototype.toString` behavior.

When original function-capture headers include the unformatted source SHA-256
and exact byte spans, pass `--origin-source path/to/raw-original.js` alongside
`--context-source` to produce `lexical-context/handler-origins/` annotated
views **directly in the individual recovered handlers**. The tool verifies
the raw original hash, exact function span and enclosing lexical symbol,
then annotates a property only if the readable handler still has an unresolved
reference to that same proven external binding. This avoids confusing a
shadowed parameter with the original `push`/`length` alias. A pretty-printed
version of the original is useful for browsing but must not be used as the
span provenance source. `context.json` records the original declaration
spans, assignment alternatives, and linked handler paths.

An opt-in **whole-program lexical reconstruction** can prove additional
statement boundaries which are invisible in detached helper expressions.
Supply `--context-source original.js --context-full-iterations 48` to
`deobfuscate-safe source-tree`. The whole original lexical source is passed
through the existing safe-deobfuscation engine to a checked fixed point
and *then* its functions are re-extracted under their original lexical
symbol identities. The alternate `lexical-context/whole-program/` contains
`readable.js`, a transformation/source-hash report, and a helper index
with extracted source. The whole-program helper index distinguishes original lexical helpers
from derived internal bindings using parsed declaration identities from
the preserved original source, never generated-name prefixes. Derived
bindings remain navigable because transformed code may depend on them, but
they are not counted as recovered original helpers. The v4 helpers.json
report records binding_origin per entry and separates original_helper_count,
derived_internal_binding_count and total_definition_count. The whole-context
summary exposes the same distinction through helper_count (original only),
derived_internal_binding_count and total_definition_count.

The iteration argument is a **cap**, not a requested
rewrite count: if a validated fixed point is not reached below it, the
command fails rather than claiming completion. This additional work is
opt-in so ordinary source-tree capture runs do not needlessly process the
whole enclosing program again. Function#toString-sensitive formatting
and byte offsets belong to the alternate *analyst* view only; the
`lexical-context/original.js` and captured executable files remain exact.
A detached helper can fail to prove an enclosing identifier binding,
so it may retain an opaque assignment sequence that the context-aware
view safely reconstructs. The full-context **derived helper files** then
go through the same single-trip loop reflow and post-reflow control-flow
polishing as ordinary helper views. Long derived expressions also get the
same AST-verified, whitespace-only `expression-layouts/`, nested assignment
`assignment-outlines/`, and deep-call `call-spines/` as original lexical
helpers. These links are included in the whole-program helper index. The
layouts insert whitespace only, retaining identical AST code generation;
the assignment outlines describe containment, **not execution order**.
Both original and whole-program lexical helpers now also offer
`evaluation-phases/` static phase plans for long nested assignments.
These show target-reference formation, GetValue, RHS evaluation and PutValue
within each possible branch path. Mutually exclusive branches are marked;
any step may throw, and complex calls/destructuring/optional chains remain
opaque instead of inventing an order. Computed property key coercion is
deferred until target GetValue or PutValue, so simple assignment may evaluate
its RHS *before* ToPropertyKey while compound assignment does not.
The plans are analyst navigation, not observed traces or executable rewrites.
Each view records its source hash and generated artifact hash in the
whole-program `helpers.json` v4 report, without modifying the polished
helper or its source-backed extract. Every exact source-backed helper extract
is kept separately in \`whole-program/source-helpers/\`, with a per-helper
\`helpers.json\` report recording both source hashes, which polishing
passes ran, and any remaining reflow errors. Thus the improved lexical
statement boundaries and the previously proven loop/return recovery are
combined, without losing their traceable source or changing captured code.

For source-level direct-call and constructor forwarding, add
`--caller-view-entry <member-property>` (for instance, a site's exposed API
method name). The output `lexical-context/caller-views/` traces Oxc-resolved
function-to-function calls and explains which final callee parameters still
originate at entrypoint parameters, preserving unknown/dynamic arguments.
This gives an actual caller-oriented view of obfuscated helper plumbing
without making an executable replacement from incomplete lexical fragments.
The same forwarding information is available in `context.json` as
`caller_views`. When the source-tree command specifies
`--caller-view-entry`, it also materializes readable, original-callsite
specialized helper implementations at
`lexical-context/caller-views/specializations/`, including the variants
reached beyond four direct calls. These use the **same shared implementation**
as the standalone `caller-views --specialize` mode; unlike the separately
preserved captured-handler specializations, they are joined by original
function spans and carry original lexical callsites in `context.json` under
`graph_specializations`. This runs only when a caller entrypoint is requested.
The analysis resolves stable function and argument aliases
through direct lexical assignments such as `const local = original`, and also
accepts `let`/`var` aliases when they have no subsequent resolved writes and
the program does not use direct `eval` or `with`. It does not infer dynamic
property dispatch, runtime reassignment, or computed argument values.

To inspect a standalone source file without reconstructing the full handler
tree, use the focused caller-view command:

~~~sh
cargo +1.99.1 run --locked -p jsvm-lift --bin deobfuscate-safe -- caller-views   path/to/already-formatted-original.js work/caller-views --entry-member someMethod
~~~

The output includes linked Markdown source excerpts and a machine-readable
`caller-views.json` with function spans, exact callsite locations, and
parameter-origin chains. Every entry also exposes all statically reachable
`reachable_edges` in a finite call graph: each distinct callsite is recorded
once, including recursive cycles and edges beyond the short path listing.
`reachable_functions` additionally propagates entry-parameter origins
through arbitrary call depth using a finite fixed-point calculation, retaining
multiple possible source parameters and unknown/non-entry values rather than
guessing a single caller. The analysis distinguishes positional arguments
from spreads, and does not falsely treat default/destructured parameters as
unchanged forwarding. This is a static may-flow analysis, not evidence that
all syntactic paths execute. The browsable path examples intentionally stop
after four call edges to avoid exponential path enumeration; the complete
graph and parameter origins do not.
On individual resolved paths, the caller report can also recognize a
**fresh constructor receiver** passed as an actual this-expression argument.
For example, when an exported function invokes a stable function with new
and that constructor immediately passes its own this to a helper, the helper's
parameter is tagged with the constructor's original callsite byte span.
The label follows exact unchanged parameter forwarding, but never treats a
supplied object or an ordinary function call as a newly allocated receiver.
This proves the receiver's allocation along that path, **not** the absence
of effectful inherited setters or proxies in its prototype chain, and does
not imply all runtime invocations follow that path. The complete may-flow
table retains unknown/non-entry possibilities from other callsites.

The entry member is optional; no provider-specific code or entrypoint name
is baked in.

To turn resolved constant selectors into **actual simplified helper bodies**,
use the same standalone command with `--specialize`:

~~~sh
cargo +1.99.1 run --locked -p jsvm-lift --bin deobfuscate-safe -- caller-views \
  path/to/original.js work/caller-views --entry-member someMethod --specialize
~~~

When the source has many unrelated helper families, repeat `--only-helper NAME`
to retain only source-resolved entrypoint paths and specialized implementations
for the chosen helpers, without materializing hundreds of other variants.
This filter changes only the analyst output selection; the same lexical symbol,
callsite and exact-argument proofs still determine every variant. An example
using more than one helper:

~~~sh
cargo +1.99.1 run --locked -p jsvm-lift --bin deobfuscate-safe -- caller-views \
  path/to/original.js work/focused-helpers --specialize \
  --only-helper da --only-helper eU
~~~

Exception-sensitive state dispatchers retain their original try/catch
and one-state-per-iteration semantics. Exact lexical-state reachability
includes catch-resume assignments as additional roots, so unreachable
case comparisons can be removed without erasing recovery paths or moving
potentially throwing operations across the handler.

Numeric-state control-flow recovery also structures single-entry reducible
cycles with early exits from the middle of their bodies. The original
state-transition graph determines a common exit; every emitted path must
reach either that exit or the loop header, so irreducible or multi-entry
cycles remain unchanged. Early exits render as ordinary break/continue
without losing the effects of intermediate states.

The tool recovers source-resolved direct calls, constructors, and eligible
Function.prototype.call forwarding through original lexical function bindings
throughout the reachable graph, not only calls in extracted handlers. For a
function.call(receiver, args...) edge, the receiver is linked separately from
the actual callee formal arguments, preserving their correct parameter indices.
Direct property writes/deletions overriding a function's call method, or dynamic
eval/with, prevent this exact call-method inference. Each callsite's
**primitive arguments and side-effect-free constant expressions** are matched
to the original function's formal parameter symbols. This includes immutable
lexical constants and their chained aliases, resolved by semantic symbol
identity (not spelling); pure JavaScript arithmetic, logical and conditional
expressions use the same value evaluator as the deobfuscator. It also **carries
those values through further helper calls whose arguments are unchanged,
lexically resolved caller parameters**. It also **evaluates pure expressions
of known caller parameters at each original callsite**, including arithmetic,
bitwise, comparison and conditional operators. Original AST symbol references
are matched to formal parameters before any substitution, so shadowed
identifiers do not become unrelated constants.
This works at arbitrary graph depth, including cycles, and preserves each
reachable constant tuple separately rather than combining unrelated caller
values into impossible variants. Recursive computed selectors use
constant-invariant widening after a representative recursion, rather than
enumerating unbounded values from expressions such as f(x + 1). Callers using
mapped arguments, direct eval,
or dynamic with-scope do not forward inferred parameter constants; programs
with dynamic eval/with do not infer lexical-identifier constants. Reassigned
bindings and effects cannot become inferred values. An
example_call_chain in the JSON metadata links each variant to one real
original callsite sequence; the original program stays intact. It can still use stable constants when other formal
parameters are reassigned; shadowed same-name functions are distinguished
by source span, and spread arguments never shift inferred parameter indices.
The output contains `specializations/*.js` with deobfuscated, formatted
original helper bodies, `specializations/original/` for comparison, and
per-variant callsite, source-span, constant-argument, and transform metadata
in `caller-views.json`. The generated specialization index lists the
**20 largest source reductions first**, then all variants grouped by resolved
helper, with direct links to readable and original bodies, call depth,
rewrite count, callsite count and byte-size change. These are also included
as the semantic_rewrites, source_depth, saved_bytes, original_bytes and
readable_bytes fields in the machine-readable metadata. These are
closure-context *reading views*, not standalone executable replacements.
Expensive variant generation is opt-in.

### Specialize original helper code at constant-argument callsites

When the original enclosing JavaScript is supplied with --context-source,
the same source-tree pass also generates a lexical-context/specializations
directory. Each JS file is a rewritten helper body: literal arguments from
an actual extracted handler call replace references to the corresponding
unchanged lexical parameter symbols, and the regular static deobfuscator
then simplifies the result. Derived original-helper and specialized-helper views
also structurally reduce single-trip `for`/`while`/`do-while` loops when an
unconditional terminal break proves that a second iteration is impossible.
This includes a final break guarded by a provably truthy test: every
effectful comma operand is evaluated in order (such as `record()` in
`if ((record(), {})) break`), but provably inert discarded operands are
removed in function contexts. Top-level script/eval loops are left
unchanged because replacing a loop with an `if` can itself change an
observable completion value. The original initializer and loop condition
are evaluated exactly once in eligible functions; updates remain
unreachable, and potential earlier breaks or continues prevent the rewrite.
A second run of the existing proof-oriented static deobfuscator then folds dead conditions and redundant blocks exposed by
that structural change (for example, a specialized `if (false)` branch).
The source-backed helper views also recover direct values from terminal
return temporaries. An assignment immediately feeding a return can become
a direct return even when the function previously read or wrote that
variable: those earlier effects remain in place. Oxc verifies that the
binding belongs to the function being rewritten and that no nested
closure can observe its terminal write. The same symbol-resolved
dataflow applies to labeled branch joins, conditional assignments with a
fallback return, and complete `if/else` joins. Branch blocks may contain
earlier side effects, calls, declarations, and conditional exits: their
original source and lexical scope are retained, and only the final plain
assignment is replaced by a direct return. An outer guard may enclose a
labeled join: the result is returned directly only when that guard executes,
leaving the original fallback return intact. The temporary must belong to
the function being rewritten; writes to captured or enclosing lexical
bindings remain observable even if only written and returned once.
Dynamic scope, `eval`, `arguments` access, or extra reads/writes also
prevent these rewrites.
These improvements are fed through the existing static deobfuscator again;
they are not runtime-execution or value-guessing shortcuts.
Any unsuccessful follow-up analysis is recorded rather than aborting
other helpers. The lexical program remains byte-exact in
`lexical-context/original.js`; reflow counts, follow-up transforms, and
errors are recorded per helper and specialization in
`lexical-context/context.json`. Both original helper and specialized body
are kept and linked by original handler callsite.

Specialization handles primitive literal arguments, including multiple
constant parameters in a call. It rejects parameter writes, direct eval,
arguments aliasing, dynamically scoped with blocks, and substitutions that
would produce invalid JavaScript. Mutable or ambiguously named helper
bindings remain linked to the unspecialized original. A specialized helper
view applies to its recorded fixed arguments; it is not a universal
replacement for the general helper.
