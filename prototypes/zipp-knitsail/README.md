# ZIPP x Knitsail — exact-origin handler 208 experiment (2026-11-10)

A minimal, reproducible **execution and instruction-trace comparison**, not a new deobfuscator. The checked-in sources contain **no captured Knitsail payloads**. They reconstruct two local test programs using the private original capture and an existing js-redox result, then run each in Node and ZIPP.

## Provenance and scope

* Original: `embedded-4148a06d2aa37711.js`; SHA-256 `d016538d95a679e1604c8e6f4c1fa5d78ff3d729eace6c832e54a10b550b4a98`. Extract **exact byte span [28591, 29605)** for the captured handler 208 function, as recorded in js-redox's source-tree metadata. Byte length 1,014.
* Comparison: `exception-sensitive-dispatch-20261109/knitsail-scc-c555f75-source-tree/key-208.js` from the active js-redox feature work. The reconstructed JS is 1,257 bytes **including its provenance header**, not a claim of size savings.
* Pinned ZIPP: [f2i-com/zipp.org @ b7521d2a2a4b562a1764194de56659277232291e](https://github.com/f2i-com/zipp.org/commit/b7521d2a2a4b562a1764194de56659277232291e), `zipp-vm` instrumented interpreter, built with Rust 1.99 via the machine's normal sccache wrapper.
* Both programs run against the **same explicit synthetic stand-ins** for Knitsail's closed-over `AM, O, V, t, y, T, JM, r, YX`. The lexical parent is not executed, so this experiment **does not prove the conditional aliases** `T='push'`/`JM='length'` or cover the full browser execution context.

## Build and run

From this directory, create a sparse checkout of ZIPP at the pinned commit:

```bash
git clone --filter=blob:none --sparse https://github.com/f2i-com/zipp.org.git upstream-zipp
git -C upstream-zipp checkout b7521d2a2a4b562a1764194de56659277232291e
git -C upstream-zipp sparse-checkout set crates/zipp-vm crates/zipp-cli crates/regress-fork crates/zipp-wasm crates/zipp-sandbox crates/zipp-numparse crates/zipp-gpu
```

By default, `scripts/make-fixtures.mjs` uses the canonical Acer capture and current js-redox output. Override `KNITSAIL_ORIGINAL` and `KNITSAIL_RECOVERED` to use other paths; the original's SHA is always verified. Needs Node and Rust 1.99, and preserves configured sccache.

```bash
node scripts/make-fixtures.mjs
node --check inputs/raw-208.js
node --check inputs/recovered-208.js
CARGO_TARGET_DIR="$PWD/target" cargo +1.99.0 build --manifest-path harness/Cargo.toml
for kind in raw recovered; do
  node "inputs/$kind-208.js" > "inputs/$kind.node.out"
  target/debug/zipp-knitsail-probe "inputs/$kind-208.js" \
     > "inputs/$kind.zipp.out" 2> "inputs/$kind.stats"
  cmp "inputs/$kind.node.out" "inputs/$kind.zipp.out"
done
cmp inputs/raw.zipp.out inputs/recovered.zipp.out
rg '^TRACE:' inputs/*.stats
```

The instrumented VM is started with a step budget and 400,000 trace rows, and its tracer disables ZIPP's native JIT. This evaluates whether ZIPP itself *recovers source structure*, not whether native compiled code can run the original function faster. The existing `TraceStep` format lacks source spans/lexical identity/property-value data needed for a proper devirtualizer.

## Observed on Acer (2026-11-10)

| Metric | Raw flattened Knitsail | js-redox structured |
| --- | ---: | ---: |
| Source body bytes | 1,014 | 1,257 (includes provenance comments) |
| ZIPP instruction-equivalent steps | 7,256 | 2,318 |
| ZIPP recorded trace rows | 7,228 | 2,290 |
| Distinct executed PCs | 277 | 129 |
| Distinct executed PC transitions | 402 | 197 |
| Coarse trace JUMP rows | 2,020 | 308 |

Both deterministic scenarios returned byte-identical `RESULT:` lines on Node and ZIPP; output SHA-256 `b64cc2c5fda8c1e0abfa9a0a8e31ea650dde90956a0b418a9cc5dbd1a5a6f77c`. The scenarios cover input bit extraction, a literal/reference mix, array construction, helper call order and callback behavior. The step difference is ~3.13x; this is an instruction-count comparison, **not an execution-time benchmark**.

A separate `capturedHandler.toString()` probe in ZIPP returned the raw flattened code beginning `for(z=87;z!=14;)` for the original, whereas the js-redox output had readable loops. ZIPP's VM/JIT doesn't emit readable deobfuscated JS. Its useful reuse prospect is as an optional *dynamic semantic observer* with new provenance-aware instrumentation. Current row-per-instruction proof traces are insufficient to reconstruct the source.

## Follow-up only if pursued

Instrument ZIPP's common dynamic compiler for exact generated `eval`/`Function` sources and add separate diagnostic events (original source hash, function identity, bytecode PC + source span, branch and property/value observations). Compare new recoverable facts on a genuinely unresolved Knitsail region. Do not change the prover `TraceStep` wire contract, replace Oxc, or treat observed runtime behavior as a whole-program proof.

Detailed decision: [Notion assessment](https://app.notion.com/p/414f74be90208186b1bef661549d3866).

## Follow-up: the native optimizing JIT *was* exercised (2026-11-10)

The earlier trace experiment used ZIPP's interpreter, because `start_trace` disables the JIT. This follow-up builds the actual x86-64 JIT and enables experimental **Tier O** with `ZIPP_OPT=1`. Tier O constructs a bytecode CFG in SSA form, unboxes numeric values, tracks liveness/phi nodes, inlines eligible short callees and inserts deoptimization guards; source: [`codegen/opt/{mod,build,emit}.rs`](https://github.com/f2i-com/zipp.org/tree/b7521d2a2a4b562a1764194de56659277232291e/crates/zipp-vm/src/codegen/opt). It is **off by default** and ordinarily waits for 1,000 entries into Tier C before upgrading. `ZIPP_NO_OPT_TIER_UP=1` requests it at the first eligible compilation.

Build the same crate with `features = ["instrument", "jit"]` in `harness/Cargo.toml`; the separate `jit` executable below **never** starts an instruction trace or installs a metering budget, so the JIT is eligible:

```bash
node scripts/make-fixtures.mjs
node scripts/make-jit-fixtures.mjs
CARGO_TARGET_DIR="$PWD/build" cargo +1.99.0 build --manifest-path harness/Cargo.toml --bins
ZIPP_OPT=1 ZIPP_OPT_ONLY=14 ZIPP_NO_OPT_TIER_UP=1 ZIPP_JITLOG=1 \
  build/debug/jit inputs/raw-208-warm.js
ZIPP_OPT=1 ZIPP_NO_OPT_TIER_UP=1 ZIPP_JITLOG=1 \
  build/debug/jit tests/tier-o-dispatch.js
```

The 1,600-call warming step hits the actual original extracted function. For **both** raw and recovered Knitsail handler 208, ZIPP reports:

```text
[jit] Tier O fn14 declines at ip 0: MakeCell { reg: 4 }
```

This is a shared mutable captured lexical variable (handler 208's nested bitreader/callback). Tier O's bytecode admission does not include `MakeCell`; the relevant baseline whole-function compiler also rejects the original's `LooseNe` operator (`z != 14`). Thus neither handler is compiled by Tier O, irrespective of whether its number of instructions (277 raw, 129 recovered) is under Tier O's 4,096-instruction limit. The raw and recovered outputs still match Node exactly in the earlier interpreter experiment.

**Independent self-contained dispatcher test:** `tests/tier-o-dispatch.js` uses a plain local numeric state and strict comparisons so Tier O accepts both versions. On ZIPP `b7521d2`:

| Function | Bytecode ops | SSA blocks | SSA values | Guards | Inlined |
| --- | ---: | ---: | ---: | ---: | ---: |
| Numeric-state flattened | 27 | 9 | 31 | 5 | 0 |
| Structured equivalent | 6 | 1 | 11 | 1 | 0 |

Node and ZIPP agree on `CHECK:2561600/2561600`. The optimizer lowers the original CFG into an SSA CFG but **does not eliminate the artificial dispatcher** or reconstruct the straight-line program. Its constant hoisting/CSE, type inference, guarded property/call optimization and register allocation are useful for native throughput, but are not a general path-sensitive SCCP/devirtualization engine that can recover navigable JavaScript. The decompilation/lifting research overlap is real at the dataflow/CFG level, not an existing solution to Knitsail.

**Reproducible upstream defect candidate:** `tests/tier-o-entry-loop.js` and four structurally similar `while`/`for`/`do-while` loop cases panic under `ZIPP_OPT=1 ZIPP_NO_OPT_TIER_UP=1` with `codegen/opt/build.rs:1785:13: the entry has no predecessor`. Source constructs `bpreds` from actual CFG edges, but the first block's `debug_assert!(preds.is_empty())` rejects a legitimate loop back-edge to entry. Normal baseline run completes; Tier O's debug compiler triggers a reproducible panic. We have **not** tested release builds or verified a fix; no upstream issue/PR was filed. A proper repair must handle entry phi values (e.g. via a synthetic unique entry) rather than deleting the assertion and assuming SSA remains correct. The full Knitsail harness with Tier O enabled also hit this bug while promoting an unrelated helper; `ZIPP_OPT_ONLY=14` isolates handler 208 and completes without the crash.

**Updated recommendation:** Keep ZIPP as a separate optional differential execution/semantic-trace backend; do not transplant the current Tier O into js-redox. If pursuing shared work, first expose a diagnostic bytecode/SSA graph with exact source mapping and add genuinely generalized constant/reachability propagation. The latter would be new functionality, not free reuse.

## ZIPP upstream bug #93: independently tested patch

We filed [ZIPP #93](https://github.com/f2i-com/zipp.org/issues/93) after
discovering that Tier O panics when bytecode entry has a legitimate loop back-edge.
The proposed general fix is carried as
[`patches/zipp-issue-93-entry-preheader.patch`](patches/zipp-issue-93-entry-preheader.patch),
generated via `git format-patch` from ZIPP commit
`362be460bba6f6ab3da4c369eb418bb070cbb4b7` based on upstream
`b7521d2a2a4b562a1764194de56659277232291e`.

It adds a conditional synthetic SSA preheader when bytecode entry has incoming
edges. Initial values and loop-carried values become distinct phi predecessors;
the compiler continues to assert that its *actual* entry has no predecessors.
No `MakeCell` admission or other unrelated JIT changes are made.

Apply against a clean ZIPP checkout at the pinned upstream revision:

```bash
git am /path/to/zipp-issue-93-entry-preheader.patch
cargo +1.99.0 test -p zipp-vm --no-default-features --features jit \
  --test jit_opt_entry_loops --test jit_opt_tier --test jit_opt_tier_up \
  --test jit_opt_int --test jit_opt_fold --test jit_opt_breadth \
  --test jit_opt_deopt_stress --test jit_opt_finally --test jit_opt_tier_up_stress
```

Validation on Acer with normal sccache:
- Five standalone Node-differential loop shapes: all compiled and executed in
  experimental Tier O, with exact output parity in **debug and release builds**.
  Includes nested loops, `do/while`, several back-edges and phi-carried state.
- New upstream integration test: passed, covering mixed numeric inputs,
  uninitialized locals, and zero-iteration cases.
- Eight existing targeted Tier O suites plus the new regression: all passed
  (four functional, four stress, one new regression).

Upstream fork creation from the available GitHub App credential returned
HTTP 403 (`Resource not accessible by integration`); no upstream PR is
claimed. The patch is preserved here on GitHub so it can be forked/cherry-picked
by an account with permission. It is not a js-redox production dependency.

## Follow-up: source-correlated computed-property witnesses (2026-11-10)

We tried to answer a narrower, actually unresolved Knitsail question: what
runtime property keys do the two conditional lexical aliases in handler 164
select? Unlike the original handler-208 experiment, this probes a specific
unresolved property-name choice rather than counting instruction steps.

**Input provenance:** original Knitsail file SHA-256
`d016538d95a679e1604c8e6f4c1fa5d78ff3d729eace6c832e54a10b550b4a98`,
exact 235-byte handler-164 function `[27625,27860)`. The generator
`scripts/make-key164-fixtures.mjs` verifies that hash and extracts the original
function bytes; raw payload and generated files stay untracked. Its context
models the original caller's observed lexical condition
`T="push"; JM="length"; if (H.length < 2) { T=H; JM=H; }`.
The rest of the browser initializer is **not executed**: the handler's other
dependencies are explicit deterministic stand-ins.

**Diagnostic extension:** The reproducible `git am` patch
[`patches/zipp-computed-property-witness.patch`](patches/zipp-computed-property-witness.patch)
is based on ZIPP `b7521d2`. It adds an optional embedder API
`start_property_witnesses(cap)` and `take_property_witnesses()`, separate from
the ZK proof recorder. Events include function ID/name, function source range in
the compiled source, bytecode IP, operation (`get`, `set`, `call`), raw key
bits/display, and whether the raw operand is an object. The buffer has an
explicit truncation bit and disables JIT during observation. **These are raw
computed-property operands, not claimed post-ToPropertyKey results or precise
expression source spans** (function spans and bytecode PCs are all ZIPP exposes).
The observer does not run ToPropertyKey, so it does not add guest coercion
effects. Instrumented interception is currently for the ordinary GetIndex,
SetIndex and CallMethodComputed bytecode paths: other fused/optimized property
opcodes are not claimed covered.

**Run:**

```bash
git -C upstream-zipp am ../patches/zipp-computed-property-witness.patch
mkdir -p inputs
node scripts/make-key164-fixtures.mjs
CARGO_TARGET_DIR="$PWD/build" cargo +1.99.0 build --manifest-path harness/Cargo.toml --bin witness
for case in normal short; do
  node "inputs/raw-164-$case.js"
  build/debug/witness "inputs/raw-164-$case.js"
done
node tests/property-no-extra-coercion.js
build/debug/witness tests/property-no-extra-coercion.js
```

**Measured** (both inputs ZIPP == Node byte-for-byte):
- `H="healthy"`: handler 164, compiled function range 573..808, IP 35
  reads raw key `length`; IP 63 reads `push`; successful
  `x(G,24,[10,20])` write.
- `H="x"`: handler 164, source range 567..802, IP 35 reads `x`;
  IP 63 reads `x`; a subsequent index is `NaN`. The call throws
  `TypeError`, matching Node. No write.
- Object-key `get` / `set` / `call` test:
  `tests/property-no-extra-coercion.js` matched Node including all
  `toString` invocation counts. An object operand is explicitly marked
  as such; its diagnostic display is **not** substituted for a resolved key.
- For the normal / short fixtures the observer recorded 19 / 9 total events,
  respectively, including activity inside test helper functions; no truncation.

**Verdict:** This independently observes actual alias operands on the original
Knitsail handler under two modeled inputs. It does **not** uncover a new alias
or establish which input the live browser supplied: js-redox's static lexical
analysis had already described both conditional outcomes. **Do not integrate
this into production js-redox based on this evidence alone.** Further work
would need a genuine novel witness from the live caller with source-specific
provenance, and must distinguish observed executions from universal rewrites.

No changes to active js-redox reconstruction worktree. Experimental ZIPP patch
is versioned only in this draft PR, not proposed as an upstream performance or
correctness change.

## Real archived caller -> handler 164 -> ZIPP (2026-11-10)

This follow-up uses **the actual captured Google Knitsail challenge wrapper**
rather than choosing the caller's `H` in a synthetic fixture. No new live
network requests are made. The original HTML and the captured program string
are private inputs and are **not committed**.

**Reproducible provenance:**

- Saved 2026-09-27 HTML: 92,667 bytes; SHA-256
  `fa1a074588751a928703945a359792756f3be075752f3e8a1ff252a578581c6c`,
  originally under cold-storage's
  `/srv/scratch/searxrs2/research/google-historical-2026-09-27/fresh-vm-replay2/p15601/initial.html`.
- VM script embedded in that exact HTML: 63,650 bytes; SHA-256
  `e414463345509a89678cd7dc9afa9b9391e4dce58a56f6a1e641990f2884fa5e`.
  Its source contains **exactly** the original 235-byte Knitsail handler 164
  also embedded in the pinned js-redox source
  `d016538d95a679e1604c8e6f4c1fa5d78ff3d729eace6c832e54a10b550b4a98`.
- The original, readable outer wrapper calls `knitsail.a(p, callback, ...)`.
  The actual VM dispatcher
  `hV` selects `AV[Q.substring(0, 3) + "_"]` and calls it with
  `Q.substring(3)`. The exact source caller chain
  `AV.aoF_(J, ...) -> new Wd(..., J, ...) -> oU(..., H=J, ...)`
  identifies this string as the conditional property-alias control.

**Real archived execution:**

- The original HTML wrapper executed under the archived Node VM browser
  simulation; the entry observer wraps exported `a` and dynamically selected
  `<prefix>_` methods *after* VM installation but before wrapper execution.
  Baseline and wrapped replays both produce a usable `SG_SS` cookie
  (851-character value). No cookie or challenge payload is committed.
- Exactly one `knitsail.a` call: 8 arguments; first argument is a
  **16,039-character** string, starting with dispatch prefix `aoF`.
- Exactly one `knitsail.aoF_` call: 9 arguments, first argument is the exact
  **16,036-character** `knitsail.a` first argument after `.slice(3)`;
  SHA-256 `150e6812ca473b15ed5a415fc2c99e62db468dbc354d3d41b51992dfe6531eba`.
- This clarifies an initial misleading measurement: an unparsed `var p='...'`
  **source literal text** is 16,042 characters because it includes escape
  sequences; the *runtime* string is 16,039. There is **no** six-character
  mutation. The function receives the 3-character-trimmed runtime value.
- For this H, `H.length < 2` is false, preserving `JM="length"` and
  `T="push"`. Under the original handler 164, ZIPP observed
  `GetIndex` at IP 35 with key `length`, IP 63 with `push`, and IP 64
  with numeric index `0` then `1`. Function source span in generated
  JS: `16602..16837`. 19 events, no truncation.
- **Node/ZIPP stdout parity passes** for all three modeled handler cases
  (`normal`, `short`, `archived`). The rest of the handler's closure
  dependencies remain deterministic stand-ins; the full original browser
  initializer is not run in ZIPP. Runtime witness != universal source proof.

**Replay on Acer (Rust 1.99, configured sccache):**

```bash
cd prototypes/zipp-knitsail
# Apply the observer patch first to a sparse checkout of pinned ZIPP b7521d2.
git -C upstream-zipp am ../patches/zipp-computed-property-witness.patch

mkdir -p inputs
export KNITSAIL_HTML_SHA256=fa1a074588751a928703945a359792756f3be075752f3e8a1ff252a578581c6c
export KNITSAIL_CAPTURE_H_PATH="$PWD/inputs/archived-h.json"
node scripts/replay-captured-html.cjs /path/to/private/initial.html \
  > inputs/archived-caller-report.json 2> inputs/archived-caller.log

KNITSAIL_H_INPUT="$PWD/inputs/archived-h.json" node scripts/make-key164-fixtures.mjs
CARGO_TARGET_DIR="$PWD/build" cargo +1.99.0 build --manifest-path harness/Cargo.toml --bin witness
node inputs/raw-164-archived.js > inputs/archived-node.out
build/debug/witness inputs/raw-164-archived.js \
  > inputs/archived-zipp.out 2> inputs/archived-zipp.log
cmp inputs/archived-node.out inputs/archived-zipp.out
```

`replay-captured-html.cjs` reuses the existing historical Node browser mocks,
with an opt-in captured-`H` output path and output redaction. It is deliberately
not a general browser emulator; function wrappers can affect reflection, and
one archived challenge does not establish that all real-world `H` values are
long strings. Keep js-redox's conditional property aliases intact.

**Verdict:** This closes the missing *observed real caller input* loop for the
archived source. It supplies a new **execution witness**, not a new structural
recovery or a new static proof. ZIPP integration beyond the experiment remains
unjustified until it recovers a fact unavailable from the actual source graph.
