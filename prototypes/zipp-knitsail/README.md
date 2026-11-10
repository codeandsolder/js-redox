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
