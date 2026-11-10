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
git -C upstream-zipp sparse-checkout set crates/zipp-vm crates/regress-fork crates/zipp-numparse
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
