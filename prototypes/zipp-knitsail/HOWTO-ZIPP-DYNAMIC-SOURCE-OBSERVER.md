# Native ZIPP runtime-source observer (experimental)

This is an **engine-native alternative** to source-rewriting capture for
investigating JavaScript-generated JavaScript. It is an optional prototype,
not an importer or replacement for the original OXC/source-tree proofs.

## Exact base and patch

- ZIPP upstream repository: https://github.com/f2i-com/zipp.org
- Patch base: `bcca68127fe86f0b8a59fd9e6c694f7518406647` (2026-11-12 ZIPP main, v0.0.35 line).
- Local source commit that generated the patch: `38aa7942c1f1d11b6c10a5bf2d4329e0ff7610ef`.
- Patch: [zipp-native-dynamic-source-observer.patch](patches/zipp-native-dynamic-source-observer.patch).
- It modifies **only** `zipp-vm` embedding/instrumentation and adds a focused
  Rust integration test; no copied full ZIPP source tree or private payload.

From a clean ZIPP checkout at the pinned commit, with Rust 1.99 and the
configured sccache wrapper:

```bash
git checkout bcca68127fe86f0b8a59fd9e6c694f7518406647
git apply --check /path/to/js-redox/prototypes/zipp-knitsail/patches/zipp-native-dynamic-source-observer.patch
git apply /path/to/js-redox/prototypes/zipp-knitsail/patches/zipp-native-dynamic-source-observer.patch
cargo +1.99.0 test -p zipp-vm --no-default-features --features instrument --test dynamic_source_capture
```

## Host API (instrument feature)

```rust
use zipp_vm::embed::{compile_script, DynamicSourceKind};

let mut state = compile_script("let result = eval('1+2');")?;
state.set_limits(1_000_000, None);
state.start_dynamic_source_capture(100, 1_000_000);
state.run_init()?;
let capture = state.take_dynamic_source_capture().expect("observer enabled");
assert!(!capture.truncated);
assert_eq!(capture.events[0].kind, DynamicSourceKind::DirectEval);
assert_eq!(capture.events[0].source_bytes, b"1+2");
assert!(matches!(
    capture.events[0].outcome,
    Some(zipp_vm::embed::DynamicSourceOutcome::Returned { type_name: "number" })
));
```

This is **an observation of attempts reaching ZIPP's common runtime compiler**:
direct eval, indirect/host/ShadowRealm eval, and `Function` constructor
wrappers. It does not change original JS, move eval out of lexical scope, or
turn on per-instruction tracing. A `Function` constructor cache hit remains
an attempted dynamic evaluation; syntax errors appear as attempts as well.
Non-string eval never compiles new code and emits no source event.

Events are ordered at **compiler entry**; that is not JS return order. Native
source is stored as exact bytes, not a lossy UTF-8 string: ZIPP may supply
WTF-8 source containing unpaired UTF-16 surrogates. `Function` constructor
events contain the assembled wrapper given to the compiler, not merely the
literal body argument.

**Runtime outcome extension (2026-11-13):** every captured event now has
`outcome` = `Returned { type_name }`, `Threw`, or `None` while in
flight. It observes the return from that *specific* runtime compiler
attempt, including its compile/instantiation failures; it does not represent
the success or failure of the outer script. The type name is ZIPP's
side-effect-free internal JavaScript `typeof`, not a serialization or exact
value. In particular, an object or function is **not** converted with
`toString`, a thrown value is not reconstructed, and an asynchronous
Promise resolution is not observed. Nested calls finish their own events by
session-qualified event ticket, not by "last event" or textual source match;
starting a new observer mid-flight cannot finish an unrelated event.

The observer has independent maximum event-count and aggregate source-byte
caps, both chosen by the host. It marks `truncated=true` and drops further
events when exhausted but does not change guest execution. The recorder must
first be installed through `set_limits`; without it the capture request is
a no-op.

### Direct-eval caller identity and cached evaluations

For **direct eval**, the VM has explicitly synchronized the caller instruction
offset, so each event also exposes an optional `DynamicSourceCaller` with
the VM-local function ID, bytecode IP and the exact stack-style **1-based
source line / UTF-16 column**. The compiler's existing callsite table supplies
the location; no second source mapping system was added. The caller's
`DynamicCallerOrigin` distinguishes functions from the **initial compiled
program** from functions **installed at runtime** (e.g. an eval-generated
function). This matters before attempting to join a site to the original
source's OXC AST.

The optimized direct-eval compilation cache has a fast path that bypasses
`do_eval`. This patch instruments that path too: otherwise repeated
calls could disappear from a supposedly complete event history. The source
bytes and event order are retained for cached attempts.

**Indirect eval and Function constructor callsites remain explicitly
unavailable**: their native call paths do not consistently synchronize
the JS frame IP. Reusing a stale frame position risks falsely identifying a
different call. Their exact compiler-input bytes and event ordering are still
captured; the `caller` field is `None` until a correct native-callsite
handoff is implemented. This is a deliberate evidence constraint, not a
claim that those expressions are unobservable.

## Proof boundary and follow-up

**This captures source bytes, not original AST callsite provenance.** The
current event does not contain exact original UTF-16 eval expression/argument
spans, static source hashes, stable lexical binding identity, outcome status,
or browser host effects. Therefore it is **not yet a source-tree importer
input** and should not be promoted into PR #184 as if it were equivalent to
the Node v2/v3 witnesses.

The next integration experiment is to pair **InitialProgram** direct-eval
caller line/column with an **exact-hash-verified original executable** and
OXC's lexical `eval-sites` inventory. The source location is a pointer
to an existing executable callsite, not yet a full original AST interval or
argument binding proof. Ambiguous/unmatched sites must remain unresolved.
For indirect eval and Function, first add an explicit native call dispatch
origin that does not fall back to stale frames. Compare against the Node
v2/v3 witnesses before defining a shared importer schema; do not replace
the proof-gated static reconstruction.

The unrelated ZIPP Tier O preheader bug #93 was already fixed upstream
in v0.0.35; **do not apply the old issue-93 patch** to this checkout.

## Verified validation (2026-11-13)

- Rust 1.99, configured sccache: **18/18 focused native Rust integration tests PASS** on the outcome prototype before the recorder-session regression tests were added. Recorder-session edge tests were added separately; see the current checkpoint for their final result.
- `cargo +1.99.0 clippy -p zipp-vm --no-default-features --features instrument --test dynamic_source_capture` completed, with three pre-existing build-script warnings in ZIPP `build/minify.rs` and `build/sha256.rs`. The strict `-D warnings` run fails on those same baseline warnings, not on the observer.
- A clean pinned upstream ZIPP checkout accepted the patch with `git apply --check`. No full Knitsail corpus run was made.

- New tests cover cached direct eval, nested caller positions, UTF-16 columns, unavailable native-call origins, and original-vs-runtime-installed function provenance.
