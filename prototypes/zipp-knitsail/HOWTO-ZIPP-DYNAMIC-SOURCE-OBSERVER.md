# Native ZIPP runtime-source observer (experimental)

This is an **engine-native alternative** to source-rewriting capture for
investigating JavaScript-generated JavaScript. It is an optional prototype,
not an importer or replacement for the original OXC/source-tree proofs.

## Exact base and patch

- ZIPP upstream repository: https://github.com/f2i-com/zipp.org
- Patch base: `bcca68127fe86f0b8a59fd9e6c694f7518406647` (2026-11-12 ZIPP main, v0.0.35 line).
- Local source commit that generated the patch: `d73d166`.
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

The observer has independent maximum event-count and aggregate source-byte
caps, both chosen by the host. It marks `truncated=true` and drops further
events when exhausted but does not change guest execution. The recorder must
first be installed through `set_limits`; without it the capture request is
a no-op.

## Proof boundary and follow-up

**This captures source bytes, not original AST callsite provenance.** The
current event does not contain exact original UTF-16 eval expression/argument
spans, static source hashes, stable lexical binding identity, outcome status,
or browser host effects. Therefore it is **not yet a source-tree importer
input** and should not be promoted into PR #184 as if it were equivalent to
the Node v2/v3 witnesses.

The next valuable engine experiment is provenance: correlate the compiler
event with an actual caller function and a verified original source callsite,
including nested eval/Function and indirect cases. Compare against native
OXC `eval-sites` discovery and Node capture before defining a shared witness
schema. Do not add another bytecode-step counter or JIT benchmark as a proxy
for source recovery.

The unrelated ZIPP Tier O preheader bug #93 was already fixed upstream
in v0.0.35; **do not apply the old issue-93 patch** to this checkout.
