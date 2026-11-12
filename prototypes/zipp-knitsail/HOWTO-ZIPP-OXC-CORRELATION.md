# Join native ZIPP dynamic source observations to the original OXC direct-eval inventory

An **experimental source-correlated runtime observation**, not an importer
witness. This path deliberately does not rewrite JavaScript, read the entire
corpus, or turn on per-instruction trace logging.

## Inputs and execution

This builds on the [native ZIPP observer patch](HOWTO-ZIPP-DYNAMIC-SOURCE-OBSERVER.md)
at upstream ZIPP `bcca68127fe86f0b8a59fd9e6c694f7518406647`.
The `harness` Cargo manifest expects the checkout at `upstream-zipp/`
(the directory is gitignored). Use Rust **1.99** and the configured sccache.

```bash
cd prototypes/zipp-knitsail
git clone https://github.com/f2i-com/zipp.org upstream-zipp
git -C upstream-zipp checkout bcca68127fe86f0b8a59fd9e6c694f7518406647
git -C upstream-zipp apply --check ../patches/zipp-native-dynamic-source-observer.patch
git -C upstream-zipp apply ../patches/zipp-native-dynamic-source-observer.patch

# Original source is loaded BYTE-FOR-BYTE by both engines.
cargo +1.99.0 run --manifest-path harness/Cargo.toml --bin zipp-observe \
  -- original.js > zipp-events.json

# Command from the separately developed OXC inventory PR #184:
deobfuscate-safe eval-sites original.js > oxc-sites.json

node scripts/link-zipp-eval-sites.mjs \
  original.js oxc-sites.json zipp-events.json > correlated.json

node --test tests/zipp-source-correlation.test.mjs
```

The runner also accepts `ENTRY.js` as its second path argument; this is
evaluated by the host *after* the original script. Its own compiler event is
classified indirect/host and cannot be attributed to the original, but calls
into original-program functions can produce attributable direct evals.
The runner includes execution status (including exceptions), source SHA-256,
ordered source attempts, raw WTF-8-capable source bytes as `sourceHex`,
VM caller metadata, and the observer's truncation flag. It does **not**
enable a per-instruction execution trace or disable the JIT. Its fixed pilot
budgets are 10 million VM steps, 10,000 captured events, and 32 MiB captured
source; a truncated observation is explicitly incomplete.

## Exact joining rules

1. Read the original as UTF-8 bytes without removing a UTF-8 BOM, hash it
   with SHA-256 and require that both independent `sourceSha256` values match.
   Reject incompatible inventory/observer schemas.
2. Validate every OXC original `evalSite` and `firstArgumentSite` UTF-16
   span against the original bytes decoded as UTF-8. Surrogate-pair-splitting
   boundaries and altered expressions fail validation.
3. Compute ECMAScript line/UTF-16-column positions (CRLF, CR, LF, U+2028 and
   U+2029, and non-BMP code points). Index each OXC call *start* by position.
4. Only a ZIPP `direct-eval` event with `origin:initial-program` and an
   available VM callsite location may match. Require one and only one OXC
   executable call at that exact location. Attach the exact verified AST
   expression and argument spans, the input SHA-256, and the VM function/IP.
5. Preserve every other event as `unmatched`, `ambiguous` or `unavailable`
   with the reason. Do not silently choose the first duplicate site, claim a
   generated function belongs to the original, classify an indirect eval as
   direct, or infer an original callsite from the last native stack frame.

The result is an event-by-event **source correlation**, not a successful
execution/return witness. An OXC call span whose opening parenthesis differs
from ZIPP's callsite coordinate may remain unmatched: this is the correct
outcome until we have a verified callee-position contract. No fabricated
span shifting. A runtime-generated function needs its *own* compiled-source
identity before it can be safely joined; a VM-local function ID alone is not
stable between executions.

## Remaining integration boundary

This is not yet a valid `--observed-direct-bundle` producer for PR #184:
that importer requires additional dynamic source representations and
runtime-result/throw outcome witnesses. The engine stream cannot replace
the Node v2/v3 producer as-is. It only provides an independent and
non-rewriting source-location observation channel. Do not treat the
`matched` status as full original lexical binding proof or universal
deobfuscation; the source locations are from ZIPP's existing stack-callsite
metadata, checked against OXC's exact original AST inventory.

See [js-redox PR #179](https://github.com/codeandsolder/js-redox/pull/179)
and [the Notion ZIPP technical handoff](https://app.notion.com/p/416f74be902081d296edf930c0520607).
