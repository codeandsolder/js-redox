# Generic two-stage VM source capture (v2)

This producer is separate from the archived Knitsail browser-model runner.
Use it when an **already acquired** JavaScript loader supplies one decoded
executable string via an indirect eval and a second script invokes a specific
direct eval inside that executable. No Knitsail API, challenge token, DOM
emulator, or external service is required.

It produces an exact original outer loader, exact original executable, raw
content-addressed operand files, and a report accepted by the existing v2
exporter and native Rust/OXC importer. Source trees remain static-first;
captured code is evidence about **one execution**, not universal recovery.

## Inputs

Create `outer.js` and `entry.js`. The outer loader must contain one selected
`(0,eval)(` invocation that decodes the executable at runtime. `entry.js`
runs after loading the outer script and triggers the dynamic behavior.

Optionally provide `inner.js` to require the observed decoded executable to
match an independently saved original byte-for-byte. For example, a small
fixture can use:

```js
// outer.js
var packed = "var worker = function(D) { return eval(D + ' + 1'); };";
(0,eval)(packed);

// entry.js
if (worker('1') !== 2) throw Error('wrong result');
```

With a matching `inner.js`, the capture configuration can be:

```json
{
  "outerFile": "outer.js",
  "innerFile": "inner.js",
  "entryFile": "entry.js",
  "evalExpression": "eval(D + ' + 1')",
  "firstArgumentExpression": "D + ' + 1'",
  "maxEvents": 10000,
  "timeoutMs": 10000
}
```

The two expression snippets **must be unique** in their respective original
source layers; ambiguous snippets are rejected instead of picking the first
textual match. Alternatively, configure precise `outerSite`, `evalSite`,
and `firstArgumentSite` objects with `start`, `end` and `expression` fields;
all intervals are original UTF-16 code-unit positions.

`firstArgumentSite` covers the *first non-spread argument*, and the
instrumenter wraps only that original argument expression, leaving later
arguments and their side effects untouched. It wraps the direct eval result
without moving the eval into a new lexical function scope. The original
source files remain unmodified. The Rust importer independently checks that
the original direct eval site is an actual executable AST node; textual site
location in the Node producer alone is **not** proof.

JSON `globals` adds serializable globals to the modeled Node VM. Optional
`identityFile` chooses the **raw bytes** hashed for the capture identity
(by default `outer.js`); it can be a binary archive and need not decode as
UTF-8. The v2 JSON field remains named `htmlSha256` for importer
compatibility even when the identity file is *not* HTML; `identityKind`
discloses the distinction.

## Capture, export, import

From the experimental project directory:

```bash
node scripts/capture-vm-eval.mjs path/to/config.json inputs/generic-capture

node scripts/export-runtime-eval.mjs \
  inputs/generic-capture/report.json \
  inputs/generic-capture/sources \
  inputs/generic-export \
  /path/to/deobfuscate-safe

deobfuscate-safe source-tree /path/to/static-source-tree /path/to/combined \
  --observed-eval inputs/generic-export \
    inputs/generic-capture/outer.js inputs/generic-capture/inner.js
```

The native import CLI in [PR #184](https://github.com/codeandsolder/js-redox/pull/184)
checks both source layers, the executable OXC direct-eval callsite, operand
hashes/UTF-16 lengths, and lexical matching. It retains a separate observed
tree and never substitutes runtime source for static reconstruction.

## Exactness and scope

- The Node runner is synchronous and captures one specified direct-eval site
  in a decoded executable. It is **not** a browser environment, general
  instrument-every-eval engine, or a security boundary.
- The producer records strings only; nonstring eval inputs have no generated
  source bytes and are counted separately. Every captured source is hashed
  and retained as exact UTF-8 bytes. Isolated UTF-16 surrogates, which cannot
  round-trip through UTF-8, are rejected instead of changed silently.
- Returned outcomes are measured. If a captured call does not return through
  the observer, it is recorded as a throw with an **unknown type**. Nested or
  re-entrant captures that would make return attribution ambiguous are
  rejected. This does not infer exception classes. A following capture after
  a caught unresolved throw is also rejected rather than misattributed.
  When eval has later arguments, a nonreturning call is rejected outright:
  a later argument might throw **before eval runs**, and its first operand
  alone is not evidence of executed eval code.
- Only the first outer indirect eval is intercepted and the native eval
  binding is restored before running the inner executable, preserving direct
  eval's original caller lexical scope. The instrumentation copy is never
  considered original-source proof.
- The run must complete successfully. Errors, mismatched decoded source,
  ambiguous expression snippets, and reused output paths do not publish a
  capture. More complex browser behavior still needs appropriate modeled
  globals/entry input rather than treating arbitrary JS as a browser.
- The v2 exporter independently reformats standalone-parseable sources;
  raw-only fragments are retained. Both source and report directories are
  private inputs, not intended for source control.

Run focused tests:

```bash
node --test tests/generic-vm-eval-capture.test.mjs \
  tests/runtime-eval-export.test.mjs tests/runtime-source-tree-link.test.mjs

# Stronger end-to-end verification requires the built native importer in PR #184:
JSREDOX_DEOBFUSCATE_BIN=/path/to/deobfuscate-safe \
  node --test tests/generic-vm-native-import.test.mjs
```

[Knitsail-specific archived replay](HOWTO-RUNTIME-PROVENANCE.md) remains a
separate fixture and proof of the historical 51-event, 40-source sample.
