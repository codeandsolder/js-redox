# Reproduce the two-stage Knitsail source overlay

This is an **execution-observed**, nonproduction source-tree extension.

The saved private HTML challenge is at
`/srv/scratch/searxrs2/research/google-historical-2026-09-27/fresh-vm-replay2/p15601/initial.html`
on cold-storage. Exact HTML SHA-256:
`fa1a074588751a928703945a359792756f3be075752f3e8a1ff252a578581c6c`.
Never commit the HTML, generated VM or challenge output.

From `prototypes/zipp-knitsail`:

```bash
mkdir -p inputs/eval
cp /path/to/private/initial.html inputs/archived.html
export KNITSAIL_HTML_SHA256=fa1a074588751a928703945a359792756f3be075752f3e8a1ff252a578581c6c
export KNITSAIL_VM_SOURCE_OUT="$PWD/inputs/outer-vm.js"
export KNITSAIL_INNER_VM_OUT="$PWD/inputs/inner-vm.js"
export KNITSAIL_DYNAMIC_DIR="$PWD/inputs/eval"
node scripts/replay-captured-html.cjs inputs/archived.html \
  > inputs/runtime-report.json 2> inputs/replay.stderr

export CARGO_TARGET_DIR="$PWD/inputs/build"
cargo +1.99.0 build --manifest-path ast-site-probe/Cargo.toml
node scripts/export-runtime-eval.mjs \
  inputs/runtime-report.json inputs/eval inputs/observed \
  /path/to/deobfuscate-safe

export STATIC=/path/to/complete/knitsail-static-source-tree
node scripts/link-runtime-source-tree.mjs \
  "$STATIC" inputs/combined \
  "$CARGO_TARGET_DIR/debug/knitsail-ast-site-probe" \
  inputs/observed inputs/outer-vm.js inputs/inner-vm.js

node --test tests/runtime-eval-export.test.mjs \
  tests/runtime-source-tree-link.test.mjs
cargo +1.99.0 test --manifest-path ast-site-probe/Cargo.toml
```

The exporter **requires v2** `sourceProvenance`, retaining both
`outerLoader` SHA-256 and `indirectEvalSite` at `735..744` and
`innerExecutable` SHA-256 and executable `evalSite` at `28442..28449`.
The outer source location is *text-verified* and the loader's indirect eval
is execution-observed. The inner source is normalized by stripping the
random leading newline prefix, hashed exactly, and its direct eval callsite
is independently checked by the Rust/OXC AST+semantic probe.

The linker signature is intentionally incompatible with v1:
`STATIC_TREE OUTPUT_TREE AST_PROBE_BIN [OBSERVED_TREE OUTER_LOADER_JS INNER_EXECUTABLE_JS]...`.
Repeat source triplets for multiple archives. It refuses mismatched source
hashes, invalid sites, absent AST proof, duplicate capture IDs, symlinks,
overlapping paths and existing outputs; original static JS and
`reconstruction.json` remain unchanged. The combined tree adds
`runtime-observed/` navigation, origin manifests and static-side back-links
marked as **AST lexical-site matches**, not whole-function equivalence.

The real captured replay completes with an 851-character `SG_SS` value
both with and without the observer. It records 51 calls, 40 unique operands,
27 normal results and 24 throws, with no truncation. Setting
`KNITSAIL_DYNAMIC_MAX_EVENTS=3` tests explicit bounded truncation.

All private captures, exported readable trees and build artifacts belong
in ignored `inputs/`. Prior experimental notes live in
[RESEARCH-HISTORY.md](RESEARCH-HISTORY.md), separate from current instructions.
