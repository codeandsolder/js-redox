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

Use the helper rather than raw `cargo`:

```sh
scripts/build-jsvm-lift.sh
```

It:

1. uses Rust 1.98.1's real Cargo binary;
2. keeps build artifacts on the spacious `/srv/scratch` filesystem in `.cargo-target/`;
3. preserves `RUSTC_WRAPPER=/usr/local/libexec/sccache-client`, so rustc work remains distributed;
4. derives a sensible job count from live sccache-dist capacity and current farm occupancy.

The scheduler currently has 12 remote CPUs. The normal project cap is 8, but the helper leaves a two-slot reserve and reduces jobs when other distributed work is already in flight.

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
Webpack/Next chunk + direct module-table recovery into src/_modules/
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
- `src/_modules/` contains explicit Webpack/Next modules recovered from chunk payloads and strict direct module-table shapes.
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
```

For a normal browser **Save Page / Webpage, Complete** export, the companion `Saved Page_files/` directory is discovered automatically. `--assets-dir` can override it. Saved-page files get stable synthetic URLs for graph resolution; an original page URL from Chromium's `saved from url=(...)` marker is retained separately when available.

The driver runs capture normalization, readable-source materialization, source-map recovery, literal module/worker reference analysis, document import-map resolution, safe deobfuscation, explicit bundle-module extraction, generated-code recovery, VM triage/devirtualization, provenance-graph construction, and an analyst-facing project README. Import maps are resolved with exact, prefix and scoped mappings; multiple maps keep earlier exact definitions, and document context is propagated only through captured module imports so worker graphs do not accidentally inherit page import maps.

`har-project` remains the HAR-specific importer. `saved-page-to-manifest.py` performs the equivalent normalization for saved HTML plus its resource directory. Both converge on the same internal resource/inline-script model.

`materialize-har-source.py` produces the readable `src/` tree. JavaScript is parsed and regenerated by Oxc; parse failures fall back to the exact raw body and are recorded rather than silently discarded.

`scan-har-project.py` prefers a proven safe-deobfuscated view for captured units while retaining the captured file as provenance. Static `Function(...)` payloads become bounded recursive code units: each exact recovered child is passed through the same safe string-recovery + deob stack, hash/provenance validated, and scanned from the furthest proven-safe result. If semantic validation or a recovery stage refuses the child, scanning falls back to the exact recovered bytes and records that decision in `analysis/generated-recovery.json`. Supported direct-switch VMs are lifted with `switch-ir`; linked function-table VMs use `table-ir`. Large unlinked handler tables are retained as explicit VM candidates rather than mislabeled as successfully devirtualized.

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
