# Knitsail dynamic-source recovery research

**Current state (2026-11-12).** This experimental js-redox extension recovers
JavaScript emitted at actual runtime eval sites and links it alongside static
reconstruction. The static tree remains authoritative for universal recovery;
runtime fragments remain **execution-observed**, never silently substituted
for proven static source.

## Verified result

The saved September 27 Knitsail challenge has a two-stage loader.
The **outer loader** indirectly evaluates a newly constructed **inner VM**;
the inner VM subsequently executes direct `eval(D)` in a nested `oU` callback.
The archived replay produces 51 eval calls and 40 unique strings (25
standalone formatted, 15 retained as exact raw-only). Five strings construct
new function definitions absent from the existing static tree.

The current **v2 dual-layer provenance** records the outer loader SHA-256
`e4144633...f2884fa5e` and indirect invocation at UTF-16 `735..744`, plus
the normalized inner executable SHA-256 `0aa3362a...75f67d` and its
direct `eval(D)` at `28442..28449`. The random loader-added newline prefix is
accounted for separately.

The linker verifies both hashes, invokes the Rust/OXC semantic AST probe,
and attaches all 40 operands to the three structurally matching static views:
extracted `oU` helper, explained `oU`, and full lexical source.
The match checks the function parameter/binding chain and the direct,
unresolved `eval` call; it is **not proof of whole-function equivalence**.

All 785 static JS/manifest files remain byte-identical in the combined tree.

## Components and documentation

- `scripts/capture-direct-eval.mjs`: original JavaScript direct-eval capture
  across **multiple selected callsites in a single execution**, emitting
  run-wide events and one v3 witness per observed site. No invented loader.
  Optional entry
  script. Verifies exact original executable bytes and UTF-16 callsite.
  [Direct-source usage](HOWTO-GENERIC-RUNTIME-EVAL.md#direct-original-javascript-no-loader).
- `scripts/export-runtime-eval-bundle.mjs`: export each observed direct site
  independently while preserving global event ordering and one bundle index.
- `scripts/eval-capture-core.mjs`: shared source-location, argument-observer
  and content-addressed capture logic for direct and decoded executables.
- `scripts/capture-vm-eval.mjs`: **generic configurable** synchronous Node VM
  producer for arbitrary two-layer loaders and exact direct-eval source sites;
  no Knitsail/DOM requirements. Emits original source layers, raw operands and
  a v2 report usable by the same exporter and native importer.
  [Generic setup, scope and limitations](HOWTO-GENERIC-RUNTIME-EVAL.md).
- `scripts/replay-captured-html.cjs`: modeled archived browser replay;
  outer/inner source capture and observed eval inputs/outcomes.
- `scripts/export-runtime-eval.mjs`: v2 loader and v3 direct manifests,
  exact deduplicated raw source and independent readable formatting.
- `ast-site-probe/`: Rust 1.99 / OXC AST and semantic resolver.
- `scripts/link-runtime-source-tree.mjs`: verifiable multi-capture overlay
  with bidirectional AST-linked navigation.
- `tests/`: focused regression coverage for integrity, failures and cleanup.

[Reproduction steps and schema](HOWTO-RUNTIME-PROVENANCE.md).

[Historical experiments and pre-v2 findings](RESEARCH-HISTORY.md).

## ZIPP upstream

Our Tier O synthetic-preheader fix, authored `codeandsolder`, shipped as
[ZIPP v0.0.35](https://github.com/f2i-com/zipp.org/releases/tag/v0.0.35),
commit `041f280`. The old `patches/zipp-issue-93-entry-preheader.patch` is
**historical for pre-fix ZIPP b7521d2 only**; don't apply it to current ZIPP.
Node recovered the runtime source, while experimental ZIPP independently
executed five captured generated function expressions with Node parity.

## Native ZIPP dynamic-source capture pilot

A separate engine-level observer records bounded compiler-entry source bytes
without rewriting JavaScript, including direct/indirect eval, Function
constructors, nested eval and cache-hit attempts. Direct eval events now
carry original-vs-runtime-installed caller identity and stack-style UTF-16
positions; indirect/constructor origin remains explicitly unavailable.
**13/13 focused Rust tests pass.** This still lacks independently verified OXC
AST identity, so Node v2/v3 capture and native OXC import remain the
operative provenance pipeline.

[Implementation, pinned ZIPP patch and proof boundaries](HOWTO-ZIPP-DYNAMIC-SOURCE-OBSERVER.md).

## Exact original-source correlation

The optional [ZIPP → OXC callsite correlation pilot](HOWTO-ZIPP-OXC-CORRELATION.md)
adds a native ZIPP runtime-source CLI and an exact-SHA-256/UTF-16 join against
the native OXC `eval-sites` inventory. Direct eval events can be paired with
one verified initial-program AST callsite; ambiguous, unsupported, generated,
indirect and otherwise unlocatable events stay explicitly unresolved. This is
diagnostic evidence, **not yet** an importer witness.
