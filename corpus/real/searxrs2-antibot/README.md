# searxrs2 anti-bot real-world corpus

This directory mirrors selected JavaScript specimens from `/srv/scratch/searxrs2` for deobfuscator/devirtualizer regression work.

## Rules

- `*.raw.js` is byte-for-byte capture/reference input and is the provenance source of truth.
- `*.pretty.js` is an Oxc-codegen analyst view generated with `js-format`; never treat it as capture truth.
- `*.deobfuscated.reference.js` / `*.reference.js` are external or previously prepared comparison references, not output expected to match byte-for-byte.
- Exact source path, SHA-256, size, family, date and purpose live in `manifest.json`.

## Families

- **DataDome** — Qwant DataDome 5.10.0 production browser tag.
- **Cloudflare Managed Challenge** — two fresh Ecosia orchestrators from the same build with per-instance reshuffling, plus a smaller raw/reference pair.
- **Castle** — large browser anti-fraud/fingerprinting bundle with a paired deobfuscated reference.
- **Google Knitsail** — current live custom-VM wrapper plus a September 2026 public reference for cross-version structural comparison. The scanner now statically recovers the current wrapper's 62,648-byte literal-`Array.join` generated source unit without executing it.
- **acw_sc__v2 challenge** — two compact captures with different per-request `arg1` values; useful reversible-obfuscation / non-VM hard negatives covering table rotation, string-decoder indirection, self-defending scaffolding, permutation/XOR cookie derivation and reload.

Run `uv run --no-project python scripts/check-real-antibot-corpus.py` from the repository root for the non-executing corpus smoke/regression pass. The current manifest contains 8 raw specimens and 3 comparison/reference specimens.
