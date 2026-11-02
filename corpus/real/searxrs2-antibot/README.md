# Private anti-bot regression corpus metadata

Real captured/reference JavaScript is intentionally **not stored in this public repository**.
This directory retains provenance, hashes, roles, and the acceptance policy in `manifest.json`.

Mount the private corpus with the same relative sample layout and evaluate it with the Rust corpus evaluator:

```sh
cargo +1.99.1 run -p jsvm-lift --bin corpus-eval -- \
  corpus/real/searxrs2-antibot/manifest.json \
  --corpus-root /path/to/private/js-redox-corpus-workspace/corpus/real/searxrs2-antibot \
  --report /path/to/report.json
```

The evaluator verifies capture hashes, regenerates analyst formatting in-process, runs safe deobfuscation in-process, checks generated syntax with Node, scans the formatted source in-process, and enforces the manifest-owned transform/string/scanner thresholds. It writes no source artifacts outside a temporary directory; `--report` is the only durable output.

The canonical development corpus lives outside Git. Generated/minimal synthetic fixtures remain in
`corpus/generated/` because they are authored specifically for this project.

`*.raw.js`, `*.pretty.js`, and external deobfuscated/reference bodies described by the manifest are
private corpus data. SHA-256, byte size, family, date, purpose, and acceptance thresholds remain public so a mounted corpus can be verified without publishing its contents.
