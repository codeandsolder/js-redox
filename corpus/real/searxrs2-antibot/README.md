# Private anti-bot regression corpus metadata

Real captured/reference JavaScript is intentionally **not stored in this public repository**.
This directory retains only provenance, hashes, roles, and regression metadata in `manifest.json`.

Provide the private corpus in the same relative layout under an external workspace and set:

```sh
export JSVM_FIXTURE_ROOT=/path/to/private/js-redox-corpus-workspace
uv run --no-project python scripts/check-real-antibot-corpus.py
```

The canonical development corpus lives outside Git. Generated/minimal synthetic fixtures remain in
`corpus/generated/` because they are authored specifically for this project.

`*.raw.js`, `*.pretty.js`, and external deobfuscated/reference bodies described by the manifest are
private corpus data. SHA-256, byte size, family, date, and purpose remain public so a mounted corpus
can be verified without publishing its contents.
