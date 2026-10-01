#!/usr/bin/env python3
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe"
FIXTURE = ROOT / "corpus/generated/reversible-obfuscation/selector-dispatch.js"
TMP = ROOT / "work/test-tmp/castle-normalization"


def run(argv, timeout=60):
    cp = subprocess.run(
        [str(x) for x in argv],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
    )
    if cp.returncode:
        raise RuntimeError(
            f"command failed ({cp.returncode}): {' '.join(map(str, argv))}\n"
            f"{cp.stdout}{cp.stderr}"
        )
    return cp


def main():
    if not BIN.is_file():
        raise SystemExit(f"missing binary: {BIN}")
    TMP.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="selector-", dir=TMP) as td:
        td = Path(td)
        out = td / "out.js"
        report = td / "report.json"
        before = run(["node", FIXTURE]).stdout
        run([BIN, FIXTURE, out, "--report", report])
        run(["node", "--check", out])
        after = run(["node", out]).stdout
        expected = "5 2 20 5 5 3 16 99 5\n6\n5\n"
        assert before == after == expected, (before, after)

        text = out.read_text()
        assert "dispatch(42, 9, 4)" in text, "alias-selected branch must remain dynamic"
        assert text.count("ambiguous(1, 4)") == 2, (
            "selector equal to a possibly-uninitialized var alias must fail closed"
        )

        meta = json.loads(report.read_text())
        transforms = meta["transforms"]
        assert transforms.get("selector_dispatch_specialize") == 7, transforms
        assert meta["safe_static_only"] is True
        print("PASS selector-dispatch", transforms)


if __name__ == "__main__":
    main()
