#!/usr/bin/env python3
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe"
FIXTURE = ROOT / "corpus/generated/reversible-obfuscation/datadome-direct-table.js"
SPARSE_FIXTURE = ROOT / "corpus/generated/reversible-obfuscation/sparse-direct-table.js"
IDENTITY_FIXTURE = ROOT / "corpus/generated/reversible-obfuscation/reference-identity-table.js"
TMP = ROOT / "work/test-tmp/datadome-normalization"


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
    with tempfile.TemporaryDirectory(prefix="direct-table-", dir=TMP) as td:
        td = Path(td)
        out = td / "out.js"
        report = td / "report.json"
        before = run(["node", FIXTURE]).stdout
        run([BIN, FIXTURE, out, "--report", report])
        run(["node", "--check", out])
        after = run(["node", out]).stdout
        assert (
            before
            == after
            == "cookie reload parseInt 17 true null invalid bm90LWRlY29kZWQ= dGhpcy1tdXN0LXN0YXktcmF3 17 true false 1 3 3 112 0 0 par 3 256 undefined b c x a 1 17 undefined parseInt 3\n"
        ), (before, after)
        text = out.read_text()
        assert "QInvalid(0)" in text, "invalid atob input must remain dynamic"
        assert "QDecoy(0)" in text, "unrelated atob use must not turn a raw table into a decoder"
        assert "CDecoy(0)" in text, "alphabet-like code must not turn a raw table into a decoder"
        assert "reassigned(5, 2)" in text, "reassigned helper functions must not be statically folded"
        assert "QEscaped(0)" in text, "escaped/mutable literal tables must not be statically decoded"
        assert "QInternalEscaped(0)" in text, "internally aliased/mutable literal tables must not be statically decoded"
        assert "QReassigned(0)" in text, "reassigned decoder functions must not be statically decoded"
        assert "QSideEffect(0)" in text, "decoder-looking functions with extra side effects must remain dynamic"
        assert "C(7)" in text, "out-of-range direct table lookups must not wrap modulo table length"
        assert "C(dynamicChoice ? 0 : 1)" not in text, "conditional decoder indices should become a literal-valued conditional"
        assert "C(dynamicChoice ? 0 : 7)" in text, "conditional decoder rewrites must fail closed when either branch is out of range"
        assert "CFixedSide(0)" in text, "fixed-alphabet decoder candidates with outer writes must remain dynamic"

        text = out.read_text()
        for expected in ('"cookie"', '"reload"', '"parseInt"', "17", "true", "null"):
            assert expected in text, (expected, text[:3000])
        meta = json.loads(report.read_text())
        transforms = meta["transforms"]
        assert transforms.get("string_array_decode", 0) >= 15, transforms
        assert transforms.get("pure_function_eval", 0) >= 5, transforms
        assert meta["safe_static_only"] is True
        print("PASS direct-table", transforms)

    with tempfile.TemporaryDirectory(prefix="sparse-direct-table-", dir=TMP) as td:
        td = Path(td)
        out = td / "out.js"
        report = td / "report.json"
        before = run(["node", SPARSE_FIXTURE]).stdout
        run([BIN, SPARSE_FIXTURE, out, "--report", report])
        run(["node", "--check", out])
        after = run(["node", out]).stdout
        assert before == after == "a b parseInt 17 c 99 parseInt 99 3\n", (before, after)
        text = out.read_text()
        for folded in ("QSparse(0)", "QSparse(2)", "CSparse(0)", "CSparse(2)"):
            assert folded not in text, folded
        assert "QSparse(1)" in text, "dynamic standard-table element must remain dynamic"
        assert "CSparse(1)" in text, "dynamic fixed-table element must remain dynamic"
        assert "INested(0)" not in text, "proven two-statement nested decoder should fold"
        assert "INested(1)" in text, "dynamic nested-table element must remain dynamic"
        meta = json.loads(report.read_text())
        transforms = meta["transforms"]
        assert transforms.get("string_array_decode", 0) >= 5, transforms
        print("PASS sparse-direct-table", transforms)

    with tempfile.TemporaryDirectory(prefix="identity-table-", dir=TMP) as td:
        td = Path(td)
        out = td / "out.js"
        report = td / "report.json"
        before = run(["node", IDENTITY_FIXTURE]).stdout
        run([BIN, IDENTITY_FIXTURE, out, "--report", report])
        run(["node", "--check", out])
        after = run(["node", out]).stdout
        assert before == after == "true true true true ab\n", (before, after)
        text = out.read_text()
        assert "S[0][0] === S[4][0]" not in text, text
        assert "S[0][0] !== S[0][1]" not in text, text
        assert "switch (state)" not in text and "switch(state)" not in text, text
        meta = json.loads(report.read_text())
        transforms = meta["transforms"]
        assert transforms.get("reference_identity_compare", 0) >= 4, transforms
        assert transforms.get("reference_state_unflatten", 0) >= 1, transforms
        assert meta["safe_static_only"] is True
        print("PASS reference-identity", transforms)


if __name__ == "__main__":
    main()
