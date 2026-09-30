#!/usr/bin/env python3
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe"
TEMP_ROOT = ROOT / "work" / "test-tmp"

CASES = [
    (
        "split-strings",
        ROOT / "third_party/obscura/fixtures/golden/split-strings/trivial/hello.js",
        ['"hello, world"', ".log("],
    ),
    (
        "number-expressions",
        ROOT / "third_party/obscura/fixtures/golden/numbers-to-expressions/numbers/literals.js",
        ["const integer = 42", ".log("],
    ),
    (
        "unicode-escape",
        ROOT / "third_party/obscura/fixtures/golden/unicode-escape/trivial/hello.js",
        ['"hello, world"', ".log("],
    ),
    (
        "static-string-array",
        ROOT / "third_party/obscura/fixtures/golden/string-array-only/trivial/hello.js",
        ['const greeting = "hello, world"', 'console.log("hello, world")'],
    ),
    (
        "rotated-base64-string-array",
        ROOT / "corpus/generated/reversible-obfuscation/rotated-base64-string-array.js",
        ['console.log("cookie", "reload")'],
    ),
    (
        "safe-mix",
        ROOT / "corpus/generated/reversible-obfuscation/safe-mix.js",
        ['"hello, world"', '"beta"', "console.log", "seq"],
    ),
    (
        "const-aliases",
        ROOT / "corpus/generated/reversible-obfuscation/const-aliases.js",
        ['"hello"', "42", "return later", "{ answer }"],
    ),
    (
        "control-flow-storage",
        ROOT / "third_party/obscura/fixtures/golden/control-flow-flattening/control-flow/branches.js",
        [
            'return "negative"',
            'return "zero"',
            'return "small"',
            'return "medium"',
            'return "large"',
        ],
    ),
    (
        "proxy-calls",
        ROOT / "corpus/generated/reversible-obfuscation/proxy-calls.js",
        ["detached", "(0, add)(20, 22)", "(0, holder.method)()"],
    ),
    (
        "ordered-switch",
        ROOT / "corpus/generated/reversible-obfuscation/ordered-switch.js",
        ['out.push("A")', 'out.push("B")', 'out.push("C")', 'out.push("D")'],
    ),
    (
        "arithmetic-state",
        ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state.js",
        ['out += "A"', 'out += "B"', 'out += "C"', 'out += "D"'],
    ),
]


def node_stdout(path: Path) -> str:
    cp = subprocess.run(
        ["node", str(path)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=20,
    )
    if cp.returncode:
        raise RuntimeError(f"node failed for {path}:\n{cp.stderr}")
    return cp.stdout


def node_check(path: Path) -> None:
    cp = subprocess.run(
        ["node", "--check", str(path)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )
    if cp.returncode:
        raise RuntimeError(f"node --check failed for {path}:\n{cp.stderr}")


def main():
    if not BIN.is_file():
        raise SystemExit(f"missing binary: {BIN}")

    TEMP_ROOT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="js-safe-deobf-", dir=TEMP_ROOT) as td:
        td = Path(td)
        totals = {}
        for name, source, needles in CASES:
            out = td / f"{name}.js"
            report = td / f"{name}.json"
            before = node_stdout(source)
            cp = subprocess.run(
                [str(BIN), str(source), str(out), "--report", str(report)],
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=60,
            )
            if cp.returncode:
                raise RuntimeError(
                    f"deobfuscator failed for {name}:\n{cp.stdout}\n{cp.stderr}"
                )
            after = node_stdout(out)
            assert before == after, (name, before, after)

            text = out.read_text()
            for needle in needles:
                assert needle in text, (name, needle, text[:2000])

            meta = json.loads(report.read_text())
            assert meta["schema"] == "js-safe-deobfuscate/v0"
            if name == "proxy-calls":
                assert meta["transforms"].get("proxy_call", 0) >= 3, meta
                assert meta["transforms"].get("proxy_binary", 0) >= 1, meta
            if name == "ordered-switch":
                assert meta["transforms"].get("ordered_switch_unflatten", 0) >= 1, meta
            if name == "arithmetic-state":
                assert meta["transforms"].get("arithmetic_state_unflatten", 0) >= 1, meta
                proofs = meta["arithmetic_state_proofs"]
                assert len(proofs) == 1, proofs
                proof = proofs[0]
                assert proof["iteration"] == 1, proof
                assert proof["state_var"] == "state", proof
                assert proof["state_path"] == ["6", "1", "16", "0"], proof
                assert proof["termination"] == "undefined", proof
                assert 0 <= proof["input_start"] < proof["input_end"], proof
            assert meta["safe_static_only"] is True
            assert meta["changed"] is True
            for kind, count in meta["transforms"].items():
                totals[kind] = totals.get(kind, 0) + count
            print(name, meta["transforms"])

        assert totals.get("constant_fold", 0) >= 5, totals
        assert totals.get("computed_property", 0) >= 3, totals
        assert totals.get("string_array_decode", 0) >= 2, totals
        assert totals.get("static_array_lookup", 0) >= 1, totals
        assert totals.get("dead_branch", 0) >= 1, totals
        assert totals.get("split_sequence", 0) >= 1, totals
        assert totals.get("const_propagate", 0) >= 4, totals
        assert totals.get("proxy_binary", 0) >= 5, totals
        assert totals.get("proxy_string", 0) >= 5, totals
        assert totals.get("proxy_call", 0) >= 3, totals
        assert totals.get("ordered_switch_unflatten", 0) >= 1, totals
        assert totals.get("arithmetic_state_unflatten", 0) >= 1, totals

        safety_source = ROOT / "corpus/generated/reversible-obfuscation/proxy-safety.js"
        safety_out = td / "proxy-safety.js"
        safety_report = td / "proxy-safety.json"
        before = node_stdout(safety_source)
        cp = subprocess.run(
            [str(BIN), str(safety_source), str(safety_out), "--report", str(safety_report)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(
                f"proxy safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}"
            )
        assert node_stdout(safety_out) == before
        safety_meta = json.loads(safety_report.read_text())
        assert safety_meta["transforms"].get("proxy_binary", 0) == 0, safety_meta
        assert safety_meta["transforms"].get("proxy_string", 0) == 0, safety_meta
        assert safety_meta["transforms"].get("proxy_call", 0) == 0, safety_meta
        print("proxy-safety", safety_meta["transforms"])

        ordered_safety_source = ROOT / "corpus/generated/reversible-obfuscation/ordered-switch-safety.js"
        ordered_safety_out = td / "ordered-switch-safety.js"
        ordered_safety_report = td / "ordered-switch-safety.json"
        before = node_stdout(ordered_safety_source)
        cp = subprocess.run(
            [str(BIN), str(ordered_safety_source), str(ordered_safety_out), "--report", str(ordered_safety_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(f"ordered-switch safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        assert node_stdout(ordered_safety_out) == before
        ordered_safety_meta = json.loads(ordered_safety_report.read_text())
        assert ordered_safety_meta["transforms"].get("ordered_switch_unflatten", 0) == 0, ordered_safety_meta
        print("ordered-switch-safety", ordered_safety_meta["transforms"])

        arithmetic_safety_source = ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-safety.js"
        arithmetic_safety_out = td / "arithmetic-state-safety.js"
        arithmetic_safety_report = td / "arithmetic-state-safety.json"
        before = node_stdout(arithmetic_safety_source)
        cp = subprocess.run(
            [str(BIN), str(arithmetic_safety_source), str(arithmetic_safety_out), "--report", str(arithmetic_safety_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(f"arithmetic-state safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        assert node_stdout(arithmetic_safety_out) == before
        arithmetic_safety_meta = json.loads(arithmetic_safety_report.read_text())
        assert arithmetic_safety_meta["transforms"].get("arithmetic_state_unflatten", 0) == 0, arithmetic_safety_meta
        assert arithmetic_safety_meta["arithmetic_state_proofs"] == [], arithmetic_safety_meta
        print("arithmetic-state-safety", arithmetic_safety_meta["transforms"])

        arithmetic_iife_safety_source = ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-iife-safety.js"
        arithmetic_iife_safety_out = td / "arithmetic-state-iife-safety.js"
        arithmetic_iife_safety_report = td / "arithmetic-state-iife-safety.json"
        before = node_stdout(arithmetic_iife_safety_source)
        cp = subprocess.run(
            [str(BIN), str(arithmetic_iife_safety_source), str(arithmetic_iife_safety_out), "--report", str(arithmetic_iife_safety_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(f"arithmetic-state IIFE safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        assert node_stdout(arithmetic_iife_safety_out) == before
        arithmetic_iife_safety_meta = json.loads(arithmetic_iife_safety_report.read_text())
        assert arithmetic_iife_safety_meta["transforms"].get("arithmetic_state_unflatten", 0) == 0, arithmetic_iife_safety_meta
        assert arithmetic_iife_safety_meta["arithmetic_state_proofs"] == [], arithmetic_iife_safety_meta
        print("arithmetic-state-iife-safety", arithmetic_iife_safety_meta["transforms"])

        # Pin the real ET arithmetic-CFF behavior that motivated this pass. The
        # normal sibling has one fully deterministic helper; the captcha sibling
        # used to false-positive because a nested IIFE invalidated outer values.
        real_positive = ROOT / "corpus/taobao/normal_et_f(1).js"
        real_positive_out = td / "normal-et-real.js"
        real_positive_report = td / "normal-et-real.json"
        cp = subprocess.run(
            [str(BIN), str(real_positive), str(real_positive_out), "--report", str(real_positive_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120,
        )
        if cp.returncode:
            raise RuntimeError(f"real ET positive deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        node_check(real_positive_out)
        real_positive_meta = json.loads(real_positive_report.read_text())
        assert real_positive_meta["transforms"].get("arithmetic_state_unflatten", 0) == 1, real_positive_meta
        assert len(real_positive_meta["arithmetic_state_proofs"]) == 1, real_positive_meta
        assert real_positive_meta["arithmetic_state_proofs"][0]["termination"] in {"undefined", "return", "throw"}
        print("real-et-positive", real_positive_meta["transforms"], real_positive_meta["arithmetic_state_proofs"])

        real_negative = ROOT / "corpus/taobao/captcha_et_f(1).js"
        real_negative_out = td / "captcha-et-real.js"
        real_negative_report = td / "captcha-et-real.json"
        cp = subprocess.run(
            [str(BIN), str(real_negative), str(real_negative_out), "--report", str(real_negative_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120,
        )
        if cp.returncode:
            raise RuntimeError(f"real ET negative deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        node_check(real_negative_out)
        real_negative_meta = json.loads(real_negative_report.read_text())
        assert real_negative_meta["transforms"].get("arithmetic_state_unflatten", 0) == 0, real_negative_meta
        assert real_negative_meta["arithmetic_state_proofs"] == [], real_negative_meta
        print("real-et-negative", real_negative_meta["transforms"])

        print("PASS: safe reversible deobfuscation runtime-equivalent across", len(CASES), "families")
        print("totals", totals)


if __name__ == "__main__":
    main()
