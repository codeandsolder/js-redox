#!/usr/bin/env python3
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe"
TEMP_ROOT = ROOT / "work" / "test-tmp"

CASES = [
    (
        "split-strings",
        ROOT / "corpus/generated/reversible-obfuscation/obscura-split-strings.js",
        ['"hello, world"', ".log("],
    ),
    (
        "number-expressions",
        ROOT / "corpus/generated/reversible-obfuscation/obscura-number-expressions.js",
        ["const integer = 42", ".log("],
    ),
    (
        "unicode-escape",
        ROOT / "corpus/generated/reversible-obfuscation/obscura-unicode-escape.js",
        ['"hello, world"', ".log("],
    ),
    (
        "static-string-array",
        ROOT / "corpus/generated/reversible-obfuscation/obscura-string-array.js",
        ['const greeting = "hello, world"', 'console.log("hello, world")'],
    ),
    (
        "rotated-base64-string-array",
        ROOT / "corpus/generated/reversible-obfuscation/rotated-base64-string-array.js",
        ['console.log("cookie", "reload")'],
    ),
    (
        "direct-rotated-string-array",
        ROOT / "corpus/generated/reversible-obfuscation/direct-rotated-string-array.js",
        ['"44close"', '"11cookie"', "return alias1(index)"],
    ),
    (
        "formatted-base64-string-array",
        ROOT / "corpus/generated/reversible-obfuscation/formatted-base64-string-array.js",
        ['console.log("cookie", "reload")'],
    ),
    (
        "token-boundaries",
        ROOT / "corpus/generated/reversible-obfuscation/token-boundaries.js",
        ["return false", "return true", "throw true"],
    ),
    (
        "proxy-literals-unary",
        ROOT / "corpus/generated/reversible-obfuscation/proxy-literals-unary.js",
        ['"visible"', "42", "true", "null", "void 0", "void (bump())"],
    ),
    (
        "proxy-members",
        ROOT / "corpus/generated/reversible-obfuscation/proxy-members.js",
        ["((makeTarget()).value)", "((makeTarget())[makeKey()])"],
    ),
    (
        "safe-mix",
        ROOT / "corpus/generated/reversible-obfuscation/safe-mix.js",
        ['"hello, world"', '"beta"', "console.log", "seq"],
    ),
    (
        "proven-helper-prune",
        ROOT / "corpus/generated/reversible-obfuscation/proven-helper-prune.js",
        ["function keepMe", "console.log", "5"],
    ),
    (
        "const-aliases",
        ROOT / "corpus/generated/reversible-obfuscation/const-aliases.js",
        ['"hello"', "42", "return later", "{ answer }"],
    ),
    (
        "from-char-code-alias",
        ROOT / "corpus/generated/reversible-obfuscation/from-char-code-alias.js",
        ['"ABC"', '"😀"', '"D"', "c(0xd800)", "mutable(65)", "before(65)", "outer(65)"],
    ),
    (
        "control-flow-storage",
        ROOT / "corpus/generated/reversible-obfuscation/obscura-control-flow-storage.js",
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
        ["detached", "((0, (add)))(20, 22)", "((0, (holder.method)))()"],
    ),
    (
        "selector-trailing-params",
        ROOT / "corpus/generated/reversible-obfuscation/selector-trailing-params.js",
        ["function(selector, left)", "bump(9)", "bump(12)"],
    ),
    (
        "reference-identity-table",
        ROOT / "corpus/generated/reversible-obfuscation/reference-identity-table.js",
        [],
    ),
    (
        "ordered-switch",
        ROOT / "corpus/generated/reversible-obfuscation/ordered-switch.js",
        ['out.push("A")', 'out.push("B")', 'out.push("C")', 'out.push("D")'],
    ),
    (
        "ordered-switch-for",
        ROOT / "corpus/generated/reversible-obfuscation/ordered-switch-for.js",
        ['out.push("A")', 'out.push("B")', 'out.push("C")', 'out.push("D")'],
    ),
    (
        "arithmetic-state",
        ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state.js",
        ['out += "A"', 'out += "B"', 'out += "C"', 'out += "D"'],
    ),
    (
        "arithmetic-state-external",
        ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-external.js",
        ['out += "A"', 'out += "B"'],
    ),
    (
        "arithmetic-state-registers",
        ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-registers.js",
        ['out = "RegExp:test:1:t2AA"'],
    ),
    (
        "arithmetic-state-try",
        ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-try.js",
        ['out += "A"', 'out += "C"', 'out += "B"'],
    ),
    (
        "arithmetic-state-conditional",
        ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-conditional.js",
        ['if (choose(flag))', 'out += "T"', 'out += "F"', 'out += "!"'],
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
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-real-corpus", action="store_true")
    args = parser.parse_args()

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
            compact_text = re.sub(r"\s+", "", text)
            for needle in needles:
                compact_needle = re.sub(r"\s+", "", needle)
                assert compact_needle in compact_text, (name, needle, text[:2000])

            meta = json.loads(report.read_text())
            assert meta["schema"] == "js-safe-deobfuscate/v0"
            assert meta["safe_static_only"] is True
            assert meta["presentation_formatted"] is False
            assert meta["runtime_semantics_preserved_by_design"] is True
            if name in {
                "rotated-base64-string-array",
                "direct-rotated-string-array",
                "formatted-base64-string-array",
            }:
                assert meta["transforms"].get("string_array_decode", 0) >= 2, meta
                assert meta["transforms"].get("materialize_decoder_rotation", 0) >= 1, meta
                assert meta["transforms"].get("remove_decoder_rotation_iife", 0) >= 1, meta
            if name == "direct-rotated-string-array":
                # The unresolved identifier-argument call remains executable after
                # the runtime rotation IIFE has been eliminated.
                assert "return alias1(index)" in text, text
                assert "while (true)" not in text, text
            if name == "from-char-code-alias":
                assert meta["transforms"].get("from_char_code_alias", 0) >= 4, meta
                assert "c(68)" not in text, text
                assert "c(0xd800)" in text, text
                assert "mutable(65)" in text, text
            if name == "token-boundaries":
                # These merged forms are valid JavaScript identifiers, so a
                # syntax check alone cannot detect the semantic corruption.
                assert "returnfalse" not in text, text
                assert "returntrue" not in text, text
                assert "throwtrue" not in text, text
                assert "return false" in text, text
                assert "return true" in text, text
                assert "throw true" in text, text
            if name == "proxy-literals-unary":
                assert meta["transforms"].get("proxy_literal", 0) >= 4, meta
                assert meta["transforms"].get("proxy_string", 0) >= 1, meta
                assert meta["transforms"].get("proxy_unary", 0) >= 4, meta
            if name == "proxy-members":
                assert meta["transforms"].get("proxy_static_member", 0) >= 2, meta
                assert meta["transforms"].get("proxy_computed_member", 0) >= 2, meta
            if name == "proxy-calls":
                assert meta["transforms"].get("proxy_call", 0) >= 3, meta
                assert meta["transforms"].get("proxy_binary", 0) >= 1, meta
            if name == "proven-helper-prune":
                assert "function pruneMe" not in text, text
                assert "function keepMe" in text, text
                assert "function trailingUnused" not in text, text
                assert "function scratchParam" not in text, text
                assert meta["transforms"].get("pure_function_eval", 0) >= 3, meta
                assert meta["transforms"].get("remove_unused_proven_helper", 0) >= 1, meta
            if name == "selector-trailing-params":
                assert meta["transforms"].get("selector_dispatch_specialize", 0) >= 2, meta
                assert "function(selector, left, p2, p3, p4, p5, p6, p7, p8, p9){return (left | 0);}" not in text, text
            if name == "reference-identity-table":
                assert meta["transforms"].get("reference_identity_compare", 0) >= 4, meta
                assert meta["transforms"].get("reference_state_unflatten", 0) >= 1, meta
            if name in {"ordered-switch", "ordered-switch-for"}:
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
            if name == "arithmetic-state-external":
                assert meta["transforms"].get("arithmetic_state_unflatten", 0) >= 1, meta
                proofs = meta["arithmetic_state_proofs"]
                assert len(proofs) == 1, proofs
                proof = proofs[0]
                assert proof["state_var"] == "state", proof
                assert proof["state_path"] == ["2", "4"], proof
                assert proof["termination"] == "loop_test", proof
                assert 0 <= proof["input_start"] < proof["input_end"], proof
            if name == "arithmetic-state-registers":
                assert meta["transforms"].get("arithmetic_state_unflatten", 0) >= 1, meta
                assert 'regs[5] = "t"' in text, text
                assert 'regs[5] += "2"' in text, text
                assert 'regs[5] += "AA"' in text, text
                assert 'out = "RegExp:test:1:t2AA"' in text, text
                assert "return regs[0][0]" in text, text
                assert meta["arithmetic_state_proofs"][0]["register_reads_rewritten"] >= 4, meta
            if name == "arithmetic-state-conditional":
                assert meta["transforms"].get("arithmetic_state_unflatten", 0) >= 1, meta
                proofs = meta["arithmetic_state_proofs"]
                assert len(proofs) == 1, proofs
                proof = proofs[0]
                assert proof["state_var"] == "state", proof
                assert proof["state_path"] == ["2"], proof
                assert proof["termination"] == "conditional", proof
                assert proof["branch_test"] == "choose(flag)", proof
                assert proof["branch_paths"] == [["3"], ["5", "7"]], proof
                assert proof["branch_terminations"] == ["loop_test", "loop_test"], proof
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
        assert totals.get("proxy_literal", 0) >= 4, totals
        assert totals.get("proxy_unary", 0) >= 4, totals
        assert totals.get("proxy_static_member", 0) >= 2, totals
        assert totals.get("proxy_computed_member", 0) >= 2, totals
        assert totals.get("proxy_call", 0) >= 3, totals
        assert totals.get("pure_function_eval", 0) >= 1, totals
        assert totals.get("remove_unused_proven_helper", 0) >= 1, totals
        assert totals.get("selector_dispatch_specialize", 0) >= 2, totals
        assert totals.get("reference_identity_compare", 0) >= 4, totals
        assert totals.get("reference_state_unflatten", 0) >= 1, totals
        assert totals.get("ordered_switch_unflatten", 0) >= 1, totals
        assert totals.get("arithmetic_state_unflatten", 0) >= 1, totals

        classic_source = ROOT / "corpus/generated/reversible-obfuscation/classic-script-redeclaration.js"
        classic_out = td / "classic-script-redeclaration.js"
        classic_report = td / "classic-script-redeclaration.json"
        before = node_stdout(classic_source)
        cp = subprocess.run(
            [str(BIN), str(classic_source), str(classic_out), "--report", str(classic_report)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(
                f"classic-script semantic fallback deobfuscation failed:\n{cp.stdout}\n{cp.stderr}"
            )
        assert node_stdout(classic_out) == before
        classic_meta = json.loads(classic_report.read_text())
        assert classic_meta["transforms"].get("constant_fold", 0) >= 1, classic_meta
        print("classic-script-semantic-fallback", classic_meta["transforms"])

        with_source = td / "with-statement-negative.js"
        with_out = td / "with-statement-negative.out.js"
        with_report = td / "with-statement-negative.json"
        with_source.write_text(
            "const scope = { x: 1 }; with (scope) { console.log(x, 1 + 2); }\n"
        )
        cp = subprocess.run(
            [str(BIN), str(with_source), str(with_out), "--report", str(with_report)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        assert cp.returncode != 0, "with-statement source must fail closed"
        assert not with_report.exists(), "unsafe with-statement report must not be emitted"
        print("with-statement-safety: fail-closed")

        rotated_source = td / "fixed-rotated-direct-decoder.js"
        rotated_out = td / "fixed-rotated-direct-decoder.out.js"
        rotated_report = td / "fixed-rotated-direct-decoder.json"
        rotated_source.write_text(
            "const table=['SEED','cookie=','array'];"
            "(function(a,n){const rotate=function(k){while(--k){a['push'](a['shift']());}};"
            "rotate(++n);}(table,4));"
            "const decode=function(i,_unused){i=i-0x0;let value=table[i];return value;};"
            "console.log(decode('0x2'),decode('0x1'),decode('0x0'));\n"
        )
        before = node_stdout(rotated_source)
        cp = subprocess.run(
            [str(BIN), str(rotated_source), str(rotated_out), "--report", str(rotated_report)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(
                f"fixed rotated direct decoder deobfuscation failed:\n{cp.stdout}\n{cp.stderr}"
            )
        assert node_stdout(rotated_out) == before
        rotated_meta = json.loads(rotated_report.read_text())
        assert rotated_meta["transforms"].get("materialize_fixed_decoder_rotation", 0) >= 1, rotated_meta
        assert rotated_meta["transforms"].get("remove_fixed_decoder_rotation_iife", 0) >= 1, rotated_meta
        assert rotated_meta["transforms"].get("string_array_decode", 0) >= 3, rotated_meta
        print("fixed-rotated-direct-decoder", rotated_meta["transforms"])

        duplicate_source = ROOT / "corpus/generated/reversible-obfuscation/duplicate-scope-decoder-negative.js"
        duplicate_out = td / "duplicate-scope-decoder-negative.js"
        duplicate_report = td / "duplicate-scope-decoder-negative.json"
        before = node_stdout(duplicate_source)
        cp = subprocess.run(
            [str(BIN), str(duplicate_source), str(duplicate_out), "--report", str(duplicate_report)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(
                f"duplicate-scope decoder safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}"
            )
        assert node_stdout(duplicate_out) == before
        duplicate_meta = json.loads(duplicate_report.read_text())
        assert duplicate_meta["transforms"].get("string_array_decode", 0) == 0, duplicate_meta
        print("duplicate-scope-decoder-safety", duplicate_meta["transforms"])

        eval_prune_source = ROOT / "corpus/generated/reversible-obfuscation/proven-helper-prune-eval-safety.js"
        eval_prune_out = td / "proven-helper-prune-eval-safety.js"
        eval_prune_report = td / "proven-helper-prune-eval-safety.json"
        before = node_stdout(eval_prune_source)
        cp = subprocess.run(
            [str(BIN), str(eval_prune_source), str(eval_prune_out), "--report", str(eval_prune_report)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(
                f"direct-eval helper prune safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}"
            )
        assert node_stdout(eval_prune_out) == before
        eval_prune_text = eval_prune_out.read_text()
        eval_prune_meta = json.loads(eval_prune_report.read_text())
        assert "function hiddenHelper" in eval_prune_text, eval_prune_text
        assert eval_prune_meta["transforms"].get("remove_unused_proven_helper", 0) == 0, eval_prune_meta
        print("direct-eval-helper-prune-safety", eval_prune_meta["transforms"])

        mutable_alias_source = ROOT / "corpus/generated/reversible-obfuscation/mutable-decoder-alias-safety.js"
        mutable_alias_out = td / "mutable-decoder-alias-safety.js"
        mutable_alias_report = td / "mutable-decoder-alias-safety.json"
        before = node_stdout(mutable_alias_source)
        cp = subprocess.run(
            [str(BIN), str(mutable_alias_source), str(mutable_alias_out), "--report", str(mutable_alias_report)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(
                f"mutable decoder alias safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}"
            )
        assert node_stdout(mutable_alias_out) == before
        mutable_alias_meta = json.loads(mutable_alias_report.read_text())
        assert mutable_alias_meta["transforms"].get("string_array_decode", 0) == 0, mutable_alias_meta
        print("mutable-decoder-alias-safety", mutable_alias_meta["transforms"])

        guarded_source = ROOT / "corpus/generated/reversible-obfuscation/source-sensitive-base64-negative.js"
        guarded_out = td / "source-sensitive-base64-negative.js"
        guarded_report = td / "source-sensitive-base64-negative.json"
        before = node_stdout(guarded_source)
        cp = subprocess.run(
            [str(BIN), str(guarded_source), str(guarded_out), "--report", str(guarded_report)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(
                f"source-sensitive base64 safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}"
            )
        assert node_stdout(guarded_out) == before
        guarded_meta = json.loads(guarded_report.read_text())
        assert guarded_meta["transforms"].get("string_array_decode", 0) == 0, guarded_meta
        print("source-sensitive-base64-safety", guarded_meta["transforms"])

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

        ordered_for_safety_source = ROOT / "corpus/generated/reversible-obfuscation/ordered-switch-for-safety.js"
        ordered_for_safety_out = td / "ordered-switch-for-safety.js"
        ordered_for_safety_report = td / "ordered-switch-for-safety.json"
        before = node_stdout(ordered_for_safety_source)
        cp = subprocess.run(
            [str(BIN), str(ordered_for_safety_source), str(ordered_for_safety_out), "--report", str(ordered_for_safety_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(f"ordered-switch for-loop safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        assert node_stdout(ordered_for_safety_out) == before
        ordered_for_safety_meta = json.loads(ordered_for_safety_report.read_text())
        assert ordered_for_safety_meta["transforms"].get("ordered_switch_unflatten", 0) == 0, ordered_for_safety_meta
        print("ordered-switch-for-safety", ordered_for_safety_meta["transforms"])

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
        assert arithmetic_safety_meta["transforms"].get("arithmetic_state_unflatten", 0) == 1, arithmetic_safety_meta
        arithmetic_safety_proofs = arithmetic_safety_meta["arithmetic_state_proofs"]
        assert len(arithmetic_safety_proofs) == 1, arithmetic_safety_proofs
        arithmetic_safety_proof = arithmetic_safety_proofs[0]
        assert arithmetic_safety_proof["termination"] == "conditional", arithmetic_safety_proof
        assert arithmetic_safety_proof["branch_test"] == "flag", arithmetic_safety_proof
        assert arithmetic_safety_proof["branch_paths"] == [["0"], ["2"]], arithmetic_safety_proof
        assert arithmetic_safety_proof["branch_terminations"] == ["undefined", "undefined"], arithmetic_safety_proof
        print("arithmetic-state-legacy-conditional", arithmetic_safety_meta["transforms"])

        arithmetic_external_safety_source = ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-external-safety.js"
        arithmetic_external_safety_out = td / "arithmetic-state-external-safety.js"
        arithmetic_external_safety_report = td / "arithmetic-state-external-safety.json"
        before = node_stdout(arithmetic_external_safety_source)
        cp = subprocess.run(
            [str(BIN), str(arithmetic_external_safety_source), str(arithmetic_external_safety_out), "--report", str(arithmetic_external_safety_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(f"external arithmetic-state safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        assert node_stdout(arithmetic_external_safety_out) == before
        arithmetic_external_safety_meta = json.loads(arithmetic_external_safety_report.read_text())
        assert arithmetic_external_safety_meta["transforms"].get("arithmetic_state_unflatten", 0) == 0, arithmetic_external_safety_meta
        assert arithmetic_external_safety_meta["arithmetic_state_proofs"] == [], arithmetic_external_safety_meta
        print("arithmetic-state-external-safety", arithmetic_external_safety_meta["transforms"])

        arithmetic_register_safety_source = ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-registers-safety.js"
        arithmetic_register_safety_out = td / "arithmetic-state-registers-safety.js"
        arithmetic_register_safety_report = td / "arithmetic-state-registers-safety.json"
        before = node_stdout(arithmetic_register_safety_source)
        cp = subprocess.run(
            [str(BIN), str(arithmetic_register_safety_source), str(arithmetic_register_safety_out), "--report", str(arithmetic_register_safety_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(f"arithmetic-state register safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        assert node_stdout(arithmetic_register_safety_out) == before
        arithmetic_register_safety_text = arithmetic_register_safety_out.read_text()
        arithmetic_register_safety_meta = json.loads(arithmetic_register_safety_report.read_text())
        assert arithmetic_register_safety_meta["transforms"].get("arithmetic_state_unflatten", 0) >= 1, arithmetic_register_safety_meta
        assert "regs[1]" in arithmetic_register_safety_text, arithmetic_register_safety_text
        assert 'out = "A"' not in arithmetic_register_safety_text, arithmetic_register_safety_text
        assert arithmetic_register_safety_meta["arithmetic_state_proofs"][0]["register_reads_rewritten"] == 0, arithmetic_register_safety_meta
        print("arithmetic-state-registers-safety", arithmetic_register_safety_meta["transforms"])

        arithmetic_try_safety_source = ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-try-safety.js"
        arithmetic_try_safety_out = td / "arithmetic-state-try-safety.js"
        arithmetic_try_safety_report = td / "arithmetic-state-try-safety.json"
        before = node_stdout(arithmetic_try_safety_source)
        cp = subprocess.run(
            [str(BIN), str(arithmetic_try_safety_source), str(arithmetic_try_safety_out), "--report", str(arithmetic_try_safety_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(f"arithmetic-state try safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        assert node_stdout(arithmetic_try_safety_out) == before
        arithmetic_try_safety_meta = json.loads(arithmetic_try_safety_report.read_text())
        assert arithmetic_try_safety_meta["transforms"].get("arithmetic_state_unflatten", 0) == 0, arithmetic_try_safety_meta
        assert arithmetic_try_safety_meta["arithmetic_state_proofs"] == [], arithmetic_try_safety_meta
        print("arithmetic-state-try-safety", arithmetic_try_safety_meta["transforms"])

        arithmetic_conditional_safety_source = ROOT / "corpus/generated/reversible-obfuscation/arithmetic-state-conditional-safety.js"
        arithmetic_conditional_safety_out = td / "arithmetic-state-conditional-safety.js"
        arithmetic_conditional_safety_report = td / "arithmetic-state-conditional-safety.json"
        before = node_stdout(arithmetic_conditional_safety_source)
        cp = subprocess.run(
            [str(BIN), str(arithmetic_conditional_safety_source), str(arithmetic_conditional_safety_out), "--report", str(arithmetic_conditional_safety_report)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60,
        )
        if cp.returncode:
            raise RuntimeError(f"arithmetic-state conditional safety deobfuscation failed:\n{cp.stdout}\n{cp.stderr}")
        assert node_stdout(arithmetic_conditional_safety_out) == before
        arithmetic_conditional_safety_meta = json.loads(arithmetic_conditional_safety_report.read_text())
        assert arithmetic_conditional_safety_meta["transforms"].get("arithmetic_state_unflatten", 0) == 0, arithmetic_conditional_safety_meta
        assert arithmetic_conditional_safety_meta["arithmetic_state_proofs"] == [], arithmetic_conditional_safety_meta
        print("arithmetic-state-conditional-safety", arithmetic_conditional_safety_meta["transforms"])

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
        real_negative = ROOT / "corpus/taobao/captcha_et_f(1).js"
        if real_positive.is_file() and real_negative.is_file():
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
        elif args.require_real_corpus:
            raise SystemExit(
                "real ET corpus is required but missing; run this gate from a full-corpus workspace"
            )
        else:
            print("SKIP real-et: external Taobao corpus is not present in this worktree")

        print("PASS: safe reversible deobfuscation runtime-equivalent across", len(CASES), "families")
        print("totals", totals)


if __name__ == "__main__":
    main()
