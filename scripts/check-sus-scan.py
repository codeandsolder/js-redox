#!/usr/bin/env python3
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".cargo-target-nodebug/debug/sus-scan"
FIXTURES = ROOT / "corpus/generated/sus-scanner"


def run(*args, timeout=60):
    cp = subprocess.run(
        [str(x) for x in args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
    )
    if cp.returncode:
        raise RuntimeError(
            f"{' '.join(map(str, args))} failed {cp.returncode}:\n"
            f"{cp.stdout}\n{cp.stderr}"
        )
    return cp


def main():
    if not BIN.is_file():
        raise SystemExit(f"missing binary: {BIN}")

    cp = run(
        BIN,
        "--json",
        "--include-signals",
        FIXTURES,
    )
    report = json.loads(cp.stdout)
    assert report["schema"] == "js-sus-scan/v1"

    by_name = {Path(item["input"]).name: item for item in report["files"]}
    expected = {
        "dense-obfuscation.js",
        "clean-control.js",
        "asset-control.js",
        "long-string-control.js",
        "array-rotation.js",
        "array-rotation-control.js",
        "rotation-bootstrap.js",
        "rotation-bootstrap-control.js",
        "operator-proxy-table.js",
        "operator-proxy-table-control.js",
        "one-shot-wrapper.js",
        "one-shot-wrapper-control.js",
        "direct-table-decoder.js",
        "direct-table-decoder-control.js",
        "mba-helper-cluster.js",
        "mba-helper-control.js",
        "selector-dispatcher.js",
        "selector-dispatcher-control.js",
    }
    assert expected <= by_name.keys(), sorted(by_name)

    dense = by_name["dense-obfuscation.js"]
    clean = by_name["clean-control.js"]
    asset = by_name["asset-control.js"]
    long_string = by_name["long-string-control.js"]
    rotation = by_name["array-rotation.js"]
    rotation_control = by_name["array-rotation-control.js"]
    bootstrap = by_name["rotation-bootstrap.js"]
    bootstrap_control = by_name["rotation-bootstrap-control.js"]
    proxy_table = by_name["operator-proxy-table.js"]
    proxy_control = by_name["operator-proxy-table-control.js"]
    one_shot = by_name["one-shot-wrapper.js"]
    one_shot_control = by_name["one-shot-wrapper-control.js"]
    direct_decoder = by_name["direct-table-decoder.js"]
    direct_decoder_control = by_name["direct-table-decoder-control.js"]
    mba_helpers = by_name["mba-helper-cluster.js"]
    mba_control = by_name["mba-helper-control.js"]
    selector = by_name["selector-dispatcher.js"]
    selector_control = by_name["selector-dispatcher-control.js"]

    assert dense["clusters"], dense
    assert dense["top_score"] >= 30, dense["top_score"]
    kinds = dense["signal_kinds"]
    assert kinds.get("api_string_table", 0) >= 1, kinds
    assert kinds.get("indexed_lookup", 0) >= 10, kinds
    assert kinds.get("charcode_decode_call", 0) >= 1, kinds
    assert kinds.get("base64_blob", 0) >= 1, kinds
    assert kinds.get("base64_decode_call", 0) >= 1, kinds
    assert kinds.get("numeric_decoder_call_candidate", 0) >= 4, kinds
    assert kinds.get("bitwise_mix", 0) >= 1, kinds

    repeated = [
        subject
        for cluster in dense["clusters"]
        for subject in cluster["repeated_subjects"]
    ]
    assert any(item["subject"] in {"pool", "chars"} and item["count"] >= 3 for item in repeated), repeated

    assert clean["clusters"] == [], clean
    assert clean["top_score"] == 0, clean["top_score"]
    assert asset["clusters"] == [], asset
    assert asset["signal_kinds"].get("base64_blob", 0) == 0, asset["signal_kinds"]

    # One long, ordinary concatenation must contribute only one normalized
    # string-plus signal instead of one signal per nested BinaryExpression.
    assert long_string["clusters"] == [], long_string
    assert long_string["top_score"] == 0, long_string["top_score"]
    assert long_string["signal_kinds"].get("string_plus_chain", 0) == 1, long_string["signal_kinds"]

    assert rotation["clusters"], rotation
    assert rotation["signal_kinds"].get("array_rotation", 0) == 2, rotation["signal_kinds"]
    rotation_signals = [
        signal
        for signal in rotation["signals"]
        if signal["kind"] == "array_rotation"
    ]
    assert all(signal.get("subject") == "table" for signal in rotation_signals), rotation_signals

    # A single ordinary queue rotation is still structurally the same operation,
    # but weight 8 intentionally leaves it below the default cluster threshold.
    assert rotation_control["clusters"] == [], rotation_control
    assert rotation_control["signal_kinds"].get("array_rotation", 0) == 1, rotation_control["signal_kinds"]

    # Bracket-literal push/shift must normalize to the same low-level rotation signal,
    # while the checksum IIFE contributes one stronger composite structure.
    assert bootstrap["signal_kinds"].get("array_rotation", 0) == 2, bootstrap["signal_kinds"]
    assert bootstrap["signal_kinds"].get("rotation_checksum_iife", 0) == 1, bootstrap["signal_kinds"]
    assert bootstrap_control["signal_kinds"].get("rotation_checksum_iife", 0) == 0, bootstrap_control["signal_kinds"]

    assert proxy_table["signal_kinds"].get("operator_proxy_table", 0) == 1, proxy_table["signal_kinds"]
    assert proxy_control["signal_kinds"].get("operator_proxy_table", 0) == 0, proxy_control["signal_kinds"]

    assert one_shot["signal_kinds"].get("one_shot_wrapper", 0) == 1, one_shot["signal_kinds"]
    assert one_shot_control["signal_kinds"].get("one_shot_wrapper", 0) == 0, one_shot_control["signal_kinds"]

    assert direct_decoder["signal_kinds"].get("direct_table_decoder", 0) == 1, direct_decoder["signal_kinds"]
    assert direct_decoder_control["signal_kinds"].get("direct_table_decoder", 0) == 0, direct_decoder_control["signal_kinds"]

    assert mba_helpers["signal_kinds"].get("mba_helper", 0) == 4, mba_helpers["signal_kinds"]
    assert mba_control["signal_kinds"].get("mba_helper", 0) == 0, mba_control["signal_kinds"]

    assert selector["signal_kinds"].get("selector_dispatcher", 0) == 1, selector["signal_kinds"]
    assert selector_control["signal_kinds"].get("selector_dispatcher", 0) == 0, selector_control["signal_kinds"]

    text = run(BIN, FIXTURES / "dense-obfuscation.js").stdout
    assert "SUS summary:" in text
    assert "api_string_table" in text
    assert "base64" in text
    assert "repeated=[" in text

    rotation_text = run(BIN, FIXTURES / "array-rotation.js").stdout
    assert "array_rotation" in rotation_text

    print(
        "PASS: sus-scan dense fixture ranked",
        f"score={dense['top_score']}",
        f"signals={dense['signal_count']}",
        "and clean control stayed below threshold",
    )


if __name__ == "__main__":
    main()
