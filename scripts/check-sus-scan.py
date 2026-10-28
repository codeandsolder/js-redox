#!/usr/bin/env python3
import json
import subprocess
import tempfile
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
    assert report["schema"] == "js-sus-scan/v7"

    # Explicit corpus bodies are content-addressed and intentionally have no
    # JavaScript extension. Explicit file arguments must therefore be scanned
    # even though recursive directory discovery remains extension-filtered.
    with tempfile.TemporaryDirectory(dir=ROOT / "work") as tmp:
        extensionless = Path(tmp) / "0123456789abcdef"
        extensionless.write_text("const value = 1;\n")
        direct = json.loads(run(BIN, "--json", extensionless).stdout)
        assert direct["schema"] == "js-sus-scan/v7"
        assert len(direct["files"]) == 1, direct
        assert Path(direct["files"][0]["input"]) == extensionless, direct

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

    # Invalid transport bytes are a decode anomaly, not automatically a JS parse
    # failure. Browser-compatible replacement must keep the batch alive and keep
    # decode provenance separate from parser diagnostics.
    with tempfile.TemporaryDirectory(prefix="sus-scan-extensionless-") as tmp:
        malformed = Path(tmp) / "deadbeef"
        malformed.write_bytes(b"// Copyright \xa9 2013\nconst ok = 1;\n")
        malformed_report = json.loads(run(BIN, "--json", malformed).stdout)
        assert malformed_report["schema"] == "js-sus-scan/v7"
        assert len(malformed_report["files"]) == 1, malformed_report
        malformed_file = malformed_report["files"][0]
        assert malformed_file["fatal_error"] is False, malformed_file
        assert malformed_file["decode_had_errors"] is True, malformed_file
        assert malformed_file["decode_uncertain"] is True, malformed_file
        assert malformed_file["decode_encoding"] == "UTF-8", malformed_file

    # Chromium/V8 accepts the legacy web form `CallExpression = value` and
    # throws ReferenceError only if execution reaches the assignment. Oxc has
    # no AssignmentTarget AST variant for the call expression. sus-scan must
    # therefore recover an analysis-only AST without treating the original
    # source as rewritten or semantically complete.
    with tempfile.TemporaryDirectory(prefix="sus-scan-browser-legacy-") as tmp:
        legacy = Path(tmp) / "legacy.js"
        legacy.write_text(
            "function target() { return 1; }\n"
            "target() = 2;\n"
            "eval('visible');\n"
        )
        legacy_file = json.loads(run(BIN, "--json", legacy).stdout)["files"][0]
        assert legacy_file["parser_fatal_error"] is True, legacy_file
        assert legacy_file["fatal_error"] is False, legacy_file
        assert legacy_file["analysis_complete"] is False, legacy_file
        assert legacy_file["parse_recovery"] == "browser-legacy-call-assignment", legacy_file
        assert [span["kind"] for span in legacy_file["opaque_parse_spans"]] == [
            "browser_legacy_call_assignment_target"
        ], legacy_file
        assert legacy_file["signal_kinds"].get("dynamic_code_call", 0) >= 1, legacy_file

        legacy_html = Path(tmp) / "legacy-html-comment.js"
        legacy_html.write_text("<!--\n$(document).ready(function() { $('#slideshow0').nivoSlider(); });\n-->")
        html_file = json.loads(run(BIN, "--json", legacy_html).stdout)["files"][0]
        assert html_file["parser_fatal_error"] is True, html_file
        assert html_file["fatal_error"] is False, html_file
        assert html_file["analysis_complete"] is True, html_file
        assert html_file["parse_recovery"] == "classic-script-fallback", html_file
        assert html_file["opaque_parse_spans"] == [], html_file

        invalid = Path(tmp) / "invalid-assignment.js"
        invalid.write_text("(1 + 2) = 3;\n")
        invalid_file = json.loads(run(BIN, "--json", invalid).stdout)["files"][0]
        assert invalid_file["parser_fatal_error"] is True, invalid_file
        assert invalid_file["fatal_error"] is True, invalid_file
        assert invalid_file["analysis_complete"] is False, invalid_file
        assert invalid_file.get("parse_recovery") is None, invalid_file
        assert invalid_file["opaque_parse_spans"] == [], invalid_file

    # Generic codec operations are useful discovery evidence, but they are common
    # in ordinary Unicode/base64/identifier plumbing and must not create residual
    # debt on their own. Literal code-point reconstruction remains actionable.
    with tempfile.TemporaryDirectory(prefix="sus-scan-codec-policy-") as tmp:
        tmp = Path(tmp)
        codec = tmp / "codec-control.js"
        codec.write_text(
            "function utf8(cp) { return String.fromCharCode(cp); }\n"
            "function decode(x) { return atob(x); }\n"
            "function id(n) { return n.toString(36); }\n"
        )
        codec_file = json.loads(run(BIN, "--json", codec).stdout)["files"][0]
        assert codec_file["signal_kinds"].get("charcode_decode_call", 0) == 1, codec_file
        assert codec_file["signal_kinds"].get("base64_decode_call", 0) == 1, codec_file
        assert codec_file["signal_kinds"].get("radix_string_call", 0) == 1, codec_file
        assert codec_file["actionable_signal_count"] == 0, codec_file
        assert codec_file["actionable_top_score"] == 0, codec_file

        literal = tmp / "literal-codepoints.js"
        literal.write_text(
            "const hidden = String.fromCharCode(120, 116, 49);\n"
            "sink(hidden);\n"
        )
        literal_file = json.loads(run(BIN, "--json", literal).stdout)["files"][0]
        assert literal_file["signal_kinds"].get("charcode_decode_call", 0) == 1, literal_file
        assert literal_file["signal_kinds"].get("charcode_literal_decode", 0) == 1, literal_file
        assert literal_file["actionable_signal_kinds"].get("charcode_literal_decode", 0) == 1, literal_file
        assert literal_file["actionable_signal_kinds"].get("charcode_decode_call", 0) == 0, literal_file

        encoded = "QUJD" * 40
        opaque = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ-_~!@#$%^&*()[]{}:;,.?|" * 6
        blobs = tmp / "data-blobs.js"
        blobs.write_text(
            f'const encoded = "{encoded}";\n'
            f'const opaque = "{opaque}";\n'
            'sink(encoded, opaque);\n'
        )
        blob_file = json.loads(run(BIN, "--json", blobs).stdout)["files"][0]
        assert blob_file["signal_kinds"].get("base64_blob", 0) >= 1, blob_file
        assert blob_file["signal_kinds"].get("opaque_blob", 0) >= 1, blob_file
        assert blob_file["actionable_signal_kinds"].get("base64_blob", 0) == 0, blob_file
        assert blob_file["actionable_signal_kinds"].get("opaque_blob", 0) == 0, blob_file
        assert blob_file["actionable_signal_count"] == 0, blob_file

        cookie_helper = tmp / "cookie-helper.js"
        cookie_helper.write_text(
            'function getCookieValue(name) {\n'
            '  const cookie = {};\n'
            '  document.cookie.split(";").forEach((item) => {\n'
            '    const [key, value] = item.split("=");\n'
            '    cookie[key.trim()] = value ? decodeURIComponent(value) : "";\n'
            '  });\n'
            '  return cookie[name];\n'
            '}\n'
        )
        cookie_file = json.loads(run(BIN, "--json", cookie_helper).stdout)["files"][0]
        assert cookie_file["actionable_signal_kinds"].get("direct_table_decoder", 0) == 0, cookie_file

        direct_decoder = tmp / "direct-table-decoder.js"
        direct_decoder.write_text(
            'const table = ["QQ==", "Qg=="];\n'
            'function decode(i) { return atob(table[i]); }\n'
            'sink(decode(0));\n'
        )
        direct_file = json.loads(run(BIN, "--json", direct_decoder).stdout)["files"][0]
        assert direct_file["actionable_signal_kinds"].get("direct_table_decoder", 0) >= 1, direct_file

    dense = by_name["dense-obfuscation.js"]
    clean = by_name["clean-control.js"]
    module_loader = by_name["module-loader-control.js"]
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
    assert dense["actionable_clusters"], dense
    assert dense["actionable_top_score"] >= 12, dense["actionable_top_score"]
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
    assert clean["actionable_clusters"] == [], clean
    assert clean["actionable_top_score"] == 0, clean["actionable_top_score"]
    assert module_loader["signal_kinds"].get("numeric_decoder_call_candidate", 0) >= 4, module_loader["signal_kinds"]
    assert module_loader["top_score"] > 0, module_loader["top_score"]
    assert module_loader["actionable_top_score"] == 0, module_loader
    assert module_loader["actionable_clusters"] == [], module_loader
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
