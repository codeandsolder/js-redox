#!/usr/bin/env python3
import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RECOVER = ROOT / "scripts/recover-js-obfuscator-strings.py"
TMP = ROOT / "work/test-tmp/static-string-recovery"


def run(argv, timeout=120):
    cp = subprocess.run(
        [str(x) for x in argv], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout,
    )
    if cp.returncode:
        raise RuntimeError(
            f"command failed ({cp.returncode}): {' '.join(map(str, argv))}\n"
            f"{cp.stdout}{cp.stderr}"
        )
    return cp


def recover(name, source, timeout=120):
    out = TMP / f"{name}.recovered.js"
    report = TMP / f"{name}.json"
    run(["uv", "run", "--no-project", "python", RECOVER, source, out, "--report", report], timeout)
    run(["node", "--check", out], 60)
    return out, json.loads(report.read_text())


def decoder(report):
    assert len(report["decoders"]) == 1, report
    return report["decoders"][0]


def load_recover_module():
    spec = importlib.util.spec_from_file_location("static_string_recover", RECOVER)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def check_immutable_literal_tables():
    module = load_recover_module()
    positive = (
        'const t = ["alpha", "beta"]; '
        'function f(i) { return t[i] + t[1] + String(t[999]); }\n'
    )
    arrays = module.discover_simple_arrays(positive)
    proven = module.immutable_literal_string_arrays(positive, arrays)
    assert proven["t"] == ["alpha", "beta"]
    replaced, count = module.replace_immutable_string_table_reads(positive, proven)
    assert count == 1
    assert 't[i]' in replaced
    assert '"beta"' in replaced
    assert 't[999]' in replaced

    unsafe = (
        'const alias = t;',
        't[0] = "changed";',
        't[i]++;',
        'delete t[i];',
        't.push("changed");',
        't["push"]("changed");',
        't["push"]?.("changed");',
        't["push"].call(t, "changed");',
        't["push"].bind(t)("changed");',
    )
    for ordinal, use in enumerate(unsafe):
        source = f'const t = ["alpha", "beta"]; {use} console.log(t[0]);\n'
        arrays = module.discover_simple_arrays(source)
        proven = module.immutable_literal_string_arrays(source, arrays)
        assert "t" not in proven, (ordinal, use)


def check_semantic_affine_base91():
    module = load_recover_module()
    constants = [None] * 24
    for index, value in {
        2: 8,
        3: 255,
        14: 7,
        17: 91,
        18: 8191,
        19: 88,
        20: 13,
        21: 14,
    }.items():
        constants[index] = value
    window = (
        "alphabet.indexOf(ch); "
        "pending += index * 91; "
        "bits += (pending & c[s0 + 18]) > 88 ? c[s0 + 20] : 14; "
        "out.push(acc & c[s1 + 3]); "
        "acc >>= c[s2 + 2]; bits -= 8; pending = -1; "
        "while (bits > c[s2 + 14]); if (pending > -1) out.push(acc & 255);"
    )
    assert module.semantic_affine_base91_signature_matches(
        window, {"c": constants}
    )
    broken = list(constants)
    broken[18] = 8190
    assert not module.semantic_affine_base91_signature_matches(
        window, {"c": broken}
    )


def main():
    TMP.mkdir(parents=True, exist_ok=True)
    check_immutable_literal_tables()
    check_semantic_affine_base91()

    acw1 = ROOT / "corpus/real/searxrs2-antibot/acw-sc-v2/mpall518-challenge.pretty.js"
    acw2 = ROOT / "corpus/real/searxrs2-antibot/acw-sc-v2/mpall518-challenge2.pretty.js"
    for name, source in (("acw1", acw1), ("acw2", acw2)):
        out, report = recover(name, source)
        d = decoder(report)
        assert d["mode"] == "base64"
        assert d["offset"] == 251
        assert d["rotation"] == 8
        assert d["table_entries"] == 42
        assert d["replacements"] == 57
        assert report["replacements"] == 57
        text = out.read_text()
        for needle in (
            'p = "3000176000856006061501533003690027800375"',
            'q["join"]("")',
            'u["slice"](x, x + 2)',
            'document["cookie"] = "acw_sc__v2="',
            'document["location"]["reload"]()',
            'Date["now"]()',
            '["toGMTString"]()',
        ):
            assert needle in text, (name, needle)

    # Safety regression: if the generated rotation checksum no longer proves,
    # do not decode any call using an assumed table order.
    bad = TMP / "acw-bad-rotation.js"
    bad_text = acw1.read_text().replace("})(a0i, 483519)", "})(a0i, 483520)", 1)
    assert bad_text != acw1.read_text()
    bad.write_text(bad_text)
    out, report = recover("acw-bad-rotation", bad)
    d = decoder(report)
    assert d["rotation"] is None
    assert d["status"] == "rotation-unproven"
    assert report["replacements"] == 0
    assert out.read_text() == bad_text

    taobao_cases = (
        ("taobao-normal", ROOT / "corpus/taobao/normal_securitySDK.umd.js"),
        ("taobao-captcha", ROOT / "corpus/taobao/captcha_securitySDK.umd.js"),
    )
    taobao_available = all(source.is_file() for _, source in taobao_cases)
    if taobao_available:
        for name, source in taobao_cases:
            out, report = recover(name, source, timeout=180)
            d = decoder(report)
            assert d["mode"] == "rc4"
            assert d["offset"] == 0xC2
            assert d["rotation"] == 409
            assert d["table_entries"] == 1855
            assert d["replacements"] >= 646
            text = out.read_text()
            for needle in ('"defineProperty"', '"length"', '"prototype"', '"undefined"'):
                assert needle in text, (name, needle)

    plain = TMP / "plain.js"
    plain_text = 'const table = ["alpha", "beta"]; function f(x) { return table[x]; } console.log(f(1));\n'
    plain.write_text(plain_text)
    out, report = recover("plain", plain)
    assert report["decoders"] == []
    assert report["replacements"] == 0
    assert report["base91_iterations"][0]["preflight_skipped"] is True
    assert out.read_text() == plain_text
    assert run(["node", out]).stdout.strip() == "beta"

    plain_crlf = TMP / "plain-crlf.js"
    plain_crlf_bytes = (
        b'const table = ["alpha", "beta"];\r\n'
        b'function f(x) { return table[x]; }\r\n'
        b'console.log(f(1));\r\n'
    )
    plain_crlf.write_bytes(plain_crlf_bytes)
    out, report = recover("plain-crlf", plain_crlf)
    assert report["decoders"] == []
    assert report["replacements"] == 0
    assert report["base91_iterations"][0]["preflight_skipped"] is True
    assert report["input_sha256"] == hashlib.sha256(plain_crlf_bytes).hexdigest()
    assert out.read_bytes() == plain_crlf_bytes
    assert run(["node", out]).stdout.strip() == "beta"

    print("PASS: static javascript-obfuscator string recovery")
    print("  immutable literal tables: numeric reads fold; dynamic reads stay; mutation/alias cases reject")
    print("  acw_sc__v2: 2 captures, rotation=8, 57 replacements each")
    if taobao_available:
        print("  Taobao securitySDK: 2 captures, RC4 rotation=409, >=646 replacements each")
    else:
        print("  Taobao securitySDK: skipped (external corpus absent)")
    print("  unresolved-rotation negative: zero rewrites")
    print("  ordinary-JS negatives: LF/CRLF byte-identical + runtime-equivalent + Base91 preflight skipped")


if __name__ == "__main__":
    main()
