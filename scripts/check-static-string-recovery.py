#!/usr/bin/env python3
import json
import subprocess
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


def main():
    TMP.mkdir(parents=True, exist_ok=True)

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

    for name, source in (
        ("taobao-normal", ROOT / "corpus/taobao/normal_securitySDK.umd.js"),
        ("taobao-captcha", ROOT / "corpus/taobao/captcha_securitySDK.umd.js"),
    ):
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
    assert out.read_text() == plain_text
    assert run(["node", out]).stdout.strip() == "beta"

    print("PASS: static javascript-obfuscator string recovery")
    print("  acw_sc__v2: 2 captures, rotation=8, 57 replacements each")
    print("  Taobao securitySDK: 2 captures, RC4 rotation=409, >=646 replacements each")
    print("  unresolved-rotation negative: zero rewrites")
    print("  ordinary-JS negative: byte-identical + runtime-equivalent")


if __name__ == "__main__":
    main()
