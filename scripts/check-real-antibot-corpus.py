#!/usr/bin/env python3
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "corpus/real/searxrs2-antibot"
MANIFEST = CORPUS / "manifest.json"
WORK = ROOT / "work/real-antibot-corpus"
TMP = ROOT / "work/test-tmp/real-antibot-corpus"
FORMATTER = ROOT / ".cargo-target-nodebug/debug/js-format"
DEOB = ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe"
SCANNER = ROOT / ".cargo-target-nodebug/debug/jsvm-lift"

MIN_DEOB_TRANSFORMS = {
    # Filled only for transforms whose presence is part of the readability
    # contract, not for incidental optimizer counts.
    "datadome-qwant-5.10.0": {
        "string_array_decode": 4000,
        "pure_function_eval": 120,
    },
}

EXPECTED_DEOB_STRINGS = {
    # Stable semantic strings recovered from DataDome's two literal tables:
    # the ordinary atob table and the fixed-permutation Base64 table.
    "datadome-qwant-5.10.0": (
        "__selenium_evaluate",
        "AudioContext",
        "enumerateDevices",
        "parseInt",
    ),
}

FORBIDDEN_DEOB_STRINGS = {
    # Use this sparingly for known-bad rewrite signatures caught by a real
    # regression, not as a generic textual blacklist.
}

MIN_SIGNALS = {
    "cloudflare-ecosia-orchestrate-1": {
        "direct_switch_maps": 2,
        "handler_function_tables": 6,
    },
    "cloudflare-ecosia-orchestrate-2": {
        "direct_switch_maps": 2,
        "handler_function_tables": 6,
    },
    "cloudflare-main-chrome-raw": {
        "handler_function_tables": 1,
    },
    "castle-raw": {
        "handler_function_tables": 4,
    },
    "datadome-qwant-5.10.0": {
        "handler_tables": 3,
    },
    "google-knitsail-current": {
        "embedded": 1,
        "if_ladder_state_machines_recursive": 4,
    },
}


def run(argv, timeout=240):
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


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def count_list(report, key):
    value = report.get(key, [])
    if not isinstance(value, list):
        raise AssertionError((key, type(value).__name__))
    return len(value)


def recursive_count(report, key):
    total = count_list(report, key)
    for child in report.get("embedded", []):
        total += recursive_count(child, key)
    return total


def main():
    for binary in (FORMATTER, DEOB, SCANNER):
        if not binary.is_file():
            raise SystemExit(f"missing binary: {binary}")

    manifest = json.loads(MANIFEST.read_text())
    assert manifest["schema"] == "jsvm-real-corpus/v1"
    samples = manifest["samples"]
    ids = [s["id"] for s in samples]
    assert len(ids) == len(set(ids)), "duplicate sample ids"

    TMP.mkdir(parents=True, exist_ok=True)
    WORK.mkdir(parents=True, exist_ok=True)

    rows = []
    for sample in samples:
        path = CORPUS / sample["path"]
        assert path.is_file(), path
        assert path.stat().st_size == sample["bytes"], sample["id"]
        assert sha256(path) == sample["sha256"], sample["id"]

        source = Path(sample["source"])
        if source.is_file():
            assert sha256(source) == sample["sha256"], (
                sample["id"],
                "mirrored bytes differ from source",
            )

        if sample["role"] != "raw":
            rows.append(
                {
                    "id": sample["id"],
                    "family": sample["family"],
                    "role": sample["role"],
                    "bytes": sample["bytes"],
                    "sha256": sample["sha256"],
                    "status": "reference-hash-ok",
                }
            )
            continue

        stem = sample["id"].replace("/", "_")
        pretty = TMP / f"{stem}.pretty.js"
        deob = TMP / f"{stem}.deob.js"
        report_path = TMP / f"{stem}.deob.json"

        run([FORMATTER, path, pretty])
        run(["node", "--check", pretty], timeout=60)

        run([DEOB, path, deob, "--report", report_path], timeout=300)
        run(["node", "--check", deob], timeout=60)
        deob_report = json.loads(report_path.read_text())
        assert deob_report["safe_static_only"] is True

        transforms = deob_report.get("transforms", {})
        for transform, minimum in MIN_DEOB_TRANSFORMS.get(sample["id"], {}).items():
            assert transforms.get(transform, 0) >= minimum, (
                sample["id"],
                transform,
                transforms.get(transform, 0),
                minimum,
            )

        expected_strings = EXPECTED_DEOB_STRINGS.get(sample["id"], ())
        forbidden_strings = FORBIDDEN_DEOB_STRINGS.get(sample["id"], ())
        if expected_strings or forbidden_strings:
            deob_text = deob.read_text()
            for expected in expected_strings:
                assert expected in deob_text, (sample["id"], expected)
            for forbidden in forbidden_strings:
                assert forbidden not in deob_text, (sample["id"], forbidden)

        scan_cp = run([SCANNER, "--json", pretty], timeout=300)
        scan_lines = [line for line in scan_cp.stdout.splitlines() if line.strip()]
        assert len(scan_lines) == 1, (sample["id"], len(scan_lines))
        scan = json.loads(scan_lines[0])
        assert scan.get("panicked") is False, sample["id"]
        assert not scan.get("diagnostics"), (sample["id"], scan.get("diagnostics"))

        metrics = {
            key: count_list(scan, key)
            for key in (
                "arrays",
                "decoder_candidates",
                "direct_switch_maps",
                "handler_function_tables",
                "handler_tables",
                "opcode_maps",
                "push_builders",
                "state_machines",
                "table_vms",
                "byte_transducers",
                "embedded",
            )
        }
        metrics["functions"] = len(scan.get("functions", []))
        metrics["if_ladder_state_machines_recursive"] = recursive_count(
            scan, "if_ladder_state_machines"
        )

        for key, minimum in MIN_SIGNALS.get(sample["id"], {}).items():
            assert metrics[key] >= minimum, (sample["id"], key, metrics[key], minimum)

        row = {
            "id": sample["id"],
            "family": sample["family"],
            "role": sample["role"],
            "bytes": sample["bytes"],
            "sha256": sample["sha256"],
            "formatter_bytes": pretty.stat().st_size,
            "deob_changed": bool(deob_report.get("changed")),
            "deob_iterations": deob_report.get("iterations"),
            "deob_transforms": deob_report.get("transforms", {}),
            "arithmetic_state_proofs": deob_report.get("arithmetic_state_proofs", []),
            "scanner": metrics,
            "status": "ok",
        }
        rows.append(row)
        print(
            sample["id"],
            "deob=", row["deob_transforms"],
            "scan=", metrics,
        )

    result = {
        "schema": "jsvm-real-corpus-check/v1",
        "manifest": str(MANIFEST.relative_to(ROOT)),
        "samples": rows,
    }
    out = WORK / "latest.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    raw_ok = sum(row["status"] == "ok" for row in rows)
    refs_ok = sum(row["status"] == "reference-hash-ok" for row in rows)
    print(f"PASS: {raw_ok} raw anti-bot samples + {refs_ok} reference samples")
    print(f"report: {out}")


if __name__ == "__main__":
    main()
