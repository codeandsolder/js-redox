#!/usr/bin/env python3
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = ROOT / "corpus/real/adtech-20260930"
DEFAULT_WORK = ROOT / "work/real-adtech-corpus"
FORMATTER = ROOT / ".cargo-target-nodebug/debug/js-format"
DEOB = ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe"
SCANNER = ROOT / ".cargo-target-nodebug/debug/jsvm-lift"


def run(argv, timeout=300):
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


def recursive_items(report: dict, key: str) -> list:
    out = list(report.get(key, []))
    for child in report.get("embedded", []):
        out.extend(recursive_items(child, key))
    return out


def confirmed_count(report: dict) -> int:
    total = sum(bool(f.get("confirmed_dispatch")) for f in report.get("functions", []))
    for child in report.get("embedded", []):
        total += confirmed_count(child)
    return total


def main():
    ap = argparse.ArgumentParser(description="Validate the pinned real-world adtech JS corpus")
    ap.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    ap.add_argument("--work", type=Path, default=DEFAULT_WORK)
    args = ap.parse_args()

    corpus = args.corpus.resolve()
    manifest_path = corpus / "manifest.json"
    tmp = args.work.resolve() / "tmp"
    work = args.work.resolve()
    if not manifest_path.is_file():
        raise SystemExit(
            f"missing real-adtech corpus manifest: {manifest_path}\n"
            "Pass --corpus PATH when the corpus is kept outside the source checkout."
        )
    for binary in (FORMATTER, DEOB, SCANNER):
        if not binary.is_file():
            raise SystemExit(f"missing binary: {binary}")

    manifest = json.loads(manifest_path.read_text())
    assert manifest["schema"] == "js-real-adtech-corpus/v1"
    samples = manifest["samples"]
    assert len({s["id"] for s in samples}) == len(samples), "duplicate sample id"

    tmp.mkdir(parents=True, exist_ok=True)
    work.mkdir(parents=True, exist_ok=True)
    rows = []

    for sample in samples:
        raw = corpus / sample["path"]
        pretty = corpus / sample["pretty_path"]
        assert raw.is_file(), raw
        assert pretty.is_file(), pretty
        assert raw.stat().st_size == sample["bytes"], sample["id"]
        assert sha256(raw) == sample["sha256"], sample["id"]
        assert pretty.stat().st_size == sample["pretty_bytes"], sample["id"]
        assert sha256(pretty) == sample["pretty_sha256"], sample["id"]

        stem = sample["id"]
        regenerated_pretty = tmp / f"{stem}.pretty.js"
        deob = tmp / f"{stem}.deob.js"
        deob_report_path = tmp / f"{stem}.deob.json"

        # Pretty views are deterministic analyst artifacts, not capture truth.
        run([FORMATTER, raw, regenerated_pretty])
        run(["node", "--check", regenerated_pretty], timeout=90)
        assert sha256(regenerated_pretty) == sample["pretty_sha256"], (
            sample["id"],
            "committed analyst view is stale",
        )

        # Safe deobfuscation must preserve source formatting except for proven
        # span rewrites. Never execute these production adtech samples.
        run([DEOB, raw, deob, "--report", deob_report_path], timeout=360)
        run(["node", "--check", deob], timeout=90)
        meta = json.loads(deob_report_path.read_text())
        assert meta["safe_static_only"] is True, sample["id"]
        assert meta.get("presentation_formatted") is False, sample["id"]
        assert meta.get("runtime_semantics_preserved_by_design") is True, sample["id"]
        assert "presentation_codegen" not in meta.get("transforms", {}), sample["id"]
        rewrites = sum(
            count
            for kind, count in meta.get("transforms", {}).items()
            if kind not in {"canonical_codegen", "presentation_codegen"}
        )
        assert rewrites >= sample["expect_deob_rewrites_min"], (
            sample["id"],
            rewrites,
            sample["expect_deob_rewrites_min"],
            meta.get("transforms"),
        )

        scan_cp = run([SCANNER, "--json", pretty], timeout=360)
        scan_lines = [line for line in scan_cp.stdout.splitlines() if line.strip()]
        assert len(scan_lines) == 1, (sample["id"], len(scan_lines))
        scan = json.loads(scan_lines[0])
        assert scan.get("panicked") is False, sample["id"]
        # Oxc can recover an AST from a small number of production-syntax
        # diagnostics (for example unusual generated regexp/module forms).
        # Keep the pressure useful without pretending zero diagnostics is a
        # prerequisite for a large real-world hard negative.
        diagnostics = int(scan.get("diagnostics") or 0)
        assert diagnostics <= int(sample.get("expect_diagnostics_max", 16)), (
            sample["id"],
            diagnostics,
        )

        confirmed = confirmed_count(scan)
        opcode_maps = len(recursive_items(scan, "opcode_maps"))
        table_vms = len(recursive_items(scan, "table_vms"))
        assert confirmed <= sample["expect_confirmed_max"], (sample["id"], confirmed)
        assert opcode_maps <= sample["expect_opcode_map_max"], (sample["id"], opcode_maps)
        assert table_vms <= sample["expect_table_vm_max"], (sample["id"], table_vms)

        scanner = {
            "diagnostics": diagnostics,
            "functions": len(scan.get("functions", [])),
            "embedded_recursive": len(recursive_items(scan, "embedded")),
            "direct_switch_maps_recursive": len(recursive_items(scan, "direct_switch_maps")),
            "handler_function_tables_recursive": len(
                recursive_items(scan, "handler_function_tables")
            ),
            "if_ladder_state_machines_recursive": len(
                recursive_items(scan, "if_ladder_state_machines")
            ),
            "confirmed_dispatchers_recursive": confirmed,
            "opcode_maps_recursive": opcode_maps,
            "table_vms_recursive": table_vms,
        }
        row = {
            "id": sample["id"],
            "family": sample["family"],
            "bytes": sample["bytes"],
            "sha256": sample["sha256"],
            "deob_changed": bool(meta.get("changed")),
            "deob_iterations": meta.get("iterations"),
            "deob_rewrites": rewrites,
            "deob_transforms": meta.get("transforms", {}),
            "scanner": scanner,
            "status": "ok",
        }
        rows.append(row)
        print(
            sample["id"],
            f"rewrites={rewrites}",
            f"transforms={row['deob_transforms']}",
            f"scanner={scanner}",
        )

    result = {
        "schema": "js-real-adtech-corpus-check/v1",
        "manifest": str(manifest_path),
        "samples": rows,
        "summary": {
            "samples": len(rows),
            "rewrites": sum(r["deob_rewrites"] for r in rows),
            "confirmed_dispatchers": sum(
                r["scanner"]["confirmed_dispatchers_recursive"] for r in rows
            ),
        },
    }
    out = work / "latest.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(
        f"PASS: {len(rows)} real adtech samples; "
        f"{result['summary']['rewrites']} proven readability rewrites; "
        f"{result['summary']['confirmed_dispatchers']} confirmed VM dispatchers"
    )
    print(f"report: {out}")


if __name__ == "__main__":
    main()
