#!/usr/bin/env python3
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STRING_RECOVERER = ROOT / "scripts/recover-js-obfuscator-strings.py"
DEFAULT_FORMATTER = ROOT / ".cargo-target-nodebug/debug/js-format"


def derived_path(raw_path: str, root: str) -> Path:
    p = Path(raw_path)
    parts = list(p.parts)
    if parts and parts[0] == "resources":
        parts = parts[1:]
    elif parts and parts[0] == "src":
        parts = parts[1:]
    return Path("src", root, *parts)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(argv, timeout):
    return subprocess.run(
        [str(x) for x in argv],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
    )


def main():
    ap = argparse.ArgumentParser(
        description=(
            "Run conservative non-executing static source recovery and reversible "
            "JS deobfuscation over normalized browser-capture source units"
        )
    )
    ap.add_argument("project", type=Path)
    ap.add_argument(
        "--deobfuscator",
        type=Path,
        default=ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe",
    )
    ap.add_argument(
        "--string-recoverer",
        type=Path,
        default=DEFAULT_STRING_RECOVERER,
    )
    ap.add_argument(
        "--formatter",
        type=Path,
        default=DEFAULT_FORMATTER,
    )
    args = ap.parse_args()

    project = args.project.resolve()
    source_index = json.loads((project / "analysis/source-index.json").read_text())
    out_dir = project / "analysis/deobfuscation"
    string_dir = project / "analysis/string-recovery"
    out_dir.mkdir(parents=True, exist_ok=True)
    string_dir.mkdir(parents=True, exist_ok=True)

    project_key = hashlib.sha256(str(project).encode()).hexdigest()[:16]
    tmp_dir = ROOT / "work/test-tmp/har-static-string-recovery" / project_key
    tmp_dir.mkdir(parents=True, exist_ok=True)

    units = []
    string_units = []
    for ordinal, unit in enumerate(source_index.get("units", [])):
        if unit.get("kind") != "javascript" or not unit.get("source_path"):
            continue
        raw_path = unit.get("raw_path")
        if not raw_path:
            continue
        source = project / raw_path
        if not source.is_file():
            continue

        rel = derived_path(raw_path, "_deobfuscated")
        readable_rel = derived_path(raw_path, "_readable")
        dest = project / rel
        readable_dest = project / readable_rel
        report_rel = Path("analysis/deobfuscation") / f"{ordinal:04}.json"
        report = project / report_rel
        string_report_rel = Path("analysis/string-recovery") / f"{ordinal:04}.json"
        string_report = project / string_report_rel
        recovered_tmp = tmp_dir / f"{ordinal:04}.js"
        dest.parent.mkdir(parents=True, exist_ok=True)
        readable_dest.parent.mkdir(parents=True, exist_ok=True)

        original_sha = sha256_bytes(source.read_bytes())
        string_row = {
            "ordinal": ordinal,
            "resource_id": unit.get("resource_id"),
            "url": unit.get("url"),
            "input_path": raw_path,
            "readable_baseline_path": unit.get("source_path"),
            "report_path": str(string_report_rel),
            "input_sha256": original_sha,
        }

        recovery_cp = run(
            [
                "uv", "run", "--no-project", "python",
                args.string_recoverer,
                source,
                recovered_tmp,
                "--report", string_report,
            ],
            timeout=180,
        )
        deob_input = source
        string_meta = None
        if recovery_cp.returncode == 0 and string_report.is_file() and recovered_tmp.is_file():
            string_meta = json.loads(string_report.read_text())
            if not string_meta.get("safe_static_only"):
                raise RuntimeError(f"unsafe string recovery report for {source}")
            if string_meta.get("input_sha256") != original_sha:
                raise RuntimeError(f"string recovery input hash mismatch for {source}")
            recovered_sha = sha256_bytes(recovered_tmp.read_bytes())
            if string_meta.get("output_sha256") != recovered_sha:
                raise RuntimeError(f"string recovery output hash mismatch for {source}")
            deob_input = recovered_tmp
            string_row.update(
                {
                    "exit": 0,
                    "changed": bool(string_meta.get("changed")),
                    "replacements": int(string_meta.get("replacements", 0)),
                    "output_sha256": recovered_sha,
                    "decoders": string_meta.get("decoders", []),
                }
            )
        else:
            string_row.update(
                {
                    "exit": recovery_cp.returncode or 1,
                    "changed": False,
                    "replacements": 0,
                    "output_sha256": original_sha,
                    "decoders": [],
                    "error": (recovery_cp.stdout + recovery_cp.stderr)[-3000:],
                    "fallback": "original source passed to safe deobfuscator",
                }
            )
        string_units.append(string_row)

        cp = run(
            [
                args.deobfuscator,
                deob_input,
                dest,
                "--report",
                report,
            ],
            timeout=180,
        )
        row = {
            "ordinal": ordinal,
            "resource_id": unit.get("resource_id"),
            "url": unit.get("url"),
            "raw_path": raw_path,
            "input_path": raw_path,
            "readable_baseline_path": unit.get("source_path"),
            "output_path": str(rel),
            "readable_output_path": str(readable_rel),
            "report_path": str(report_rel),
            "string_recovery_report_path": str(string_report_rel),
            "string_recovery_changed": bool(string_row.get("changed")),
            "string_recovery_replacements": int(string_row.get("replacements", 0)),
            "input_sha256": original_sha,
            "pre_deob_sha256": string_row.get("output_sha256", original_sha),
            "exit": cp.returncode,
        }
        if cp.returncode:
            row["error"] = (cp.stdout + cp.stderr)[-3000:]
            units.append(row)
            continue

        meta = json.loads(report.read_text())
        if not meta.get("safe_static_only"):
            raise RuntimeError(f"unsafe deobfuscation report for {source}")
        if not meta.get("runtime_semantics_preserved_by_design", True):
            raise RuntimeError(
                f"presentation-formatted deobfuscation is not allowed in the exact-safe capture stage: {source}"
            )
        transforms = dict(meta.get("transforms", {}))
        if string_row.get("replacements"):
            transforms["encoded_string_decode"] = int(string_row["replacements"])
        row["changed"] = bool(meta.get("changed")) or bool(string_row.get("changed"))
        row["iterations"] = meta.get("iterations")
        row["transforms"] = transforms
        row["arithmetic_state_proofs"] = meta.get("arithmetic_state_proofs", [])
        row["safe_static_only"] = bool(meta.get("safe_static_only"))
        row["presentation_formatted"] = bool(meta.get("presentation_formatted", False))
        row["runtime_semantics_preserved_by_design"] = bool(
            meta.get("runtime_semantics_preserved_by_design", True)
        )
        row["output_sha256"] = meta.get("output_sha256")

        format_cp = run([args.formatter, dest, readable_dest], timeout=120)
        if format_cp.returncode == 0:
            row["readable_formatted"] = True
            row["readable_output_sha256"] = sha256_bytes(readable_dest.read_bytes())
        else:
            readable_dest.write_bytes(dest.read_bytes())
            row["readable_formatted"] = False
            row["readable_output_sha256"] = row["output_sha256"]
            row["readable_format_error"] = (format_cp.stdout + format_cp.stderr)[-3000:]
        units.append(row)

    string_changed = [u for u in string_units if u.get("changed")]
    string_failed = [u for u in string_units if u.get("exit")]
    string_index = {
        "schema": "har-static-string-recovery/v1",
        "safe_static_only": True,
        "recoverer": str(args.string_recoverer),
        "units": string_units,
        "summary": {
            "javascript_units": len(string_units),
            "changed_units": len(string_changed),
            "failed_units": len(string_failed),
            "replacements": sum(int(u.get("replacements", 0)) for u in string_units),
        },
    }
    (project / "analysis/string-recovery.json").write_text(
        json.dumps(string_index, indent=2) + "\n"
    )

    changed = [u for u in units if u.get("changed")]
    failed = [u for u in units if u.get("exit")]
    totals = {}
    for unit in units:
        for kind, count in unit.get("transforms", {}).items():
            totals[kind] = totals.get(kind, 0) + count

    index = {
        "schema": "har-safe-deobfuscation/v1",
        "safe_static_only": True,
        "runtime_semantics_preserved_by_design": True,
        "presentation_formatted": False,
        "deobfuscator": str(args.deobfuscator),
        "formatter": str(args.formatter),
        "string_recovery": "analysis/string-recovery.json",
        "units": units,
        "summary": {
            "javascript_units": len(units),
            "changed_units": len(changed),
            "failed_units": len(failed),
            "string_recovery_changed_units": len(string_changed),
            "string_recovery_replacements": string_index["summary"]["replacements"],
            "transforms": dict(sorted(totals.items())),
        },
    }
    (project / "analysis/deobfuscation.json").write_text(
        json.dumps(index, indent=2) + "\n"
    )
    print(
        f"safe source recovery: {len(units)} JS units, "
        f"{len(changed)} changed, {len(failed)} deob failures, "
        f"string recovery={len(string_changed)} units/"
        f"{string_index['summary']['replacements']} replacements/"
        f"{len(string_failed)} failures, transforms={totals}"
    )


if __name__ == "__main__":
    main()
