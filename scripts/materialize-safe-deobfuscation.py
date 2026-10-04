#!/usr/bin/env python3
import argparse
import hashlib
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from content_dedup import default_jobs, link_or_copy, sha256_path

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


def run(argv, timeout):
    argv = [str(x) for x in argv]
    try:
        return subprocess.run(
            argv,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", "replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", "replace")
        return subprocess.CompletedProcess(
            argv,
            124,
            stdout,
            stderr + f"\ntimed out after {timeout}s",
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
    ap.add_argument("--jobs", type=int, default=default_jobs())
    args = ap.parse_args()
    jobs = max(1, args.jobs)

    project = args.project.resolve()
    source_index = json.loads((project / "analysis/source-index.json").read_text())
    out_dir = project / "analysis/deobfuscation"
    string_dir = project / "analysis/string-recovery"
    out_dir.mkdir(parents=True, exist_ok=True)
    string_dir.mkdir(parents=True, exist_ok=True)

    project_key = hashlib.sha256(str(project).encode()).hexdigest()[:16]
    tmp_dir = ROOT / "work/test-tmp/har-static-string-recovery" / project_key
    tmp_dir.mkdir(parents=True, exist_ok=True)

    occurrences = []
    raw_groups = {}
    for ordinal, unit in enumerate(source_index.get("units", [])):
        if unit.get("kind") != "javascript" or not unit.get("source_path"):
            continue
        raw_path = unit.get("raw_path")
        if not raw_path:
            continue
        source = project / raw_path
        if not source.is_file():
            continue
        raw_sha = sha256_path(source)
        occurrence = {
            "ordinal": ordinal,
            "unit": unit,
            "raw_path": raw_path,
            "source": source,
            "raw_sha": raw_sha,
        }
        occurrences.append(occurrence)
        raw_groups.setdefault(raw_sha, []).append(occurrence)

    def recover_strings(raw_sha, group):
        canonical = group[0]
        cache = tmp_dir / "string" / raw_sha
        cache.mkdir(parents=True, exist_ok=True)
        recovered = cache / "recovered.js"
        report = cache / "report.json"
        cp = run(
            [
                sys.executable,
                args.string_recoverer,
                canonical["source"],
                recovered,
                "--report",
                report,
            ],
            timeout=180,
        )
        result = {
            "raw_sha": raw_sha,
            "canonical_ordinal": canonical["ordinal"],
            "canonical_raw_path": canonical["raw_path"],
            "report": report,
            "exit": cp.returncode,
            "changed": False,
            "replacements": 0,
            "decoders": [],
            "selected": canonical["source"],
            "selected_sha": raw_sha,
            "error": None,
        }
        if cp.returncode == 0 and report.is_file() and recovered.is_file():
            meta = json.loads(report.read_text())
            recovered_sha = sha256_path(recovered)
            if not meta.get("safe_static_only"):
                raise RuntimeError(
                    f"unsafe string recovery report for {canonical['source']}"
                )
            if meta.get("input_sha256") != raw_sha:
                raise RuntimeError(
                    f"string recovery input hash mismatch for {canonical['source']}"
                )
            if meta.get("output_sha256") != recovered_sha:
                raise RuntimeError(
                    f"string recovery output hash mismatch for {canonical['source']}"
                )
            result.update(
                {
                    "exit": 0,
                    "changed": bool(meta.get("changed")),
                    "replacements": int(meta.get("replacements", 0)),
                    "decoders": meta.get("decoders", []),
                    "selected": recovered,
                    "selected_sha": recovered_sha,
                }
            )
        else:
            result["exit"] = cp.returncode or 1
            result["error"] = (cp.stdout + cp.stderr)[-3000:]
        return result

    string_results = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {
            pool.submit(recover_strings, digest, group): digest
            for digest, group in raw_groups.items()
        }
        for future in as_completed(futures):
            result = future.result()
            string_results[result["raw_sha"]] = result

    pre_deob_groups = {}
    for raw_sha, result in string_results.items():
        pre_deob_groups.setdefault(result["selected_sha"], []).append(raw_sha)

    def safe_deob(selected_sha, raw_shas):
        representative = string_results[raw_shas[0]]
        cache = tmp_dir / "deob" / selected_sha
        cache.mkdir(parents=True, exist_ok=True)
        output = cache / "safe.js"
        report = cache / "report.json"
        cp = run(
            [
                args.deobfuscator,
                representative["selected"],
                output,
                "--report",
                report,
            ],
            timeout=180,
        )
        result = {
            "selected_sha": selected_sha,
            "raw_shas": list(raw_shas),
            "canonical_raw_sha": raw_shas[0],
            "report": report,
            "output": output,
            "exit": cp.returncode,
            "changed": False,
            "iterations": None,
            "transforms": {},
            "arithmetic_state_proofs": [],
            "output_sha": None,
            "safe_static_only": False,
            "presentation_formatted": False,
            "runtime_semantics_preserved_by_design": True,
            "error": None,
        }
        if cp.returncode:
            result["error"] = (cp.stdout + cp.stderr)[-3000:]
            return result
        meta = json.loads(report.read_text())
        output_sha = sha256_path(output)
        if not meta.get("safe_static_only"):
            raise RuntimeError(
                f"unsafe deobfuscation report for {representative['selected']}"
            )
        if not meta.get("runtime_semantics_preserved_by_design", True):
            raise RuntimeError(
                "presentation-formatted deobfuscation is not allowed in the exact-safe "
                f"capture stage: {representative['selected']}"
            )
        if meta.get("input_sha256") != selected_sha:
            raise RuntimeError(
                f"safe deobfuscation input hash mismatch for {representative['selected']}"
            )
        if meta.get("output_sha256") != output_sha:
            raise RuntimeError(
                f"safe deobfuscation output hash mismatch for {representative['selected']}"
            )
        result.update(
            {
                "exit": 0,
                "changed": bool(meta.get("changed")),
                "iterations": meta.get("iterations"),
                "transforms": dict(meta.get("transforms", {})),
                "arithmetic_state_proofs": meta.get("arithmetic_state_proofs", []),
                "output_sha": output_sha,
                "safe_static_only": True,
                "presentation_formatted": bool(
                    meta.get("presentation_formatted", False)
                ),
                "runtime_semantics_preserved_by_design": bool(
                    meta.get("runtime_semantics_preserved_by_design", True)
                ),
            }
        )
        return result

    deob_results = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {
            pool.submit(safe_deob, digest, raw_shas): digest
            for digest, raw_shas in pre_deob_groups.items()
        }
        for future in as_completed(futures):
            result = future.result()
            deob_results[result["selected_sha"]] = result

    output_groups = {}
    for result in deob_results.values():
        if result["exit"] == 0 and result["output_sha"]:
            output_groups.setdefault(result["output_sha"], []).append(
                result["selected_sha"]
            )

    def format_output(output_sha, selected_shas):
        representative = deob_results[selected_shas[0]]
        cache = tmp_dir / "readable" / output_sha
        cache.mkdir(parents=True, exist_ok=True)
        readable = cache / "readable.js"
        cp = run([args.formatter, representative["output"], readable], timeout=120)
        if cp.returncode:
            readable.write_bytes(representative["output"].read_bytes())
        return {
            "output_sha": output_sha,
            "selected_shas": list(selected_shas),
            "readable": readable,
            "formatted": cp.returncode == 0,
            "readable_sha": sha256_path(readable),
            "error": (cp.stdout + cp.stderr)[-3000:] if cp.returncode else None,
        }

    readable_results = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {
            pool.submit(format_output, digest, selected_shas): digest
            for digest, selected_shas in output_groups.items()
        }
        for future in as_completed(futures):
            result = future.result()
            readable_results[result["output_sha"]] = result

    units = []
    string_units = []
    for occurrence in occurrences:
        ordinal = occurrence["ordinal"]
        unit = occurrence["unit"]
        raw_path = occurrence["raw_path"]
        raw_sha = occurrence["raw_sha"]
        raw_group = raw_groups[raw_sha]
        string_result = string_results[raw_sha]
        deob_result = deob_results[string_result["selected_sha"]]

        report_rel = Path("analysis/deobfuscation") / f"{ordinal:04}.json"
        report = project / report_rel
        string_report_rel = Path("analysis/string-recovery") / f"{ordinal:04}.json"
        string_report = project / string_report_rel
        if string_result["report"].is_file():
            link_or_copy(string_result["report"], string_report)
        if deob_result["report"].is_file():
            link_or_copy(deob_result["report"], report)

        string_row = {
            "ordinal": ordinal,
            "resource_id": unit.get("resource_id"),
            "url": unit.get("url"),
            "input_path": raw_path,
            "readable_baseline_path": unit.get("source_path"),
            "report_path": str(string_report_rel),
            "input_sha256": raw_sha,
            "output_sha256": string_result["selected_sha"],
            "exit": string_result["exit"],
            "changed": string_result["changed"],
            "replacements": string_result["replacements"],
            "decoders": string_result["decoders"],
            "content_group_size": len(raw_group),
            "deduplicated": ordinal != string_result["canonical_ordinal"],
            "deduplicated_from_ordinal": (
                string_result["canonical_ordinal"]
                if ordinal != string_result["canonical_ordinal"]
                else None
            ),
        }
        if string_result["error"]:
            string_row["error"] = string_result["error"]
            string_row["fallback"] = "original source passed to safe deobfuscator"
        string_units.append(string_row)

        rel = derived_path(raw_path, "_deobfuscated")
        readable_rel = derived_path(raw_path, "_readable")
        dest = project / rel
        readable_dest = project / readable_rel
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
            "string_recovery_changed": string_result["changed"],
            "string_recovery_replacements": string_result["replacements"],
            "input_sha256": raw_sha,
            "pre_deob_sha256": string_result["selected_sha"],
            "exit": deob_result["exit"],
            "content_group_size": len(raw_group),
            "deduplicated": ordinal != string_result["canonical_ordinal"],
            "deduplicated_from_ordinal": (
                string_result["canonical_ordinal"]
                if ordinal != string_result["canonical_ordinal"]
                else None
            ),
            "pre_deob_group_size": sum(
                len(raw_groups[member]) for member in deob_result["raw_shas"]
            ),
        }
        if deob_result["exit"]:
            row["error"] = deob_result["error"]
            units.append(row)
            continue

        transforms = dict(deob_result["transforms"])
        if string_result["replacements"]:
            transforms["encoded_string_decode"] = string_result["replacements"]
        row.update(
            {
                "changed": deob_result["changed"] or string_result["changed"],
                "iterations": deob_result["iterations"],
                "transforms": transforms,
                "arithmetic_state_proofs": deob_result[
                    "arithmetic_state_proofs"
                ],
                "safe_static_only": deob_result["safe_static_only"],
                "presentation_formatted": deob_result["presentation_formatted"],
                "runtime_semantics_preserved_by_design": deob_result[
                    "runtime_semantics_preserved_by_design"
                ],
                "output_sha256": deob_result["output_sha"],
            }
        )
        row["output_materialization"] = link_or_copy(deob_result["output"], dest)
        readable_result = readable_results[deob_result["output_sha"]]
        row["readable_materialization"] = link_or_copy(
            readable_result["readable"], readable_dest
        )
        row["readable_formatted"] = readable_result["formatted"]
        row["readable_output_sha256"] = readable_result["readable_sha"]
        if readable_result["error"]:
            row["readable_format_error"] = readable_result["error"]
        units.append(row)

    string_changed = [u for u in string_units if u.get("changed")]
    string_failed = [u for u in string_units if u.get("exit")]
    string_index = {
        "schema": "har-static-string-recovery/v2",
        "safe_static_only": True,
        "recoverer": str(args.string_recoverer),
        "units": string_units,
        "summary": {
            "javascript_units": len(string_units),
            "unique_input_bodies": len(raw_groups),
            "deduplicated_units": len(string_units) - len(raw_groups),
            "unique_post_recovery_bodies": len(pre_deob_groups),
            "changed_units": len(string_changed),
            "failed_units": len(string_failed),
            "replacements": sum(
                int(u.get("replacements", 0)) for u in string_units
            ),
            "invocations": len(raw_groups),
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
        "schema": "har-safe-deobfuscation/v2",
        "safe_static_only": True,
        "runtime_semantics_preserved_by_design": True,
        "presentation_formatted": False,
        "deobfuscator": str(args.deobfuscator),
        "formatter": str(args.formatter),
        "string_recovery": "analysis/string-recovery.json",
        "units": units,
        "summary": {
            "javascript_units": len(units),
            "unique_raw_inputs": len(raw_groups),
            "deduplicated_raw_units": len(units) - len(raw_groups),
            "unique_pre_deob_inputs": len(pre_deob_groups),
            "unique_deob_outputs": len(output_groups),
            "string_recovery_invocations": len(raw_groups),
            "safe_deob_invocations": len(pre_deob_groups),
            "readable_format_invocations": len(output_groups),
            "jobs": jobs,
            "changed_units": len(changed),
            "failed_units": len(failed),
            "string_recovery_changed_units": len(string_changed),
            "string_recovery_replacements": string_index["summary"][
                "replacements"
            ],
            "transforms": dict(sorted(totals.items())),
        },
    }
    (project / "analysis/deobfuscation.json").write_text(
        json.dumps(index, indent=2) + "\n"
    )
    print(
        f"safe source recovery: {len(units)} JS occurrences / "
        f"{len(raw_groups)} unique raw / {len(pre_deob_groups)} unique pre-deob / "
        f"{len(output_groups)} unique safe outputs; "
        f"{len(changed)} changed, {len(failed)} deob failures, "
        f"string recovery={len(string_changed)} units/"
        f"{string_index['summary']['replacements']} replacements/"
        f"{len(string_failed)} failures; jobs={jobs}, transforms={totals}"
    )


if __name__ == "__main__":
    main()
