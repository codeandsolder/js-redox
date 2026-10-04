#!/usr/bin/env python3
import argparse
import copy
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

from browser_script_types import is_executable_script
from content_dedup import sha256_path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_STRING_RECOVERER = ROOT / "scripts/recover-js-obfuscator-strings.py"


def direct_summary(report):
    direct_switches = report.get("direct_switch_maps", [])
    handler_tables = report.get("handler_function_tables", [])
    return {
        "confirmed_dispatchers": sum(
            bool(f.get("confirmed_dispatch")) for f in report.get("functions", [])
        ),
        "opcode_maps": len(report.get("opcode_maps", [])),
        "direct_switch_maps": len(direct_switches),
        "confirmed_direct_switch_maps": sum(
            bool(m.get("confirmed_vm")) for m in direct_switches
        ),
        "handler_tables": len(handler_tables),
        "largest_handler_table": max(
            (int(t.get("function_values", 0)) for t in handler_tables),
            default=0,
        ),
        "byte_transducers": len(report.get("byte_transducers", [])),
        "table_vms": len(report.get("table_vms", [])),
        "embedded_code_units": len(report.get("embedded", [])),
    }


def run_tool(argv, timeout):
    return subprocess.run(
        [str(x) for x in argv],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
    )


def sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generated_output_path(root: str, scan_id: int, ordinal: int) -> Path:
    return Path("src") / root / f"{scan_id:04}" / f"embedded-{ordinal:03}.js"


def recover_generated_unit(
    project: Path,
    raw: Path,
    raw_rel: str,
    scan_id: int,
    ordinal: int,
    args,
):
    recovery_rel = Path("analysis/generated-recovery") / f"{scan_id:04}-{ordinal:03}"
    recovery_dir = project / recovery_rel
    recovery_dir.mkdir(parents=True, exist_ok=True)

    string_tmp = recovery_dir / "string-recovered.js"
    string_report = recovery_dir / "string-recovery.json"
    deob_report = recovery_dir / "deobfuscation.json"

    safe_rel = generated_output_path("_dynamic_deobfuscated", scan_id, ordinal)
    safe_dest = project / safe_rel
    readable_rel = generated_output_path("_dynamic", scan_id, ordinal)
    readable_dest = project / readable_rel
    safe_dest.parent.mkdir(parents=True, exist_ok=True)
    readable_dest.parent.mkdir(parents=True, exist_ok=True)

    raw_sha = sha256_path(raw)
    row = {
        "parent_scan_id": scan_id,
        "ordinal": ordinal,
        "raw_path": raw_rel,
        "raw_sha256": raw_sha,
        "string_recovery_report": str(string_report.relative_to(project)),
        "deobfuscation_report": str(deob_report.relative_to(project)),
    }

    string_cp = run_tool(
        [
            "uv",
            "run",
            "--no-project",
            "python",
            args.string_recoverer,
            raw,
            string_tmp,
            "--report",
            string_report,
        ],
        timeout=180,
    )
    selected = raw
    string_ok = False
    string_changed = False
    if string_cp.returncode == 0 and string_tmp.is_file() and string_report.is_file():
        try:
            meta = json.loads(string_report.read_text())
            output_sha = sha256_path(string_tmp)
            string_ok = (
                bool(meta.get("safe_static_only"))
                and meta.get("input_sha256") == raw_sha
                and meta.get("output_sha256") == output_sha
            )
        except (OSError, ValueError, TypeError):
            meta = {}
            string_ok = False
        if string_ok:
            selected = string_tmp
            string_changed = bool(meta.get("changed"))
            row["string_recovery"] = {
                "exit": 0,
                "changed": string_changed,
                "replacements": int(meta.get("replacements", 0)),
                "output_sha256": output_sha,
            }
        else:
            row["string_recovery"] = {
                "exit": 1,
                "changed": False,
                "replacements": 0,
                "error": "string-recovery provenance/hash validation failed",
            }
    else:
        row["string_recovery"] = {
            "exit": string_cp.returncode or 1,
            "changed": False,
            "replacements": 0,
            "error": (string_cp.stdout + string_cp.stderr)[-3000:],
        }

    selected_sha = sha256_path(selected)
    deob_cp = run_tool(
        [
            args.deobfuscator,
            selected,
            safe_dest,
            "--report",
            deob_report,
        ],
        timeout=180,
    )

    if deob_cp.returncode == 0 and safe_dest.is_file() and deob_report.is_file():
        try:
            meta = json.loads(deob_report.read_text())
            output_sha = sha256_path(safe_dest)
            deob_ok = (
                bool(meta.get("safe_static_only"))
                and bool(meta.get("runtime_semantics_preserved_by_design", True))
                and not bool(meta.get("presentation_formatted", False))
                and meta.get("input_sha256") == selected_sha
                and meta.get("output_sha256") == output_sha
            )
        except (OSError, ValueError, TypeError):
            meta = {}
            deob_ok = False
        if deob_ok:
            analysis_rel = safe_rel
            selected_stage = "safe_deobfuscation"
            row["deobfuscation"] = {
                "exit": 0,
                "changed": bool(meta.get("changed")),
                "iterations": int(meta.get("iterations", 0)),
                "transforms": meta.get("transforms", {}),
                "output_sha256": output_sha,
            }
        else:
            deob_cp = subprocess.CompletedProcess([], 1, "", "deob provenance/hash validation failed")
    if deob_cp.returncode != 0:
        row["deobfuscation"] = {
            "exit": deob_cp.returncode or 1,
            "changed": False,
            "error": (deob_cp.stdout + deob_cp.stderr)[-3000:],
        }
        if string_ok and string_changed:
            shutil.copyfile(string_tmp, safe_dest)
            analysis_rel = safe_rel
            selected_stage = "string_recovery_only"
        else:
            analysis_rel = Path(raw_rel)
            selected_stage = "exact_fallback"

    analysis_source = project / analysis_rel
    format_cp = run_tool([args.formatter, analysis_source, readable_dest], timeout=120)
    if format_cp.returncode:
        shutil.copyfile(analysis_source, readable_dest)

    row.update(
        {
            "selected_stage": selected_stage,
            "analysis_path": str(analysis_rel),
            "analysis_sha256": sha256_path(analysis_source),
            "readable_path": str(readable_rel),
            "readable_formatted": format_cp.returncode == 0,
            "readable_sha256": sha256_path(readable_dest),
        }
    )
    if format_cp.returncode:
        row["readable_format_error"] = (format_cp.stdout + format_cp.stderr)[-3000:]
    return row


def main():
    ap = argparse.ArgumentParser(
        description="Recursively recover and scan JavaScript code units for generated code and VM structures"
    )
    ap.add_argument("project", type=Path)
    ap.add_argument(
        "--scanner",
        type=Path,
        default=ROOT / ".cargo-target-nodebug/debug/jsvm-lift",
    )
    ap.add_argument(
        "--formatter",
        type=Path,
        default=ROOT / ".cargo-target-nodebug/debug/js-format",
    )
    ap.add_argument(
        "--switch-ir",
        type=Path,
        default=ROOT / ".cargo-target-nodebug/debug/switch-ir",
    )
    ap.add_argument(
        "--table-ir",
        type=Path,
        default=ROOT / ".cargo-target-nodebug/debug/table-ir",
    )
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
    ap.add_argument("--max-generated-depth", type=int, default=8)
    ap.add_argument("--max-code-units", type=int, default=256)
    args = ap.parse_args()

    project = args.project.resolve()
    manifest = json.loads((project / "har-manifest.json").read_text())
    deob_path = project / "analysis/deobfuscation.json"
    deob = json.loads(deob_path.read_text()) if deob_path.exists() else {"units": []}
    deob_by_raw = {
        unit.get("raw_path"): unit
        for unit in deob.get("units", [])
        if unit.get("raw_path") and not unit.get("exit") and unit.get("output_path")
    }
    outdir = project / "analysis" / "jsvm"
    outdir.mkdir(parents=True, exist_ok=True)

    bundle_spans_by_parent = {}
    bundles_path = project / "analysis/bundles.json"
    if bundles_path.exists():
        bundle_index = json.loads(bundles_path.read_text())
        for bundle in bundle_index.get("bundles", []):
            parent_path = bundle.get("parent_path")
            start = bundle.get("module_table_start")
            end = bundle.get("module_table_end")
            if parent_path and start is not None and end is not None:
                bundle_spans_by_parent.setdefault(parent_path, set()).add(
                    (int(start), int(end))
                )

    code_units = []
    generated_recovery = []
    seen_scan_paths = set()

    def queue(unit):
        path = unit.get("path")
        if not path or path in seen_scan_paths or len(code_units) >= args.max_code_units:
            return None
        seen_scan_paths.add(path)
        code_units.append(unit)
        return len(code_units) - 1

    for resource in manifest.get("resources", []):
        raw_path = resource.get("output_path")
        if resource.get("kind") != "javascript" or not raw_path:
            continue
        derived = deob_by_raw.get(raw_path)
        scan_path = derived.get("output_path") if derived else raw_path
        queue(
            {
                "origin": "resource",
                "resource_id": resource["id"],
                "url": resource["url"],
                "raw_path": raw_path,
                "path": scan_path,
                "analysis_origin": "safe_deobfuscation" if derived else "captured_source",
                "deobfuscation_ordinal": derived.get("ordinal") if derived else None,
                "generated_depth": 0,
            }
        )

    for script in manifest.get("inline_scripts", []):
        raw_path = script.get("output_path")
        if not raw_path or not is_executable_script(script.get("script_type")):
            continue
        parent = manifest["resources"][script["parent_resource_id"]]
        derived = deob_by_raw.get(raw_path)
        scan_path = derived.get("output_path") if derived else raw_path
        queue(
            {
                "origin": "inline_script",
                "resource_id": script["parent_resource_id"],
                "url": parent["url"],
                "ordinal": script["ordinal"],
                "raw_path": raw_path,
                "path": scan_path,
                "analysis_origin": "safe_deobfuscation" if derived else "captured_source",
                "deobfuscation_ordinal": derived.get("ordinal") if derived else None,
                "generated_depth": 0,
            }
        )

    rows = []
    dynamic_units = []
    scanner_cache = {}
    scanner_invocations = 0
    deduplicated_scans = 0
    scan_id = 0
    while scan_id < len(code_units):
        unit = code_units[scan_id]
        source = project / unit["path"]
        row = dict(unit)
        row["scan_id"] = scan_id

        if not source.is_file():
            row["scanner_exit"] = 1
            row["error"] = f"missing source path: {source}"
            rows.append(row)
            scan_id += 1
            continue

        source_sha = sha256_path(source)
        row["analysis_sha256"] = source_sha
        cached = scanner_cache.get(source_sha)
        reused_scan = cached is not None and not cached["report"].get("embedded")
        if reused_scan:
            report = copy.deepcopy(cached["report"])
            row["scanner_exit"] = 0
            row["scanner_deduplicated"] = True
            row["scanner_deduplicated_from_scan_id"] = cached["scan_id"]
            deduplicated_scans += 1
        else:
            dump_dir = outdir / "embedded" / f"{scan_id:04}"
            cp = run_tool(
                [
                    args.scanner,
                    "--json",
                    "--dump-embedded",
                    dump_dir,
                    source,
                ],
                timeout=120,
            )
            scanner_invocations += 1
            row["scanner_exit"] = cp.returncode
            row["scanner_deduplicated"] = False
            if cp.returncode:
                row["error"] = cp.stderr[-3000:]
                rows.append(row)
                scan_id += 1
                continue

            lines = [line for line in cp.stdout.splitlines() if line.strip()]
            if len(lines) != 1:
                row["error"] = f"expected one JSON report, got {len(lines)}"
                rows.append(row)
                scan_id += 1
                continue
            report = json.loads(lines[0])
            if not report.get("embedded"):
                scanner_cache[source_sha] = {
                    "scan_id": scan_id,
                    "report": copy.deepcopy(report),
                }

        row["bytes"] = source.stat().st_size
        report_path = outdir / f"{scan_id:04}.json"
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        row["report"] = str(report_path.relative_to(project))
        row.update(direct_summary(report))
        known_bundle_spans = bundle_spans_by_parent.get(unit["path"], set())
        large_handler_tables = [
            table
            for table in report.get("handler_function_tables", [])
            if int(table.get("function_values", 0)) >= 32
        ]
        bundle_handler_tables = [
            table
            for table in large_handler_tables
            if (int(table.get("start", -1)), int(table.get("end", -1)))
            in known_bundle_spans
        ]
        non_bundle_handler_tables = [
            table
            for table in large_handler_tables
            if (int(table.get("start", -1)), int(table.get("end", -1)))
            not in known_bundle_spans
        ]
        looped_dynamic_handler_tables = [
            table
            for table in non_bundle_handler_tables
            if int(table.get("looped_dynamic_call_sites", 0)) > 0
        ]
        row["bundle_module_table_handler_tables"] = len(bundle_handler_tables)
        row["largest_non_bundle_handler_table"] = max(
            (int(table.get("function_values", 0)) for table in non_bundle_handler_tables),
            default=0,
        )
        row["looped_dynamic_handler_tables"] = len(looped_dynamic_handler_tables)
        row["largest_looped_dynamic_handler_table"] = max(
            (
                int(table.get("function_values", 0))
                for table in looped_dynamic_handler_tables
            ),
            default=0,
        )

        embedded = []
        parent_depth = int(unit.get("generated_depth", 0))
        for ordinal, node in enumerate(report.get("embedded", []), 1):
            dumped = node.get("dump_path")
            if not dumped:
                continue
            raw = Path(dumped)
            raw_rel = str(raw.relative_to(project))
            depth = parent_depth + 1

            recovery = recover_generated_unit(
                project,
                raw,
                raw_rel,
                scan_id,
                ordinal,
                args,
            )
            generated_recovery.append(recovery)

            item = {
                "parent_scan_id": scan_id,
                "ordinal": ordinal,
                "depth": depth,
                "kind": node.get("kind"),
                "outer_start": node.get("outer_start"),
                "outer_end": node.get("outer_end"),
                "body_bytes": node.get("body_bytes"),
                "raw_dump": raw_rel,
                "source_path": recovery["readable_path"],
                "analysis_path": recovery["analysis_path"],
                "analysis_stage": recovery["selected_stage"],
                "recovery_report": str(
                    Path("analysis/generated-recovery")
                    / f"{scan_id:04}-{ordinal:03}"
                ),
                "formatted": recovery["readable_formatted"],
                "handler_tables": len(node.get("handler_function_tables", [])),
                "table_vms": len(node.get("table_vms", [])),
                "opcode_maps": len(node.get("opcode_maps", [])),
            }

            child_scan_id = None
            if depth <= args.max_generated_depth:
                child_scan_id = queue(
                    {
                        "origin": "generated_dynamic_code",
                        "resource_id": unit.get("resource_id"),
                        "url": unit.get("url"),
                        "raw_path": raw_rel,
                        "path": recovery["analysis_path"],
                        "readable_path": recovery["readable_path"],
                        "analysis_origin": recovery["selected_stage"],
                        "generated_recovery_ordinal": len(generated_recovery) - 1,
                        "parent_scan_id": scan_id,
                        "parent_dynamic_ordinal": ordinal,
                        "generated_depth": depth,
                    }
                )
            item["child_scan_id"] = child_scan_id
            embedded.append(item)
            dynamic_units.append(item)

        row["embedded_units"] = embedded

        if row["confirmed_direct_switch_maps"]:
            switch_ir_path = outdir / f"{scan_id:04}.switch-ir.json"
            sp = run_tool(
                [
                    args.switch_ir,
                    source,
                    report_path,
                    "--output",
                    switch_ir_path,
                ],
                timeout=180,
            )
            row["switch_ir_exit"] = sp.returncode
            if sp.returncode:
                row["switch_ir_error"] = (sp.stdout + sp.stderr)[-3000:]
            else:
                row["switch_ir"] = str(switch_ir_path.relative_to(project))

        if row["table_vms"]:
            table_ir_path = outdir / f"{scan_id:04}.table-ir.json"
            tp = run_tool(
                [
                    args.table_ir,
                    source,
                    report_path,
                    "--output",
                    table_ir_path,
                ],
                timeout=180,
            )
            row["table_ir_exit"] = tp.returncode
            if tp.returncode:
                row["table_ir_error"] = (tp.stdout + tp.stderr)[-3000:]
            else:
                row["table_ir"] = str(table_ir_path.relative_to(project))

        row["confirmed_vm_signal"] = any(
            row[k]
            for k in (
                "confirmed_dispatchers",
                "opcode_maps",
                "confirmed_direct_switch_maps",
                "table_vms",
                "byte_transducers",
            )
        )
        row["large_handler_table_candidate"] = (
            not row["confirmed_vm_signal"]
            and row["largest_looped_dynamic_handler_table"] >= 32
        )
        row["vm_signal"] = (
            row["confirmed_vm_signal"]
            or row["direct_switch_maps"] > 0
            or row["large_handler_table_candidate"]
        )
        rows.append(row)
        scan_id += 1

    generated_recovery_index = {
        "schema": "generated-code-safe-recovery/v1",
        "safe_static_only": True,
        "units": generated_recovery,
        "summary": {
            "generated_units": len(generated_recovery),
            "safe_deobfuscation": sum(
                u.get("selected_stage") == "safe_deobfuscation"
                for u in generated_recovery
            ),
            "string_recovery_only": sum(
                u.get("selected_stage") == "string_recovery_only"
                for u in generated_recovery
            ),
            "exact_fallback": sum(
                u.get("selected_stage") == "exact_fallback"
                for u in generated_recovery
            ),
        },
    }
    (project / "analysis/generated-recovery.json").write_text(
        json.dumps(generated_recovery_index, indent=2) + "\n"
    )

    index = {
        "schema": "har-project-jsvm-analysis/v2",
        "scanner": str(args.scanner),
        "formatter": str(args.formatter),
        "switch_ir": str(args.switch_ir),
        "table_ir": str(args.table_ir),
        "deobfuscator": str(args.deobfuscator),
        "string_recoverer": str(args.string_recoverer),
        "recursive_generated_code": True,
        "generated_recovery": "analysis/generated-recovery.json",
        "max_generated_depth": args.max_generated_depth,
        "max_code_units": args.max_code_units,
        "scanner_invocations": scanner_invocations,
        "deduplicated_scans": deduplicated_scans,
        "code_units": rows,
        "dynamic_code_units": dynamic_units,
    }
    (outdir / "index.json").write_text(json.dumps(index, indent=2) + "\n")

    signaled = [r for r in rows if r.get("vm_signal")]
    confirmed = [r for r in rows if r.get("confirmed_vm_signal")]
    handler_candidates = [r for r in rows if r.get("large_handler_table_candidate")]
    failed = [
        r
        for r in rows
        if r.get("scanner_exit")
        or r.get("error")
        or r.get("switch_ir_exit")
        or r.get("table_ir_exit")
    ]
    print(
        f"scanned {len(rows)} JavaScript units recursively; "
        f"{scanner_invocations} scanner invocations / {deduplicated_scans} exact-hash reuses; "
        f"{len(dynamic_units)} static dynamic-code units materialized; "
        f"generated recovery safe={generated_recovery_index['summary']['safe_deobfuscation']} "
        f"string-only={generated_recovery_index['summary']['string_recovery_only']} "
        f"exact-fallback={generated_recovery_index['summary']['exact_fallback']}; "
        f"{len(confirmed)} confirmed VM units; "
        f"{len(handler_candidates)} large handler-table candidate(s); "
        f"{len(signaled) - len(confirmed) - len(handler_candidates)} other candidate(s); "
        f"{len(failed)} scan/IR failures"
    )
    for row in signaled:
        label = (
            "VM"
            if row.get("confirmed_vm_signal")
            else "handler-table candidate"
            if row.get("large_handler_table_candidate")
            else "candidate"
        )
        print(
            f"{label} {row['path']}: confirmed={row.get('confirmed_dispatchers',0)} "
            f"opmaps={row.get('opcode_maps',0)} switches={row.get('direct_switch_maps',0)} "
            f"confirmed_switches={row.get('confirmed_direct_switch_maps',0)} "
            f"handlers={row.get('largest_looped_dynamic_handler_table',0)} "
            f"(raw_non_bundle={row.get('largest_non_bundle_handler_table',0)} "
            f"bundle_tables={row.get('bundle_module_table_handler_tables',0)}) "
            f"transducers={row.get('byte_transducers',0)} table_vms={row.get('table_vms',0)}"
        )


if __name__ == "__main__":
    main()
