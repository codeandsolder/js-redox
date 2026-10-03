#!/usr/bin/env python3
import argparse
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


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


def main():
    ap = argparse.ArgumentParser(
        description="Recursively scan recovered JavaScript code units for generated code and VM structures"
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

    code_units = []
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
        if not raw_path or not raw_path.endswith((".js", ".mjs", ".cjs")):
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
        row["bytes"] = source.stat().st_size
        row["scanner_exit"] = cp.returncode
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
        report_path = outdir / f"{scan_id:04}.json"
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        row["report"] = str(report_path.relative_to(project))
        row.update(direct_summary(report))

        embedded = []
        parent_depth = int(unit.get("generated_depth", 0))
        for ordinal, node in enumerate(report.get("embedded", []), 1):
            dumped = node.get("dump_path")
            if not dumped:
                continue
            raw = Path(dumped)
            raw_rel = str(raw.relative_to(project))
            readable = (
                project
                / "src"
                / "_dynamic"
                / f"{scan_id:04}"
                / f"embedded-{ordinal:03}.js"
            )
            readable.parent.mkdir(parents=True, exist_ok=True)
            fp = run_tool([args.formatter, raw, readable], timeout=120)
            if fp.returncode:
                readable.write_bytes(raw.read_bytes())

            depth = parent_depth + 1
            item = {
                "parent_scan_id": scan_id,
                "ordinal": ordinal,
                "depth": depth,
                "kind": node.get("kind"),
                "outer_start": node.get("outer_start"),
                "outer_end": node.get("outer_end"),
                "body_bytes": node.get("body_bytes"),
                "raw_dump": raw_rel,
                "source_path": str(readable.relative_to(project)),
                "formatted": fp.returncode == 0,
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
                        "path": raw_rel,
                        "readable_path": str(readable.relative_to(project)),
                        "analysis_origin": "generated_code_exact",
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
            and row["largest_handler_table"] >= 32
        )
        row["vm_signal"] = (
            row["confirmed_vm_signal"]
            or row["direct_switch_maps"] > 0
            or row["large_handler_table_candidate"]
        )
        rows.append(row)
        scan_id += 1

    index = {
        "schema": "har-project-jsvm-analysis/v1",
        "scanner": str(args.scanner),
        "formatter": str(args.formatter),
        "switch_ir": str(args.switch_ir),
        "table_ir": str(args.table_ir),
        "recursive_generated_code": True,
        "max_generated_depth": args.max_generated_depth,
        "max_code_units": args.max_code_units,
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
        f"{len(dynamic_units)} static dynamic-code units materialized; "
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
            f"handlers={row.get('largest_handler_table',0)} "
            f"transducers={row.get('byte_transducers',0)} table_vms={row.get('table_vms',0)}"
        )


if __name__ == "__main__":
    main()
