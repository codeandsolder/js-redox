#!/usr/bin/env python3
import argparse
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def recursive_items(report, key):
    out = list(report.get(key, []))
    for child in report.get("embedded", []):
        out.extend(recursive_items(child, key))
    return out


def confirmed_count(report):
    n = sum(bool(f.get("confirmed_dispatch")) for f in report.get("functions", []))
    for child in report.get("embedded", []):
        n += confirmed_count(child)
    return n


def summary(report):
    direct = recursive_items(report, "direct_switch_maps")
    return {
        "confirmed_dispatchers": confirmed_count(report),
        "opcode_maps": len(recursive_items(report, "opcode_maps")),
        "direct_switch_maps": len(direct),
        "confirmed_direct_switch_maps": sum(bool(m.get("confirmed_vm")) for m in direct),
        "handler_tables": len(recursive_items(report, "handler_function_tables")),
        "byte_transducers": len(recursive_items(report, "byte_transducers")),
        "table_vms": len(recursive_items(report, "table_vms")),
        "embedded_code_units": len(recursive_items(report, "embedded")),
    }


def main():
    ap = argparse.ArgumentParser()
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
    args = ap.parse_args()

    project = args.project.resolve()
    manifest = json.loads((project / "har-manifest.json").read_text())
    outdir = project / "analysis" / "jsvm"
    outdir.mkdir(parents=True, exist_ok=True)

    code_units = []
    seen = set()

    for r in manifest.get("resources", []):
        path = r.get("output_path")
        if r.get("kind") == "javascript" and path and path not in seen:
            seen.add(path)
            code_units.append(
                {
                    "origin": "resource",
                    "resource_id": r["id"],
                    "url": r["url"],
                    "path": path,
                }
            )

    for s in manifest.get("inline_scripts", []):
        path = s.get("output_path")
        if path and path.endswith((".js", ".mjs", ".cjs")) and path not in seen:
            seen.add(path)
            parent = manifest["resources"][s["parent_resource_id"]]
            code_units.append(
                {
                    "origin": "inline_script",
                    "resource_id": s["parent_resource_id"],
                    "url": parent["url"],
                    "ordinal": s["ordinal"],
                    "path": path,
                }
            )

    def embedded_nodes(report):
        out = []
        def walk(nodes, depth=1):
            for node in nodes:
                out.append((depth, node))
                walk(node.get("embedded", []), depth + 1)
        walk(report.get("embedded", []))
        return out

    rows = []
    dynamic_units = []
    for i, unit in enumerate(code_units):
        source = project / unit["path"]
        dump_dir = outdir / "embedded" / f"{i:04}"
        cp = subprocess.run(
            [
                str(args.scanner),
                "--json",
                "--dump-embedded",
                str(dump_dir),
                str(source),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=120,
        )
        row = dict(unit)
        row["scan_id"] = i
        row["bytes"] = source.stat().st_size
        row["scanner_exit"] = cp.returncode
        if cp.returncode:
            row["error"] = cp.stderr[-2000:]
            rows.append(row)
            continue
        lines = [line for line in cp.stdout.splitlines() if line.strip()]
        if len(lines) != 1:
            row["error"] = f"expected one JSON report, got {len(lines)}"
            rows.append(row)
            continue

        report = json.loads(lines[0])
        report_path = outdir / f"{i:04}.json"
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        row["report"] = str(report_path.relative_to(project))

        embedded = []
        for ordinal, (depth, node) in enumerate(embedded_nodes(report), 1):
            dumped = node.get("dump_path")
            if not dumped:
                continue
            raw = Path(dumped)
            readable = project / "src" / "_dynamic" / f"{i:04}" / f"embedded-{ordinal:03}.js"
            readable.parent.mkdir(parents=True, exist_ok=True)
            fp = subprocess.run(
                [str(args.formatter), str(raw), str(readable)],
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=120,
            )
            if fp.returncode:
                readable.write_bytes(raw.read_bytes())
            item = {
                "parent_scan_id": i,
                "ordinal": ordinal,
                "depth": depth,
                "kind": node.get("kind"),
                "outer_start": node.get("outer_start"),
                "outer_end": node.get("outer_end"),
                "body_bytes": node.get("body_bytes"),
                "raw_dump": str(raw.relative_to(project)),
                "source_path": str(readable.relative_to(project)),
                "formatted": fp.returncode == 0,
                "handler_tables": len(node.get("handler_function_tables", [])),
                "table_vms": len(node.get("table_vms", [])),
                "opcode_maps": len(node.get("opcode_maps", [])),
            }
            embedded.append(item)
            dynamic_units.append(item)
        row["embedded_units"] = embedded
        row.update(summary(report))

        if row["confirmed_direct_switch_maps"]:
            switch_ir_path = outdir / f"{i:04}.switch-ir.json"
            sp = subprocess.run(
                [
                    str(args.switch_ir),
                    str(source),
                    str(report_path),
                    "--output",
                    str(switch_ir_path),
                ],
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=180,
            )
            row["switch_ir_exit"] = sp.returncode
            if sp.returncode:
                row["switch_ir_error"] = (sp.stdout + sp.stderr)[-3000:]
            else:
                row["switch_ir"] = str(switch_ir_path.relative_to(project))

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
        row["vm_signal"] = row["confirmed_vm_signal"] or row["direct_switch_maps"] > 0
        rows.append(row)

    index = {
        "schema": "har-project-jsvm-analysis/v0",
        "scanner": str(args.scanner),
        "formatter": str(args.formatter),
        "switch_ir": str(args.switch_ir),
        "code_units": rows,
        "dynamic_code_units": dynamic_units,
    }
    (outdir / "index.json").write_text(json.dumps(index, indent=2) + "\n")

    signaled = [r for r in rows if r.get("vm_signal")]
    confirmed = [r for r in rows if r.get("confirmed_vm_signal")]
    failed = [
        r
        for r in rows
        if r.get("scanner_exit")
        or r.get("error")
        or r.get("switch_ir_exit")
    ]
    print(
        f"scanned {len(rows)} JavaScript units; "
        f"{len(dynamic_units)} static dynamic-code units materialized; "
        f"{len(confirmed)} confirmed VM units; {len(signaled) - len(confirmed)} candidates; "
        f"{len(failed)} scan failures"
    )
    for r in signaled:
        label = "VM" if r.get("confirmed_vm_signal") else "candidate"
        print(
            f"{label} {r['path']}: confirmed={r.get('confirmed_dispatchers',0)} "
            f"opmaps={r.get('opcode_maps',0)} switches={r.get('direct_switch_maps',0)} "
            f"confirmed_switches={r.get('confirmed_direct_switch_maps',0)} "
            f"transducers={r.get('byte_transducers',0)} table_vms={r.get('table_vms',0)}"
        )


if __name__ == "__main__":
    main()
