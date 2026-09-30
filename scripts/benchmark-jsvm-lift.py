#!/usr/bin/env python3
import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def find_binary(explicit: str | None) -> Path:
    if explicit:
        p = Path(explicit)
        if p.is_file():
            return p
        raise SystemExit(f"binary not found: {p}")
    candidates: list[Path] = []
    for local in (
        ROOT / ".cargo-target-nodebug/debug/jsvm-lift",
        ROOT / ".cargo-target/debug/jsvm-lift",
        ROOT / "src/jsvm-lift/target/debug/jsvm-lift",
    ):
        if local.is_file():
            candidates.append(local)

    for target_root in (
        ROOT / ".cargo-target-nodebug",
        Path("/var/cache/sentinelx/cargo-target"),
    ):
        if target_root.is_dir():
            candidates.extend(
                p for p in target_root.glob("*/debug/jsvm-lift") if p.is_file()
            )

    if candidates:
        # Cargo site shims may redirect a requested target directory. Never
        # let an older canonical-looking binary shadow the actually newest one.
        return max(candidates, key=lambda p: p.stat().st_mtime)
    raise SystemExit("jsvm-lift binary not found; run scripts/build-jsvm-lift.sh")

def confirmed_count(report: dict) -> int:
    total = sum(bool(f.get("confirmed_dispatch")) for f in report.get("functions", []))
    def walk(e: dict) -> int:
        n = sum(bool(f.get("confirmed_dispatch")) for f in e.get("functions", []))
        for child in e.get("embedded", []):
            n += walk(child)
        return n
    for e in report.get("embedded", []):
        total += walk(e)
    return total

def recursive_items(report: dict, key: str) -> list[dict]:
    out = list(report.get(key, []))
    for child in report.get("embedded", []):
        out.extend(recursive_items(child, key))
    return out

def run_stdout(path: Path) -> str:
    cp = subprocess.run(
        ["node", str(path)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )
    if cp.returncode:
        raise RuntimeError(f"{path}: node exit {cp.returncode}: {cp.stderr[-500:]}")
    return cp.stdout.strip()

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", default="corpus/manifest.json")
    ap.add_argument("--binary")
    ap.add_argument("--skip-runtime", action="store_true")
    args = ap.parse_args()

    manifest = json.loads((ROOT / args.manifest).read_text())
    entries = [
        ("positive", x) for x in manifest["positive"]
    ] + [
        ("negative", x) for x in manifest["negative"]
    ]
    binary = find_binary(args.binary)

    reports = []
    for cls, entry in entries:
        path = ROOT / entry["path"]
        try:
            cp = subprocess.run(
                [str(binary), "--json", str(path)],
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=120,
            )
        except subprocess.TimeoutExpired:
            raise RuntimeError(f"{entry['family']}: scan timed out after 120s: {path}")
        if cp.returncode:
            raise RuntimeError(
                f"{entry['family']}: scanner exit {cp.returncode}: {cp.stderr[-1000:]}"
            )
        lines=[line for line in cp.stdout.splitlines() if line.strip()]
        if len(lines) != 1:
            raise RuntimeError(
                f"{entry['family']}: expected 1 report, got {len(lines)}"
            )
        reports.append(json.loads(lines[0]))

    failures = []
    print(f"binary: {binary}")
    print(f"{'class':9} {'family':27} {'confirmed':>9}  {'linked':>10}  {'opmaps':>7}  result")
    print("-" * 88)
    for (cls, entry), report in zip(entries, reports):
        n = confirmed_count(report)
        decoders = report.get("decoder_candidates", [])
        linked = [d for d in decoders if d.get("builder_var")]
        opcode_maps = recursive_items(report, "opcode_maps")
        direct_switch_maps = recursive_items(report, "direct_switch_maps")
        handler_tables = recursive_items(report, "handler_function_tables")
        byte_transducers = recursive_items(report, "byte_transducers")
        table_vms = recursive_items(report, "table_vms")
        embedded_units = recursive_items(report, "embedded")
        if_ladder_state_machines = recursive_items(report, "if_ladder_state_machines")
        result = "observe"
        lo = entry.get("expect_confirmed_min")
        hi = entry.get("expect_confirmed_max")
        if lo is not None:
            result = "PASS" if n >= lo else "FAIL"
            if n < lo:
                failures.append(f"{entry['family']}: confirmed {n} < {lo}")
        if hi is not None:
            ok = n <= hi
            result = "PASS" if ok else "FAIL"
            if not ok:
                failures.append(f"{entry['family']}: confirmed {n} > {hi}")

        dmin = entry.get("expect_linked_decoder_min")
        dmax = entry.get("expect_linked_decoder_max")
        if result == "observe" and any(
            entry.get(k) is not None
            for k in (
                "expect_linked_decoder_min",
                "expect_linked_decoder_max",
                "expect_decoder_width",
                "expect_full_width_layout_min",
            )
        ):
            result = "PASS"
        if dmin is not None and len(linked) < dmin:
            result = "FAIL"
            failures.append(f"{entry['family']}: linked decoders {len(linked)} < {dmin}")
        if dmax is not None and len(linked) > dmax:
            result = "FAIL"
            failures.append(f"{entry['family']}: linked decoders {len(linked)} > {dmax}")

        width = entry.get("expect_decoder_width")
        if width is not None:
            wrong = [d['width'] for d in linked if d.get('width') != width]
            if not linked or wrong:
                result = "FAIL"
                failures.append(
                    f"{entry['family']}: decoder widths "
                    f"{sorted({d.get('width') for d in linked})} != {{{width}}}"
                )

        full_min = entry.get("expect_full_width_layout_min")
        if full_min is not None:
            full = sum(
                d.get("operand_offsets") == list(range(d.get("width", 0)))
                for d in linked
            )
            if full < full_min:
                result = "FAIL"
                failures.append(f"{entry['family']}: full-width layouts {full} < {full_min}")

        omin = entry.get("expect_opcode_map_min")
        omax = entry.get("expect_opcode_map_max")
        if result == "observe" and (omin is not None or omax is not None):
            result = "PASS"
        if omin is not None and len(opcode_maps) < omin:
            result = "FAIL"
            failures.append(f"{entry['family']}: opcode maps {len(opcode_maps)} < {omin}")
        if omax is not None and len(opcode_maps) > omax:
            result = "FAIL"
            failures.append(f"{entry['family']}: opcode maps {len(opcode_maps)} > {omax}")

        expected_opmax = entry.get("expect_opcode_max")
        if expected_opmax is not None:
            actual = sorted({m.get("opcode_max") for m in opcode_maps})
            if expected_opmax not in actual:
                result = "FAIL"
                failures.append(
                    f"{entry['family']}: opcode_max values {actual} do not contain {expected_opmax}"
                )

        expected_bindings = entry.get("expect_selector_masks")
        if expected_bindings is not None:
            want = sorted(int(x) for x in expected_bindings)
            got = [
                sorted(int(v) for v in m.get("selector_bindings", {}).values())
                for m in opcode_maps
            ]
            if want not in got:
                result = "FAIL"
                failures.append(
                    f"{entry['family']}: selector mask sets {got} do not contain {want}"
                )

        expected_observed = entry.get("expect_observed_opcodes")
        if expected_observed is not None:
            want = sorted(int(x) for x in expected_observed)
            got = [
                sorted(int(v) for v in m.get("observed_opcodes", []))
                for m in opcode_maps
            ]
            if want not in got:
                result = "FAIL"
                failures.append(
                    f"{entry['family']}: observed opcode sets {got} do not contain {want}"
                )

        switch_min = entry.get("expect_direct_switch_map_min")
        switch_max = entry.get("expect_direct_switch_map_max")
        confirmed_switches = [
            m for m in direct_switch_maps if m.get("confirmed_vm")
        ]
        confirmed_switch_min = entry.get("expect_confirmed_direct_switch_map_min")
        confirmed_switch_max = entry.get("expect_confirmed_direct_switch_map_max")
        if switch_min is not None and len(direct_switch_maps) < switch_min:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: direct switch maps {len(direct_switch_maps)} < {switch_min}"
            )
        if switch_max is not None and len(direct_switch_maps) > switch_max:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: direct switch maps {len(direct_switch_maps)} > {switch_max}"
            )
        if confirmed_switch_min is not None and len(confirmed_switches) < confirmed_switch_min:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: confirmed direct switch maps "
                f"{len(confirmed_switches)} < {confirmed_switch_min}"
            )
        if confirmed_switch_max is not None and len(confirmed_switches) > confirmed_switch_max:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: confirmed direct switch maps "
                f"{len(confirmed_switches)} > {confirmed_switch_max}"
            )

        handler_min = entry.get("expect_handler_function_table_min")
        if result == "observe" and any(
            value is not None
            for value in (
                switch_min,
                switch_max,
                confirmed_switch_min,
                confirmed_switch_max,
                handler_min,
                entry.get("expect_byte_transducer_min"),
                entry.get("expect_byte_transducer_max"),
                entry.get("expect_table_vm_min"),
                entry.get("expect_table_vm_max"),
                entry.get("expect_table_vm_architecture"),
                entry.get("expect_embedded_min"),
                entry.get("expect_embedded_max"),
                entry.get("expect_if_ladder_state_machine_min"),
                entry.get("expect_if_ladder_state_machine_max"),
            )
        ):
            result = "PASS"
        if handler_min is not None:
            biggest = max((int(t.get("function_values", 0)) for t in handler_tables), default=0)
            if biggest < handler_min:
                result = "FAIL"
                failures.append(
                    f"{entry['family']}: biggest handler table {biggest} < {handler_min}"
                )

        transducer_min = entry.get("expect_byte_transducer_min")
        transducer_max = entry.get("expect_byte_transducer_max")
        if transducer_min is not None and len(byte_transducers) < transducer_min:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: byte transducers {len(byte_transducers)} < {transducer_min}"
            )
        if transducer_max is not None and len(byte_transducers) > transducer_max:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: byte transducers {len(byte_transducers)} > {transducer_max}"
            )

        table_vm_min = entry.get("expect_table_vm_min")
        table_vm_max = entry.get("expect_table_vm_max")
        if table_vm_min is not None and len(table_vms) < table_vm_min:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: table VMs {len(table_vms)} < {table_vm_min}"
            )
        if table_vm_max is not None and len(table_vms) > table_vm_max:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: table VMs {len(table_vms)} > {table_vm_max}"
            )

        arch = entry.get("expect_table_vm_architecture")
        if arch is not None:
            architectures = {str(v.get("architecture")) for v in table_vms}
            if arch not in architectures:
                result = "FAIL"
                failures.append(
                    f"{entry['family']}: table VM architectures {sorted(architectures)} "
                    f"do not contain {arch!r}"
                )

        embedded_min = entry.get("expect_embedded_min")
        embedded_max = entry.get("expect_embedded_max")
        if embedded_min is not None and len(embedded_units) < embedded_min:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: embedded units {len(embedded_units)} < {embedded_min}"
            )
        if embedded_max is not None and len(embedded_units) > embedded_max:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: embedded units {len(embedded_units)} > {embedded_max}"
            )

        if_ladder_min = entry.get("expect_if_ladder_state_machine_min")
        if_ladder_max = entry.get("expect_if_ladder_state_machine_max")
        if if_ladder_min is not None and len(if_ladder_state_machines) < if_ladder_min:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: if-ladder state machines "
                f"{len(if_ladder_state_machines)} < {if_ladder_min}"
            )
        if if_ladder_max is not None and len(if_ladder_state_machines) > if_ladder_max:
            result = "FAIL"
            failures.append(
                f"{entry['family']}: if-ladder state machines "
                f"{len(if_ladder_state_machines)} > {if_ladder_max}"
            )

        if entry.get("expect_observed_no_stuck"):
            live_handlers = [
                h
                for m in opcode_maps
                for h in m.get("handlers", [])
                if h.get("observed")
            ]
            stuck = [int(h.get("opcode", -1)) for h in live_handlers if h.get("terminal") == "stuck"]
            if not live_handlers or stuck:
                result = "FAIL"
                failures.append(
                    f"{entry['family']}: observed handlers missing or stuck: {stuck}"
                )

        print(
            f"{cls:9} {entry['family'][:27]:27} {n:9d}  "
            f"linked={len(linked):3d}  maps={len(opcode_maps):3d}  "
            f"sw={len(direct_switch_maps):2d}/{len(confirmed_switches):2d} "
            f"trans={len(byte_transducers):2d} "
            f"tvm={len(table_vms):2d} emb={len(embedded_units):2d} "
            f"ifl={len(if_ladder_state_machines):2d}  {result}"
        )

        if not args.skip_runtime and entry.get("expected_stdout") is not None:
            expected = str(entry["expected_stdout"])
            for key in ("source", "execution_path"):
                if key not in entry:
                    continue
                got = run_stdout(ROOT / entry[key])
                if got != expected:
                    failures.append(
                        f"{entry['family']} {key}: stdout {got!r} != {expected!r}"
                    )

    if failures:
        print("\nFAILURES:")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("\nAll asserted structural/runtime checks passed.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
