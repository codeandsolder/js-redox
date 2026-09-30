#!/usr/bin/env python3
import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_HAR_PROJECT = ROOT / ".cargo-target-nodebug/debug/har-project"
DEFAULT_SCANNER = ROOT / ".cargo-target-nodebug/debug/jsvm-lift"
DEFAULT_FORMATTER = ROOT / ".cargo-target-nodebug/debug/js-format"
DEFAULT_SWITCH_IR = ROOT / ".cargo-target-nodebug/debug/switch-ir"
DEFAULT_JS_REFS = ROOT / ".cargo-target-nodebug/debug/js-refs"
DEFAULT_DEOBFUSCATOR = ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe"


def run(args):
    cp = subprocess.run(
        [str(x) for x in args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if cp.returncode:
        raise SystemExit(
            f"command failed ({cp.returncode}): {' '.join(map(str,args))}\n"
            f"{cp.stdout}{cp.stderr}"
        )
    if cp.stdout.strip():
        print(cp.stdout.rstrip())


def main():
    ap = argparse.ArgumentParser(
        description="Build a provenance-preserving readable source project from a browser HAR"
    )
    ap.add_argument("har", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--overwrite", action="store_true")
    ap.add_argument("--har-project-bin", type=Path, default=DEFAULT_HAR_PROJECT)
    ap.add_argument("--scanner", type=Path, default=DEFAULT_SCANNER)
    ap.add_argument("--formatter", type=Path, default=DEFAULT_FORMATTER)
    ap.add_argument("--switch-ir", type=Path, default=DEFAULT_SWITCH_IR)
    ap.add_argument("--js-refs", type=Path, default=DEFAULT_JS_REFS)
    ap.add_argument("--deobfuscator", type=Path, default=DEFAULT_DEOBFUSCATOR)
    ap.add_argument("--skip-safe-deobfuscation", action="store_true")
    ap.add_argument("--skip-vm-scan", action="store_true")
    args = ap.parse_args()

    importer = [args.har_project_bin, args.har, "--output", args.output]
    if args.overwrite:
        importer.append("--overwrite")
    run(importer)

    run(
        [
            sys.executable,
            ROOT / "scripts/materialize-har-source.py",
            args.output,
            "--formatter",
            args.formatter,
        ]
    )
    run([sys.executable, ROOT / "scripts/recover-sourcemaps.py", args.output])
    run(
        [
            sys.executable,
            ROOT / "scripts/scan-js-references.py",
            args.output,
            "--extractor",
            args.js_refs,
        ]
    )
    if not args.skip_safe_deobfuscation:
        run(
            [
                sys.executable,
                ROOT / "scripts/materialize-safe-deobfuscation.py",
                args.output,
                "--deobfuscator",
                args.deobfuscator,
            ]
        )

    if not args.skip_vm_scan:
        run(
            [
                sys.executable,
                ROOT / "scripts/scan-har-project.py",
                args.output,
                "--scanner",
                args.scanner,
                "--formatter",
                args.formatter,
                "--switch-ir",
                args.switch_ir,
            ]
        )
        run([sys.executable, ROOT / "scripts/materialize-switch-ir.py", args.output])

    run([sys.executable, ROOT / "scripts/build-source-graph.py", args.output])
    run([sys.executable, ROOT / "scripts/refresh-project-readme.py", args.output])

    manifest = json.loads((args.output / "har-manifest.json").read_text())
    source_index = json.loads((args.output / "analysis/source-index.json").read_text())
    maps = json.loads((args.output / "analysis/sourcemaps.json").read_text())
    graph = json.loads((args.output / "analysis/source-graph.json").read_text())
    jsrefs = json.loads((args.output / "analysis/js-references.json").read_text())
    deob = None
    if not args.skip_safe_deobfuscation:
        deob = json.loads((args.output / "analysis/deobfuscation.json").read_text())

    js_units = sum(u.get("kind") == "javascript" for u in source_index["units"])
    originals = sum(
        s.get("status") == "recovered"
        for m in maps["source_maps"]
        for s in m.get("recovered", [])
    )
    dynamic = 0
    devirtualized = 0
    confirmed_vms = 0
    vm_candidates = 0
    if not args.skip_vm_scan:
        analysis = json.loads((args.output / "analysis/jsvm/index.json").read_text())
        dynamic = len(analysis.get("dynamic_code_units", []))
        devirtualized = len(analysis.get("devirtualized_units", []))
        units = analysis.get("code_units", [])
        confirmed_vms = sum(bool(u.get("confirmed_vm_signal")) for u in units)
        vm_candidates = sum(
            bool(u.get("vm_signal")) and not bool(u.get("confirmed_vm_signal"))
            for u in units
        )

    capture_state = "SALVAGED / truncated" if manifest.get("salvaged") else "complete"
    print(
        "\nProject ready: "
        f"{args.output}\n"
        f"  capture state:      {capture_state}\n"
        f"  captured resources: {len(manifest['resources'])}\n"
        f"  JavaScript units:   {js_units}\n"
        f"  literal JS references: {jsrefs['summary']['references']}\n"
        f"  safe-deobfuscated JS units: "
        f"{deob['summary']['changed_units'] if deob else 0}\n"
        f"  source-map originals: {originals}\n"
        f"  recovered dynamic units: {dynamic}\n"
        f"  readable devirtualized VM modules: {devirtualized}\n"
        f"  confirmed VM units: {confirmed_vms}\n"
        f"  VM candidates:      {vm_candidates}\n"
        f"  source graph:       {graph['summary']['nodes']} nodes / "
        f"{graph['summary']['edges']} edges"
    )



if __name__ == "__main__":
    main()
