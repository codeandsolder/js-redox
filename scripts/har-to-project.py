#!/usr/bin/env python3
"""Backward-compatible HAR-only wrapper around the shared capture pipeline."""

import argparse
from pathlib import Path

from capture_pipeline import PipelineOptions, Toolchain, print_project_summary, run_capture_pipeline


def main() -> None:
    defaults = Toolchain()
    ap = argparse.ArgumentParser(
        description="Build a provenance-preserving readable source project from a browser HAR"
    )
    ap.add_argument("har", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--overwrite", action="store_true")
    ap.add_argument("--har-project-bin", type=Path, default=defaults.har_project)
    ap.add_argument("--scanner", type=Path, default=defaults.scanner)
    ap.add_argument("--formatter", type=Path, default=defaults.formatter)
    ap.add_argument("--switch-ir", type=Path, default=defaults.switch_ir)
    ap.add_argument("--table-ir", type=Path, default=defaults.table_ir)
    ap.add_argument("--js-refs", type=Path, default=defaults.js_refs)
    ap.add_argument("--deobfuscator", type=Path, default=defaults.deobfuscator)
    ap.add_argument("--string-recoverer", type=Path, default=defaults.string_recoverer)
    ap.add_argument("--jobs", type=int, help="parallel workers for content-only analysis stages")
    ap.add_argument("--skip-safe-deobfuscation", action="store_true")
    ap.add_argument("--skip-vm-scan", action="store_true")
    args = ap.parse_args()

    if args.har.suffix.lower() not in {".har", ".json"}:
        ap.error("har-to-project.py accepts HAR/JSON HAR only; use capture-to-project.py otherwise")

    tools = Toolchain(
        har_project=args.har_project_bin,
        scanner=args.scanner,
        formatter=args.formatter,
        switch_ir=args.switch_ir,
        table_ir=args.table_ir,
        js_refs=args.js_refs,
        deobfuscator=args.deobfuscator,
        string_recoverer=args.string_recoverer,
        bundle_inventory=defaults.bundle_inventory,
    )
    # Keep the historical HAR-only entry point's behavior: it did not extract
    # structured bundle modules. New callers should use capture-to-project.py.
    options = PipelineOptions(
        overwrite=args.overwrite,
        jobs=args.jobs,
        safe_deobfuscation=not args.skip_safe_deobfuscation,
        bundle_unpack=False,
        vm_scan=not args.skip_vm_scan,
    )
    summary = run_capture_pipeline(args.har, args.output, tools=tools, options=options)
    print_project_summary(summary)


if __name__ == "__main__":
    main()
