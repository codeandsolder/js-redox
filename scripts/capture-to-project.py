#!/usr/bin/env python3
"""CLI front door for capture -> readable/deobfuscated/devirtualized project."""

import argparse
from pathlib import Path

from capture_pipeline import PipelineOptions, Toolchain, print_project_summary, run_capture_pipeline


def main() -> None:
    defaults = Toolchain()
    ap = argparse.ArgumentParser(
        description=(
            "Recover a readable, provenance-preserving JavaScript project from a browser HAR "
            "or a saved HTML/Webpage Complete capture"
        )
    )
    ap.add_argument("capture", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--assets-dir", type=Path, help="saved-page companion resource directory")
    ap.add_argument("--overwrite", action="store_true")
    ap.add_argument("--har-project-bin", type=Path, default=defaults.har_project)
    ap.add_argument("--scanner", type=Path, default=defaults.scanner)
    ap.add_argument("--formatter", type=Path, default=defaults.formatter)
    ap.add_argument("--switch-ir", type=Path, default=defaults.switch_ir)
    ap.add_argument("--table-ir", type=Path, default=defaults.table_ir)
    ap.add_argument("--js-refs", type=Path, default=defaults.js_refs)
    ap.add_argument("--deobfuscator", type=Path, default=defaults.deobfuscator)
    ap.add_argument("--string-recoverer", type=Path, default=defaults.string_recoverer)
    ap.add_argument("--bundle-inventory", type=Path, default=defaults.bundle_inventory)
    ap.add_argument("--sourcemap-composer", type=Path, default=defaults.sourcemap_composer)
    ap.add_argument("--wasm-redox", type=Path, default=defaults.wasm_redox)
    ap.add_argument("--jobs", type=int, help="parallel workers for content-only analysis stages")
    ap.add_argument("--skip-safe-deobfuscation", action="store_true")
    ap.add_argument("--skip-bundle-unpack", action="store_true")
    ap.add_argument("--skip-vm-scan", action="store_true")
    ap.add_argument("--skip-wasm-analysis", action="store_true")
    args = ap.parse_args()

    tools = Toolchain(
        har_project=args.har_project_bin,
        scanner=args.scanner,
        formatter=args.formatter,
        switch_ir=args.switch_ir,
        table_ir=args.table_ir,
        js_refs=args.js_refs,
        deobfuscator=args.deobfuscator,
        string_recoverer=args.string_recoverer,
        bundle_inventory=args.bundle_inventory,
        sourcemap_composer=args.sourcemap_composer,
        wasm_redox=args.wasm_redox,
    )
    options = PipelineOptions(
        overwrite=args.overwrite,
        assets_dir=args.assets_dir,
        jobs=args.jobs,
        safe_deobfuscation=not args.skip_safe_deobfuscation,
        bundle_unpack=not args.skip_bundle_unpack,
        vm_scan=not args.skip_vm_scan,
        wasm_analysis=not args.skip_wasm_analysis,
    )
    summary = run_capture_pipeline(args.capture, args.output, tools=tools, options=options)
    print_project_summary(summary)


if __name__ == "__main__":
    main()
