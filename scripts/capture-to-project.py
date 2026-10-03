#!/usr/bin/env python3
import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_HAR_PROJECT = ROOT / ".cargo-target-nodebug/debug/har-project"
DEFAULT_SCANNER = ROOT / ".cargo-target-nodebug/debug/jsvm-lift"
DEFAULT_FORMATTER = ROOT / ".cargo-target-nodebug/debug/js-format"
DEFAULT_SWITCH_IR = ROOT / ".cargo-target-nodebug/debug/switch-ir"
DEFAULT_TABLE_IR = ROOT / ".cargo-target-nodebug/debug/table-ir"
DEFAULT_JS_REFS = ROOT / ".cargo-target-nodebug/debug/js-refs"
DEFAULT_DEOBFUSCATOR = ROOT / ".cargo-target-nodebug/debug/deobfuscate-safe"
DEFAULT_STRING_RECOVERER = ROOT / "scripts/recover-js-obfuscator-strings.py"
DEFAULT_BUNDLE_INVENTORY = ROOT / ".cargo-target-nodebug/debug/bundle-unpack"


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
            f"command failed ({cp.returncode}): {' '.join(map(str, args))}\n"
            f"{cp.stdout}{cp.stderr}"
        )
    if cp.stdout.strip():
        print(cp.stdout.rstrip())


def detect_capture(path: Path) -> str:
    suffix = path.suffix.lower()
    if suffix in {".html", ".htm", ".xhtml"}:
        return "saved_page"
    if suffix == ".har":
        return "har"
    if suffix == ".json":
        # Let the HAR importer perform structural validation; avoid parsing a huge
        # capture twice merely to decide which importer should receive it.
        return "har"
    raise SystemExit(
        f"unsupported capture input: {path}\n"
        "Expected a HAR/JSON HAR or the HTML file from browser Save Page / Webpage, Complete."
    )


def main():
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
    ap.add_argument("--har-project-bin", type=Path, default=DEFAULT_HAR_PROJECT)
    ap.add_argument("--scanner", type=Path, default=DEFAULT_SCANNER)
    ap.add_argument("--formatter", type=Path, default=DEFAULT_FORMATTER)
    ap.add_argument("--switch-ir", type=Path, default=DEFAULT_SWITCH_IR)
    ap.add_argument("--table-ir", type=Path, default=DEFAULT_TABLE_IR)
    ap.add_argument("--js-refs", type=Path, default=DEFAULT_JS_REFS)
    ap.add_argument("--deobfuscator", type=Path, default=DEFAULT_DEOBFUSCATOR)
    ap.add_argument("--string-recoverer", type=Path, default=DEFAULT_STRING_RECOVERER)
    ap.add_argument("--bundle-inventory", type=Path, default=DEFAULT_BUNDLE_INVENTORY)
    ap.add_argument("--skip-safe-deobfuscation", action="store_true")
    ap.add_argument("--skip-bundle-unpack", action="store_true")
    ap.add_argument("--skip-vm-scan", action="store_true")
    args = ap.parse_args()

    capture = args.capture.resolve()
    output = args.output.resolve()
    if not capture.is_file():
        raise SystemExit(f"capture does not exist: {capture}")
    kind = detect_capture(capture)

    if kind == "har":
        importer = [args.har_project_bin, capture, "--output", output]
        if args.overwrite:
            importer.append("--overwrite")
        run(importer)
    else:
        importer = [
            sys.executable,
            ROOT / "scripts/saved-page-to-manifest.py",
            capture,
            "--output",
            output,
        ]
        if args.assets_dir:
            importer.extend(["--assets-dir", args.assets_dir])
        if args.overwrite:
            importer.append("--overwrite")
        run(importer)

    manifest_path = output / "har-manifest.json"
    if not manifest_path.is_file():
        raise SystemExit(f"capture importer did not create {manifest_path}")
    capture_manifest = output / "capture-manifest.json"
    if not capture_manifest.exists():
        shutil.copyfile(manifest_path, capture_manifest)

    run(
        [
            sys.executable,
            ROOT / "scripts/materialize-har-source.py",
            output,
            "--formatter",
            args.formatter,
        ]
    )
    run([sys.executable, ROOT / "scripts/recover-sourcemaps.py", output])
    run(
        [
            sys.executable,
            ROOT / "scripts/scan-js-references.py",
            output,
            "--extractor",
            args.js_refs,
        ]
    )

    if not args.skip_safe_deobfuscation:
        run(
            [
                sys.executable,
                ROOT / "scripts/materialize-safe-deobfuscation.py",
                output,
                "--deobfuscator",
                args.deobfuscator,
                "--string-recoverer",
                args.string_recoverer,
                "--formatter",
                args.formatter,
            ]
        )
        if not args.skip_bundle_unpack:
            run(
                [
                    sys.executable,
                    ROOT / "scripts/materialize-bundle-modules.py",
                    output,
                    "--inventory",
                    args.bundle_inventory,
                    "--formatter",
                    args.formatter,
                ]
            )

    if not args.skip_vm_scan:
        run(
            [
                sys.executable,
                ROOT / "scripts/scan-har-project.py",
                output,
                "--scanner",
                args.scanner,
                "--formatter",
                args.formatter,
                "--switch-ir",
                args.switch_ir,
                "--table-ir",
                args.table_ir,
                "--deobfuscator",
                args.deobfuscator,
                "--string-recoverer",
                args.string_recoverer,
            ]
        )
        run([sys.executable, ROOT / "scripts/materialize-switch-ir.py", output])

    run([sys.executable, ROOT / "scripts/build-source-graph.py", output])
    run([sys.executable, ROOT / "scripts/refresh-project-readme.py", output])

    manifest = json.loads(manifest_path.read_text())
    source_index = json.loads((output / "analysis/source-index.json").read_text())
    maps = json.loads((output / "analysis/sourcemaps.json").read_text())
    graph = json.loads((output / "analysis/source-graph.json").read_text())
    jsrefs = json.loads((output / "analysis/js-references.json").read_text())

    deob = None
    if not args.skip_safe_deobfuscation:
        deob = json.loads((output / "analysis/deobfuscation.json").read_text())

    bundles = {"summary": {}}
    if not args.skip_safe_deobfuscation and not args.skip_bundle_unpack:
        bundle_path = output / "analysis/bundles.json"
        if bundle_path.exists():
            bundles = json.loads(bundle_path.read_text())

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
    generated_recovery = {"summary": {}}
    if not args.skip_vm_scan:
        analysis = json.loads((output / "analysis/jsvm/index.json").read_text())
        generated_recovery_path = output / "analysis/generated-recovery.json"
        if generated_recovery_path.exists():
            generated_recovery = json.loads(generated_recovery_path.read_text())
        dynamic = len(analysis.get("dynamic_code_units", []))
        devirtualized = len(analysis.get("devirtualized_units", []))
        units = analysis.get("code_units", [])
        confirmed_vms = sum(bool(u.get("confirmed_vm_signal")) for u in units)
        vm_candidates = sum(
            bool(u.get("vm_signal")) and not bool(u.get("confirmed_vm_signal"))
            for u in units
        )

    capture_state = "SALVAGED / truncated" if manifest.get("salvaged") else "complete"
    source_kind = manifest.get("source_kind") or "har"
    print(
        "\nProject ready: "
        f"{output}\n"
        f"  input kind:         {source_kind}\n"
        f"  capture state:      {capture_state}\n"
        f"  captured resources: {len(manifest['resources'])}\n"
        f"  JavaScript units:   {js_units}\n"
        f"  literal JS/module/worker references: {jsrefs['summary']['references']}\n"
        f"  import-map resolutions: {jsrefs['summary'].get('resolved_by_import_map', 0)} "
        f"(unresolved bare: {jsrefs['summary'].get('unresolved_bare_specifiers', 0)})\n"
        f"  safe-deobfuscated JS units: {deob['summary']['changed_units'] if deob else 0}\n"
        f"  structured bundle modules: {bundles.get('summary', {}).get('modules', 0)}\n"
        f"  source-map originals: {originals}\n"
        f"  recovered dynamic units: {dynamic}\n"
        f"  generated recovery: safe={generated_recovery.get('summary', {}).get('safe_deobfuscation', 0)} "
        f"string-only={generated_recovery.get('summary', {}).get('string_recovery_only', 0)} "
        f"exact-fallback={generated_recovery.get('summary', {}).get('exact_fallback', 0)}\n"
        f"  readable devirtualized VM modules: {devirtualized}\n"
        f"  confirmed VM units: {confirmed_vms}\n"
        f"  VM candidates:      {vm_candidates}\n"
        f"  source graph:       {graph['summary']['nodes']} nodes / "
        f"{graph['summary']['edges']} edges"
    )


if __name__ == "__main__":
    main()
