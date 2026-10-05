#!/usr/bin/env python3
"""Shared orchestration for browser-capture source recovery.

The CLI entry points intentionally stay thin. This module owns the stage order,
tool locations, capture normalization, and final summary so HAR-only compatibility
and the general HAR/saved-page front door cannot silently drift apart.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

ROOT = Path(__file__).resolve().parents[1]
TOOL_ROOT = ROOT / ".cargo-target-nodebug/debug"


@dataclass(frozen=True)
class Toolchain:
    har_project: Path = TOOL_ROOT / "har-project"
    scanner: Path = TOOL_ROOT / "jsvm-lift"
    formatter: Path = TOOL_ROOT / "js-format"
    switch_ir: Path = TOOL_ROOT / "switch-ir"
    table_ir: Path = TOOL_ROOT / "table-ir"
    js_refs: Path = TOOL_ROOT / "js-refs"
    deobfuscator: Path = TOOL_ROOT / "deobfuscate-safe"
    string_recoverer: Path = ROOT / "scripts/recover-js-obfuscator-strings.py"
    bundle_inventory: Path = TOOL_ROOT / "bundle-unpack"
    sourcemap_composer: Path = TOOL_ROOT / "sourcemap-compose"


@dataclass(frozen=True)
class PipelineOptions:
    overwrite: bool = False
    assets_dir: Path | None = None
    jobs: int | None = None
    safe_deobfuscation: bool = True
    bundle_unpack: bool = True
    vm_scan: bool = True


@dataclass(frozen=True)
class ProjectSummary:
    output: Path
    source_kind: str
    capture_state: str
    captured_resources: int
    javascript_units: int
    references: int
    import_map_resolutions: int
    unresolved_bare_specifiers: int
    safe_deobfuscated_units: int
    bundle_modules: int
    sourcemap_originals: int
    dynamic_units: int
    generated_safe: int
    generated_string_only: int
    generated_exact_fallback: int
    generated_unique: int
    generated_reused: int
    devirtualized_modules: int
    confirmed_vm_units: int
    vm_candidates: int
    graph_nodes: int
    graph_edges: int


def run_checked(args: Sequence[object]) -> None:
    argv = [str(x) for x in args]
    cp = subprocess.run(
        argv,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if cp.returncode:
        raise SystemExit(
            f"command failed ({cp.returncode}): {' '.join(argv)}\n{cp.stdout}{cp.stderr}"
        )
    if cp.stdout.strip():
        print(cp.stdout.rstrip())


def detect_capture(path: Path) -> str:
    suffix = path.suffix.lower()
    if suffix in {".html", ".htm", ".xhtml"}:
        return "saved_page"
    if suffix in {".har", ".json"}:
        # The HAR importer performs structural validation. Avoid parsing very
        # large JSON captures twice merely to select an importer.
        return "har"
    raise SystemExit(
        f"unsupported capture input: {path}\n"
        "Expected a HAR/JSON HAR or the HTML file from browser Save Page / Webpage, Complete."
    )


def _parallel_args(jobs: int | None) -> list[str]:
    return ["--jobs", str(jobs)] if jobs else []


def _import_capture(
    capture: Path,
    output: Path,
    kind: str,
    tools: Toolchain,
    options: PipelineOptions,
) -> Path:
    if kind == "har":
        importer: list[object] = [tools.har_project, capture, "--output", output]
    else:
        importer = [
            sys.executable,
            ROOT / "scripts/saved-page-to-manifest.py",
            capture,
            "--output",
            output,
        ]
        if options.assets_dir:
            importer.extend(["--assets-dir", options.assets_dir])
    if options.overwrite:
        importer.append("--overwrite")
    run_checked(importer)

    manifest_path = output / "har-manifest.json"
    if not manifest_path.is_file():
        raise SystemExit(f"capture importer did not create {manifest_path}")
    capture_manifest = output / "capture-manifest.json"
    if not capture_manifest.exists():
        shutil.copyfile(manifest_path, capture_manifest)
    return manifest_path


def run_capture_pipeline(
    capture: Path,
    output: Path,
    *,
    tools: Toolchain | None = None,
    options: PipelineOptions | None = None,
) -> ProjectSummary:
    tools = tools or Toolchain()
    options = options or PipelineOptions()
    capture = capture.resolve()
    output = output.resolve()
    if not capture.is_file():
        raise SystemExit(f"capture does not exist: {capture}")

    kind = detect_capture(capture)
    manifest_path = _import_capture(capture, output, kind, tools, options)

    run_checked(
        [
            sys.executable,
            ROOT / "scripts/materialize-har-source.py",
            output,
            "--formatter",
            tools.formatter,
            *_parallel_args(options.jobs),
        ]
    )
    run_checked(
        [
            sys.executable,
            ROOT / "scripts/recover-sourcemaps.py",
            output,
            "--composer",
            tools.sourcemap_composer,
        ]
    )
    run_checked(
        [
            sys.executable,
            ROOT / "scripts/scan-js-references.py",
            output,
            "--extractor",
            tools.js_refs,
            *_parallel_args(options.jobs),
        ]
    )

    if options.safe_deobfuscation:
        run_checked(
            [
                sys.executable,
                ROOT / "scripts/materialize-safe-deobfuscation.py",
                output,
                "--deobfuscator",
                tools.deobfuscator,
                "--string-recoverer",
                tools.string_recoverer,
                "--formatter",
                tools.formatter,
                *_parallel_args(options.jobs),
            ]
        )
        if options.bundle_unpack:
            run_checked(
                [
                    sys.executable,
                    ROOT / "scripts/materialize-bundle-modules.py",
                    output,
                    "--inventory",
                    tools.bundle_inventory,
                    "--formatter",
                    tools.formatter,
                    *_parallel_args(options.jobs),
                ]
            )

    if options.vm_scan:
        run_checked(
            [
                sys.executable,
                ROOT / "scripts/scan-har-project.py",
                output,
                "--scanner",
                tools.scanner,
                "--formatter",
                tools.formatter,
                "--switch-ir",
                tools.switch_ir,
                "--table-ir",
                tools.table_ir,
                "--deobfuscator",
                tools.deobfuscator,
                "--string-recoverer",
                tools.string_recoverer,
            ]
        )
        run_checked([sys.executable, ROOT / "scripts/materialize-switch-ir.py", output])

    run_checked([sys.executable, ROOT / "scripts/build-source-graph.py", output])
    run_checked([sys.executable, ROOT / "scripts/refresh-project-readme.py", output])

    return load_project_summary(
        output,
        manifest_path=manifest_path,
        safe_deobfuscation=options.safe_deobfuscation,
        bundle_unpack=options.bundle_unpack,
        vm_scan=options.vm_scan,
    )


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def load_project_summary(
    output: Path,
    *,
    manifest_path: Path | None = None,
    safe_deobfuscation: bool = True,
    bundle_unpack: bool = True,
    vm_scan: bool = True,
) -> ProjectSummary:
    output = output.resolve()
    manifest = _read_json(manifest_path or output / "har-manifest.json")
    source_index = _read_json(output / "analysis/source-index.json")
    maps = _read_json(output / "analysis/sourcemaps.json")
    graph = _read_json(output / "analysis/source-graph.json")
    jsrefs = _read_json(output / "analysis/js-references.json")

    deob = _read_json(output / "analysis/deobfuscation.json") if safe_deobfuscation else None
    bundles = {"summary": {}}
    if safe_deobfuscation and bundle_unpack:
        bundle_path = output / "analysis/bundles.json"
        if bundle_path.exists():
            bundles = _read_json(bundle_path)

    dynamic = 0
    devirtualized = 0
    confirmed_vms = 0
    vm_candidates = 0
    generated_recovery = {"summary": {}}
    if vm_scan:
        analysis = _read_json(output / "analysis/jsvm/index.json")
        generated_path = output / "analysis/generated-recovery.json"
        if generated_path.exists():
            generated_recovery = _read_json(generated_path)
        dynamic = len(analysis.get("dynamic_code_units", []))
        devirtualized = len(analysis.get("devirtualized_units", []))
        units = analysis.get("code_units", [])
        confirmed_vms = sum(bool(unit.get("confirmed_vm_signal")) for unit in units)
        vm_candidates = sum(
            bool(unit.get("vm_signal")) and not bool(unit.get("confirmed_vm_signal"))
            for unit in units
        )

    generated = generated_recovery.get("summary", {})
    originals = sum(
        source.get("status") == "recovered"
        for source_map in maps["source_maps"]
        for source in (
            source_map.get("composed_recovered") or source_map.get("recovered", [])
        )
    )
    return ProjectSummary(
        output=output,
        source_kind=manifest.get("source_kind") or "har",
        capture_state="SALVAGED / truncated" if manifest.get("salvaged") else "complete",
        captured_resources=len(manifest["resources"]),
        javascript_units=sum(unit.get("kind") == "javascript" for unit in source_index["units"]),
        references=jsrefs["summary"]["references"],
        import_map_resolutions=jsrefs["summary"].get("resolved_by_import_map", 0),
        unresolved_bare_specifiers=jsrefs["summary"].get("unresolved_bare_specifiers", 0),
        safe_deobfuscated_units=deob["summary"]["changed_units"] if deob else 0,
        bundle_modules=bundles.get("summary", {}).get("modules", 0),
        sourcemap_originals=originals,
        dynamic_units=dynamic,
        generated_safe=generated.get("safe_deobfuscation", 0),
        generated_string_only=generated.get("string_recovery_only", 0),
        generated_exact_fallback=generated.get("exact_fallback", 0),
        generated_unique=generated.get("unique_raw_inputs", generated.get("generated_units", 0)),
        generated_reused=generated.get("deduplicated_units", 0),
        devirtualized_modules=devirtualized,
        confirmed_vm_units=confirmed_vms,
        vm_candidates=vm_candidates,
        graph_nodes=graph["summary"]["nodes"],
        graph_edges=graph["summary"]["edges"],
    )


def print_project_summary(summary: ProjectSummary) -> None:
    print(
        "\nProject ready: "
        f"{summary.output}\n"
        f"  input kind:         {summary.source_kind}\n"
        f"  capture state:      {summary.capture_state}\n"
        f"  captured resources: {summary.captured_resources}\n"
        f"  JavaScript units:   {summary.javascript_units}\n"
        f"  literal JS/module/worker references: {summary.references}\n"
        f"  import-map resolutions: {summary.import_map_resolutions} "
        f"(unresolved bare: {summary.unresolved_bare_specifiers})\n"
        f"  safe-deobfuscated JS units: {summary.safe_deobfuscated_units}\n"
        f"  structured bundle modules: {summary.bundle_modules}\n"
        f"  source-map originals: {summary.sourcemap_originals}\n"
        f"  recovered dynamic units: {summary.dynamic_units}\n"
        f"  generated recovery: safe={summary.generated_safe} "
        f"string-only={summary.generated_string_only} "
        f"exact-fallback={summary.generated_exact_fallback} "
        f"unique={summary.generated_unique} reused={summary.generated_reused}\n"
        f"  readable devirtualized VM modules: {summary.devirtualized_modules}\n"
        f"  confirmed VM units: {summary.confirmed_vm_units}\n"
        f"  VM candidates:      {summary.vm_candidates}\n"
        f"  source graph:       {summary.graph_nodes} nodes / {summary.graph_edges} edges"
    )
