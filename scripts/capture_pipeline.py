#!/usr/bin/env python3
"""Shared orchestration for browser-capture source recovery.

The CLI entry points intentionally stay thin. This module owns the stage order,
tool locations, capture normalization, and final summary so every capture frontend
feeds the same analysis pipeline without duplicating orchestration.
"""

from __future__ import annotations

import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from analysis_artifacts import (
    API_SURFACE,
    BUNDLES,
    DEOBFUSCATION,
    GENERATED_RECOVERY,
    JS_REFERENCES,
    JSVM_INDEX,
    RUNTIME_SCRIPTS,
    SOURCE_GRAPH,
    SOURCE_INDEX,
    SOURCEMAPS,
    WASM_JS_BOUNDARY,
    WASM_INDEX,
    artifact_path,
    load_artifact,
)

from capture_project import MANIFEST_NAME, read_manifest, write_manifest

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
    source_directives: Path = TOOL_ROOT / "source-directives"
    api_surface: Path = TOOL_ROOT / "api-surface"
    deobfuscator: Path = TOOL_ROOT / "deobfuscate-safe"
    string_recoverer: Path = ROOT / "scripts/recover-js-obfuscator-strings.py"
    bundle_inventory: Path = TOOL_ROOT / "bundle-unpack"
    sourcemap_composer: Path = TOOL_ROOT / "sourcemap-compose"
    wasm_redox: Path = TOOL_ROOT / "wasm-redox"
    wasm_import_semantics: Path = TOOL_ROOT / "wasm-import-semantics"


@dataclass(frozen=True)
class PipelineOptions:
    overwrite: bool = False
    assets_dir: Path | None = None
    jobs: int | None = None
    safe_deobfuscation: bool = True
    bundle_unpack: bool = True
    vm_scan: bool = True
    wasm_analysis: bool = True


@dataclass(frozen=True)
class ProjectSummary:
    output: Path
    source_kind: str
    capture_state: str
    captured_resources: int
    javascript_units: int
    wasm_modules: int
    wasm_origins: int
    wasm_host_effect_pairs: int
    wasm_copied_input_candidates: int
    wasm_proven_typed_array_copy_semantics: int
    wasm_proven_host_set_u32_shapes: int
    references: int
    import_map_resolutions: int
    unresolved_bare_specifiers: int
    api_callsites: int
    api_absolute_urls: int
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
    runtime_script_events: int
    runtime_unique_sources: int
    runtime_alpine_expressions: int
    runtime_alpine_families: int
    runtime_gtm_scripts: int
    runtime_gtm_families: int
    runtime_generated_sources: int
    runtime_capture_instrumentation: int
    runtime_anonymous_sources: int
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
    if path.is_dir():
        if (path / "recorder-manifest.json").is_file() and (path / "capture.har").is_file():
            return "recorder"
        raise SystemExit(
            f"unsupported capture directory: {path}\n"
            "Expected a CloakBrowser recorder bundle containing recorder-manifest.json and capture.har."
        )
    suffix = path.suffix.lower()
    if suffix in {".html", ".htm", ".xhtml"}:
        return "saved_page"
    if suffix in {".har", ".json"}:
        # The HAR importer performs structural validation. Avoid parsing very
        # large JSON captures twice merely to select an importer.
        return "har"
    raise SystemExit(
        f"unsupported capture input: {path}\n"
        "Expected a CloakBrowser recorder bundle, HAR/JSON HAR, or the HTML file from browser Save Page / Webpage, Complete."
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
    if kind in {"har", "recorder"}:
        har_input = capture / "capture.har" if kind == "recorder" else capture
        importer: list[object] = [tools.har_project, har_input, "--output", output]
    else:
        importer = [
            sys.executable,
            ROOT / "scripts/saved-page-to-manifest.py",
            capture,
            "--output",
            output,
            "--source-directives",
            tools.source_directives,
        ]
        if options.assets_dir:
            importer.extend(["--assets-dir", options.assets_dir])
    if options.overwrite:
        importer.append("--overwrite")
    run_checked(importer)

    manifest_path = output / MANIFEST_NAME
    if not manifest_path.is_file():
        raise SystemExit(f"capture importer did not create {manifest_path}")
    if kind == "recorder":
        manifest = read_manifest(manifest_path)
        source = manifest["source"]
        source["kind"] = "recorder"
        source["input"] = str(capture)
        source["har_input"] = str(capture / "capture.har")
        write_manifest(manifest_path, manifest)
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
    if not capture.exists():
        raise SystemExit(f"capture does not exist: {capture}")

    kind = detect_capture(capture)
    manifest_path = _import_capture(capture, output, kind, tools, options)
    if kind == "recorder":
        run_checked(
            [
                sys.executable,
                ROOT / "scripts/analyze-runtime-scripts.py",
                capture,
                "--output",
                artifact_path(output, RUNTIME_SCRIPTS),
            ]
        )

    run_checked(
        [
            sys.executable,
            ROOT / "scripts/materialize-capture-source.py",
            output,
            "--formatter",
            tools.formatter,
            *_parallel_args(options.jobs),
        ]
    )
    if options.wasm_analysis:
        run_checked(
            [
                sys.executable,
                ROOT / "scripts/materialize-wasm.py",
                output,
                "--wasm-redox",
                tools.wasm_redox,
            ]
        )

    run_checked(
        [
            sys.executable,
            ROOT / "scripts/recover-sourcemaps.py",
            output,
            "--composer",
            tools.sourcemap_composer,
            "--source-directives",
            tools.source_directives,
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

    if options.wasm_analysis and options.safe_deobfuscation:
        run_checked(
            [
                sys.executable,
                ROOT / "scripts/correlate-wasm-js-boundary.py",
                output,
                "--analyzer",
                tools.wasm_import_semantics,
            ]
        )

    if options.vm_scan:
        run_checked(
            [
                sys.executable,
                ROOT / "scripts/scan-capture-project.py",
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

    run_checked(
        [
            sys.executable,
            ROOT / "scripts/analyze-api-surface.py",
            output,
            "--analyzer",
            tools.api_surface,
        ]
    )
    run_checked([sys.executable, ROOT / "scripts/build-source-graph.py", output])
    run_checked([sys.executable, ROOT / "scripts/refresh-project-readme.py", output])

    return load_project_summary(
        output,
        manifest_path=manifest_path,
        safe_deobfuscation=options.safe_deobfuscation,
        bundle_unpack=options.bundle_unpack,
        vm_scan=options.vm_scan,
        wasm_analysis=options.wasm_analysis,
    )



def load_project_summary(
    output: Path,
    *,
    manifest_path: Path | None = None,
    safe_deobfuscation: bool = True,
    bundle_unpack: bool = True,
    vm_scan: bool = True,
    wasm_analysis: bool = True,
) -> ProjectSummary:
    output = output.resolve()
    manifest = read_manifest(manifest_path or output / MANIFEST_NAME)
    source_index = load_artifact(output, SOURCE_INDEX)
    maps = load_artifact(output, SOURCEMAPS)
    graph = load_artifact(output, SOURCE_GRAPH)
    api_surface = load_artifact(output, API_SURFACE, optional=True) or {"summary": {}}
    jsrefs = load_artifact(output, JS_REFERENCES)
    wasm = (
        load_artifact(output, WASM_INDEX, optional=True) or {"summary": {}}
        if wasm_analysis
        else {"summary": {}}
    )
    wasm_js_boundary = (
        load_artifact(output, WASM_JS_BOUNDARY, optional=True) or {"summary": {}}
        if wasm_analysis and safe_deobfuscation
        else {"summary": {}}
    )
    deob = load_artifact(output, DEOBFUSCATION) if safe_deobfuscation else None
    bundles = (
        load_artifact(output, BUNDLES)
        if safe_deobfuscation and bundle_unpack
        else {"summary": {}}
    )

    dynamic = 0
    devirtualized = 0
    confirmed_vms = 0
    vm_candidates = 0
    generated_recovery = {"summary": {}}
    if vm_scan:
        analysis = load_artifact(output, JSVM_INDEX)
        generated_recovery = load_artifact(output, GENERATED_RECOVERY)
        dynamic = len(analysis.get("dynamic_code_units", []))
        devirtualized = len(analysis.get("devirtualized_units", []))
        units = analysis.get("code_units", [])
        confirmed_vms = sum(bool(unit.get("confirmed_vm_signal")) for unit in units)
        vm_candidates = sum(
            bool(unit.get("vm_signal")) and not bool(unit.get("confirmed_vm_signal"))
            for unit in units
        )

    generated = generated_recovery.get("summary", {})
    runtime = load_artifact(output, RUNTIME_SCRIPTS, optional=True) or {"summary": {}}
    runtime_summary = runtime.get("summary", {})
    runtime_classes = runtime_summary.get("classifications", {})
    originals = sum(
        source.get("status") == "recovered"
        for source_map in maps["source_maps"]
        for source in (
            source_map.get("composed_recovered") or source_map.get("recovered", [])
        )
    )
    return ProjectSummary(
        output=output,
        source_kind=manifest["source"]["kind"],
        capture_state="SALVAGED / truncated" if manifest["source"].get("salvaged") else "complete",
        captured_resources=len(manifest["resources"]),
        javascript_units=sum(unit.get("kind") == "javascript" for unit in source_index["units"]),
        wasm_modules=wasm.get("summary", {}).get("modules", 0),
        wasm_origins=wasm.get("summary", {}).get("origins", 0),
        wasm_host_effect_pairs=wasm_js_boundary.get("summary", {}).get("host_effect_pairs", 0),
        wasm_copied_input_candidates=wasm_js_boundary.get("summary", {}).get(
            "copied_input_candidates", 0
        ),
        wasm_proven_typed_array_copy_semantics=wasm_js_boundary.get("summary", {}).get(
            "proven_js_typed_array_copy_semantics", 0
        ),
        wasm_proven_host_set_u32_shapes=wasm_js_boundary.get("summary", {}).get(
            "proven_js_set_u32_shapes", 0
        ),
        references=jsrefs["summary"]["references"],
        import_map_resolutions=jsrefs["summary"].get("resolved_by_import_map", 0),
        unresolved_bare_specifiers=jsrefs["summary"].get("unresolved_bare_specifiers", 0),
        api_callsites=api_surface.get("summary", {}).get("callsites", 0),
        api_absolute_urls=api_surface.get("summary", {}).get("absolute_network_urls", 0),
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
        runtime_script_events=runtime_summary.get("script_parsed_events", 0),
        runtime_unique_sources=runtime_summary.get("unique_javascript_sources", 0),
        runtime_alpine_expressions=runtime_classes.get("alpine_expression", 0),
        runtime_alpine_families=runtime_summary.get("alpine_expression_shapes", 0),
        runtime_gtm_scripts=runtime_classes.get("gtm_custom_javascript", 0),
        runtime_gtm_families=runtime_summary.get("gtm_expression_shapes", 0),
        runtime_generated_sources=runtime_classes.get("generated_runtime", 0),
        runtime_capture_instrumentation=runtime_classes.get("capture_instrumentation", 0),
        runtime_anonymous_sources=runtime_summary.get("anonymous_runtime_sources", 0),
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
        f"  WebAssembly modules: {summary.wasm_modules} ({summary.wasm_origins} origin(s))\n"
        f"  WASM host-effect DataView.setUint32 shapes: {summary.wasm_proven_host_set_u32_shapes}/{summary.wasm_host_effect_pairs} proven\n"
        f"  WASM copied-input Uint32Array semantics: {summary.wasm_proven_typed_array_copy_semantics}/{summary.wasm_copied_input_candidates} proven\n"
        f"  JS/module/worker references: {summary.references}\n"
        f"  import-map resolutions: {summary.import_map_resolutions} "
        f"(unresolved bare: {summary.unresolved_bare_specifiers})\n"
        f"  static API callsites: {summary.api_callsites} "
        f"({summary.api_absolute_urls} exact absolute URL(s))\n"
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
        + (
            f"  runtime scripts:    {summary.runtime_script_events} events -> "
            f"{summary.runtime_unique_sources} unique; "
            f"Alpine={summary.runtime_alpine_expressions}/{summary.runtime_alpine_families} families, "
            f"GTM={summary.runtime_gtm_scripts}/{summary.runtime_gtm_families} families, "
            f"generated={summary.runtime_generated_sources}, "
            f"instrumentation={summary.runtime_capture_instrumentation}, "
            f"anonymous={summary.runtime_anonymous_sources}\n"
            if summary.runtime_script_events
            else ""
        )
        + f"  source graph:       {summary.graph_nodes} nodes / {summary.graph_edges} edges"
    )
