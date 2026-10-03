#!/usr/bin/env python3
import argparse
import json
from collections import Counter
from pathlib import Path


def load(path: Path, default):
    return json.loads(path.read_text()) if path.exists() else default


def main():
    ap = argparse.ArgumentParser(
        description="Refresh the analyst-facing README for a recovered browser-capture source project"
    )
    ap.add_argument("project", type=Path)
    args = ap.parse_args()
    project = args.project.resolve()

    manifest = load(project / "har-manifest.json", {"resources": [], "inline_scripts": []})
    source_index = load(project / "analysis/source-index.json", {"units": []})
    sourcemaps = load(project / "analysis/sourcemaps.json", {"source_maps": []})
    jsrefs = load(project / "analysis/js-references.json", {"code_units": [], "summary": {}})
    deob = load(project / "analysis/deobfuscation.json", {"units": [], "summary": {}})
    jsvm = load(
        project / "analysis/jsvm/index.json",
        {"code_units": [], "dynamic_code_units": [], "devirtualized_units": []},
    )
    graph = load(project / "analysis/source-graph.json", {"summary": {}})
    bundles = load(project / "analysis/bundles.json", {"bundles": [], "modules": [], "summary": {}})
    generated_recovery = load(
        project / "analysis/generated-recovery.json",
        {"units": [], "summary": {}},
    )

    resources = manifest.get("resources", [])
    source_units = source_index.get("units", [])
    js_units = [u for u in source_units if u.get("kind") == "javascript"]
    source_kinds = Counter(u.get("kind", "unknown") for u in source_units)

    recovered_originals = [
        rec
        for sm in sourcemaps.get("source_maps", [])
        for rec in sm.get("recovered", [])
        if rec.get("status") == "recovered"
    ]

    vm_units = jsvm.get("code_units", [])
    confirmed = [u for u in vm_units if u.get("confirmed_vm_signal")]
    candidates = [
        u for u in vm_units if u.get("vm_signal") and not u.get("confirmed_vm_signal")
    ]
    devirtualized = jsvm.get("devirtualized_units", [])
    dynamic = jsvm.get("dynamic_code_units", [])
    recursive_generated = [
        u for u in vm_units if u.get("origin") == "generated_dynamic_code"
    ]
    large_handler_candidates = [
        u for u in candidates if u.get("large_handler_table_candidate")
    ]
    switch_devirtualized = [
        u for u in devirtualized if u.get("vm_kind") == "direct_switch"
    ]
    table_devirtualized = [
        u for u in devirtualized if u.get("vm_kind") == "function_table"
    ]

    deob_summary = deob.get("summary", {})
    changed_deob = deob_summary.get(
        "changed_units",
        sum(bool(unit.get("changed")) for unit in deob.get("units", [])),
    )
    deob_failures = deob_summary.get(
        "failures",
        sum(bool(unit.get("exit")) for unit in deob.get("units", [])),
    )
    arithmetic_state_proofs = sum(
        len(unit.get("arithmetic_state_proofs", []))
        for unit in deob.get("units", [])
    )
    encoded_string_replacements = deob_summary.get("string_recovery_replacements", 0)
    encoded_string_units = deob_summary.get("string_recovery_changed_units", 0)

    capture_state = "SALVAGED / truncated" if manifest.get("salvaged") else "complete"
    source_capture = manifest.get("source_har") or manifest.get("source") or "browser capture"
    source_kind = manifest.get("source_kind") or "har"
    original_url = manifest.get("original_page_url")
    bundle_summary = bundles.get("summary", {})
    generated_recovery_summary = generated_recovery.get("summary", {})

    lines = [
        "# Recovered source project",
        "",
        f"Generated from {source_capture}. Input kind: **{source_kind}**. Capture state: **{capture_state}**.",
        *([f"Original page URL recorded by the saved page: {original_url}."] if original_url else []),
        "",
        "This tree keeps capture truth separate from analyst transformations. Start in src/ for readable code, and use analysis/source-graph.json when you need exact provenance back to the browser capture.",
        "",
        "## Start here",
        "",
        "- [src/](src/) — Oxc-formatted baseline view of captured text/code resources.",
        "- [src/_deobfuscated/](src/_deobfuscated/) — semantics-preserving static recovery run from the exact captured JS bytes; formatting is intentionally left untouched here.",
        "- [src/_readable/](src/_readable/) — formatted analyst view of the safe-deobfuscated result; use this as the normal human reading tree.",
        "- [src/_devirtualized/](src/_devirtualized/) — readable modules/pseudocode for confirmed JavaScript VM interpreters.",
        "- [src/_dynamic/](src/_dynamic/) — formatted analyst views of statically recovered generated-code bodies such as Function(...).",
        "- [src/_dynamic_deobfuscated/](src/_dynamic_deobfuscated/) — proven safe recovery of generated-code children when string/deob passes validate; exact bytes remain the fallback.",
        "- [src/_sourcemap/](src/_sourcemap/) — original sources recovered from captured source maps.",
        "- [src/_modules/](src/_modules/) — statically extracted Webpack/Next module wrappers where bundle structure is explicit.",
        "- [resources/](resources/) — capture-faithful response bodies or saved-page files.",
        "- [capture-manifest.json](capture-manifest.json) — normalized capture provenance and resource inventory.",
        "- [har-manifest.json](har-manifest.json) — compatibility manifest consumed by the current analysis stages.",
        "- [analysis/source-graph.json](analysis/source-graph.json) — machine-readable relationship/provenance graph.",
        "",
        "## Capture summary",
        "",
        f"- Captured resources: **{len(resources)}**",
        f"- Inline scripts: **{len(manifest.get('inline_scripts', []))}**",
        f"- Readable source units: **{len(source_units)}** ({len(js_units)} JavaScript)",
        f"- Source kinds: {dict(sorted(source_kinds.items()))}",
        f"- Literal JS/module/worker references: **{jsrefs.get('summary', {}).get('references', 0)}**",
        f"- Source-map originals recovered: **{len(recovered_originals)}**",
        f"- Literal generated-code units recovered: **{len(dynamic)}**",
        f"- Generated-code units recursively scanned: **{len(recursive_generated)}**",
        f"- Generated-code safe recovery: **{generated_recovery.get('summary', {}).get('safe_deobfuscation', 0)}** safe deob, "
        f"**{generated_recovery.get('summary', {}).get('string_recovery_only', 0)}** string-only, "
        f"**{generated_recovery.get('summary', {}).get('exact_fallback', 0)}** exact fallback",
        f"- Generated children with full safe deobfuscation: **{generated_recovery_summary.get('safe_deobfuscation', 0)}**",
        f"- Generated children with string-recovery only: **{generated_recovery_summary.get('string_recovery_only', 0)}**",
        f"- Generated children scanned from exact fallback bytes: **{generated_recovery_summary.get('exact_fallback', 0)}**",
        "",
        "## Safe static deobfuscation",
        "",
        f"- Changed JavaScript units: **{changed_deob}**",
        f"- Failed units: **{deob_failures}**",
        f"- Encoded string-decoder recovery: **{encoded_string_replacements}** call sites across **{encoded_string_units}** unit(s)",
        f"- Proven arithmetic-state unflattenings: **{arithmetic_state_proofs}**",
        "- Encoded string-table proof/provenance: [analysis/string-recovery.json](analysis/string-recovery.json)",
        "- Detailed captured-unit final-view hashes, pass counts and provenance: [analysis/deobfuscation.json](analysis/deobfuscation.json)",
        "- Recursive generated-code recovery/fallback provenance: [analysis/generated-recovery.json](analysis/generated-recovery.json)",
        "",
        "## Structured bundle modules",
        "",
        f"- Explicit bundle payloads recovered: **{bundle_summary.get('bundles', 0)}**",
        f"- Readable module wrappers materialized: **{bundle_summary.get('modules', 0)}**",
        f"- Literal intra-bundle/module-loader dependencies recovered: **{bundle_summary.get('literal_module_dependencies', 0)}**",
        f"- Bundle-analysis failures: **{bundle_summary.get('failed_units', 0)}**",
        "- Module inventory/provenance: [analysis/bundles.json](analysis/bundles.json)",
        "",
        "## VM analysis",
        "",
        f"- Confirmed VM-bearing JavaScript units: **{len(confirmed)}**",
        f"- Weaker VM candidates: **{len(candidates)}**",
        f"- Large unlinked handler-table candidates: **{len(large_handler_candidates)}**",
        f"- Materialized devirtualized interpreter modules: **{len(devirtualized)}** "
        f"({len(switch_devirtualized)} direct-switch, {len(table_devirtualized)} function-table)",
    ]

    if confirmed:
        lines.extend(["", "Confirmed VM-bearing resources/code units:"])
        for unit in confirmed:
            label = unit.get("path") or unit.get("url") or f"scan {unit.get('scan_id')}"
            count = len(unit.get("devirtualized_units", []))
            lines.append(f"- {label} — {count} devirtualized interpreter module(s)")

    if large_handler_candidates:
        lines.extend(["", "Large handler-table candidates not yet linked to a supported dispatcher:"])
        for unit in large_handler_candidates:
            label = unit.get("path") or unit.get("url") or f"scan {unit.get('scan_id')}"
            lines.append(
                f"- {label} — largest static function table "
                f"{unit.get('largest_handler_table', 0)} handlers"
            )

    graph_summary = graph.get("summary", {})
    if graph_summary:
        lines.extend(
            [
                "",
                "## Provenance graph",
                "",
                f"- Nodes: **{graph_summary.get('nodes', 0)}**",
                f"- Edges: **{graph_summary.get('edges', 0)}**",
                f"- External uncaptured URLs: **{graph_summary.get('external_urls', 0)}**",
                f"- Edge kinds: {graph_summary.get('edge_kinds', {})}",
            ]
        )

    if manifest.get("salvaged"):
        parse_error = manifest.get("parse_error")
        lines.extend(
            [
                "",
                "## Capture caveat",
                "",
                "The input HAR ended before valid JSON completion. Structurally complete entries before the truncation point were salvaged; absence of later resources is not evidence they were never requested.",
            ]
        )
        if parse_error:
            lines.append(f"- HAR parse error: {parse_error}")

    lines.extend(
        [
            "",
            "## Provenance rule",
            "",
            "resources/ is capture truth. Everything under src/, including _deobfuscated/, _readable/, _dynamic_deobfuscated/, _dynamic/, _devirtualized/, _modules/, and _sourcemap/, is a derived analyst view and should be traced through the files in analysis/ before treating it as original captured source.",
            "",
        ]
    )

    out = project / "README.md"
    out.write_text("\n".join(lines))
    print(f"refreshed {out}")


if __name__ == "__main__":
    main()
