#!/usr/bin/env python3
import argparse
import json
from collections import Counter
from pathlib import Path


def load(path: Path, default):
    return json.loads(path.read_text()) if path.exists() else default


def main():
    ap = argparse.ArgumentParser(
        description="Refresh the analyst-facing README for a generated HAR source project"
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
    source_har = manifest.get("source_har") or manifest.get("source") or "HAR capture"

    lines = [
        "# HAR source project",
        "",
        f"Generated from {source_har}. Capture state: **{capture_state}**.",
        "",
        "This tree keeps capture truth separate from analyst transformations. Start in src/ for readable code, and use analysis/source-graph.json when you need exact provenance back to the HAR.",
        "",
        "## Start here",
        "",
        "- [src/](src/) — Oxc-parsed readable source materialized from captured text/code resources.",
        "- [src/_deobfuscated/](src/_deobfuscated/) — conservative static rewrites; captured source is never overwritten.",
        "- [src/_devirtualized/](src/_devirtualized/) — readable modules/pseudocode for confirmed JavaScript VM interpreters.",
        "- [src/_dynamic/](src/_dynamic/) — statically recovered literal generated-code bodies such as Function(...).",
        "- [src/_sourcemap/](src/_sourcemap/) — original sources recovered from captured source maps.",
        "- [resources/](resources/) — capture-faithful response bodies arranged by URL.",
        "- [har-manifest.json](har-manifest.json) — request/response provenance, hashes, headers and capture references.",
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
        "",
        "## Safe static deobfuscation",
        "",
        f"- Changed JavaScript units: **{changed_deob}**",
        f"- Failed units: **{deob_failures}**",
        f"- Encoded string-decoder recovery: **{encoded_string_replacements}** call sites across **{encoded_string_units}** unit(s)",
        f"- Proven arithmetic-state unflattenings: **{arithmetic_state_proofs}**",
        "- Encoded string-table proof/provenance: [analysis/string-recovery.json](analysis/string-recovery.json)",
        "- Detailed final-view hashes, pass counts and provenance: [analysis/deobfuscation.json](analysis/deobfuscation.json)",
        "",
        "## VM analysis",
        "",
        f"- Confirmed VM-bearing JavaScript units: **{len(confirmed)}**",
        f"- Weaker VM candidates: **{len(candidates)}**",
        f"- Materialized devirtualized interpreter modules: **{len(devirtualized)}**",
    ]

    if confirmed:
        lines.extend(["", "Confirmed VM-bearing resources:"])
        for unit in confirmed:
            url = unit.get("url") or unit.get("path") or f"scan {unit.get('scan_id')}"
            count = len(unit.get("devirtualized_units", []))
            lines.append(f"- {url} — {count} devirtualized interpreter module(s)")

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
            "resources/ is capture truth. Everything under src/_deobfuscated/, src/_devirtualized/, src/_dynamic/, and src/_sourcemap/ is a derived analyst view and should be traced through the files in analysis/ before treating it as original captured source.",
            "",
        ]
    )

    out = project / "README.md"
    out.write_text("\n".join(lines))
    print(f"refreshed {out}")


if __name__ == "__main__":
    main()
