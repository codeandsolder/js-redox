#!/usr/bin/env python3
"""Correlate proven WASM host-effect/read pairs with proven JS import writes."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

from analysis_artifacts import DEOBFUSCATION, WASM_HOST_EFFECTS, WASM_INDEX, load_artifact, write_artifact

ROOT = Path(__file__).resolve().parents[1]
TOOL_ROOT = ROOT / ".cargo-target-nodebug/debug"


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def run_probe(
    analyzer: Path,
    source: Path,
    import_module: str,
    import_name: str,
    offset: int,
) -> dict:
    cp = subprocess.run(
        [
            str(analyzer),
            str(source),
            "--import-module",
            import_module,
            "--import-name",
            import_name,
            "--offset",
            str(offset),
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=60,
    )
    if cp.returncode:
        raise RuntimeError(
            f"JS WASM-import analyzer failed ({cp.returncode}) for {source}:\n"
            f"{cp.stdout}{cp.stderr}"
        )
    document = json.loads(cp.stdout)
    if document.get("schema") != "jsvm-wasm-import-semantics/v2":
        raise RuntimeError(
            f"unexpected JS WASM-import analyzer schema for {source}: "
            f"{document.get('schema')!r}"
        )
    writes = document.get("shapes", [])
    usages = document.get("import_object_usages", [])
    if len(writes) > 1:
        raise RuntimeError(
            f"ambiguous JS WASM-import proof for {source}: {import_name}@{offset}"
        )
    return {
        "write": writes[0] if writes else None,
        "import_object_usages": usages,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("project", type=Path)
    ap.add_argument(
        "--analyzer",
        type=Path,
        default=TOOL_ROOT / "wasm-import-semantics",
    )
    args = ap.parse_args()

    project = args.project.resolve()
    wasm_index = load_artifact(project, WASM_INDEX)
    deob = load_artifact(project, DEOBFUSCATION)
    deob_by_raw = {
        unit["raw_path"]: unit["output_path"]
        for unit in deob.get("units", [])
        if unit.get("raw_path") and unit.get("output_path") and unit.get("exit") == 0
    }

    cache: dict[tuple[str, str, str, int], dict] = {}
    rows: list[dict] = []
    skipped_modules: list[dict] = []
    carrier_sources: set[str] = set()

    for module in wasm_index.get("modules", []):
        if module.get("status") != "ok" or not module.get("deep_path"):
            continue
        deep = load(project / module["deep_path"])
        report = load(project / module["report_path"])
        # module.report preserves WASM import-section order; filtering to function
        # imports therefore preserves the WebAssembly function-index prefix used
        # by deep-v5 host_import_function.
        function_imports = [
            imported
            for imported in report.get("imports", [])
            if imported.get("kind") == "function"
        ]
        if deep.get("schema") != "wasm-redox/deep-v5":
            skipped_modules.append(
                {
                    "sha256": module.get("sha256"),
                    "schema": deep.get("schema"),
                    "reason": "host-effect/read proof requires wasm-redox/deep-v5",
                }
            )
            continue

        carrier_candidates = []
        for origin in module.get("origins", []):
            raw = origin.get("source_path")
            output = deob_by_raw.get(raw)
            if output and output not in carrier_candidates:
                carrier_candidates.append(output)

        for export in deep.get("exports", []):
            analysis = export.get("analysis") or {}
            for pair in analysis.get("opaque_host_effect_memory_reads", []):
                host_import = pair.get("host_import")
                host_import_function = pair.get("host_import_function")
                raw_host_import = None
                raw_host_module = None
                if (
                    isinstance(host_import_function, int)
                    and 0 <= host_import_function < len(function_imports)
                ):
                    raw_host_import = function_imports[host_import_function].get("name")
                    raw_host_module = function_imports[host_import_function].get("module")
                offset = pair.get("offset")
                proofs = []
                import_object_usage_proofs = []
                if (
                    isinstance(raw_host_module, str)
                    and isinstance(raw_host_import, str)
                    and isinstance(offset, int)
                ):
                    for relative in carrier_candidates:
                        source = project / relative
                        if not source.is_file():
                            continue
                        carrier_sources.add(relative)
                        key = (relative, raw_host_module, raw_host_import, offset)
                        if key not in cache:
                            cache[key] = run_probe(
                                args.analyzer,
                                source,
                                raw_host_module,
                                raw_host_import,
                                offset,
                            )
                        probe = cache[key]
                        proof = probe["write"]
                        if proof is not None:
                            proofs.append({"source_path": relative, **proof})
                        for usage in probe["import_object_usages"]:
                            import_object_usage_proofs.append(
                                {"source_path": relative, **usage}
                            )

                row = {
                    "module_sha256": module.get("sha256"),
                    "export": export.get("export"),
                    "host_import": host_import,
                    "raw_host_import_module": raw_host_module,
                    "raw_host_import": raw_host_import,
                    "offset": offset,
                    "carrier_candidates": carrier_candidates,
                    "correlation_basis": "exact_import_module_and_name",
                    "js_import_object_instantiation_site_proven": len(import_object_usage_proofs) == 1,
                    "js_import_object_instantiation_site_proofs": import_object_usage_proofs,
                    "import_binding_identity_proven": False,
                    "import_binding_identity_limitation": (
                        "the exact stable JS import object is proven at an unshadowed "
                        "WebAssembly instantiation site when reported, but the instantiated "
                        "module bytes are not yet tied to this recovered WASM module"
                    ),
                    "js_set_u32_shape_proven": len(proofs) == 1,
                    "js_set_u32_shape_proofs": proofs,
                    "wasm_relation": {
                        key: pair.get(key)
                        for key in (
                            "block",
                            "host_effect_value",
                            "host_wrapper_function",
                            "host_import_function",
                            "memory_read_value",
                            "memory_read_helper",
                            "base_value",
                            "runtime_binding",
                        )
                    },
                }
                ambiguities = []
                if len(proofs) > 1:
                    row["js_set_u32_shape_proven"] = False
                    ambiguities.append("multiple carrier sources prove the same import write/offset")
                if len(import_object_usage_proofs) > 1:
                    row["js_import_object_instantiation_site_proven"] = False
                    ambiguities.append(
                        "multiple carrier sources prove import-object WebAssembly instantiation sites"
                    )
                if ambiguities:
                    row["ambiguity"] = "; ".join(ambiguities)
                rows.append(row)

    out = {
        "schema": WASM_HOST_EFFECTS.schema,
        "wasm_schema_required": "wasm-redox/deep-v5",
        "js_schema": "jsvm-wasm-import-semantics/v2",
        "safe_static_only": True,
        "correlation_contract": (
            "exact WASM import module+name match; the same stable JS import object may be "
            "proven as an argument at an unshadowed WebAssembly instantiation site, but "
            "exact recovered-module byte identity at that site is not yet proven"
        ),
        "memory_write_interpretation": "requires standard unmodified DataView builtin semantics",
        "rows": rows,
        "skipped_modules": skipped_modules,
        "summary": {
            "pairs": len(rows),
            "proven_js_set_u32_shapes": sum(row["js_set_u32_shape_proven"] for row in rows),
            "proven_js_import_object_instantiation_sites": sum(
                row["js_import_object_instantiation_site_proven"] for row in rows
            ),
            "opaque_only": sum(not row["js_set_u32_shape_proven"] for row in rows),
            "modules": len({row["module_sha256"] for row in rows}),
            "carrier_sources": len(carrier_sources),
            "probe_invocations": len(cache),
            "skipped_modules": len(skipped_modules),
        },
    }
    output = project / WASM_HOST_EFFECTS.relative_path
    write_artifact(project, WASM_HOST_EFFECTS, out)
    summary = out["summary"]
    print(
        "WASM host effects: "
        f"{summary['proven_js_set_u32_shapes']}/{summary['pairs']} pair(s) have proven JS DataView.setUint32 shapes; "
        f"{summary['proven_js_import_object_instantiation_sites']}/{summary['pairs']} pair(s) have proven JS import-object WebAssembly instantiation sites; "
        f"{summary['opaque_only']} remain opaque; "
        f"{summary['carrier_sources']} carrier source(s)"
    )


if __name__ == "__main__":
    main()
