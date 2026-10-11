#!/usr/bin/env python3
"""Correlate proof-gated WebAssembly/JavaScript boundary semantics."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

from analysis_artifacts import DEOBFUSCATION, WASM_INDEX, WASM_JS_BOUNDARY, load_artifact, write_artifact

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
    if document.get("schema") != "jsvm-wasm-import-semantics/v3":
        raise RuntimeError(
            f"unexpected JS WASM-import analyzer schema for {source}: "
            f"{document.get('schema')!r}"
        )
    writes = document.get("shapes", [])
    handler_semantics = document.get("handler_semantics", [])
    usages = document.get("import_object_usages", [])
    if len(writes) > 1:
        raise RuntimeError(
            f"ambiguous JS WASM-import proof for {source}: {import_name}@{offset}"
        )
    return {
        "write": writes[0] if writes else None,
        "handler_semantics": handler_semantics,
        "import_object_usages": usages,
    }


def run_full_probe(analyzer: Path, source: Path) -> dict:
    cp = subprocess.run(
        [str(analyzer), str(source)],
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
    if document.get("schema") != "jsvm-wasm-import-semantics/v3":
        raise RuntimeError(
            f"unexpected JS WASM-import analyzer schema for {source}: "
            f"{document.get('schema')!r}"
        )
    return document


def matching_handler(document: dict, import_module: str, import_name: str, kind: str) -> list[dict]:
    return [
        handler
        for handler in document.get("handler_semantics", [])
        if handler.get("import_module") == import_module
        and handler.get("import_name") == import_name
        and handler.get("kind") == kind
    ]


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
    full_probe_cache: dict[str, dict] = {}
    host_effect_rows: list[dict] = []
    copied_input_rows: list[dict] = []
    skipped_modules: list[dict] = []
    carrier_sources: set[str] = set()

    for module in wasm_index.get("modules", []):
        if module.get("status") != "ok" or not module.get("deep_path"):
            continue
        deep = load(project / module["deep_path"])
        report = load(project / module["report_path"])
        # module.report preserves WASM import-section order; filtering to function
        # imports therefore preserves the WebAssembly function-index prefix used
        # by deep-v6 host_import_function.
        function_imports = [
            imported
            for imported in report.get("imports", [])
            if imported.get("kind") == "function"
        ]
        if deep.get("schema") != "wasm-redox/deep-v6":
            skipped_modules.append(
                {
                    "sha256": module.get("sha256"),
                    "schema": deep.get("schema"),
                    "reason": "host-effect/read proof requires wasm-redox/deep-v6",
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
                host_effect_rows.append(row)

            for candidate in analysis.get("externref_bulk_copy_candidates", []):
                set_index = candidate.get("set_import_function")
                constructor_index = candidate.get("constructor_import_function")
                set_import = (
                    function_imports[set_index]
                    if isinstance(set_index, int) and 0 <= set_index < len(function_imports)
                    else None
                )
                constructor_import = (
                    function_imports[constructor_index]
                    if isinstance(constructor_index, int)
                    and 0 <= constructor_index < len(function_imports)
                    else None
                )
                set_module = set_import.get("module") if set_import else None
                set_name = set_import.get("name") if set_import else None
                constructor_module = constructor_import.get("module") if constructor_import else None
                constructor_name = constructor_import.get("name") if constructor_import else None

                proofs = []
                if all(isinstance(value, str) for value in (
                    set_module, set_name, constructor_module, constructor_name
                )):
                    for relative in carrier_candidates:
                        source = project / relative
                        if not source.is_file():
                            continue
                        carrier_sources.add(relative)
                        if relative not in full_probe_cache:
                            full_probe_cache[relative] = run_full_probe(args.analyzer, source)
                        document = full_probe_cache[relative]
                        set_matches = matching_handler(document, set_module, set_name, "typed_array_set")
                        constructor_matches = [
                            handler
                            for handler in matching_handler(
                                document, constructor_module, constructor_name, "uint32_array_constructor"
                            )
                            if handler.get("element_width_bits") == 32
                        ]
                        if len(set_matches) == 1 and len(constructor_matches) == 1:
                            proofs.append({
                                "source_path": relative,
                                "set_handler": set_matches[0],
                                "constructor_handler": constructor_matches[0],
                            })

                row = {
                    "module_sha256": module.get("sha256"),
                    "export": export.get("export"),
                    "carrier_candidates": carrier_candidates,
                    "correlation_basis": "exact_import_module_and_name",
                    "raw_set_import_module": set_module,
                    "raw_set_import": set_name,
                    "raw_constructor_import_module": constructor_module,
                    "raw_constructor_import": constructor_name,
                    "wasm_structural_copy_candidate_proven": True,
                    "wasm_candidate": candidate,
                    "js_typed_array_copy_semantics_proven": len(proofs) == 1,
                    "js_typed_array_copy_semantics_proofs": proofs,
                    "module_memory_identity_proven": False,
                    "module_memory_identity_limitation": (
                        "the WASM structural candidate and matching JS Uint32Array constructor/set "
                        "handlers are proven, but the constructor input ArrayBuffer is not yet tied "
                        "to the memory export of this exact recovered module instance"
                    ),
                    "destination_load_interpretation_proven": False,
                }
                if len(proofs) > 1:
                    row["js_typed_array_copy_semantics_proven"] = False
                    row["ambiguity"] = (
                        "multiple carrier sources prove the same constructor/set import semantics"
                    )
                copied_input_rows.append(row)

    out = {
        "schema": WASM_JS_BOUNDARY.schema,
        "wasm_schema_required": "wasm-redox/deep-v6",
        "js_schema": "jsvm-wasm-import-semantics/v3",
        "safe_static_only": True,
        "correlation_contract": (
            "cross-language claims require exact WASM import module+name matches. "
            "Host-effect writes and typed-array input-copy candidates remain independent evidence "
            "families; exact recovered-module instance/memory identity is a separate proof."
        ),
        "memory_write_interpretation": (
            "DataView and typed-array interpretations require standard unmodified platform builtins"
        ),
        "host_effect_rows": host_effect_rows,
        "copied_input_rows": copied_input_rows,
        "skipped_modules": skipped_modules,
        "summary": {
            "host_effect_pairs": len(host_effect_rows),
            "proven_js_set_u32_shapes": sum(row["js_set_u32_shape_proven"] for row in host_effect_rows),
            "proven_js_import_object_instantiation_sites": sum(
                row["js_import_object_instantiation_site_proven"] for row in host_effect_rows
            ),
            "opaque_host_effect_pairs": sum(
                not row["js_set_u32_shape_proven"] for row in host_effect_rows
            ),
            "copied_input_candidates": len(copied_input_rows),
            "proven_js_typed_array_copy_semantics": sum(
                row["js_typed_array_copy_semantics_proven"] for row in copied_input_rows
            ),
            "proven_module_memory_identities": sum(
                row["module_memory_identity_proven"] for row in copied_input_rows
            ),
            "modules": len({
                row["module_sha256"] for row in [*host_effect_rows, *copied_input_rows]
            }),
            "carrier_sources": len(carrier_sources),
            "probe_invocations": len(cache) + len(full_probe_cache),
            "skipped_modules": len(skipped_modules),
        },
    }
    output = project / WASM_JS_BOUNDARY.relative_path
    write_artifact(project, WASM_JS_BOUNDARY, out)
    summary = out["summary"]
    print(
        "WASM/JS boundary: "
        f"{summary['proven_js_set_u32_shapes']}/{summary['host_effect_pairs']} host-effect pair(s) "
        "have proven JS DataView.setUint32 shapes; "
        f"{summary['proven_js_typed_array_copy_semantics']}/"
        f"{summary['copied_input_candidates']} copied-input candidate(s) have proven "
        "JS Uint32Array constructor/set semantics; "
        f"{summary['proven_module_memory_identities']} copied-input candidate(s) have proven "
        "exact module-memory identity"
    )


if __name__ == "__main__":
    main()
