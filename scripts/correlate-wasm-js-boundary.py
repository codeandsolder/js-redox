#!/usr/bin/env python3
"""Correlate proof-gated WebAssembly/JavaScript boundary semantics."""

from __future__ import annotations

import argparse
import hashlib
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
    if document.get("schema") != "jsvm-wasm-import-semantics/v7":
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
    if document.get("schema") != "jsvm-wasm-import-semantics/v7":
        raise RuntimeError(
            f"unexpected JS WASM-import analyzer schema for {source}: "
            f"{document.get('schema')!r}"
        )
    return document


def run_fresh_eval(
    evaluator: Path,
    binary: Path,
    function_index: int,
    i32_args: list[int],
) -> dict:
    cp = subprocess.run(
        [
            str(evaluator),
            str(binary),
            "--function-index",
            str(function_index),
            *sum((["--i32-arg", str(value)] for value in i32_args), []),
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=60,
    )
    if cp.returncode:
        raise RuntimeError(
            f"fresh WASM evaluator failed ({cp.returncode}) for {binary}:\n"
            f"{cp.stdout}{cp.stderr}"
        )
    document = json.loads(cp.stdout)
    if document.get("schema") != "wasm-redox/fresh-i32-call-v1":
        raise RuntimeError(
            f"unexpected fresh evaluator schema for {binary}: {document.get('schema')!r}"
        )
    return document


def exact_module_usage_proofs(usages: list[dict], module_sha256: str | None) -> list[dict]:
    if not isinstance(module_sha256, str):
        return []
    proofs = []
    for usage in usages:
        exact_sites = [
            site
            for site in usage.get("instantiation_sites", [])
            if site.get("exact_import_object_identity_proven") is True
            and site.get("exact_module_identity_proven") is True
            and site.get("module_sha256") == module_sha256
        ]
        if exact_sites:
            proofs.append({**usage, "instantiation_sites": exact_sites})
    return proofs


def common_exact_binding_proofs(
    left_usages: list[dict], right_usages: list[dict], module_sha256: str | None
) -> list[dict]:
    left = exact_module_usage_proofs(left_usages, module_sha256)
    right = exact_module_usage_proofs(right_usages, module_sha256)
    proofs = []
    for lhs in left:
        for rhs in right:
            if lhs.get("import_object") != rhs.get("import_object"):
                continue
            right_sites = {
                (site.get("start"), site.get("end"), site.get("module_sha256"))
                for site in rhs.get("instantiation_sites", [])
            }
            common_sites = [
                site
                for site in lhs.get("instantiation_sites", [])
                if (site.get("start"), site.get("end"), site.get("module_sha256"))
                in right_sites
            ]
            if common_sites:
                proofs.append(
                    {
                        "import_object": lhs.get("import_object"),
                        "left_import_module": lhs.get("import_module"),
                        "left_import_name": lhs.get("import_name"),
                        "right_import_module": rhs.get("import_module"),
                        "right_import_name": rhs.get("import_name"),
                        "instantiation_sites": common_sites,
                    }
                )
    return proofs


def matching_handler(document: dict, import_module: str, import_name: str, kind: str) -> list[dict]:
    return [
        handler
        for handler in document.get("handler_semantics", [])
        if handler.get("import_module") == import_module
        and handler.get("import_name") == import_name
        and handler.get("kind") == kind
    ]


def exact_usage_matches_binding(usage: dict, binding_proofs: list[dict]) -> bool:
    usage_sites = {
        (site.get("start"), site.get("end"), site.get("module_sha256"))
        for site in usage.get("instantiation_sites", [])
    }
    return any(
        usage.get("import_object") == binding.get("import_object")
        and any(
            (site.get("start"), site.get("end"), site.get("module_sha256")) in usage_sites
            for site in binding.get("instantiation_sites", [])
        )
        for binding in binding_proofs
    )


def source_length_barrier_proofs(
    document: dict,
    function_imports: list[dict],
    candidate: dict,
    module_sha256: str | None,
    binding_proofs: list[dict],
) -> list[dict]:
    barrier_indices = sorted({
        index
        for load in candidate.get("destination_loads", [])
        for index in load.get("source_length_import_barriers", [])
        if isinstance(index, int) and not isinstance(index, bool)
    })
    proofs = []
    for index in barrier_indices:
        if not (0 <= index < len(function_imports)):
            return []
        imported = function_imports[index]
        import_module = imported.get("module")
        import_name = imported.get("name")
        if not isinstance(import_module, str) or not isinstance(import_name, str):
            return []
        handlers = [
            handler
            for handler in matching_handler(
                document, import_module, import_name, "property_getter"
            )
            if handler.get("property") == "length"
            and handler.get("standard_builtin_semantics_required") is True
        ]
        if len(handlers) != 1:
            return []
        handler = handlers[0]
        usages = [
            usage
            for usage in document.get("import_object_usages", [])
            if usage.get("import_module") == import_module
            and usage.get("import_name") == import_name
            and usage.get("assignment_start") == handler.get("assignment_start")
            and usage.get("assignment_end") == handler.get("assignment_end")
        ]
        exact = exact_module_usage_proofs(usages, module_sha256)
        exact = [usage for usage in exact if exact_usage_matches_binding(usage, binding_proofs)]
        if len(exact) != 1:
            return []
        proofs.append({
            "function_import": index,
            "import_module": import_module,
            "import_name": import_name,
            "handler": handler,
            "binding": exact[0],
        })
    return proofs


def fixed_uint32_source_lengths(
    memory_proofs: list[dict], export_name: str | None, source_parameter: object
) -> list[int] | None:
    if (
        not isinstance(export_name, str)
        or not isinstance(source_parameter, int)
        or isinstance(source_parameter, bool)
    ):
        return None
    lengths: list[int] = []
    for proof in memory_proofs:
        matching_calls = [
            call for call in proof.get("export_calls", [])
            if call.get("export_name") == export_name
        ]
        if not matching_calls:
            return None
        for call in matching_calls:
            argument_lengths = call.get("static_uint32_array_argument_lengths")
            if not isinstance(argument_lengths, list) or source_parameter >= len(argument_lengths):
                return None
            length = argument_lengths[source_parameter]
            if not isinstance(length, int) or isinstance(length, bool) or length < 0:
                return None
            lengths.append(length)
    return lengths or None


def fixed_uint32_source_length_lower_bound(
    memory_proofs: list[dict], export_name: str | None, source_parameter: object
) -> int | None:
    lengths = fixed_uint32_source_lengths(memory_proofs, export_name, source_parameter)
    return min(lengths) if lengths else None


def fixed_uint32_source_length_exact(
    memory_proofs: list[dict], export_name: str | None, source_parameter: object
) -> int | None:
    lengths = fixed_uint32_source_lengths(memory_proofs, export_name, source_parameter)
    if not lengths:
        return None
    unique = set(lengths)
    return next(iter(unique)) if len(unique) == 1 else None

def interpreted_destination_loads(
    candidate: dict,
    module_memory_proofs: list[dict],
    export_name: str | None,
    byte_integrity_proven: bool,
    base_alignment_proven: bool,
) -> tuple[list[dict], int | None]:
    loads = candidate.get("destination_loads", [])
    source_parameter = candidate.get("source_entry_parameter")
    source_length = fixed_uint32_source_length_lower_bound(
        module_memory_proofs, export_name, source_parameter
    )
    element_shift = candidate.get("destination_element_index_shift")
    if (
        not loads
        or source_length is None
        or not byte_integrity_proven
        or not base_alignment_proven
        or element_shift != 2
    ):
        return [], source_length
    interpreted = []
    for load in loads:
        offset = load.get("byte_offset")
        if (
            not isinstance(offset, int)
            or isinstance(offset, bool)
            or offset < 0
            or offset % 4 != 0
        ):
            return [], source_length
        source_index = offset // 4
        if source_index >= source_length:
            return [], source_length
        interpreted.append(
            {
                "load_value": load.get("value"),
                "load_block": load.get("block"),
                "load_instruction_index": load.get("instruction_index"),
                "memory": load.get("memory"),
                "byte_offset": offset,
                "source_parameter": source_parameter,
                "source_element_index": source_index,
                "source_conversion": "ToUint32",
                "little_endian_typed_array_storage_required": True,
            }
        )
    return interpreted, source_length


def matching_module_memory_proofs(
    document: dict,
    import_module: str | None,
    import_name: str | None,
    module_sha256: str | None,
    export_name: str | None,
    binding_proofs: list[dict],
    report: dict,
    candidate: dict,
) -> list[dict]:
    if not all(isinstance(value, str) for value in (
        import_module, import_name, module_sha256, export_name
    )):
        return []
    load_memories = {
        load.get("memory")
        for load in candidate.get("destination_loads", [])
        if isinstance(load.get("memory"), int)
    }
    if len(load_memories) != 1:
        return []
    [load_memory] = load_memories
    binding_sites = {
        (proof.get("import_object"), site.get("start"), site.get("end"), site.get("module_sha256"))
        for proof in binding_proofs
        for site in proof.get("instantiation_sites", [])
    }
    matches = []
    for proof in document.get("module_memory_identity_proofs", []):
        if proof.get("import_module") != import_module or proof.get("import_name") != import_name:
            continue
        site = proof.get("instantiation_site") or {}
        site_key = (
            proof.get("import_object"),
            site.get("start"),
            site.get("end"),
            site.get("module_sha256"),
        )
        if site_key not in binding_sites or site.get("module_sha256") != module_sha256:
            continue
        if not any(call.get("export_name") == export_name for call in proof.get("export_calls", [])):
            continue
        memory_export_name = proof.get("memory_export_name")
        memory_exports = [
            exported
            for exported in report.get("exports", [])
            if exported.get("kind") == "memory"
            and exported.get("name") == memory_export_name
            and exported.get("index") == load_memory
        ]
        if len(memory_exports) != 1:
            continue
        matches.append({**proof, "memory_export": memory_exports[0]})
    return matches


def fresh_destination_alignment_proof(
    evaluator: Path,
    project: Path,
    module: dict,
    report: dict,
    function_imports: list[dict],
    document: dict,
    candidate: dict,
    module_memory_proofs: list[dict],
    binding_proofs: list[dict],
    export_name: str | None,
) -> dict | None:
    recipe = candidate.get("fresh_destination_base_recipe")
    if not isinstance(recipe, dict) or not isinstance(export_name, str):
        return None
    function = recipe.get("function")
    length_import_index = recipe.get("source_length_import_function")
    length_shift = recipe.get("source_length_byte_shift")
    element_shift = candidate.get("destination_element_index_shift")
    alternate_bases = recipe.get("alternate_constant_bases")
    if (
        not isinstance(function, int)
        or isinstance(function, bool)
        or not isinstance(length_import_index, int)
        or isinstance(length_import_index, bool)
        or not isinstance(length_shift, int)
        or isinstance(length_shift, bool)
        or length_shift != element_shift
        or length_shift != 2
        or not isinstance(alternate_bases, list)
        or any(
            not isinstance(value, int)
            or isinstance(value, bool)
            or value < 0
            or value > 0xFFFFFFFF
            or value % 4 != 0
            for value in alternate_bases
        )
    ):
        return None
    if not (0 <= length_import_index < len(function_imports)):
        return None

    source_parameter = candidate.get("source_entry_parameter")
    exact_source_length = fixed_uint32_source_length_exact(
        module_memory_proofs, export_name, source_parameter
    )
    if exact_source_length is None or exact_source_length > (0xFFFFFFFF >> length_shift):
        return None

    # The exact instance initializer must invoke only __wbindgen_start through
    # its exports binding, and the copied-input export must be the first later
    # application export call on every proven carrier path.
    exports_bindings = set()
    for proof in module_memory_proofs:
        if (
            proof.get("initializer_only_wasm_export_call") != "__wbindgen_start"
            or proof.get("initializer_non_start_effects_memory_disjoint") is not True
        ):
            return None
        exports_binding = proof.get("exports_binding")
        if not isinstance(exports_binding, str):
            return None
        exports_bindings.add(exports_binding)
        calls = proof.get("export_calls")
        if not isinstance(calls, list) or not calls or calls[0].get("export_name") != export_name:
            return None
        argument_lengths = calls[0].get("static_uint32_array_argument_lengths")
        if (
            not isinstance(source_parameter, int)
            or isinstance(source_parameter, bool)
            or not isinstance(argument_lengths, list)
            or source_parameter >= len(argument_lengths)
            or argument_lengths[source_parameter] != exact_source_length
        ):
            return None
    if len(exports_bindings) != 1:
        return None
    [exports_binding] = exports_bindings

    start_exports = [
        exported
        for exported in report.get("exports", [])
        if exported.get("name") == "__wbindgen_start"
        and exported.get("kind") == "function"
        and isinstance(exported.get("index"), int)
        and not isinstance(exported.get("index"), bool)
    ]
    if len(start_exports) != 1:
        return None
    start_function = start_exports[0]["index"]
    if not (0 <= start_function < len(function_imports)):
        return None
    start_import = function_imports[start_function]
    start_module = start_import.get("module")
    start_name = start_import.get("name")
    if not isinstance(start_module, str) or not isinstance(start_name, str):
        return None

    table_exports = [
        exported
        for exported in report.get("exports", [])
        if exported.get("kind") == "table"
        and exported.get("name") == "__wbindgen_export_0"
    ]
    if len(table_exports) != 1:
        return None

    normalized_handlers = [
        handler
        for handler in document.get("proof_normalized_handler_semantics", [])
        if handler.get("import_module") == start_module
        and handler.get("import_name") == start_name
        and handler.get("kind") == "table_initializer_only"
        and handler.get("exports_binding") == exports_binding
        and handler.get("table_export") == "__wbindgen_export_0"
        and handler.get("standard_builtin_semantics_required") is True
        and handler.get("standard_webassembly_builtin_semantics_required") is True
    ]
    if len(normalized_handlers) != 1:
        return None

    start_usages = [
        usage
        for usage in document.get("import_object_usages", [])
        if usage.get("import_module") == start_module
        and usage.get("import_name") == start_name
    ]
    exact_start_usages = exact_module_usage_proofs(start_usages, module.get("sha256"))
    exact_start_usages = [
        usage
        for usage in exact_start_usages
        if exact_usage_matches_binding(usage, binding_proofs)
    ]
    if len(exact_start_usages) != 1:
        return None

    # The length helper in the WASM recipe must refer to a real function import.
    length_import = function_imports[length_import_index]
    if (
        not isinstance(length_import.get("module"), str)
        or not isinstance(length_import.get("name"), str)
    ):
        return None

    binary_path = module.get("binary_path")
    module_sha256 = module.get("sha256")
    if not isinstance(binary_path, str) or not isinstance(module_sha256, str):
        return None
    binary = project / binary_path
    if not binary.is_file():
        return None
    binary_sha256 = hashlib.sha256(binary.read_bytes()).hexdigest()
    if binary_sha256 != module_sha256:
        return None

    byte_count = exact_source_length << length_shift
    evaluation = run_fresh_eval(evaluator, binary, function, [byte_count])
    result = evaluation.get("i32_result")
    if (
        evaluation.get("outcome") != "returned"
        or not isinstance(result, int)
        or isinstance(result, bool)
        or result < 0
        or result > 0xFFFFFFFF
        or result % 4 != 0
    ):
        return None

    return {
        "fresh_instance_state_required": True,
        "module_sha256": module_sha256,
        "binary_path": binary_path,
        "binary_sha256_verified": True,
        "source_uint32_array_length": exact_source_length,
        "allocator_byte_count": byte_count,
        "recipe": recipe,
        "start_export": start_exports[0],
        "start_import": start_import,
        "start_import_object_usage": exact_start_usages[0],
        "start_handler": normalized_handlers[0],
        "table_export": table_exports[0],
        "exports_binding": exports_binding,
        "standard_js_numeric_builtin_semantics_required": True,
        "standard_webassembly_builtin_semantics_required": True,
        "fresh_evaluation": evaluation,
        "evaluated_destination_base": result,
        "evaluated_destination_base_trailing_zero_bits": (
            32 if result == 0 else (result & -result).bit_length() - 1
        ),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("project", type=Path)
    ap.add_argument(
        "--analyzer",
        type=Path,
        default=TOOL_ROOT / "wasm-import-semantics",
    )
    ap.add_argument(
        "--fresh-evaluator",
        type=Path,
        default=TOOL_ROOT / "fresh-eval",
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
        # by deep-v8 host_import_function.
        function_imports = [
            imported
            for imported in report.get("imports", [])
            if imported.get("kind") == "function"
        ]
        if deep.get("schema") != "wasm-redox/deep-v8":
            skipped_modules.append(
                {
                    "sha256": module.get("sha256"),
                    "schema": deep.get("schema"),
                    "reason": "host-effect/read proof requires wasm-redox/deep-v8",
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

                exact_binding_proofs = exact_module_usage_proofs(
                    import_object_usage_proofs, module.get("sha256")
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
                    "import_binding_identity_proven": len(exact_binding_proofs) == 1,
                    "import_binding_identity_proofs": exact_binding_proofs,
                    "import_binding_identity_limitation": (
                        None
                        if len(exact_binding_proofs) == 1
                        else "no unique carrier proof ties this exact recovered module SHA to the exact import object at one WebAssembly instantiation site"
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
                if len(exact_binding_proofs) > 1:
                    row["import_binding_identity_proven"] = False
                    ambiguities.append(
                        "multiple carrier sources prove exact module/import-object binding identity"
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
                memory_index = candidate.get("constructor_input_memory_import_function")
                memory_import = (
                    function_imports[memory_index]
                    if isinstance(memory_index, int) and 0 <= memory_index < len(function_imports)
                    else None
                )
                memory_module = memory_import.get("module") if memory_import else None
                memory_name = memory_import.get("name") if memory_import else None

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
                            set_usages = [
                                usage
                                for usage in document.get("import_object_usages", [])
                                if usage.get("import_module") == set_module
                                and usage.get("import_name") == set_name
                            ]
                            constructor_usages = [
                                usage
                                for usage in document.get("import_object_usages", [])
                                if usage.get("import_module") == constructor_module
                                and usage.get("import_name") == constructor_name
                            ]
                            binding_proofs = common_exact_binding_proofs(
                                set_usages, constructor_usages, module.get("sha256")
                            )
                            memory_proofs = matching_module_memory_proofs(
                                document,
                                memory_module,
                                memory_name,
                                module.get("sha256"),
                                export.get("export"),
                                binding_proofs,
                                report,
                                candidate,
                            )
                            length_barrier_proofs = source_length_barrier_proofs(
                                document,
                                function_imports,
                                candidate,
                                module.get("sha256"),
                                binding_proofs,
                            )
                            proofs.append({
                                "source_path": relative,
                                "set_handler": set_matches[0],
                                "constructor_handler": constructor_matches[0],
                                "import_binding_identity_proofs": binding_proofs,
                                "module_memory_identity_proofs": memory_proofs,
                                "source_length_barrier_proofs": length_barrier_proofs,
                            })

                copied_binding_proofs = [
                    {"source_path": proof["source_path"], **binding}
                    for proof in proofs
                    for binding in proof.get("import_binding_identity_proofs", [])
                ]
                module_memory_proofs = [
                    {"source_path": proof["source_path"], **memory}
                    for proof in proofs
                    for memory in proof.get("module_memory_identity_proofs", [])
                ]
                module_memory_sources = {proof["source_path"] for proof in module_memory_proofs}
                module_memory_proven = (
                    bool(module_memory_proofs)
                    and len(module_memory_sources) == 1
                    and len(proofs) == 1
                    and len(copied_binding_proofs) == 1
                )
                destination_loads = candidate.get("destination_loads", [])
                source_length_lower_bound = fixed_uint32_source_length_lower_bound(
                    module_memory_proofs if module_memory_proven else [],
                    export.get("export"),
                    candidate.get("source_entry_parameter"),
                )
                required_length_barriers = {
                    index
                    for load in destination_loads
                    for index in load.get("source_length_import_barriers", [])
                    if isinstance(index, int) and not isinstance(index, bool)
                }
                length_barrier_proofs = [
                    {"source_path": proof["source_path"], **barrier}
                    for proof in proofs
                    for barrier in proof.get("source_length_barrier_proofs", [])
                ]
                proven_length_barriers = {
                    proof.get("function_import") for proof in length_barrier_proofs
                }
                destination_byte_integrity_proven = (
                    bool(destination_loads)
                    and source_length_lower_bound is not None
                    and all(
                        load.get("unresolved_intervening_memory_mutation") is False
                        and not load.get("other_import_call_barriers", [])
                        for load in destination_loads
                    )
                    and proven_length_barriers == required_length_barriers
                    and (not required_length_barriers or len(proofs) == 1)
                )
                element_shift = candidate.get("destination_element_index_shift")
                base_zero_bits = candidate.get("destination_base_guaranteed_trailing_zero_bits")
                static_destination_base_alignment_proven = (
                    element_shift == 2
                    and isinstance(base_zero_bits, int)
                    and not isinstance(base_zero_bits, bool)
                    and base_zero_bits >= element_shift
                )
                fresh_alignment_proof = None
                if module_memory_proven and len(module_memory_sources) == 1:
                    source_path = next(iter(module_memory_sources))
                    document = full_probe_cache.get(source_path)
                    if document is not None:
                        fresh_alignment_proof = fresh_destination_alignment_proof(
                            args.fresh_evaluator,
                            project,
                            module,
                            report,
                            function_imports,
                            document,
                            candidate,
                            module_memory_proofs,
                            copied_binding_proofs,
                            export.get("export"),
                        )
                destination_base_alignment_proven = (
                    static_destination_base_alignment_proven
                    or fresh_alignment_proof is not None
                )
                destination_load_interpretations, _ = interpreted_destination_loads(
                    candidate,
                    module_memory_proofs if module_memory_proven else [],
                    export.get("export"),
                    destination_byte_integrity_proven,
                    destination_base_alignment_proven,
                )
                destination_load_interpretation_proven = (
                    module_memory_proven
                    and destination_byte_integrity_proven
                    and len(destination_load_interpretations) == len(destination_loads)
                    and bool(destination_load_interpretations)
                )
                row = {
                    "module_sha256": module.get("sha256"),
                    "export": export.get("export"),
                    "carrier_candidates": carrier_candidates,
                    "correlation_basis": "exact_import_module_and_name",
                    "raw_set_import_module": set_module,
                    "raw_set_import": set_name,
                    "raw_constructor_import_module": constructor_module,
                    "raw_constructor_import": constructor_name,
                    "raw_memory_import_module": memory_module,
                    "raw_memory_import": memory_name,
                    "wasm_structural_copy_candidate_proven": True,
                    "wasm_candidate": candidate,
                    "js_typed_array_copy_semantics_proven": len(proofs) == 1,
                    "js_typed_array_copy_semantics_proofs": proofs,
                    "import_binding_identity_proven": len(copied_binding_proofs) == 1,
                    "import_binding_identity_proofs": copied_binding_proofs,
                    "module_memory_identity_proven": module_memory_proven,
                    "module_memory_identity_proofs": module_memory_proofs,
                    "module_memory_identity_limitation": (
                        None
                        if module_memory_proven
                        else "no unique carrier source proves that the constructor input comes from the exported memory of the exact module instance executing this copied-input export"
                    ),
                    "destination_byte_integrity_proven": destination_byte_integrity_proven,
                    "source_length_barrier_proofs": length_barrier_proofs,
                    "static_destination_base_alignment_proven": static_destination_base_alignment_proven,
                    "fresh_destination_base_alignment_proof": fresh_alignment_proof,
                    "destination_base_alignment_proven": destination_base_alignment_proven,
                    "destination_base_alignment_basis": (
                        "static_ssa"
                        if static_destination_base_alignment_proven
                        else ("fresh_exact_evaluation" if fresh_alignment_proof is not None else None)
                    ),
                    "destination_load_interpretation_proven": destination_load_interpretation_proven,
                    "destination_load_interpretations": destination_load_interpretations,
                    "source_uint32_array_length_lower_bound": source_length_lower_bound,
                    "destination_load_interpretation_limitation": (
                        None
                        if destination_load_interpretation_proven
                        else (
                            "module-memory identity is not proven"
                            if not module_memory_proven
                            else (
                                "a potentially memory-mutating path exists between the proven Uint32Array.set and at least one destination load"
                                if not destination_byte_integrity_proven
                                else (
                                    "the destination base is not proven aligned to the Uint32Array element width"
                                    if not destination_base_alignment_proven
                                    else "the exact carrier export-call argument is not proven to be a fixed-length Uint32Array covering every destination load"
                                )
                            )
                        )
                    ),
                    "destination_load_interpretation_contract": (
                        "each proven i32.load reads the unchanged Uint32Array.set destination word corresponding to ToUint32(source[index]); numeric equality requires little-endian typed-array storage"
                    ),
                }
                if len(proofs) > 1:
                    row["js_typed_array_copy_semantics_proven"] = False
                    row["ambiguity"] = (
                        "multiple carrier sources prove the same constructor/set import semantics"
                    )
                if len(copied_binding_proofs) > 1:
                    row["import_binding_identity_proven"] = False
                    row["ambiguity"] = (
                        row.get("ambiguity", "") + "; multiple exact module/import-object binding proofs"
                    ).strip("; ")
                if len(module_memory_sources) > 1:
                    row["module_memory_identity_proven"] = False
                    row["module_memory_identity_limitation"] = (
                        "multiple carrier sources prove module-memory identity"
                    )
                    row["ambiguity"] = (
                        row.get("ambiguity", "") + "; multiple module-memory carrier proofs"
                    ).strip("; ")
                copied_input_rows.append(row)

    out = {
        "schema": WASM_JS_BOUNDARY.schema,
        "wasm_schema_required": "wasm-redox/deep-v8",
        "js_schema": "jsvm-wasm-import-semantics/v7",
        "safe_static_only": True,
        "bounded_wasm_ir_interpretation": True,
        "correlation_contract": (
            "cross-language claims require exact WASM import module+name matches. "
            "Host-effect writes and typed-array input-copy candidates remain independent evidence "
            "families; source-word interpretation additionally requires exact instance/exported-memory "
            "identity, path-complete destination-byte integrity, destination-base element alignment, "
            "and fixed Uint32Array source coverage. Fresh-state alignment may use bounded Waffle-IR "
            "interpretation only after rejecting module start functions, imported state, imported or "
            "indirect calls, recursion, and all table operations in the evaluated call graph."
        ),
        "memory_write_interpretation": (
            "DataView and typed-array interpretations require standard unmodified platform builtins; "
            "numeric equality between Uint32Array elements and WASM i32 loads additionally requires "
            "little-endian typed-array storage"
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
            "proven_host_import_binding_identities": sum(
                row["import_binding_identity_proven"] for row in host_effect_rows
            ),
            "proven_copied_input_binding_identities": sum(
                row["import_binding_identity_proven"] for row in copied_input_rows
            ),
            "proven_module_memory_identities": sum(
                row["module_memory_identity_proven"] for row in copied_input_rows
            ),
            "proven_destination_byte_integrities": sum(
                row["destination_byte_integrity_proven"] for row in copied_input_rows
            ),
            "proven_destination_base_alignments": sum(
                row["destination_base_alignment_proven"] for row in copied_input_rows
            ),
            "proven_destination_load_interpretations": sum(
                row["destination_load_interpretation_proven"] for row in copied_input_rows
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
        "exact module-memory identity; "
        f"{summary['proven_destination_load_interpretations']} copied-input candidate(s) have proven "
        "source-word load interpretation"
    )


if __name__ == "__main__":
    main()
