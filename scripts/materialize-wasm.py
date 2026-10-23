#!/usr/bin/env python3
"""Recover captured and statically produced WebAssembly with exact provenance."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from collections import defaultdict
from pathlib import Path

from analysis_artifacts import WASM_INDEX, write_artifact

from capture_project import load_manifest


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def rel(project: Path, path: Path) -> str:
    return path.relative_to(project).as_posix()


def run_static_byte_recovery(tool: Path, source: Path, output_dir: Path) -> dict | None:
    cp = subprocess.run(
        [str(tool), str(source), "--output-dir", str(output_dir)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if cp.returncode:
        diagnostic = (cp.stderr or cp.stdout or f"exit {cp.returncode}").strip()
        if "JavaScript did not parse as unambiguous or CommonJS source" in diagnostic:
            return None
        raise RuntimeError(
            f"static byte recovery failed for {source} with exit {cp.returncode}: {diagnostic}"
        )
    try:
        report = json.loads(cp.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"static byte recovery returned invalid JSON for {source}") from error
    schema = report.get("schema")
    if schema != "js-static-byte-artifacts/v2":
        raise RuntimeError(
            f"unexpected static byte recovery schema for {source}: {schema!r}"
        )
    return report


def run_analysis(tool: Path, binary: Path, output: Path) -> tuple[bool, str | None]:
    output.mkdir(parents=True, exist_ok=True)
    cp = subprocess.run(
        [str(tool), str(binary), "--output-dir", str(output), "--skip-wax"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if cp.returncode:
        message = (cp.stderr or cp.stdout or f"exit {cp.returncode}").strip()
        return False, message
    return True, None


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("project", type=Path)
    ap.add_argument("--wasm-redox", type=Path, required=True)
    ap.add_argument(
        "--static-byte-artifacts",
        type=Path,
        help="Rust static byte producer; defaults to the wasm-redox tool directory",
    )
    args = ap.parse_args()

    project = args.project.resolve()
    static_byte_artifacts = (
        args.static_byte_artifacts
        if args.static_byte_artifacts is not None
        else args.wasm_redox.with_name("static-byte-artifacts")
    )
    manifest = load_manifest(project)
    analysis_root = project / "analysis/wasm"
    modules_root = analysis_root / "modules"
    inline_root = project / "src/_wasm/inline"
    origins: dict[str, list[dict]] = defaultdict(list)
    binary_paths: dict[str, Path] = {}
    direct_origin: dict[str, bool] = defaultdict(bool)
    inline_origin: dict[str, bool] = defaultdict(bool)

    # First-class captured application/wasm resources.
    for resource in manifest.get("resources", []):
        if resource.get("kind") != "wasm" or not resource.get("body_present"):
            continue
        raw_path = resource.get("output_path")
        if not raw_path:
            continue
        path = project / raw_path
        if not path.is_file():
            continue
        data = path.read_bytes()
        digest = sha256(data)
        binary_paths.setdefault(digest, path)
        direct_origin[digest] = True
        origins[digest].append(
            {
                "type": "resource",
                "resource_id": int(resource["id"]),
                "url": resource.get("url"),
                "source_path": raw_path,
            }
        )

    sources: list[tuple[Path, dict]] = []
    for resource in manifest.get("resources", []):
        if resource.get("kind") != "javascript" or not resource.get("body_present"):
            continue
        raw_path = resource.get("output_path")
        if raw_path and (project / raw_path).is_file():
            sources.append(
                (
                    project / raw_path,
                    {
                        "type": "resource_inline_base64",
                        "resource_id": int(resource["id"]),
                        "url": resource.get("url"),
                        "source_path": raw_path,
                    },
                )
            )
    for item in manifest.get("inline_scripts", []):
        raw_path = item.get("output_path")
        if raw_path and (project / raw_path).is_file():
            sources.append(
                (
                    project / raw_path,
                    {
                        "type": "inline_script_base64",
                        "parent_resource_id": int(item["parent_resource_id"]),
                        "ordinal": int(item["ordinal"]),
                        "source_path": raw_path,
                    },
                )
            )

    # Recover exact static byte producers from captured JavaScript. The Rust
    # analyzer owns both complete validated Base64 literals and proof-gated
    # multi-chunk byte assembly; this Python layer only records provenance and
    # feeds recovered bytes into the normal wasm-redox analysis pipeline.
    seen_occurrences: set[tuple[str, str, int, int]] = set()
    for source, provenance in sources:
        raw = source.read_bytes()
        # Cheap lexical candidate gate. The semantic analyzer remains
        # authoritative and validates complete modules before reporting them.
        if b"AGFzbQ" not in raw and b"WebAssembly" not in raw:
            continue
        report = run_static_byte_recovery(static_byte_artifacts, source, inline_root)
        if report is None:
            continue

        for artifact in report.get("inline_wasm_literals", []):
            start = int(artifact["source_start"])
            end = int(artifact["source_end"])
            key = (provenance["source_path"], "inline_base64_literal", start, end)
            if key in seen_occurrences:
                continue
            seen_occurrences.add(key)
            digest = artifact["sha256"]
            binary = inline_root / f"{digest}.wasm"
            if not binary.is_file():
                continue
            binary_paths.setdefault(digest, binary)
            inline_origin[digest] = True
            origins[digest].append(
                {
                    **provenance,
                    "encoding": artifact["encoding"],
                    "byte_start": start,
                    "byte_end": end,
                    "recovery_kind": "validated_inline_base64_literal",
                }
            )

        for artifact in report.get("artifacts", []):
            start = int(artifact["allocation_start"])
            end = int(artifact["sink_end"])
            key = (provenance["source_path"], "static_byte_assembly", start, end)
            if key in seen_occurrences:
                continue
            seen_occurrences.add(key)
            digest = artifact["sha256"]
            binary = inline_root / f"{digest}.wasm"
            if not binary.is_file():
                continue
            binary_paths.setdefault(digest, binary)
            inline_origin[digest] = True
            assembled_type = (
                "resource_static_bytes"
                if provenance["type"] == "resource_inline_base64"
                else "inline_script_static_bytes"
            )
            origins[digest].append(
                {
                    **provenance,
                    "type": assembled_type,
                    "encoding": "static_byte_assembly",
                    "byte_start": start,
                    "byte_end": end,
                    "recovery_kind": "proven_static_byte_assembly",
                    "sink_kind": artifact["sink_kind"],
                    "sink_start": int(artifact["sink_start"]),
                    "sink_end": int(artifact["sink_end"]),
                    "copy_writes": int(artifact["copy_writes"]),
                }
            )

    modules = []
    for digest in sorted(origins):
        binary = binary_paths[digest]
        out = modules_root / digest
        ok, error = run_analysis(args.wasm_redox, binary, out)
        row = {
            "sha256": digest,
            "byte_len": binary.stat().st_size,
            "binary_path": rel(project, binary),
            "extracted": not direct_origin[digest],
            "has_direct_resource": bool(direct_origin[digest]),
            "has_inline_origin": bool(inline_origin[digest]),
            "status": "ok" if ok else "failed",
            "error": error,
            "origins": origins[digest],
        }
        if ok:
            row.update(
                {
                    "report_path": rel(project, out / "module.report.json"),
                    "wat_path": rel(project, out / "module.readable.wat"),
                    "deep_path": rel(project, out / "module.deep.json"),
                }
            )
        modules.append(row)

    analysis_root.mkdir(parents=True, exist_ok=True)
    index = {
        "schema": WASM_INDEX.schema,
        "modules": modules,
        "summary": {
            "modules": len(modules),
            "direct_resources": sum(row["has_direct_resource"] for row in modules),
            "inline_extracted": sum(row["has_inline_origin"] for row in modules),
            "failed": sum(row["status"] != "ok" for row in modules),
            "origins": sum(len(row["origins"]) for row in modules),
        },
    }
    write_artifact(project, WASM_INDEX, index)
    print(
        "WASM: "
        f"{index['summary']['modules']} unique module(s), "
        f"{index['summary']['origins']} origin(s), "
        f"{index['summary']['failed']} failed"
    )


if __name__ == "__main__":
    main()
