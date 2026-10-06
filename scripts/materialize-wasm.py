#!/usr/bin/env python3
"""Recover captured and simple inline-base64 WebAssembly with provenance."""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path

BASE64_WASM = re.compile(rb"AGFzbQ[A-Za-z0-9+/]{8,}={0,2}")
WASM_MAGIC = b"\x00asm"
MAX_INLINE_BASE64 = 64 * 1024 * 1024


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def rel(project: Path, path: Path) -> str:
    return path.relative_to(project).as_posix()


def decode_inline_candidates(data: bytes):
    for match in BASE64_WASM.finditer(data):
        encoded = match.group(0)
        if len(encoded) > MAX_INLINE_BASE64:
            continue
        try:
            decoded = base64.b64decode(encoded, validate=True)
        except ValueError:
            continue
        if decoded.startswith(WASM_MAGIC):
            yield match.start(), match.end(), decoded


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
    args = ap.parse_args()

    project = args.project.resolve()
    manifest = json.loads((project / "har-manifest.json").read_text())
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

    # Recover simple contiguous Base64 literals from captured JavaScript and
    # inline scripts. Validation of the decoded \0asm magic makes this a narrow
    # extraction rule rather than a generic "looks base64-ish" guess.
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

    seen_occurrences: set[tuple[str, int, int]] = set()
    for source, provenance in sources:
        raw = source.read_bytes()
        for start, end, data in decode_inline_candidates(raw):
            key = (provenance["source_path"], start, end)
            if key in seen_occurrences:
                continue
            seen_occurrences.add(key)
            digest = sha256(data)
            inline_root.mkdir(parents=True, exist_ok=True)
            binary = inline_root / f"{digest}.wasm"
            if not binary.exists():
                binary.write_bytes(data)
            binary_paths.setdefault(digest, binary)
            inline_origin[digest] = True
            origins[digest].append(
                {
                    **provenance,
                    "encoding": "base64",
                    "byte_start": start,
                    "byte_end": end,
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
        "schema": "wasm-redox/capture-v1",
        "modules": modules,
        "summary": {
            "modules": len(modules),
            "direct_resources": sum(row["has_direct_resource"] for row in modules),
            "inline_extracted": sum(row["has_inline_origin"] for row in modules),
            "failed": sum(row["status"] != "ok" for row in modules),
            "origins": sum(len(row["origins"]) for row in modules),
        },
    }
    (analysis_root / "index.json").write_text(json.dumps(index, indent=2) + "\n")
    print(
        "WASM: "
        f"{index['summary']['modules']} unique module(s), "
        f"{index['summary']['origins']} origin(s), "
        f"{index['summary']['failed']} failed"
    )


if __name__ == "__main__":
    main()
