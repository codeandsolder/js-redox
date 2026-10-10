#!/usr/bin/env python3
"""Canonical top-level analysis artifact contracts for capture projects.

Pipeline stages may have rich internal data models, but their persisted JSON
boundaries are intentionally centralized here. Consumers should load artifacts
through this module so a stale or incompatible schema fails closed instead of
being interpreted opportunistically.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, cast


@dataclass(frozen=True)
class ArtifactSpec:
    name: str
    relative_path: Path
    schema: str
    array_fields: tuple[str, ...] = ()
    object_fields: tuple[str, ...] = ()


SOURCE_INDEX = ArtifactSpec(
    "source index",
    Path("analysis/source-index.json"),
    "capture-source-index/v1",
    array_fields=("units",),
    object_fields=("summary",),
)
SOURCEMAPS = ArtifactSpec(
    "source-map recovery",
    Path("analysis/sourcemaps.json"),
    "capture-sourcemap-recovery/v1",
    array_fields=("source_maps",),
)
IMPORT_MAPS = ArtifactSpec(
    "import maps",
    Path("analysis/import-maps.json"),
    "capture-import-maps/v1",
    array_fields=("maps",),
    object_fields=("documents", "summary"),
)
JS_REFERENCES = ArtifactSpec(
    "JavaScript references",
    Path("analysis/js-references.json"),
    "capture-js-references/v1",
    array_fields=("code_units",),
    object_fields=("summary",),
)
STRING_RECOVERY = ArtifactSpec(
    "static string recovery",
    Path("analysis/string-recovery.json"),
    "capture-static-string-recovery/v1",
    array_fields=("units",),
    object_fields=("summary",),
)
DEOBFUSCATION = ArtifactSpec(
    "safe deobfuscation",
    Path("analysis/deobfuscation.json"),
    "capture-safe-deobfuscation/v1",
    array_fields=("units",),
    object_fields=("summary",),
)
BUNDLES = ArtifactSpec(
    "bundle modules",
    Path("analysis/bundles.json"),
    "capture-bundle-modules/v1",
    array_fields=("bundles", "modules", "failures"),
    object_fields=("summary",),
)
WASM_INDEX = ArtifactSpec(
    "WASM capture index",
    Path("analysis/wasm/index.json"),
    "wasm-redox/capture-v1",
    array_fields=("modules",),
    object_fields=("summary",),
)
WASM_HOST_EFFECTS = ArtifactSpec(
    "WASM host-effect correlation",
    Path("analysis/wasm-host-effects.json"),
    "wasm-host-effect-correlation/v1",
    array_fields=("rows", "skipped_modules"),
    object_fields=("summary",),
)
GENERATED_RECOVERY = ArtifactSpec(
    "generated-code recovery",
    Path("analysis/generated-recovery.json"),
    "generated-code-safe-recovery/v1",
    array_fields=("units",),
    object_fields=("summary",),
)
JSVM_INDEX = ArtifactSpec(
    "JS VM analysis",
    Path("analysis/jsvm/index.json"),
    "capture-jsvm-analysis/v1",
    array_fields=("code_units", "dynamic_code_units"),
)
SOURCE_GRAPH = ArtifactSpec(
    "source graph",
    Path("analysis/source-graph.json"),
    "source-graph/v1",
    array_fields=("nodes", "edges"),
    object_fields=("summary",),
)
RUNTIME_SCRIPTS = ArtifactSpec(
    "runtime scripts",
    Path("analysis/runtime-scripts.json"),
    "js-redox-runtime-scripts/v1",
    array_fields=("alpine_families", "gtm_families", "sources"),
    object_fields=("summary",),
)

ALL_ARTIFACTS = (
    SOURCE_INDEX,
    SOURCEMAPS,
    IMPORT_MAPS,
    JS_REFERENCES,
    STRING_RECOVERY,
    DEOBFUSCATION,
    BUNDLES,
    WASM_INDEX,
    WASM_HOST_EFFECTS,
    GENERATED_RECOVERY,
    JSVM_INDEX,
    SOURCE_GRAPH,
    RUNTIME_SCRIPTS,
)


class AnalysisArtifactError(ValueError):
    """Persisted analysis artifact is missing, unreadable, or incompatible."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise AnalysisArtifactError(message)


def artifact_path(project: Path, spec: ArtifactSpec) -> Path:
    return project / spec.relative_path


def validate_artifact(
    document: object,
    spec: ArtifactSpec,
    *,
    path: Path | None = None,
) -> dict[str, Any]:
    label = str(path) if path is not None else spec.name
    _require(isinstance(document, dict), f"{label}: artifact root must be an object")
    raw = cast(dict[str, Any], document)
    _require(
        raw.get("schema") == spec.schema,
        f"{label}: expected schema {spec.schema!r}, got {raw.get('schema')!r}",
    )
    for key in spec.array_fields:
        _require(isinstance(raw.get(key), list), f"{label}: {key} must be an array")
    for key in spec.object_fields:
        _require(isinstance(raw.get(key), dict), f"{label}: {key} must be an object")
    return raw


def build_artifact(spec: ArtifactSpec, /, **payload: Any) -> dict[str, Any]:
    if "schema" in payload:
        raise AnalysisArtifactError(f"{spec.name}: schema is owned by the artifact contract")
    document: dict[str, Any] = {"schema": spec.schema, **payload}
    return validate_artifact(document, spec)


def read_artifact(path: Path, spec: ArtifactSpec) -> dict[str, Any]:
    try:
        document = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise AnalysisArtifactError(f"failed to read {spec.name} {path}: {error}") from error
    return validate_artifact(document, spec, path=path)


def load_artifact(
    project: Path,
    spec: ArtifactSpec,
    *,
    optional: bool = False,
) -> dict[str, Any] | None:
    path = artifact_path(project, spec)
    if optional and not path.exists():
        return None
    return read_artifact(path, spec)


def write_artifact_path(
    path: Path,
    spec: ArtifactSpec,
    document: object,
) -> dict[str, Any]:
    validated = validate_artifact(document, spec, path=path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(validated, indent=2, ensure_ascii=False) + "\n")
    return validated


def write_artifact(
    project: Path,
    spec: ArtifactSpec,
    document: object,
) -> dict[str, Any]:
    return write_artifact_path(artifact_path(project, spec), spec, document)
