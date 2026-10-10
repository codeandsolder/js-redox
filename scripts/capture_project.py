#!/usr/bin/env python3
"""Canonical capture-project manifest contract for Python pipeline stages."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, NotRequired, TypedDict, cast

SCHEMA = "capture-project/v1"
MANIFEST_NAME = "capture-manifest.json"


class CaptureSource(TypedDict):
    kind: str
    input: str
    salvaged: bool
    parse_error: NotRequired[str | None]
    har_version: NotRequired[str]
    har_input: NotRequired[str]
    original_page_url: NotRequired[str | None]
    assets_dir: NotRequired[str | None]


class CaptureManifest(TypedDict):
    schema: str
    source: CaptureSource
    pages: list[dict[str, Any]]
    resources: list[dict[str, Any]]
    inline_scripts: list[dict[str, Any]]
    counts: dict[str, int]


class CaptureManifestError(ValueError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise CaptureManifestError(message)


def validate_manifest(raw: object, *, path: Path | None = None) -> CaptureManifest:
    label = str(path) if path is not None else "capture manifest"
    _require(isinstance(raw, dict), f"{label}: manifest root must be an object")
    manifest = cast(dict[str, Any], raw)
    _require(manifest.get("schema") == SCHEMA, f"{label}: expected schema {SCHEMA!r}")

    source = manifest.get("source")
    _require(isinstance(source, dict), f"{label}: source must be an object")
    _require(isinstance(source.get("kind"), str) and bool(source["kind"]), f"{label}: source.kind must be a non-empty string")
    _require(isinstance(source.get("input"), str) and bool(source["input"]), f"{label}: source.input must be a non-empty string")
    _require(isinstance(source.get("salvaged"), bool), f"{label}: source.salvaged must be a bool")

    for key in ("pages", "resources", "inline_scripts"):
        _require(isinstance(manifest.get(key), list), f"{label}: {key} must be an array")
    _require(isinstance(manifest.get("counts"), dict), f"{label}: counts must be an object")
    return cast(CaptureManifest, manifest)


def read_manifest(path: Path) -> CaptureManifest:
    try:
        raw = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise CaptureManifestError(f"failed to read capture manifest {path}: {error}") from error
    return validate_manifest(raw, path=path)


def write_manifest(path: Path, manifest: object) -> CaptureManifest:
    validated = validate_manifest(manifest, path=path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(validated, indent=2, ensure_ascii=False) + "\n")
    return validated


def load_manifest(project: Path) -> CaptureManifest:
    return read_manifest(project / MANIFEST_NAME)
