#!/usr/bin/env python3
"""Canonical capture-project manifest contract for Python pipeline stages."""

from __future__ import annotations

import json
import re
from pathlib import Path, PurePosixPath
from typing import Any, NotRequired, TypedDict, cast

SCHEMA = "capture-project/v1"
MANIFEST_NAME = "capture-manifest.json"
_WINDOWS_DRIVE = re.compile(r"^[A-Za-z]:")


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


def _project_relative_path(value: object, label: str) -> PurePosixPath:
    _require(isinstance(value, str) and bool(value), f"{label}: path must be a non-empty string")
    assert isinstance(value, str)
    _require("\x00" not in value, f"{label}: path contains NUL")
    _require("\\" not in value, f"{label}: backslash paths are not allowed")
    _require(not _WINDOWS_DRIVE.match(value), f"{label}: drive-qualified path is not allowed")
    parts = value.split("/")
    _require(all(part not in {"", ".", ".."} for part in parts), f"{label}: path must stay inside the capture project")
    parsed = PurePosixPath(value)
    _require(not parsed.is_absolute(), f"{label}: absolute path is not allowed")
    return parsed


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

    resources = manifest["resources"]
    for index, resource in enumerate(resources):
        _require(isinstance(resource, dict), f"{label}: resources[{index}] must be an object")
        _require(resource.get("id") == index, f"{label}: resources[{index}].id must equal {index}")
        output_path = resource.get("output_path")
        if output_path is not None:
            parsed = _project_relative_path(output_path, f"{label}: resources[{index}].output_path")
            _require(parsed.parts[0] == "resources", f"{label}: resources[{index}].output_path must be under resources/")

    for index, script in enumerate(manifest["inline_scripts"]):
        _require(isinstance(script, dict), f"{label}: inline_scripts[{index}] must be an object")
        parent = script.get("parent_resource_id")
        _require(isinstance(parent, int) and not isinstance(parent, bool) and 0 <= parent < len(resources), f"{label}: inline_scripts[{index}].parent_resource_id is out of range")
        output_path = script.get("output_path")
        if output_path is not None:
            parsed = _project_relative_path(output_path, f"{label}: inline_scripts[{index}].output_path")
            _require(parsed.parts[0] == "resources", f"{label}: inline_scripts[{index}].output_path must be under resources/")
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
