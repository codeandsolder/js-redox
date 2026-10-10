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


def read_manifest(path: Path) -> CaptureManifest:
    try:
        raw = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise CaptureManifestError(f"failed to read capture manifest {path}: {error}") from error

    _require(isinstance(raw, dict), f"{path}: manifest root must be an object")
    _require(raw.get("schema") == SCHEMA, f"{path}: expected schema {SCHEMA!r}")

    source = raw.get("source")
    _require(isinstance(source, dict), f"{path}: source must be an object")
    _require(isinstance(source.get("kind"), str) and bool(source["kind"]), f"{path}: source.kind must be a non-empty string")
    _require(isinstance(source.get("input"), str) and bool(source["input"]), f"{path}: source.input must be a non-empty string")
    _require(isinstance(source.get("salvaged"), bool), f"{path}: source.salvaged must be a bool")

    for key in ("pages", "resources", "inline_scripts"):
        _require(isinstance(raw.get(key), list), f"{path}: {key} must be an array")
    _require(isinstance(raw.get("counts"), dict), f"{path}: counts must be an object")

    return cast(CaptureManifest, raw)


def load_manifest(project: Path) -> CaptureManifest:
    return read_manifest(project / MANIFEST_NAME)
