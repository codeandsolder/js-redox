#!/usr/bin/env python3
from __future__ import annotations

import json
import tempfile
from pathlib import Path

from capture_project import CaptureManifestError, SCHEMA, read_manifest, write_manifest


def write(path: Path, value: object) -> None:
    path.write_text(json.dumps(value))


def valid_manifest() -> dict:
    return {
        "schema": SCHEMA,
        "source": {
            "kind": "har",
            "input": "/capture.har",
            "har_version": "1.2",
            "salvaged": False,
        },
        "pages": [],
        "resources": [],
        "inline_scripts": [],
        "counts": {},
    }


def rejects(path: Path, value: object, expected: str) -> None:
    write(path, value)
    try:
        read_manifest(path)
    except CaptureManifestError as error:
        assert expected in str(error), (expected, str(error))
    else:
        raise AssertionError(f"manifest should have been rejected: {expected}")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="js-redox-capture-contract-") as tmp:
        path = Path(tmp) / "capture-manifest.json"
        manifest = valid_manifest()
        write_manifest(path, manifest)
        assert read_manifest(path) == manifest

        wrong_schema = valid_manifest()
        wrong_schema["schema"] = "capture-project/v0"
        rejects(path, wrong_schema, "expected schema")

        missing_source = valid_manifest()
        del missing_source["source"]
        rejects(path, missing_source, "source must be an object")

        missing_resources = valid_manifest()
        del missing_resources["resources"]
        rejects(path, missing_resources, "resources must be an array")

        wrong_salvaged = valid_manifest()
        wrong_salvaged["source"]["salvaged"] = "false"
        rejects(path, wrong_salvaged, "source.salvaged must be a bool")

        for hostile_path in (
            "../../outside.js",
            "/tmp/outside.js",
            "C:/outside.js",
            "resources/../outside.js",
            r"resources\outside.js",
        ):
            hostile = valid_manifest()
            hostile["resources"] = [{"id": 0, "output_path": hostile_path}]
            rejects(path, hostile, "output_path")

        wrong_prefix = valid_manifest()
        wrong_prefix["resources"] = [{"id": 0, "output_path": "src/outside.js"}]
        rejects(path, wrong_prefix, "must be under resources/")

        sparse_id = valid_manifest()
        sparse_id["resources"] = [{"id": 7, "output_path": "resources/a.js"}]
        sparse_id["inline_scripts"] = [
            {"parent_resource_id": 7, "output_path": "resources/inline.js"}
        ]
        write(path, sparse_id)
        assert read_manifest(path) == sparse_id

        duplicate_id = valid_manifest()
        duplicate_id["resources"] = [
            {"id": 7, "output_path": "resources/a.js"},
            {"id": 7, "output_path": "resources/b.js"},
        ]
        rejects(path, duplicate_id, "duplicate resource id 7")

        invalid_id = valid_manifest()
        invalid_id["resources"] = [{"id": -1, "output_path": "resources/a.js"}]
        rejects(path, invalid_id, ".id must be a non-negative integer")

        bad_inline_parent = valid_manifest()
        bad_inline_parent["resources"] = [{"id": 7, "output_path": "resources/a.js"}]
        bad_inline_parent["inline_scripts"] = [
            {"parent_resource_id": 9, "output_path": "resources/inline.js"}
        ]
        rejects(path, bad_inline_parent, "parent_resource_id does not name a resource")

    print("capture-project contract: ok")


if __name__ == "__main__":
    main()
