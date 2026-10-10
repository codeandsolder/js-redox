#!/usr/bin/env python3
"""Regression checks for persisted top-level analysis artifact contracts."""

from __future__ import annotations

import tempfile
from copy import deepcopy
from pathlib import Path

from analysis_artifacts import (
    ALL_ARTIFACTS,
    SOURCE_INDEX,
    AnalysisArtifactError,
    build_artifact,
    load_artifact,
    validate_artifact,
    write_artifact,
)


def expect_invalid(document: object, message: str) -> None:
    try:
        validate_artifact(document, SOURCE_INDEX)
    except AnalysisArtifactError:
        return
    raise AssertionError(message)


def main() -> None:
    paths = [spec.relative_path for spec in ALL_ARTIFACTS]
    schemas = [spec.schema for spec in ALL_ARTIFACTS]
    assert len(paths) == len(set(paths)), "analysis artifact paths must be unique"
    assert len(schemas) == len(set(schemas)), "analysis artifact schemas must be unique"
    assert all(not schema.startswith("har-") for schema in schemas), schemas

    source_index = build_artifact(SOURCE_INDEX, units=[], summary={"units": 0})
    assert source_index["schema"] == SOURCE_INDEX.schema

    wrong_schema = deepcopy(source_index)
    wrong_schema["schema"] = "capture-source-index/v0"
    expect_invalid(wrong_schema, "wrong schema must fail closed")

    missing_units = deepcopy(source_index)
    del missing_units["units"]
    expect_invalid(missing_units, "missing required array must fail closed")

    bad_summary = deepcopy(source_index)
    bad_summary["summary"] = []
    expect_invalid(bad_summary, "wrong required object type must fail closed")

    with tempfile.TemporaryDirectory() as tmp:
        project = Path(tmp)
        assert load_artifact(project, SOURCE_INDEX, optional=True) is None
        write_artifact(project, SOURCE_INDEX, source_index)
        assert load_artifact(project, SOURCE_INDEX) == source_index

        path = project / SOURCE_INDEX.relative_path
        path.write_text('{"schema":"capture-source-index/v0","units":[],"summary":{}}\n')
        try:
            load_artifact(project, SOURCE_INDEX, optional=True)
        except AnalysisArtifactError:
            pass
        else:
            raise AssertionError("optional artifact must still reject incompatible present data")

    print(f"analysis artifact contract: {len(ALL_ARTIFACTS)} unique top-level artifacts validated")


if __name__ == "__main__":
    main()
