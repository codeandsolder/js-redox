#!/usr/bin/env python3
"""Extract static browser API callsites from the selected recovered JavaScript."""

from __future__ import annotations

import argparse
import json
import subprocess
from collections import Counter
from pathlib import Path
from urllib.parse import urlsplit

from analysis_artifacts import API_SURFACE, DEOBFUSCATION, SOURCE_INDEX, load_artifact, write_artifact

ROOT = Path(__file__).resolve().parents[1]


def absolute_network_url(value: object) -> bool:
    if not isinstance(value, str):
        return False
    parsed = urlsplit(value)
    return parsed.scheme.lower() in {"http", "https", "ws", "wss"} and bool(parsed.netloc)


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Extract provenance-preserving static browser API callsites"
    )
    ap.add_argument("project", type=Path)
    ap.add_argument(
        "--analyzer",
        type=Path,
        default=ROOT / ".cargo-target-nodebug/debug/api-surface",
    )
    args = ap.parse_args()
    project = args.project.resolve()

    source_index = load_artifact(project, SOURCE_INDEX)
    deobfuscation = load_artifact(project, DEOBFUSCATION, optional=True) or {"units": []}
    deob_by_raw = {
        row.get("raw_path"): row
        for row in deobfuscation.get("units", [])
        if row.get("raw_path") and not row.get("exit") and row.get("output_path")
    }

    callsites = []
    failures = []
    analyzed_units = 0
    for source_index_ordinal, unit in enumerate(source_index.get("units", [])):
        if unit.get("kind") != "javascript" or not unit.get("source_path"):
            continue
        raw_path = unit.get("raw_path")
        deob = deob_by_raw.get(raw_path)
        analysis_path = deob.get("output_path") if deob else unit.get("source_path")
        if not analysis_path:
            continue
        source = project / analysis_path
        if not source.is_file():
            failures.append(
                {
                    "source_index_ordinal": source_index_ordinal,
                    "resource_id": unit.get("resource_id"),
                    "raw_path": raw_path,
                    "analysis_path": analysis_path,
                    "error": "selected analysis source is missing",
                }
            )
            analyzed_units += 1
            continue

        cp = subprocess.run(
            [str(args.analyzer), str(source)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if cp.returncode:
            failures.append(
                {
                    "source_index_ordinal": source_index_ordinal,
                    "resource_id": unit.get("resource_id"),
                    "raw_path": raw_path,
                    "analysis_path": analysis_path,
                    "error": (cp.stdout + cp.stderr)[-3000:],
                }
            )
            analyzed_units += 1
            continue
        try:
            report = json.loads(cp.stdout)
        except json.JSONDecodeError as error:
            failures.append(
                {
                    "source_index_ordinal": source_index_ordinal,
                    "resource_id": unit.get("resource_id"),
                    "raw_path": raw_path,
                    "analysis_path": analysis_path,
                    "error": f"invalid analyzer JSON: {error}",
                }
            )
            analyzed_units += 1
            continue
        if report.get("schema") != "jsvm-api-surface/v1" or not isinstance(
            report.get("callsites"), list
        ):
            failures.append(
                {
                    "source_index_ordinal": source_index_ordinal,
                    "resource_id": unit.get("resource_id"),
                    "raw_path": raw_path,
                    "analysis_path": analysis_path,
                    "error": "incompatible analyzer output",
                }
            )
            analyzed_units += 1
            continue

        for callsite_ordinal, row in enumerate(report["callsites"]):
            out = {
                "source_index_ordinal": source_index_ordinal,
                "callsite_ordinal": callsite_ordinal,
                "resource_id": unit.get("resource_id"),
                "resource_url": unit.get("url"),
                "raw_path": raw_path,
                "source_path": unit.get("source_path"),
                "analysis_path": analysis_path,
                "deobfuscation_ordinal": deob.get("ordinal") if deob else None,
                **row,
            }
            out["absolute_network_url"] = absolute_network_url(out.get("url"))
            callsites.append(out)
        analyzed_units += 1

    kinds = Counter(row.get("kind") for row in callsites)
    summary = {
        "units": analyzed_units,
        "callsites": len(callsites),
        "failures": len(failures),
        "kinds": dict(sorted(kinds.items())),
        "static_urls": sum(isinstance(row.get("url"), str) for row in callsites),
        "absolute_network_urls": sum(
            bool(row.get("absolute_network_url")) for row in callsites
        ),
        "static_methods": sum(isinstance(row.get("method"), str) for row in callsites),
    }
    document = {
        "schema": API_SURFACE.schema,
        "callsites": callsites,
        "failures": failures,
        "summary": summary,
    }
    write_artifact(project, API_SURFACE, document)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
