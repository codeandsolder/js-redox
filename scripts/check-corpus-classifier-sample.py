#!/usr/bin/env python3
"""Stratified semantic spot-check of the cheap corpus preclassifier."""
from __future__ import annotations

import argparse
import collections
import json
import sqlite3
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = ROOT / "work/scum-corpus-20261007"
DEFAULT_DB = DEFAULT_CORPUS / "preclass/corpus.sqlite"
DEFAULT_SUS = ROOT / ".cargo-target-nodebug/debug/sus-scan"
INTERESTING_FEATURES = (
    "dynamic_code_shape",
    "flattening_shape",
    "encoded_payload_shape",
    "self_defending_shape",
    "string_table_rotation_shape",
    "wasm_carrier_shape",
    "javascript_obfuscator_names",
    "packer_eval",
    "anti_debug_interval",
    "worker_constructor",
)


def interesting_sql(alias: str = "c") -> str:
    marks = ",".join("?" for _ in INTERESTING_FEATURES)
    return (
        f"EXISTS (SELECT 1 FROM body_feature f WHERE f.sha256={alias}.sha256 "
        f"AND (f.feature IN ({marks}) OR (f.feature='large_minified' AND {alias}.cohort_count=1)))"
    )


def select_rows(db: sqlite3.Connection, per: int) -> list[dict]:
    interesting = interesting_sql()
    params = list(INTERESTING_FEATURES)
    strata = {
        "interesting-control": interesting,
        "boring-runtime": f"c.runtime_present=1 AND NOT ({interesting})",
        "boring-network": f"c.network_present=1 AND c.runtime_present=0 AND NOT ({interesting})",
        "boring-large-shared": (
            "EXISTS (SELECT 1 FROM body_feature x WHERE x.sha256=c.sha256 "
            "AND x.feature='large_minified') AND c.cohort_count>1 "
            f"AND NOT ({interesting})"
        ),
        "boring-rare": f"c.cohort_count=1 AND c.domain_count<=2 AND NOT ({interesting})",
    }
    rows = []
    for stratum, clause in strata.items():
        copies = clause.count("?")
        query = f"""
            SELECT c.sha256,c.representative_path,c.bytes,c.cohort_count,c.domain_count
            FROM current_body c JOIN body_scan s USING (sha256)
            WHERE s.content_kind LIKE 'javascript%' AND s.nuisance IS NULL AND ({clause})
            ORDER BY substr(c.sha256,1,16) LIMIT ?
        """
        bound = params * (copies // len(params)) + [per]
        for sha, path, size, cohorts, domains in db.execute(query, bound):
            rows.append(
                {
                    "stratum": stratum,
                    "sha256": sha,
                    "path": path,
                    "bytes": size,
                    "cohort_count": cohorts,
                    "domain_count": domains,
                }
            )
    return rows


def scan(binary: Path, row: dict) -> dict:
    cp = subprocess.run([str(binary), "--json", row["path"]], text=True, capture_output=True)
    if cp.returncode:
        return {**row, "error": (cp.stderr or cp.stdout).strip()[:2000]}
    payload = json.loads(cp.stdout)
    files = payload.get("files") or []
    if len(files) != 1:
        return {**row, "error": f"unexpected files={len(files)}"}
    file = files[0]
    return {
        **row,
        "error": None,
        "fatal_error": bool(file.get("fatal_error")),
        "diagnostics": int(file.get("diagnostics") or 0),
        "signal_count": int(file.get("signal_count") or 0),
        "top_score": int(file.get("top_score") or 0),
        "cluster_count": len(file.get("clusters") or []),
        "signal_kinds": file.get("signal_kinds") or {},
        "actionable_signal_count": int(file.get("actionable_signal_count") or 0),
        "actionable_top_score": int(file.get("actionable_top_score") or 0),
        "actionable_cluster_count": len(file.get("actionable_clusters") or []),
        "actionable_signal_kinds": file.get("actionable_signal_kinds") or {},
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--database", type=Path, default=DEFAULT_DB)
    parser.add_argument("--sus-scan", type=Path, default=DEFAULT_SUS)
    parser.add_argument("--sample-per-stratum", type=int, default=20)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    db = sqlite3.connect(args.database)
    rows = select_rows(db, args.sample_per_stratum)
    db.close()
    results = [scan(args.sus_scan, row) for row in rows]
    by = collections.defaultdict(
        lambda: {
            "sampled": 0,
            "errors": 0,
            "raw_hits": 0,
            "actionable_hits": 0,
            "top_score_max": 0,
            "actionable_top_score_max": 0,
            "signal_kinds": collections.Counter(),
            "actionable_signal_kinds": collections.Counter(),
        }
    )
    misses = []
    for row in results:
        bucket = by[row["stratum"]]
        bucket["sampled"] += 1
        if row.get("error"):
            bucket["errors"] += 1
            continue
        bucket["top_score_max"] = max(bucket["top_score_max"], row["top_score"])
        bucket["actionable_top_score_max"] = max(
            bucket["actionable_top_score_max"], row["actionable_top_score"]
        )
        bucket["signal_kinds"].update(row["signal_kinds"])
        bucket["actionable_signal_kinds"].update(row["actionable_signal_kinds"])
        if row["top_score"] > 0 or row["signal_count"] > 0 or row["fatal_error"]:
            bucket["raw_hits"] += 1
        if (
            row["actionable_top_score"] > 0
            or row["actionable_signal_count"] > 0
            or row["fatal_error"]
        ):
            bucket["actionable_hits"] += 1
            if row["stratum"].startswith("boring-"):
                misses.append(row)

    serial = {}
    for name, bucket in sorted(by.items()):
        serial[name] = {
            key: value
            for key, value in bucket.items()
            if key not in {"signal_kinds", "actionable_signal_kinds"}
        }
        serial[name]["signal_kinds"] = dict(bucket["signal_kinds"].most_common(20))
        serial[name]["actionable_signal_kinds"] = dict(
            bucket["actionable_signal_kinds"].most_common(20)
        )
    report = {
        "schema": "js-redox-corpus-classifier-sample/v2",
        "sample_per_stratum": args.sample_per_stratum,
        "strata": serial,
        "boring_actionable_hits": len(misses),
        "boring_actionable_hit_examples": sorted(
            misses,
            key=lambda row: (
                -row.get("actionable_top_score", 0),
                -row.get("actionable_signal_count", 0),
                row["sha256"],
            ),
        )[:50],
    }
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
