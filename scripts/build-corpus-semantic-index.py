#!/usr/bin/env python3
"""Incrementally cache parser-level sus-scan summaries for every current JavaScript body."""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import sqlite3
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = ROOT / "work/scum-corpus-20261007"
DEFAULT_DB = DEFAULT_CORPUS / "preclass/corpus.sqlite"
DEFAULT_CANDIDATES = DEFAULT_CORPUS / "preclass/candidates"
DEFAULT_SUS = ROOT / ".cargo-target-nodebug/release/sus-scan"
SEMANTIC_CONTRACT = "js-sus-scan/v3"
PREVIOUS_SEMANTIC_CONTRACT = "js-sus-scan/v2"


def utc_now() -> str:
    return dt.datetime.now(dt.UTC).isoformat(timespec="microseconds")


def ensure_schema(db: sqlite3.Connection) -> None:
    db.executescript("""
        CREATE TABLE IF NOT EXISTS body_semantic_scan (
          sha256 TEXT NOT NULL,
          scan_contract TEXT NOT NULL,
          scanned_at TEXT NOT NULL,
          diagnostics INTEGER NOT NULL,
          fatal_error INTEGER NOT NULL,
          raw_signal_count INTEGER NOT NULL,
          raw_cluster_count INTEGER NOT NULL,
          raw_top_score INTEGER NOT NULL,
          raw_signal_kinds_json TEXT NOT NULL,
          actionable_signal_count INTEGER NOT NULL,
          actionable_cluster_count INTEGER NOT NULL,
          actionable_top_score INTEGER NOT NULL,
          actionable_signal_kinds_json TEXT NOT NULL,
          PRIMARY KEY (sha256, scan_contract)
        );
        CREATE INDEX IF NOT EXISTS semantic_contract_idx
          ON body_semantic_scan(scan_contract, sha256);
        CREATE INDEX IF NOT EXISTS semantic_actionable_idx
          ON body_semantic_scan(scan_contract, fatal_error, actionable_top_score, actionable_signal_count);
        CREATE TABLE IF NOT EXISTS body_representation_edge (
          transport_sha256 TEXT NOT NULL, browser_sha256 TEXT NOT NULL,
          capture TEXT NOT NULL, url TEXT NOT NULL, evidence TEXT NOT NULL,
          PRIMARY KEY (transport_sha256, browser_sha256, capture, url)
        ) WITHOUT ROWID;
    """)
    columns = {row[1] for row in db.execute("PRAGMA table_info(body_semantic_scan)")}
    additions = {
        "decode_encoding": "TEXT NOT NULL DEFAULT 'UTF-8'",
        "decode_source": "TEXT NOT NULL DEFAULT 'legacy'",
        "decode_had_errors": "INTEGER NOT NULL DEFAULT 0",
        "decode_uncertain": "INTEGER NOT NULL DEFAULT 0",
    }
    for name, declaration in additions.items():
        if name not in columns:
            db.execute(f"ALTER TABLE body_semantic_scan ADD COLUMN {name} {declaration}")


def migrate_previous_contract(db: sqlite3.Connection) -> int:
    """Carry forward v2 rows whose decoding semantics provably did not change.

    v2 only reached a non-fatal report through strict UTF-8 decoding. Therefore
    every non-fatal v2 row has the same source text under v3 and can be copied
    without re-running the scanner. Fatal rows are deliberately re-scanned:
    they include both genuine parser failures and the old invalid-UTF-8 cases.
    """
    before = db.total_changes
    with db:
        db.execute(
            """
            INSERT OR IGNORE INTO body_semantic_scan (
              sha256,scan_contract,scanned_at,diagnostics,fatal_error,
              raw_signal_count,raw_cluster_count,raw_top_score,raw_signal_kinds_json,
              actionable_signal_count,actionable_cluster_count,actionable_top_score,
              actionable_signal_kinds_json,decode_encoding,decode_source,
              decode_had_errors,decode_uncertain
            )
            SELECT old.sha256,?,old.scanned_at,old.diagnostics,old.fatal_error,
                   old.raw_signal_count,old.raw_cluster_count,old.raw_top_score,old.raw_signal_kinds_json,
                   old.actionable_signal_count,old.actionable_cluster_count,old.actionable_top_score,
                   old.actionable_signal_kinds_json,'UTF-8','already-unicode',0,0
            FROM body_semantic_scan old
            WHERE old.scan_contract=? AND old.fatal_error=0
              AND EXISTS (SELECT 1 FROM current_body c WHERE c.sha256=old.sha256)
              AND NOT EXISTS (
                SELECT 1 FROM body_representation_edge e
                WHERE e.transport_sha256=old.sha256 AND e.evidence LIKE 'exact:%'
              )
            """,
            (SEMANTIC_CONTRACT, PREVIOUS_SEMANTIC_CONTRACT),
        )
    return db.total_changes - before


def emit_candidates(db: sqlite3.Connection, directory: Path) -> dict[str, int]:
    import importlib.util
    spec = importlib.util.spec_from_file_location("catalog_builder", ROOT / "scripts/build-corpus-catalog.py")
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load catalog builder")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.emit_candidates(db, directory)


def chunks(items: list[tuple[str, str]], size: int):
    for start in range(0, len(items), size):
        yield items[start:start + size]


def scan_chunk(binary: Path, chunk: list[tuple[str, str]]) -> list[dict]:
    paths = [path for _, path in chunk]
    cp = subprocess.run(
        [str(binary), "--json", *paths],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if cp.returncode:
        raise RuntimeError(f"sus-scan failed: {(cp.stderr or cp.stdout).strip()}")
    payload = json.loads(cp.stdout)
    if payload.get("schema") != SEMANTIC_CONTRACT:
        raise RuntimeError(f"unexpected sus-scan schema: {payload.get('schema')!r}")
    by_path = {str(Path(row["input"])): row for row in payload.get("files") or []}
    results = []
    scanned_at = utc_now()
    for digest, path in chunk:
        row = by_path.get(str(Path(path)))
        if row is None:
            raise RuntimeError(f"sus-scan omitted input: {path}")
        results.append(
            {
                "sha256": digest,
                "scan_contract": SEMANTIC_CONTRACT,
                "scanned_at": scanned_at,
                "decode_encoding": str(row.get("decode_encoding") or "UTF-8"),
                "decode_source": str(row.get("decode_source") or "legacy"),
                "decode_had_errors": int(bool(row.get("decode_had_errors"))),
                "decode_uncertain": int(bool(row.get("decode_uncertain"))),
                "diagnostics": int(row.get("diagnostics") or 0),
                "fatal_error": int(bool(row.get("fatal_error"))),
                "raw_signal_count": int(row.get("signal_count") or 0),
                "raw_cluster_count": len(row.get("clusters") or []),
                "raw_top_score": int(row.get("top_score") or 0),
                "raw_signal_kinds_json": json.dumps(row.get("signal_kinds") or {}, sort_keys=True, separators=(",", ":")),
                "actionable_signal_count": int(row.get("actionable_signal_count") or 0),
                "actionable_cluster_count": len(row.get("actionable_clusters") or []),
                "actionable_top_score": int(row.get("actionable_top_score") or 0),
                "actionable_signal_kinds_json": json.dumps(row.get("actionable_signal_kinds") or {}, sort_keys=True, separators=(",", ":")),
            }
        )
    return results


def store(db: sqlite3.Connection, rows: list[dict]) -> None:
    keys = (
        "sha256", "scan_contract", "scanned_at", "diagnostics", "fatal_error",
        "raw_signal_count", "raw_cluster_count", "raw_top_score", "raw_signal_kinds_json",
        "actionable_signal_count", "actionable_cluster_count", "actionable_top_score",
        "actionable_signal_kinds_json", "decode_encoding", "decode_source",
        "decode_had_errors", "decode_uncertain",
    )
    columns = ",".join(keys)
    placeholders = ",".join("?" for _ in keys)
    db.executemany(
        f"INSERT OR REPLACE INTO body_semantic_scan ({columns}) VALUES ({placeholders})",
        [tuple(row[key] for key in keys) for row in rows],
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--database", type=Path, default=DEFAULT_DB)
    parser.add_argument("--candidate-dir", type=Path, default=DEFAULT_CANDIDATES)
    parser.add_argument("--sus-scan", type=Path, default=DEFAULT_SUS)
    parser.add_argument("--chunk-size", type=int, default=256)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--nice", type=int, default=10)
    args = parser.parse_args()
    if args.chunk_size < 1:
        raise SystemExit("--chunk-size must be >= 1")
    if args.jobs < 1:
        raise SystemExit("--jobs must be >= 1")
    if args.nice:
        os.nice(args.nice)
    if not args.sus_scan.is_file():
        raise SystemExit(f"missing sus-scan binary: {args.sus_scan}")

    db = sqlite3.connect(args.database)
    ensure_schema(db)
    migrated = migrate_previous_contract(db)
    if migrated:
        print(f"semantic migrated={migrated} {PREVIOUS_SEMANTIC_CONTRACT}->{SEMANTIC_CONTRACT}", flush=True)
    pending = list(
        db.execute(
            """
            SELECT c.sha256,c.representative_path
            FROM current_body c JOIN body_scan s USING (sha256)
            WHERE s.content_kind LIKE 'javascript%' AND s.nuisance IS NULL
              AND NOT EXISTS (
                SELECT 1 FROM body_representation_edge e
                WHERE e.transport_sha256=c.sha256 AND e.evidence LIKE 'exact:%'
              )
              AND NOT EXISTS (
                SELECT 1 FROM body_semantic_scan ss
                WHERE ss.sha256=c.sha256 AND ss.scan_contract=?
              )
            ORDER BY c.sha256
            """,
            (SEMANTIC_CONTRACT,),
        )
    )
    if args.limit:
        pending = pending[:args.limit]
    print(f"semantic pending={len(pending)} contract={SEMANTIC_CONTRACT}", flush=True)
    done = 0
    work = list(chunks(pending, args.chunk_size))
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(scan_chunk, args.sus_scan, chunk): len(chunk) for chunk in work}
        for future in as_completed(futures):
            rows = future.result()
            with db:
                store(db, rows)
            done += len(rows)
            print(f"semantic {done}/{len(pending)} jobs={args.jobs}", flush=True)

    counts = emit_candidates(db, args.candidate_dir)
    totals = db.execute(
        """
        SELECT COUNT(*),
               SUM(fatal_error=0 AND actionable_top_score=0 AND actionable_signal_count=0),
               SUM(fatal_error!=0 OR actionable_top_score>0 OR actionable_signal_count>0)
        FROM body_semantic_scan ss JOIN current_body c USING (sha256)
        WHERE scan_contract=?
        """,
        (SEMANTIC_CONTRACT,),
    ).fetchone()
    report = {
        "schema": "js-redox-corpus-semantic-index/v1",
        "scan_contract": SEMANTIC_CONTRACT,
        "migrated_from_previous": migrated,
        "newly_scanned": done,
        "current_scanned": int(totals[0] or 0),
        "current_zero": int(totals[1] or 0),
        "current_actionable": int(totals[2] or 0),
        "decode_anomalies": int(db.execute(
            "SELECT COUNT(*) FROM body_semantic_scan WHERE scan_contract=? AND decode_had_errors!=0",
            (SEMANTIC_CONTRACT,),
        ).fetchone()[0]),
        "candidates": {
            name: counts[name]
            for name in ("semantic-actionable", "semantic-zero", "semantic-untested", "quick-focus")
            if name in counts
        },
    }
    print(json.dumps(report, indent=2))
    db.close()


if __name__ == "__main__":
    main()
