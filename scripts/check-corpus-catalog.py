#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import sqlite3
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUILDER = ROOT / "scripts/build-corpus-catalog.py"


def write_capture(root: Path, name: str, network_rows: list[dict], runtime_rows: list[dict]) -> None:
    capture = root / name
    (capture / "resources").mkdir(parents=True)
    (capture / "runtime-scripts").mkdir()
    (capture / "recorder-manifest.json").write_text("{}\n")
    for row in network_rows:
        body = row["body"]
        (capture / body["path"]).write_bytes(body.pop("_raw"))
    for row in runtime_rows:
        body = row["captured"]
        (capture / body["path"]).write_bytes(body.pop("_raw"))
    (capture / "network.json").write_text(json.dumps(network_rows))
    (capture / "runtime-scripts.json").write_text(json.dumps(runtime_rows))


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="js-redox-catalog-") as tmp:
        work = Path(tmp)
        captures = work / "captures"
        captures.mkdir()
        js = b"while(true){switch(x){case 1:eval(atob('" + b"Q" * 300 + b"'));break;}}"
        js_hash = "a" * 64
        write_capture(
            captures,
            "0001-popunder-ads-0123456789",
            [{"url":"https://ads.example/a.js","resourceType":"Script","mimeType":"application/javascript","body":{"sha256":js_hash,"path":"resources/a.js","size":len(js),"_raw":js}}],
            [],
        )
        write_capture(
            captures,
            "0002-support-ai-soc2-abcdef0123",
            [{"url":"https://chat.example/a.js","resourceType":"Script","mimeType":"application/javascript","body":{"sha256":js_hash,"path":"resources/a.js","size":len(js),"_raw":js}}],
            [{"url":"","captured":{"kind":"javascript","sha256":"b"*64,"path":"runtime-scripts/"+"b"*64+".js","size":2,"_raw":b"[]"}}],
        )
        raw_legacy = b"// Copyright \xa9 2013\nconst decoded = 1;\n"
        browser_source = raw_legacy.decode("utf-8", errors="replace").encode("utf-8")
        raw_legacy_hash = hashlib.sha256(raw_legacy).hexdigest()
        browser_source_hash = hashlib.sha256(browser_source).hexdigest()
        write_capture(
            captures,
            "0003-legacy-script-fedcba9876",
            [{"url":"https://legacy.example/client.js","resourceType":"Script","mimeType":"application/javascript","body":{"sha256":raw_legacy_hash,"path":"resources/client.js","size":len(raw_legacy),"_raw":raw_legacy}}],
            [{"url":"https://legacy.example/client.js","captured":{"kind":"javascript","sha256":browser_source_hash,"path":"runtime-scripts/"+browser_source_hash+".js","size":len(browser_source),"_raw":browser_source}}],
        )
        raw_cp1252 = b"// legacy \x81\xa9\nconst legacy = 1;\n"
        browser_cp1252 = b"// legacy \xc2\x81\xc2\xa9\nconst legacy = 1;\n"
        raw_cp1252_hash = hashlib.sha256(raw_cp1252).hexdigest()
        browser_cp1252_hash = hashlib.sha256(browser_cp1252).hexdigest()
        write_capture(
            captures,
            "0004-legacy-cp1252-0011223344",
            [{"url":"https://legacy.example/cp1252.js","resourceType":"Script","mimeType":"application/javascript","body":{"sha256":raw_cp1252_hash,"path":"resources/cp1252.js","size":len(raw_cp1252),"_raw":raw_cp1252}}],
            [{"url":"https://legacy.example/cp1252.js","captured":{"kind":"javascript","sha256":browser_cp1252_hash,"path":"runtime-scripts/"+browser_cp1252_hash+".js","size":len(browser_cp1252),"_raw":browser_cp1252}}],
        )
        db = work / "catalog.sqlite"
        candidates = work / "candidates"
        summary = work / "summary.json"
        command = [sys.executable, str(BUILDER), "--captures", str(captures), "--database", str(db), "--candidate-dir", str(candidates), "--summary", str(summary), "--jobs", "1"]
        subprocess.run(command, check=True, stdout=subprocess.PIPE, text=True)
        report = json.loads(summary.read_text())
        assert report["captures"] == 4, report
        assert report["current_unique_bodies"] == 6, report
        connection = sqlite3.connect(db)
        row = connection.execute("SELECT capture_count, cohort_count, domain_count, runtime_present FROM current_body WHERE sha256=?", (js_hash,)).fetchone()
        assert row == (2, 2, 2, 0), row
        features = dict(connection.execute("SELECT feature,count FROM body_feature WHERE sha256=?", (js_hash,)))
        assert features["eval_call"] == 1, features
        assert features["base64_blob"] >= 1, features
        assert features["flattening_shape"] == 1, features
        assert features["encoded_payload_shape"] == 1, features
        nuisance = connection.execute("SELECT nuisance FROM body_scan WHERE sha256=?", ("b"*64,)).fetchone()[0]
        assert nuisance == "trivial_anonymous_expression", nuisance
        edge = connection.execute(
            "SELECT browser_sha256,evidence FROM body_representation_edge WHERE transport_sha256=?",
            (raw_legacy_hash,),
        ).fetchone()
        assert edge == (browser_source_hash, "exact:utf8-replacement"), edge
        cp1252_edge = connection.execute(
            "SELECT browser_sha256,evidence FROM body_representation_edge WHERE transport_sha256=?",
            (raw_cp1252_hash,),
        ).fetchone()
        assert cp1252_edge == (browser_cp1252_hash, "exact:windows-1252"), cp1252_edge
        javascript_paths = (candidates / "javascript.txt").read_text().splitlines()
        assert str(captures / "0003-legacy-script-fedcba9876/resources/client.js") not in javascript_paths
        assert str(captures / "0003-legacy-script-fedcba9876/runtime-scripts" / f"{browser_source_hash}.js") in javascript_paths
        assert len((candidates / "dynamic-code.txt").read_text().splitlines()) == 1
        assert len((candidates / "obfuscation.txt").read_text().splitlines()) == 1
        assert len((candidates / "interesting.txt").read_text().splitlines()) == 1
        runs = [
            ("p1", "2026-10-26T00:00:01+00:00", 20, 8, 2, 1),
            ("p2", "2026-10-26T00:00:02+00:00", 0, 0, 0, 5),
            ("p3", "2026-10-26T00:00:03+00:00", 15, 6, 1, 7),
        ]
        for pipeline_id, observed_at, top_score, signal_count, cluster_count, transform_total in runs:
            connection.execute(
                "INSERT INTO body_analysis_run VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (js_hash, "safe-deob+sus/v1", pipeline_id, observed_at, str(captures / "0001-popunder-ads-0123456789/resources/a.js"),
                 js_hash, len(js), 1, 2, transform_total, "{}", None, 0, 0,
                 signal_count, cluster_count, top_score, "{}",
                 signal_count, cluster_count, top_score, "{}"),
            )
        connection.commit()
        best = connection.execute("SELECT pipeline_id,actionable_top_score,actionable_signal_count FROM body_analysis_best WHERE sha256=?", (js_hash,)).fetchone()
        latest = connection.execute("SELECT pipeline_id,actionable_top_score,actionable_signal_count FROM body_analysis_latest WHERE sha256=?", (js_hash,)).fetchone()
        assert best == ("p2", 0, 0), best
        assert latest == ("p3", 15, 6), latest
        connection.close()

        subprocess.run(command, check=True, stdout=subprocess.PIPE, text=True)
        second = json.loads(summary.read_text())
        assert second["new_scans"] == 0, second
        assert second["cached_scans_reused"] == 6, second
        assert len((candidates / "known-zero.txt").read_text().splitlines()) == 1
        assert len((candidates / "regressed-from-best.txt").read_text().splitlines()) == 1
        assert len((candidates / "llm-review-zero.txt").read_text().splitlines()) == 0
        assert len((candidates / "quick-focus.txt").read_text().splitlines()) == 1
        print("PASS: incremental corpus catalog stores per-hash provenance, features, best/latest analysis progress, candidate sets, and reuses cached scans")


if __name__ == "__main__":
    main()
