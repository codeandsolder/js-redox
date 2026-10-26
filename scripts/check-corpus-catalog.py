#!/usr/bin/env python3
from __future__ import annotations

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
        db = work / "catalog.sqlite"
        candidates = work / "candidates"
        summary = work / "summary.json"
        command = [sys.executable, str(BUILDER), "--captures", str(captures), "--database", str(db), "--candidate-dir", str(candidates), "--summary", str(summary), "--jobs", "1"]
        subprocess.run(command, check=True, stdout=subprocess.PIPE, text=True)
        report = json.loads(summary.read_text())
        assert report["captures"] == 2, report
        assert report["current_unique_bodies"] == 2, report
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
        assert len((candidates / "dynamic-code.txt").read_text().splitlines()) == 1
        assert len((candidates / "obfuscation.txt").read_text().splitlines()) == 1
        assert len((candidates / "interesting.txt").read_text().splitlines()) == 1
        connection.close()

        subprocess.run(command, check=True, stdout=subprocess.PIPE, text=True)
        second = json.loads(summary.read_text())
        assert second["new_scans"] == 0, second
        assert second["cached_scans_reused"] == 2, second
        print("PASS: incremental corpus catalog stores per-hash provenance, features, nuisance labels, candidate sets, and reuses cached scans")


if __name__ == "__main__":
    main()
