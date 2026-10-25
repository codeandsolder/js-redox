#!/usr/bin/env python3
import base64
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL_ROOT = ROOT / ".cargo-target-nodebug/debug"
WORK = ROOT / "work/har-content-classification-regression"
HAR = WORK / "fixture.har"
PROJECT = WORK / "project"


def run(*args):
    cp = subprocess.run(
        [str(x) for x in args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=120,
    )
    if cp.returncode:
        raise RuntimeError(
            f"{' '.join(map(str, args))} failed {cp.returncode}:\n{cp.stdout}\n{cp.stderr}"
        )
    return cp


def entry(
    url: str,
    mime: str,
    raw: bytes,
    *,
    resource_type: str = "script",
    failure=None,
    response_headers=None,
    body_ref=None,
    method: str = "GET",
    status: int = 200,
):
    headers = [{"name": "content-type", "value": mime}]
    if response_headers:
        headers.extend(response_headers)
    response = {
        "status": status,
        "statusText": "OK",
        "httpVersion": "HTTP/2",
        "headers": headers,
        "cookies": [],
        "content": {
            "size": len(raw),
            "mimeType": mime,
            "text": base64.b64encode(raw).decode("ascii"),
            "encoding": "base64",
        },
        "redirectURL": "",
        "headersSize": -1,
        "bodySize": len(raw),
    }
    if body_ref is not None:
        response["_jsRedoxBody"] = body_ref
        response["_jsRedoxBodyCapture"] = {
            "status": "captured",
            "channel": "fixture-sidecar",
        }
    return {
        "startedDateTime": "2026-10-08T00:00:00.000Z",
        "time": 1,
        "request": {
            "method": method,
            "url": url,
            "httpVersion": "HTTP/2",
            "headers": [],
            "queryString": [],
            "cookies": [],
            "headersSize": -1,
            "bodySize": 0,
        },
        "response": response,
        "cache": {},
        "timings": {"send": 0, "wait": 1, "receive": 0},
        "_resourceType": resource_type,
        "_failure": failure,
    }


def main():
    shutil.rmtree(WORK, ignore_errors=True)
    (WORK / "bodies").mkdir(parents=True)

    xssi = b'for (;;);{"payload":{"value":42}}'
    html = b"<!doctype html><html><body>not javascript</body></html>"
    html_fragment = b'<script src="https://cdn.invalid/not-code.js"></script>'
    cp1252_js = b"// Copyright \xa9 2012\nwindow.legacy = 'ok';\n"
    incomplete_js = b"function half(){ return {value: 1"
    invalid_js = b"function broken(){ return (1 + 2; }"
    plain_error = b"upstream connect error before headers: Connection refused"
    normal_js = b"export const answer = 42;\n"

    sidecar_path = WORK / "bodies/legacy-sidecar"
    sidecar_path.write_bytes(cp1252_js)
    sidecar_ref = {
        "path": "bodies/legacy-sidecar",
        "sha256": hashlib.sha256(cp1252_js).hexdigest(),
        "size": len(cp1252_js),
    }

    entries = [
        entry(
            "https://fixture.invalid/api/bootstrap.js",
            "application/javascript",
            xssi,
            resource_type="xhr",
        ),
        entry(
            "https://fixture.invalid/assets/error-page.js",
            "application/javascript",
            html,
        ),
        entry(
            "https://fixture.invalid/assets/html-fragment.js",
            "application/javascript",
            html_fragment,
        ),
        entry(
            "https://fixture.invalid/assets/legacy.js",
            "application/javascript; charset=iso-8859-1",
            b"THIS HAR TEXT MUST NOT WIN",
            body_ref=sidecar_ref,
        ),
        entry(
            "https://fixture.invalid/assets/incomplete.js",
            "application/javascript",
            incomplete_js,
            failure={"errorText": "net::ERR_NETWORK_CHANGED"},
        ),
        entry(
            "https://fixture.invalid/assets/invalid.js",
            "application/javascript",
            invalid_js,
        ),
        entry(
            "https://fixture.invalid/assets/proxy-error.js",
            "application/javascript",
            plain_error,
        ),
        entry(
            "https://fixture.invalid/assets/app.js",
            "application/javascript",
            normal_js,
        ),
        entry(
            "https://fixture.invalid/probe.wasm",
            "application/wasm",
            b"",
            resource_type="fetch",
            method="HEAD",
            failure={"errorText": "net::ERR_ABORTED"},
        ),
        entry(
            "https://fixture.invalid/redirect.wasm",
            "application/wasm",
            b"",
            resource_type="fetch",
            status=302,
        ),
    ]
    fixture = {
        "log": {
            "version": "1.2",
            "creator": {"name": "js-redox classification regression", "version": "1"},
            "pages": [],
            "entries": entries,
        }
    }
    HAR.write_text(json.dumps(fixture), encoding="utf-8")

    run(TOOL_ROOT / "har-project", HAR, "--output", PROJECT)
    run(
        "uv",
        "run",
        "--no-project",
        "python",
        "scripts/materialize-capture-source.py",
        PROJECT,
        "--formatter",
        TOOL_ROOT / "js-format",
        "--jobs",
        "4",
    )

    manifest = json.loads((PROJECT / "capture-manifest.json").read_text())
    resources = {row["url"]: row for row in manifest["resources"]}

    xssi_row = resources["https://fixture.invalid/api/bootstrap.js"]
    assert xssi_row["transport_kind"] == "javascript"
    assert xssi_row["kind"] == "json"
    assert (PROJECT / xssi_row["output_path"]).read_bytes() == xssi

    html_row = resources["https://fixture.invalid/assets/error-page.js"]
    assert html_row["transport_kind"] == "javascript"
    assert html_row["kind"] == "html"
    assert (PROJECT / html_row["output_path"]).read_bytes() == html

    fragment_row = resources["https://fixture.invalid/assets/html-fragment.js"]
    assert fragment_row["transport_kind"] == "javascript"
    assert fragment_row["kind"] == "html"
    assert (PROJECT / fragment_row["output_path"]).read_bytes() == html_fragment

    legacy_row = resources["https://fixture.invalid/assets/legacy.js"]
    assert legacy_row["kind"] == "javascript"
    assert legacy_row["body_bytes"] == len(cp1252_js)
    assert legacy_row["sha256"] == hashlib.sha256(cp1252_js).hexdigest()
    assert (PROJECT / legacy_row["output_path"]).read_bytes() == cp1252_js

    incomplete_row = resources["https://fixture.invalid/assets/incomplete.js"]
    assert incomplete_row["kind"] == "javascript"
    assert incomplete_row["body_complete"] is False
    assert incomplete_row["network_failure"]["errorText"] == "net::ERR_NETWORK_CHANGED"

    normal_row = resources["https://fixture.invalid/assets/app.js"]
    assert normal_row["body_expected"] is True
    assert normal_row["body_complete"] is True

    head_row = resources["https://fixture.invalid/probe.wasm"]
    assert head_row["body_expected"] is False
    assert head_row["body_complete"] is True
    assert head_row["network_failure"]["errorText"] == "net::ERR_ABORTED"

    redirect_row = resources["https://fixture.invalid/redirect.wasm"]
    assert redirect_row["body_expected"] is False
    assert redirect_row["body_complete"] is True

    error_row = resources["https://fixture.invalid/assets/proxy-error.js"]
    assert error_row["transport_kind"] == "javascript"
    assert error_row["kind"] == "text"

    source_index = json.loads((PROJECT / "analysis/source-index.json").read_text())
    by_id = {row["resource_id"]: row for row in source_index["units"]}

    xssi_source = by_id[xssi_row["id"]]
    assert xssi_source["kind"] == "json"
    assert xssi_source["transform"] == "json_xssi_unwrapped"
    normalized_xssi = json.loads((PROJECT / xssi_source["source_path"]).read_text())
    assert normalized_xssi == {"payload": {"value": 42}}

    legacy_source = by_id[legacy_row["id"]]
    assert legacy_source["kind"] == "javascript"
    assert legacy_source["formatted"] is True
    assert legacy_source["source_encoding"] == "cp1252"
    assert "Copyright © 2012" in (PROJECT / legacy_source["source_path"]).read_text()

    incomplete_source = by_id[incomplete_row["id"]]
    assert incomplete_source["kind"] == "incomplete"
    assert incomplete_source["source_path"] is None
    assert incomplete_source["transform"] == "skipped_incomplete_network_response"

    invalid_row = resources["https://fixture.invalid/assets/invalid.js"]
    invalid_source = by_id[invalid_row["id"]]
    assert invalid_source["kind"] == "javascript_unparsed"
    assert invalid_source["formatted"] is False
    assert invalid_source["format_error"]

    normal_row = resources["https://fixture.invalid/assets/app.js"]
    normal_source = by_id[normal_row["id"]]
    assert normal_source["kind"] == "javascript"
    assert normal_source["formatted"] is True

    summary = source_index["summary"]
    assert summary["javascript_units"] == 2
    assert summary["unparsed_javascript_units"] == 1
    assert summary["incomplete_network_units"] == 1
    assert summary["captured_javascript_units"] == 3

    print("PASS: HAR content classification, raw provenance, charset decoding, and quarantine")


if __name__ == "__main__":
    main()
