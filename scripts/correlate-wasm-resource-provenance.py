#!/usr/bin/env python3
"""Correlate exact captured WASM responses with their observed CDP script initiators."""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path

from analysis_artifacts import WASM_RESOURCE_PROVENANCE, write_artifact
from capture_project import load_manifest


def cdp_session(row: dict) -> str:
    return str(row.get("cdpSession") or "main")


def is_wasm_response(url: object, mime_type: object) -> bool:
    if not isinstance(url, str):
        return False
    mime = str(mime_type or "").lower()
    return mime == "application/wasm" or ".wasm" in url.lower().split("#", 1)[0]


def captured_runtime_scripts(capture: Path) -> dict[tuple[str, str], dict]:
    path = capture / "runtime-scripts.json"
    if not path.is_file():
        return {}
    try:
        events = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return {}
    out: dict[tuple[str, str], dict] = {}
    conflicts: set[tuple[str, str]] = set()
    for event in events if isinstance(events, list) else []:
        script_id = event.get("scriptId")
        captured = event.get("captured") or {}
        if script_id is None or captured.get("kind") != "javascript" or not captured.get("sha256"):
            continue
        key = (cdp_session(event), str(script_id))
        candidate = {
            "sha256": captured["sha256"],
            "path": captured.get("path"),
            "url": event.get("url"),
        }
        if key in conflicts:
            continue
        previous = out.get(key)
        if previous is not None and previous["sha256"] != candidate["sha256"]:
            conflicts.add(key)
            out.pop(key, None)
            continue
        out[key] = candidate
    return out


def normalized_frames(initiator: dict) -> list[dict]:
    stack = initiator.get("stack") or {}
    frames = []
    for frame in stack.get("callFrames") or []:
        frames.append(
            {
                "function_name": frame.get("functionName"),
                "script_id": None if frame.get("scriptId") is None else str(frame.get("scriptId")),
                "url": frame.get("url") or None,
                "line_number": frame.get("lineNumber"),
                "column_number": frame.get("columnNumber"),
            }
        )
    return frames


def unavailable_result(reason: str) -> dict:
    return {
        "schema": WASM_RESOURCE_PROVENANCE.schema,
        "observations": [],
        "unmatched": [],
        "summary": {
            "observations": 0,
            "unique_wasm_sha256": 0,
            "script_initiators": 0,
            "runtime_script_identities": 0,
            "captured_script_url_matches": 0,
            "direct_body_identities": 0,
            "url_unique_body_identities": 0,
            "unmatched_wasm_events": 0,
            "unmatched_reasons": {},
            "applicable": False,
            "unavailable_reason": reason,
        },
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("project", type=Path)
    args = ap.parse_args()

    project = args.project.resolve()
    manifest = load_manifest(project)
    source = manifest["source"]
    observations: list[dict] = []
    unmatched: list[dict] = []

    if source.get("kind") != "recorder":
        write_artifact(
            project, WASM_RESOURCE_PROVENANCE, unavailable_result("not_recorder_capture")
        )
        print("WASM runtime provenance: not a recorder capture")
        return

    capture = Path(source["input"]).resolve()
    cdp_path = capture / "cdp-streams.json"
    if not cdp_path.is_file():
        write_artifact(
            project, WASM_RESOURCE_PROVENANCE, unavailable_result("missing_cdp_stream")
        )
        print(f"WASM runtime provenance: unavailable (missing {cdp_path})")
        return
    try:
        cdp_rows = json.loads(cdp_path.read_text())
    except (OSError, json.JSONDecodeError):
        write_artifact(
            project, WASM_RESOURCE_PROVENANCE, unavailable_result("invalid_cdp_stream")
        )
        print(f"WASM runtime provenance: unavailable (invalid {cdp_path})")
        return
    if not isinstance(cdp_rows, list):
        write_artifact(
            project, WASM_RESOURCE_PROVENANCE, unavailable_result("invalid_cdp_stream_shape")
        )
        print(f"WASM runtime provenance: unavailable (non-array {cdp_path})")
        return

    wasm_resources: dict[tuple[str, str], list[int]] = defaultdict(list)
    wasm_resources_by_url: dict[str, list[dict]] = defaultdict(list)
    js_resources_by_url: dict[str, list[int]] = defaultdict(list)
    for resource in manifest.get("resources", []):
        url = resource.get("url")
        digest = resource.get("sha256")
        if resource.get("kind") == "wasm" and isinstance(url, str):
            wasm_resources_by_url[url].append(resource)
            if (
                resource.get("body_present")
                and resource.get("body_complete")
                and isinstance(digest, str)
            ):
                wasm_resources[(url, digest)].append(int(resource["id"]))
        if resource.get("kind") == "javascript" and url:
            js_resources_by_url[str(url)].append(int(resource["id"]))

    cdp_wasm_counts = Counter(
        row.get("url")
        for row in cdp_rows
        if isinstance(row, dict) and is_wasm_response(row.get("url"), row.get("mimeType"))
    )
    runtime_scripts = captured_runtime_scripts(capture)
    for row in cdp_rows:
        if not isinstance(row, dict):
            continue
        url = row.get("url")
        if not is_wasm_response(url, row.get("mimeType")) or not isinstance(url, str):
            continue

        body = row.get("body") or {}
        digest = body.get("sha256") if isinstance(body, dict) else None
        response_identity_basis = None
        resource_ids: list[int] = []
        if isinstance(digest, str):
            resource_ids = sorted(set(wasm_resources.get((url, digest), [])))
            if not resource_ids:
                unmatched.append(
                    {
                        "cdp_session": cdp_session(row),
                        "request_id": row.get("requestId"),
                        "url": url,
                        "sha256": digest,
                        "reason": "no_exact_project_wasm_resource",
                    }
                )
                continue
            response_identity_basis = "cdp_body_sha256"
        else:
            project_rows = wasm_resources_by_url.get(url, [])
            if not project_rows:
                unmatched.append(
                    {
                        "cdp_session": cdp_session(row),
                        "request_id": row.get("requestId"),
                        "url": url,
                        "sha256": None,
                        "reason": "no_project_wasm_resource_for_url",
                    }
                )
                continue
            if cdp_wasm_counts[url] != len(project_rows):
                unmatched.append(
                    {
                        "cdp_session": cdp_session(row),
                        "request_id": row.get("requestId"),
                        "url": url,
                        "sha256": None,
                        "reason": "request_cardinality_mismatch",
                    }
                )
                continue
            if any(
                not resource.get("body_present")
                or not resource.get("body_complete")
                or not isinstance(resource.get("sha256"), str)
                for resource in project_rows
            ):
                unmatched.append(
                    {
                        "cdp_session": cdp_session(row),
                        "request_id": row.get("requestId"),
                        "url": url,
                        "sha256": None,
                        "reason": "incomplete_project_wasm_body_capture",
                    }
                )
                continue
            digests = {str(resource["sha256"]) for resource in project_rows}
            if len(digests) != 1:
                unmatched.append(
                    {
                        "cdp_session": cdp_session(row),
                        "request_id": row.get("requestId"),
                        "url": url,
                        "sha256": None,
                        "reason": "ambiguous_project_wasm_bodies_for_url",
                    }
                )
                continue
            digest = next(iter(digests))
            resource_ids = sorted(int(resource["id"]) for resource in project_rows)
            response_identity_basis = "unique_url_body_and_request_cardinality"
            if not isinstance(body, dict) or body.get("size") is None:
                body = {"size": project_rows[0].get("body_bytes")}

        initiator = row.get("initiator") or {}
        frames = normalized_frames(initiator) if isinstance(initiator, dict) else []
        primary = frames[0] if frames else None
        runtime_identity = None
        initiator_resource_ids: list[int] = []
        if primary is not None:
            script_id = primary.get("script_id")
            if script_id is not None:
                runtime_identity = runtime_scripts.get((cdp_session(row), script_id))
            if primary.get("url"):
                initiator_resource_ids = sorted(
                    set(js_resources_by_url.get(str(primary["url"]), []))
                )

        observations.append(
            {
                "cdp_session": cdp_session(row),
                "request_id": row.get("requestId"),
                "url": url,
                "sha256": digest,
                "byte_len": body.get("size") if isinstance(body, dict) else None,
                "wasm_resource_ids": resource_ids,
                "initiator_type": initiator.get("type") if isinstance(initiator, dict) else None,
                "initiator_frames": frames,
                "primary_initiator": primary,
                "initiator_runtime_sha256": (
                    runtime_identity.get("sha256") if runtime_identity is not None else None
                ),
                "initiator_runtime_path": (
                    runtime_identity.get("path") if runtime_identity is not None else None
                ),
                "initiator_resource_ids": initiator_resource_ids,
                "evidence": "cdp_network_response_initiator",
                "response_identity_basis": response_identity_basis,
                "runtime_observed": True,
                "exact_response_identity": True,
            }
        )

    observations.sort(
        key=lambda row: (
            row["cdp_session"],
            str(row.get("request_id") or ""),
            row["url"],
            row["sha256"],
        )
    )
    unmatched.sort(key=lambda row: (row["cdp_session"], str(row.get("request_id") or ""), row["url"]))
    summary = {
        "observations": len(observations),
        "unique_wasm_sha256": len({row["sha256"] for row in observations}),
        "script_initiators": sum(row["initiator_type"] == "script" for row in observations),
        "runtime_script_identities": sum(bool(row["initiator_runtime_sha256"]) for row in observations),
        "captured_script_url_matches": sum(bool(row["initiator_resource_ids"]) for row in observations),
        "direct_body_identities": sum(row["response_identity_basis"] == "cdp_body_sha256" for row in observations),
        "url_unique_body_identities": sum(
            row["response_identity_basis"] == "unique_url_body_and_request_cardinality"
            for row in observations
        ),
        "unmatched_wasm_events": len(unmatched),
        "unmatched_reasons": dict(sorted(Counter(row["reason"] for row in unmatched).items())),
        "applicable": True,
    }
    result = {
        "schema": WASM_RESOURCE_PROVENANCE.schema,
        "observations": observations,
        "unmatched": unmatched,
        "summary": summary,
    }
    write_artifact(project, WASM_RESOURCE_PROVENANCE, result)
    print(
        "WASM runtime provenance: "
        f"{summary['observations']} exact response observation(s), "
        f"{summary['runtime_script_identities']} exact runtime initiator(s), "
        f"{summary['unmatched_wasm_events']} unmatched"
    )


if __name__ == "__main__":
    main()
