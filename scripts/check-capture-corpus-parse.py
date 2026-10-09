#!/usr/bin/env python3
import argparse
import collections
import json
import os
import re
import shutil
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PARSER = ROOT / ".cargo-target-nodebug/release/js-parse-batch"
CHARSET_RE = re.compile(r"charset\s*=\s*['\"]?([^;'\"\s]+)", re.IGNORECASE)
WEB_CHARSET_ALIASES = {
    "iso-8859-1": "cp1252",
    "iso8859-1": "cp1252",
    "latin1": "cp1252",
    "latin-1": "cp1252",
    "windows-1252": "cp1252",
    "utf8": "utf-8",
}
XSSI_PREFIXES = ("for (;;);", "for(;;);", "while (1);", "while(1);", ")]}'")
DATA_RESOURCE_TYPES = {"xhr", "fetch", "ping", "eventsource"}


def default_jobs() -> int:
    return max(1, min(16, (os.cpu_count() or 4) * 2))


def header_value(headers: dict, name: str) -> str | None:
    name = name.lower()
    for key, value in (headers or {}).items():
        if str(key).lower() == name:
            return str(value)
    return None


def declared_charset(row: dict) -> str | None:
    values = [row.get("mimeType") or "", header_value(row.get("responseHeaders") or {}, "content-type") or ""]
    for value in values:
        match = CHARSET_RE.search(value)
        if match:
            label = match.group(1).strip().lower()
            return WEB_CHARSET_ALIASES.get(label, label)
    return None


def decode_text(raw: bytes, row: dict) -> tuple[str, str, bool]:
    declared = declared_charset(row)
    encodings = []
    for encoding in (declared, "utf-8", "cp1252", "latin1"):
        if encoding and encoding not in encodings:
            encodings.append(encoding)
    for index, encoding in enumerate(encodings):
        try:
            return raw.decode(encoding), encoding, index > 0
        except (LookupError, UnicodeDecodeError):
            continue
    raise UnicodeDecodeError("utf-8", raw, 0, min(1, len(raw)), "no usable text decoding")


def strip_xssi_prefix(text: str) -> tuple[str, str | None]:
    stripped = text.lstrip("\ufeff \t\r\n")
    for prefix in XSSI_PREFIXES:
        if stripped.startswith(prefix):
            return stripped[len(prefix) :].lstrip("\r\n \t"), prefix
    return stripped, None


def looks_like_plain_text_error(text: str) -> bool:
    text = text.strip()
    if not text or len(text) > 512:
        return False
    if any(ord(c) < 32 and c not in "\t\r\n" for c in text):
        return False
    if 16 <= len(text) <= 128 and all(c in "0123456789abcdefABCDEF" for c in text):
        return True
    if any(c in text for c in "{}[]();="):
        return False
    return len(text.split()) >= 2


def transport_javascript(row: dict) -> bool:
    resource_type = (row.get("resourceType") or "").lower()
    mime = (row.get("mimeType") or "").lower()
    url = row.get("url") or ""
    path = urlparse(url).path.lower()
    return (
        resource_type == "script"
        or "javascript" in mime
        or "ecmascript" in mime
        or path.endswith((".js", ".mjs", ".cjs"))
    )


def classify_network_body(raw: bytes, row: dict) -> tuple[str, dict]:
    if not transport_javascript(row):
        return "not_javascript_transport", {}
    text, encoding, fallback = decode_text(raw, row)
    candidate, xssi = strip_xssi_prefix(text)
    lower_prefix = candidate[:256].lower()
    detail = {
        "encoding": encoding,
        "encoding_fallback": fallback,
        "declared_charset": declared_charset(row),
    }
    if lower_prefix.startswith(("<!doctype", "<html", "<head", "<body", "<script")):
        return "html", detail
    if lower_prefix.startswith(("<?xml", "<svg")):
        return "text", detail
    if xssi or candidate.startswith(("{", "[")):
        try:
            json.loads(candidate)
        except json.JSONDecodeError:
            pass
        else:
            detail["xssi_prefix"] = xssi
            return "json", detail
    resource_type = (row.get("resourceType") or "").lower()
    if resource_type in DATA_RESOURCE_TYPES:
        return "data_text", detail
    if looks_like_plain_text_error(candidate):
        return "plain_text", detail
    if row.get("failure"):
        return "incomplete_javascript", detail
    detail["text"] = text
    return "javascript", detail


def collect(capture_root: Path):
    network_groups = {}
    runtime_groups = {}
    bad_inputs = []
    manifests = sorted(capture_root.rglob("recorder-manifest.json"))

    for index, manifest in enumerate(manifests, 1):
        capture = manifest.parent
        network_path = capture / "network.json"
        if network_path.is_file():
            try:
                rows = json.loads(network_path.read_text(encoding="utf-8"))
            except Exception as exc:
                bad_inputs.append({"capture": capture.name, "file": "network.json", "error": repr(exc)})
                rows = []
            for row in rows:
                body = row.get("body") or {}
                digest = body.get("sha256")
                rel = body.get("path")
                if not digest or not rel:
                    continue
                path = capture / rel
                if not path.is_file():
                    bad_inputs.append({"capture": capture.name, "file": rel, "error": "missing body"})
                    continue
                group = network_groups.setdefault(digest, {
                    "sha256": digest,
                    "path": str(path),
                    "bytes": body.get("size") or path.stat().st_size,
                    "occurrences": 0,
                    "examples": [],
                    "classification_rows": [],
                    "classification_signatures": set(),
                })
                group["occurrences"] += 1
                compact = {
                    "capture": capture.name,
                    "url": row.get("url"),
                    "resourceType": row.get("resourceType"),
                    "mimeType": row.get("mimeType"),
                    "responseHeaders": row.get("responseHeaders") or {},
                    "status": row.get("status"),
                    "failure": row.get("failure"),
                }
                if len(group["examples"]) < 12:
                    group["examples"].append(compact)
                if transport_javascript(row):
                    signature = (
                        row.get("resourceType"),
                        row.get("mimeType"),
                        declared_charset(row),
                        bool(row.get("failure")),
                        urlparse(row.get("url") or "").path.rsplit(".", 1)[-1].lower(),
                    )
                    if signature not in group["classification_signatures"]:
                        group["classification_signatures"].add(signature)
                        group["classification_rows"].append(compact)

        runtime_path = capture / "runtime-scripts.json"
        if runtime_path.is_file():
            try:
                rows = json.loads(runtime_path.read_text(encoding="utf-8"))
            except Exception as exc:
                bad_inputs.append({"capture": capture.name, "file": "runtime-scripts.json", "error": repr(exc)})
                rows = []
            for row in rows:
                body = row.get("captured") or {}
                if body.get("kind") != "javascript":
                    continue
                digest = body.get("sha256") or row.get("hash")
                rel = body.get("path")
                if not digest or not rel:
                    continue
                path = capture / rel
                if not path.is_file():
                    bad_inputs.append({"capture": capture.name, "file": rel, "error": "missing runtime script"})
                    continue
                group = runtime_groups.setdefault(digest, {
                    "sha256": digest,
                    "path": str(path),
                    "bytes": body.get("size") or path.stat().st_size,
                    "occurrences": 0,
                    "examples": [],
                })
                group["occurrences"] += 1
                if len(group["examples"]) < 12:
                    group["examples"].append({
                        "capture": capture.name,
                        "url": row.get("url"),
                        "isModule": row.get("isModule"),
                    })

        if index % 250 == 0:
            print(
                f"collected {index}/{len(manifests)} captures: "
                f"network={len(network_groups)} runtime={len(runtime_groups)} unique",
                flush=True,
            )
    return manifests, network_groups, runtime_groups, bad_inputs


def prepare_candidates(network_groups, runtime_groups, work: Path):
    work.mkdir(parents=True, exist_ok=True)
    normalized = work / "normalized"
    shutil.rmtree(normalized, ignore_errors=True)
    normalized.mkdir()

    classifications = collections.Counter()
    classification_occurrences = collections.Counter()
    parse_groups = {}
    parse_digests = set()

    runtime_hashes = set(runtime_groups)
    for digest, group in network_groups.items():
        raw = Path(group["path"]).read_bytes()
        example_results = []
        best_js = None
        rows = group["classification_rows"] or group["examples"]
        for example in rows:
            category, detail = classify_network_body(raw, example)
            example_results.append((category, detail, example))
            if category == "javascript" and best_js is None:
                best_js = (detail, example)
        category = "javascript" if best_js else (example_results[0][0] if example_results else "not_javascript_transport")
        # If a body is observed as executable by Debugger, runtime truth wins over
        # transport metadata and it must be parse-checked as JavaScript.
        if digest in runtime_hashes:
            category = "javascript_runtime_confirmed"
        classifications[category] += 1
        classification_occurrences[category] += group["occurrences"]
        if category not in {"javascript", "javascript_runtime_confirmed"}:
            group["classification"] = category
            continue

        if digest in runtime_hashes:
            candidate_path = Path(runtime_groups[digest]["path"])
            encoding = "utf-8"
            fallback = False
            charset_hint = None
        else:
            detail, example = best_js
            text = detail.pop("text")
            encoding = detail["encoding"]
            fallback = detail["encoding_fallback"]
            charset_hint = detail["declared_charset"]
            if encoding == "utf-8" and not fallback:
                candidate_path = Path(group["path"])
            else:
                candidate_path = normalized / f"{digest}.js"
                candidate_path.write_text(text, encoding="utf-8")

        key = (digest, charset_hint)
        parse_groups[key] = {
            "sha256": digest,
            "path": str(candidate_path),
            "bytes": group["bytes"],
            "network_occurrences": group["occurrences"],
            "runtime_occurrences": runtime_groups.get(digest, {}).get("occurrences", 0),
            "encoding": encoding,
            "encoding_fallback": fallback,
            "declared_charset": charset_hint,
            "examples": group["examples"],
            "runtime_examples": runtime_groups.get(digest, {}).get("examples", []),
        }
        parse_digests.add(digest)

    for digest, group in runtime_groups.items():
        if digest in parse_digests:
            continue
        classifications["javascript_runtime_only"] += 1
        classification_occurrences["javascript_runtime_only"] += group["occurrences"]
        parse_groups[(digest, None)] = {
            "sha256": digest,
            "path": group["path"],
            "bytes": group["bytes"],
            "network_occurrences": 0,
            "runtime_occurrences": group["occurrences"],
            "encoding": "utf-8",
            "encoding_fallback": False,
            "declared_charset": None,
            "examples": [],
            "runtime_examples": group["examples"],
        }

    return parse_groups, classifications, classification_occurrences


def run_parser(parser: Path, parse_groups: dict, jobs: int, work: Path):
    groups = list(parse_groups.values())
    buckets = [[] for _ in range(max(1, jobs))]
    for index, group in enumerate(groups):
        buckets[index % len(buckets)].append(group)

    job_specs = []
    for index, bucket in enumerate(buckets):
        list_path = work / f"chunk-{index:02}.txt"
        fail_path = work / f"fail-{index:02}.jsonl"
        list_path.write_text("\n".join(group["path"] for group in bucket) + "\n", encoding="utf-8")
        job_specs.append((bucket, list_path, fail_path))

    def run(spec):
        bucket, list_path, fail_path = spec
        cp = subprocess.run(
            [str(parser), str(list_path), str(fail_path)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=600,
        )
        if cp.returncode:
            raise RuntimeError(f"{parser} failed: {cp.stdout}\n{cp.stderr}")
        return bucket, fail_path, cp.stdout.strip()

    failed_paths = {}
    with ThreadPoolExecutor(max_workers=len(job_specs)) as pool:
        futures = [pool.submit(run, spec) for spec in job_specs]
        for future in as_completed(futures):
            bucket, fail_path, stdout = future.result()
            print(stdout, flush=True)
            if fail_path.is_file():
                for line in fail_path.read_text(encoding="utf-8").splitlines():
                    if line:
                        diagnostic = json.loads(line)
                        failed_paths[diagnostic["path"]] = diagnostic

    failures = []
    for group in groups:
        diagnostic = failed_paths.get(group["path"])
        if diagnostic:
            failures.append({**group, **diagnostic})
    failures.sort(
        key=lambda row: (
            -(row["network_occurrences"] + row["runtime_occurrences"]),
            -row["bytes"],
            row["sha256"],
        )
    )
    return failures


def main():
    ap = argparse.ArgumentParser(
        description="Parse census over semantically executable JS in Cloak recorder bundles."
    )
    ap.add_argument("capture_root", type=Path)
    ap.add_argument("--parser", type=Path, default=DEFAULT_PARSER)
    ap.add_argument("--jobs", type=int, default=default_jobs())
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()

    capture_root = args.capture_root.resolve()
    output = args.output or (capture_root.parent / "semantic-parse-census.json")
    work = output.parent / ".semantic-parse-census-work"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)

    manifests, network_groups, runtime_groups, bad_inputs = collect(capture_root)
    parse_groups, classifications, classification_occurrences = prepare_candidates(
        network_groups, runtime_groups, work
    )
    print(
        f"semantic JS candidates: {len(parse_groups)} unique from "
        f"{len(network_groups)} network + {len(runtime_groups)} runtime unique bodies",
        flush=True,
    )
    failures = run_parser(args.parser, parse_groups, args.jobs, work)

    report = {
        "schema": "js-redox-semantic-parse-census/v1",
        "capture_root": str(capture_root),
        "captures": len(manifests),
        "network_unique_bodies": len(network_groups),
        "runtime_unique_javascript_bodies": len(runtime_groups),
        "semantic_javascript_candidates": len(parse_groups),
        "semantic_parse_successes": len(parse_groups) - len(failures),
        "semantic_parse_failures": len(failures),
        "network_classification_unique": dict(classifications),
        "network_classification_occurrences": dict(classification_occurrences),
        "bad_inputs": bad_inputs,
        "failures": failures,
    }
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    shutil.rmtree(work, ignore_errors=True)
    print(json.dumps({
        "captures": report["captures"],
        "network_unique_bodies": report["network_unique_bodies"],
        "runtime_unique_javascript_bodies": report["runtime_unique_javascript_bodies"],
        "semantic_javascript_candidates": report["semantic_javascript_candidates"],
        "semantic_parse_failures": report["semantic_parse_failures"],
        "classifications": report["network_classification_unique"],
        "output": str(output),
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()
