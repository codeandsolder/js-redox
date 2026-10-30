#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import hashlib
import itertools
import json
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from urllib.parse import unquote_to_bytes, urljoin, urlparse

from analysis_artifacts import SOURCEMAPS, write_artifact

from capture_project import load_manifest

MAX_CHAIN_DEPTH = 16
MAX_SOURCE_MAP_BYTES = 64 * 1024 * 1024
HELPER_TIMEOUT_SECONDS = 120


@dataclass(frozen=True)
class LoadedMap:
    document: dict
    raw_bytes: bytes
    raw_reference: str
    map_url: str | None
    map_resource_id: int | None
    map_origin: str
    base_url: str
    identity: str


def safe_component(value: str) -> str:
    value = re.sub(r"[^A-Za-z0-9._-]+", "_", value).strip("._")
    return (value or "_")[:120]


def safe_source_path(raw: str, ordinal: int) -> Path:
    parsed = urlparse(raw)
    if parsed.scheme:
        prefix = [safe_component(parsed.scheme), safe_component(parsed.netloc or "_")]
        parts = [
            safe_component(p)
            for p in PurePosixPath(parsed.path).parts
            if p not in {"", "/", ".", ".."}
        ]
    else:
        prefix = []
        parts = [
            safe_component(p)
            for p in PurePosixPath(raw).parts
            if p not in {"", "/", ".", ".."}
        ]
    if not parts:
        parts = [f"source-{ordinal:04}.js"]
    if "." not in parts[-1]:
        parts[-1] += ".js"
    return Path(*prefix, *parts)


def parse_data_url(raw: str) -> bytes:
    header, sep, data = raw.partition(",")
    if not sep:
        raise ValueError("malformed data URL")
    # Reject before decoding so a sourceMappingURL cannot double memory use with
    # an arbitrarily large decoded map. Base64 is at most 4/3 expansion.
    if len(data) > MAX_SOURCE_MAP_BYTES * 2:
        raise ValueError("inline source map exceeds size limit")
    if ";base64" in header.lower():
        decoded = base64.b64decode(data)
    else:
        decoded = unquote_to_bytes(data)
    if len(decoded) > MAX_SOURCE_MAP_BYTES:
        raise ValueError("inline source map exceeds size limit")
    return decoded


def source_mapping_urls(extractor: Path, paths: list[Path]) -> dict[str, str]:
    if not paths:
        return {}
    cp = subprocess.run(
        [str(extractor), *map(str, paths)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=HELPER_TIMEOUT_SECONDS,
    )
    if cp.returncode:
        raise RuntimeError(
            f"source directive extraction failed ({cp.returncode}):\n{cp.stdout}{cp.stderr}"
        )
    rows = json.loads(cp.stdout)
    result: dict[str, str] = {}
    for row in rows:
        source_maps = [
            directive["raw"]
            for directive in row.get("directives", [])
            if directive.get("kind") == "source_map"
        ]
        if source_maps:
            result[str(Path(row["input"]).resolve())] = source_maps[-1]
    return result



def source_mapping_url(extractor: Path, text: str) -> str | None:
    if "sourceMappingURL" not in text:
        return None
    cp = subprocess.run(
        [str(extractor), "--stdin"],
        input=text,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=HELPER_TIMEOUT_SECONDS,
    )
    if cp.returncode:
        raise RuntimeError(
            f"source directive extraction failed ({cp.returncode}):\n{cp.stdout}{cp.stderr}"
        )
    rows = json.loads(cp.stdout)
    directives = rows[0].get("directives", []) if rows else []
    source_maps = [
        directive["raw"]
        for directive in directives
        if directive.get("kind") == "source_map"
    ]
    return source_maps[-1] if source_maps else None


def join_logical(base: str, reference: str) -> str:
    if urlparse(reference).scheme:
        return reference
    parsed = urlparse(base)
    if parsed.scheme in {"http", "https", "file"}:
        return urljoin(base, reference)
    if parsed.scheme:
        prefix = base if base.endswith("/") else base.rsplit("/", 1)[0] + "/"
        return prefix + reference
    return urljoin(base, reference)


def logical_source_url(base_url: str, source_root: str, raw_source: str) -> str:
    if urlparse(raw_source).scheme:
        return raw_source
    if source_root:
        root = join_logical(base_url, source_root)
        if not root.endswith("/"):
            root += "/"
        return join_logical(root, raw_source)
    return join_logical(base_url, raw_source)


def normalize_map_document(loaded: LoadedMap) -> dict:
    document = dict(loaded.document)
    source_root = document.get("sourceRoot") or ""
    document["sources"] = [
        logical_source_url(loaded.base_url, source_root, str(source))
        for source in document.get("sources") or []
    ]
    document.pop("sourceRoot", None)
    return document


def load_map(
    raw_ref: str,
    code_url: str,
    by_url: dict[str, dict],
    project: Path,
) -> tuple[LoadedMap | None, dict | None]:
    map_url = None
    map_resource_id = None
    if raw_ref.startswith("data:"):
        try:
            map_bytes = parse_data_url(raw_ref)
        except Exception as exc:
            return None, {"status": "decode_error", "error": str(exc)}
        map_origin = "inline_data_url"
        base_url = code_url
    else:
        map_url = join_logical(code_url, raw_ref)
        linked = by_url.get(map_url)
        if not linked or not linked.get("output_path"):
            return None, {"status": "missing_map_resource", "map_url": map_url}
        map_resource_id = linked["id"]
        map_path = project / linked["output_path"]
        try:
            if map_path.stat().st_size > MAX_SOURCE_MAP_BYTES:
                return None, {
                    "status": "map_too_large",
                    "map_url": map_url,
                    "map_resource_id": map_resource_id,
                }
            map_bytes = map_path.read_bytes()
        except OSError as exc:
            return None, {
                "status": "map_read_error",
                "map_url": map_url,
                "map_resource_id": map_resource_id,
                "error": str(exc),
            }
        map_origin = "har_resource"
        base_url = map_url

    try:
        document = json.loads(map_bytes)
        if not isinstance(document, dict):
            raise ValueError("source map root is not an object")
    except Exception as exc:
        return None, {
            "status": "invalid_source_map",
            "map_url": map_url,
            "map_resource_id": map_resource_id,
            "error": str(exc),
        }

    digest = hashlib.sha256(map_bytes).hexdigest()
    identity = map_url or f"inline:{digest}"
    return (
        LoadedMap(
            document=document,
            raw_bytes=map_bytes,
            raw_reference=raw_ref,
            map_url=map_url,
            map_resource_id=map_resource_id,
            map_origin=map_origin,
            base_url=base_url,
            identity=identity,
        ),
        None,
    )


def source_code(
    document: dict,
    ordinal: int,
    logical_source: str,
    by_url: dict[str, dict],
    project: Path,
) -> tuple[str, str, int | None] | None:
    contents = document.get("sourcesContent") or []
    if ordinal < len(contents) and isinstance(contents[ordinal], str):
        return contents[ordinal], "sources_content", None

    linked = by_url.get(logical_source)
    if not linked or not linked.get("output_path"):
        return None
    source_path = project / linked["output_path"]
    if not source_path.is_file():
        return None
    try:
        return source_path.read_text(), "har_resource", linked["id"]
    except UnicodeDecodeError:
        return None


def compose_documents(
    downstream: dict,
    upstream: dict,
    source_id: int,
    composer: Path,
    work: Path,
    serial: itertools.count,
) -> dict:
    number = next(serial)
    downstream_path = work / f"{number:04}-downstream.map"
    upstream_path = work / f"{number:04}-upstream.map"
    output_path = work / f"{number:04}-composed.map"
    downstream_path.write_text(json.dumps(downstream, separators=(",", ":")))
    upstream_path.write_text(json.dumps(upstream, separators=(",", ":")))
    cp = subprocess.run(
        [
            str(composer),
            str(downstream_path),
            str(upstream_path),
            "--source-id",
            str(source_id),
            "--output",
            str(output_path),
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=HELPER_TIMEOUT_SECONDS,
    )
    if cp.returncode:
        raise RuntimeError((cp.stdout + cp.stderr).strip() or f"composer exited {cp.returncode}")
    composed = json.loads(output_path.read_text())
    if not isinstance(composed, dict):
        raise ValueError("composer output is not a source-map object")
    return composed


def expand_map(
    loaded: LoadedMap,
    *,
    by_url: dict[str, dict],
    project: Path,
    composer: Path | None,
    source_directives: Path,
    work: Path,
    serial: itertools.count,
    stack: frozenset[str],
    depth: int,
) -> tuple[dict, list[dict], int]:
    normalized = normalize_map_document(loaded)
    sources = list(normalized.get("sources") or [])
    links: list[dict] = []
    compositions = 0
    if depth >= MAX_CHAIN_DEPTH:
        return normalized, links, compositions

    composed = normalized
    # Descending ordinals keep lower original source IDs stable when a higher source is replaced
    # by multiple upstream sources.
    for ordinal in range(len(sources) - 1, -1, -1):
        logical_source = str(sources[ordinal])
        code = source_code(normalized, ordinal, logical_source, by_url, project)
        if code is None:
            continue
        code_text, code_origin, code_resource_id = code
        raw_ref = source_mapping_url(source_directives, code_text)
        if not raw_ref:
            continue

        row = {
            "depth": depth + 1,
            "source_ordinal": ordinal,
            "logical_source": logical_source,
            "code_origin": code_origin,
            "code_resource_id": code_resource_id,
            "raw_reference": raw_ref,
        }
        upstream, problem = load_map(raw_ref, logical_source, by_url, project)
        if problem:
            row.update(problem)
            links.append(row)
            continue
        assert upstream is not None
        row.update(
            {
                "map_url": upstream.map_url,
                "map_resource_id": upstream.map_resource_id,
                "map_origin": upstream.map_origin,
            }
        )
        if upstream.identity in stack:
            row["status"] = "cycle"
            links.append(row)
            continue

        expanded_upstream, nested_links, nested_compositions = expand_map(
            upstream,
            by_url=by_url,
            project=project,
            composer=composer,
            source_directives=source_directives,
            work=work,
            serial=serial,
            stack=stack | {upstream.identity},
            depth=depth + 1,
        )
        row["upstream_sources"] = len(expanded_upstream.get("sources") or [])
        if composer is None:
            row["status"] = "composer_unavailable"
            links.append(row)
            links.extend(nested_links)
            continue
        try:
            composed = compose_documents(composed, expanded_upstream, ordinal, composer, work, serial)
        except Exception as exc:
            row["status"] = "compose_error"
            row["error"] = str(exc)
            links.append(row)
            links.extend(nested_links)
            continue

        row["status"] = "composed"
        links.append(row)
        links.extend(nested_links)
        compositions += 1 + nested_compositions

    return composed, links, compositions


def materialize_sources(document: dict, root: Path, project: Path) -> list[dict]:
    sources = document.get("sources") or []
    contents = document.get("sourcesContent") or []
    recovered = []
    for ordinal, source in enumerate(sources):
        content = contents[ordinal] if ordinal < len(contents) else None
        if content is None:
            recovered.append(
                {
                    "ordinal": ordinal,
                    "source": source,
                    "logical_source": source,
                    "status": "no_sources_content",
                }
            )
            continue

        rel = safe_source_path(str(source), ordinal)
        dest = root / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(content, str):
            dest.write_text(content)
            size = len(content.encode())
        else:
            encoded = json.dumps(content, indent=2)
            dest.write_text(encoded + "\n")
            size = len(encoded.encode()) + 1
        recovered.append(
            {
                "ordinal": ordinal,
                "source": source,
                "logical_source": source,
                "status": "recovered",
                "bytes": size,
                "source_path": str(dest.relative_to(project)),
            }
        )
    return recovered


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("project", type=Path)
    ap.add_argument("--composer", type=Path)
    ap.add_argument(
        "--source-directives",
        type=Path,
        default=Path(__file__).resolve().parents[1] / ".cargo-target-nodebug/debug/source-directives",
    )
    args = ap.parse_args()

    project = args.project.resolve()
    composer = args.composer.resolve() if args.composer else None
    source_directives_bin = args.source_directives.resolve()
    if composer is not None and not composer.is_file():
        raise SystemExit(f"source-map composer does not exist: {composer}")
    if not source_directives_bin.is_file():
        raise SystemExit(f"source-directives extractor does not exist: {source_directives_bin}")
    manifest = load_manifest(project)
    by_url = {resource["url"]: resource for resource in manifest["resources"]}
    results = []
    analysis = project / "analysis"
    analysis.mkdir(parents=True, exist_ok=True)
    composed_root = analysis / "sourcemap-composed"

    source_map_paths: dict[int, Path] = {}
    candidate_paths: list[Path] = []
    for resource in manifest["resources"]:
        if resource.get("kind") != "javascript" or not resource.get("output_path"):
            continue
        js_path = project / resource["output_path"]
        if not js_path.is_file():
            continue
        try:
            js_text = js_path.read_text()
        except UnicodeDecodeError:
            continue
        if "sourceMappingURL" not in js_text:
            continue
        resolved = js_path.resolve()
        source_map_paths[resource["id"]] = resolved
        candidate_paths.append(resolved)
    source_map_refs = source_mapping_urls(
        source_directives_bin, list(dict.fromkeys(candidate_paths))
    )

    with tempfile.TemporaryDirectory(prefix="sourcemap-compose-", dir=analysis) as temp_dir:
        work = Path(temp_dir)
        serial = itertools.count()
        for resource in manifest["resources"]:
            js_path = source_map_paths.get(resource["id"])
            if js_path is None:
                continue
            raw_ref = source_map_refs.get(str(js_path))
            if not raw_ref:
                continue
            loaded, problem = load_map(raw_ref, resource["url"], by_url, project)
            if problem:
                results.append(
                    {
                        "resource_id": resource["id"],
                        "url": resource["url"],
                        "raw_reference": raw_ref,
                        **problem,
                    }
                )
                continue
            assert loaded is not None

            direct_document = normalize_map_document(loaded)
            digest = hashlib.sha256(loaded.raw_bytes).hexdigest()[:12]
            root = project / "src" / "_sourcemap" / f"{resource['id']:04}-{digest}"
            recovered = materialize_sources(direct_document, root, project)
            composed, links, compositions = expand_map(
                loaded,
                by_url=by_url,
                project=project,
                composer=composer,
                source_directives=source_directives_bin,
                work=work,
                serial=serial,
                stack=frozenset({loaded.identity}),
                depth=0,
            )

            composed_recovered = []
            composed_map_path = None
            if compositions:
                composed_root.mkdir(parents=True, exist_ok=True)
                map_dest = composed_root / f"{resource['id']:04}-{digest}.map"
                map_dest.write_text(json.dumps(composed, separators=(",", ":")) + "\n")
                composed_map_path = str(map_dest.relative_to(project))
                composed_recovered = materialize_sources(composed, root / "final", project)

            composition_status = "not_needed"
            if links:
                composition_status = "composed" if all(
                    link.get("status") == "composed" for link in links
                ) else "partial"

            results.append(
                {
                    "resource_id": resource["id"],
                    "url": resource["url"],
                    "raw_reference": raw_ref,
                    "map_url": loaded.map_url,
                    "map_resource_id": loaded.map_resource_id,
                    "map_origin": loaded.map_origin,
                    "source_root": loaded.document.get("sourceRoot") or "",
                    "sources": len(direct_document.get("sources") or []),
                    "sources_content": sum(
                        content is not None
                        for content in direct_document.get("sourcesContent") or []
                    ),
                    "recovered": recovered,
                    "composition": {
                        "status": composition_status,
                        "links": links,
                        "composed_links": compositions,
                        "composed_sources": len(composed.get("sources") or []),
                        "composed_sources_content": sum(
                            content is not None for content in composed.get("sourcesContent") or []
                        ),
                        "composed_map_path": composed_map_path,
                    },
                    "composed_recovered": composed_recovered,
                    "status": "recovered"
                    if any(item["status"] == "recovered" for item in recovered)
                    else "no_sources_content",
                }
            )

    out = {
        "schema": SOURCEMAPS.schema,
        "source_maps": results,
    }
    write_artifact(project, SOURCEMAPS, out)

    recovered = sum(
        item.get("status") == "recovered"
        for source_map in results
        for item in source_map.get("recovered", [])
    )
    composed_recovered = sum(
        item.get("status") == "recovered"
        for source_map in results
        for item in source_map.get("composed_recovered", [])
    )
    missing = sum(source_map.get("status") == "missing_map_resource" for source_map in results)
    composed_links = sum(
        source_map.get("composition", {}).get("composed_links", 0) for source_map in results
    )
    print(
        f"source maps: {len(results)} referenced; "
        f"{recovered} direct source files recovered; "
        f"{composed_links} nested map link(s) composed; "
        f"{composed_recovered} final source files recovered; "
        f"{missing} missing map resources"
    )


if __name__ == "__main__":
    main()
