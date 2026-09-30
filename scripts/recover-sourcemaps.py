#!/usr/bin/env python3
import argparse
import base64
import hashlib
import json
import re
from pathlib import Path, PurePosixPath
from urllib.parse import unquote_to_bytes, urljoin, urlparse

SOURCE_MAP_RE = re.compile(
    r"(?:\/\/[#@]|\/\*[#@])\s*sourceMappingURL\s*=\s*([^\s*]+)"
)


def safe_component(value: str) -> str:
    value = re.sub(r"[^A-Za-z0-9._-]+", "_", value).strip("._")
    return (value or "_")[:120]


def safe_source_path(raw: str, ordinal: int) -> Path:
    parsed = urlparse(raw)
    if parsed.scheme:
        prefix = [safe_component(parsed.scheme), safe_component(parsed.netloc or "_")]
        parts = [safe_component(p) for p in PurePosixPath(parsed.path).parts if p not in {"", "/", ".", ".."}]
    else:
        prefix = []
        parts = [safe_component(p) for p in PurePosixPath(raw).parts if p not in {"", "/", ".", ".."}]
    if not parts:
        parts = [f"source-{ordinal:04}.js"]
    if "." not in parts[-1]:
        parts[-1] += ".js"
    return Path(*prefix, *parts)


def parse_data_url(raw: str) -> bytes:
    header, sep, data = raw.partition(",")
    if not sep:
        raise ValueError("malformed data URL")
    if ";base64" in header.lower():
        return base64.b64decode(data)
    return unquote_to_bytes(data)


def source_mapping_url(text: str):
    matches = list(SOURCE_MAP_RE.finditer(text))
    return matches[-1].group(1).strip("'\"") if matches else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("project", type=Path)
    args = ap.parse_args()

    project = args.project.resolve()
    manifest = json.loads((project / "har-manifest.json").read_text())
    by_url = {r["url"]: r for r in manifest["resources"]}
    results = []

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

        raw_ref = source_mapping_url(js_text)
        if not raw_ref:
            continue

        map_url = None
        map_resource_id = None
        if raw_ref.startswith("data:"):
            try:
                map_bytes = parse_data_url(raw_ref)
            except Exception as exc:
                results.append({
                    "resource_id": resource["id"],
                    "url": resource["url"],
                    "status": "decode_error",
                    "error": str(exc),
                })
                continue
            map_origin = "inline_data_url"
        else:
            map_url = urljoin(resource["url"], raw_ref)
            linked = by_url.get(map_url)
            if not linked or not linked.get("output_path"):
                results.append({
                    "resource_id": resource["id"],
                    "url": resource["url"],
                    "map_url": map_url,
                    "status": "missing_map_resource",
                })
                continue
            map_resource_id = linked["id"]
            map_bytes = (project / linked["output_path"]).read_bytes()
            map_origin = "har_resource"

        try:
            smap = json.loads(map_bytes)
        except Exception as exc:
            results.append({
                "resource_id": resource["id"],
                "url": resource["url"],
                "map_url": map_url,
                "map_resource_id": map_resource_id,
                "status": "invalid_source_map",
                "error": str(exc),
            })
            continue

        sources = smap.get("sources") or []
        contents = smap.get("sourcesContent") or []
        source_root = smap.get("sourceRoot") or ""
        digest = hashlib.sha256(map_bytes).hexdigest()[:12]
        root = project / "src" / "_sourcemap" / f"{resource['id']:04}-{digest}"
        recovered = []

        for i, raw_source in enumerate(sources):
            content = contents[i] if i < len(contents) else None
            if content is None:
                recovered.append({
                    "ordinal": i,
                    "source": raw_source,
                    "status": "no_sources_content",
                })
                continue

            logical = urljoin(source_root if source_root.endswith("/") else source_root + "/", raw_source) if source_root else raw_source
            rel = safe_source_path(logical, i)
            dest = root / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            if isinstance(content, str):
                dest.write_text(content)
                size = len(content.encode())
            else:
                encoded = json.dumps(content, indent=2)
                dest.write_text(encoded + "\n")
                size = len(encoded.encode()) + 1
            recovered.append({
                "ordinal": i,
                "source": raw_source,
                "logical_source": logical,
                "status": "recovered",
                "bytes": size,
                "source_path": str(dest.relative_to(project)),
            })

        results.append({
            "resource_id": resource["id"],
            "url": resource["url"],
            "raw_reference": raw_ref,
            "map_url": map_url,
            "map_resource_id": map_resource_id,
            "map_origin": map_origin,
            "source_root": source_root,
            "sources": len(sources),
            "sources_content": sum(c is not None for c in contents),
            "recovered": recovered,
            "status": "recovered" if any(x["status"] == "recovered" for x in recovered) else "no_sources_content",
        })

    out = {
        "schema": "har-sourcemap-recovery/v0",
        "source_maps": results,
    }
    analysis = project / "analysis"
    analysis.mkdir(parents=True, exist_ok=True)
    (analysis / "sourcemaps.json").write_text(json.dumps(out, indent=2) + "\n")

    recovered = sum(
        x.get("status") == "recovered"
        for m in results
        for x in m.get("recovered", [])
    )
    missing = sum(m.get("status") == "missing_map_resource" for m in results)
    print(
        f"source maps: {len(results)} referenced; "
        f"{recovered} original source files recovered; {missing} missing map resources"
    )


if __name__ == "__main__":
    main()
