#!/usr/bin/env python3
import argparse
import json
import subprocess
from collections import defaultdict, deque
from pathlib import Path
from urllib.parse import urljoin, urlsplit

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EXTRACTOR = ROOT / ".cargo-target-nodebug/debug/js-refs"
IMPORT_KINDS = {"import_static", "import_dynamic"}


def url_like(base_url: str | None, specifier: str):
    specifier = specifier.strip()
    if not specifier:
        return None
    parsed = urlsplit(specifier)
    if parsed.scheme:
        return specifier
    if specifier.startswith("//"):
        if not base_url:
            return None
        scheme = urlsplit(base_url).scheme or "https"
        return f"{scheme}:{specifier}"
    if specifier.startswith(("./", "../", "/")):
        return urljoin(base_url, specifier) if base_url else None
    return None


def normalize_map_key(base_url: str, key: str):
    if not isinstance(key, str) or not key:
        return None
    return url_like(base_url, key) or key


def normalize_map_address(base_url: str, value):
    if value is None:
        return None
    if not isinstance(value, str):
        return None
    # Import-map addresses must be URL-like; bare replacement values are invalid.
    if not (urlsplit(value).scheme or value.startswith(("./", "../", "/", "//"))):
        return None
    return url_like(base_url, value)


def parse_specifier_map(base_url: str, obj, warnings: list[str], label: str):
    if not isinstance(obj, dict):
        warnings.append(f"{label} is not an object")
        return {}
    out = {}
    for raw_key, raw_value in obj.items():
        key = normalize_map_key(base_url, raw_key)
        if key is None:
            warnings.append(f"{label}: ignored empty/invalid key {raw_key!r}")
            continue
        value = normalize_map_address(base_url, raw_value)
        if raw_value is not None and value is None:
            warnings.append(f"{label}: {raw_key!r} has invalid non-URL address")
        if key.endswith("/") and value is not None and not value.endswith("/"):
            warnings.append(
                f"{label}: prefix key {raw_key!r} maps to non-prefix address {raw_value!r}"
            )
            value = None
        out[key] = value
    return out


def parse_import_map(base_url: str, payload, warnings: list[str]):
    if not isinstance(payload, dict):
        warnings.append("import map root is not an object")
        return {"imports": {}, "scopes": {}, "integrity": {}}

    imports = parse_specifier_map(base_url, payload.get("imports", {}), warnings, "imports")
    scopes = {}
    raw_scopes = payload.get("scopes", {})
    if raw_scopes is None:
        raw_scopes = {}
    if not isinstance(raw_scopes, dict):
        warnings.append("scopes is not an object")
    else:
        for raw_scope, specifier_map in raw_scopes.items():
            if not isinstance(raw_scope, str) or not raw_scope:
                warnings.append(f"ignored invalid scope key {raw_scope!r}")
                continue
            scope = urljoin(base_url, raw_scope)
            scopes[scope] = parse_specifier_map(
                base_url, specifier_map, warnings, f"scope {raw_scope!r}"
            )

    integrity = {}
    raw_integrity = payload.get("integrity", {})
    if isinstance(raw_integrity, dict):
        for raw_url, metadata in raw_integrity.items():
            if isinstance(raw_url, str) and isinstance(metadata, str):
                resolved = url_like(base_url, raw_url)
                if resolved:
                    integrity[resolved] = metadata

    return {"imports": imports, "scopes": scopes, "integrity": integrity}


def merge_specifier_map(existing: dict, new: dict):
    # WHATWG multiple-import-map merge keeps the existing rule on exact conflict.
    merged = dict(existing)
    for key, value in new.items():
        if key not in merged:
            merged[key] = value
    return merged


def merge_import_map(existing: dict, new: dict):
    merged = {
        "imports": merge_specifier_map(existing.get("imports", {}), new.get("imports", {})),
        "scopes": {
            scope: dict(entries)
            for scope, entries in existing.get("scopes", {}).items()
        },
        "integrity": dict(existing.get("integrity", {})),
    }
    for scope, entries in new.get("scopes", {}).items():
        merged["scopes"][scope] = merge_specifier_map(
            merged["scopes"].get(scope, {}), entries
        )
    for url, integrity in new.get("integrity", {}).items():
        merged["integrity"].setdefault(url, integrity)
    return merged


def resolve_in_specifier_map(normalized: str, specifier_map: dict):
    if normalized in specifier_map:
        return True, specifier_map[normalized], normalized
    prefixes = [
        key
        for key in specifier_map
        if key.endswith("/") and normalized.startswith(key)
    ]
    if not prefixes:
        return False, None, None
    key = max(prefixes, key=len)
    base = specifier_map[key]
    if base is None:
        return True, None, key
    suffix = normalized[len(key):]
    resolved = urljoin(base, suffix)
    if not resolved.startswith(base):
        return True, None, key
    return True, resolved, key


def resolve_with_import_map(base_url: str | None, specifier: str, import_map: dict | None):
    specifier = specifier.strip()
    normalized_url = url_like(base_url, specifier)
    normalized = normalized_url or specifier

    if import_map and base_url:
        matching_scopes = sorted(
            (
                scope
                for scope in import_map.get("scopes", {})
                if base_url.startswith(scope)
            ),
            key=len,
            reverse=True,
        )
        for scope in matching_scopes:
            matched, resolved, key = resolve_in_specifier_map(
                normalized, import_map["scopes"][scope]
            )
            if matched:
                return {
                    "resolved_url": resolved,
                    "bare_specifier": normalized_url is None,
                    "resolution": "import_map_scope" if resolved else "import_map_blocked",
                    "import_map_key": key,
                    "scope": scope,
                }

        matched, resolved, key = resolve_in_specifier_map(
            normalized, import_map.get("imports", {})
        )
        if matched:
            return {
                "resolved_url": resolved,
                "bare_specifier": normalized_url is None,
                "resolution": "import_map" if resolved else "import_map_blocked",
                "import_map_key": key,
                "scope": None,
            }

    if normalized_url is not None:
        return {
            "resolved_url": normalized_url,
            "bare_specifier": False,
            "resolution": "url",
            "import_map_key": None,
            "scope": None,
        }
    return {
        "resolved_url": None,
        "bare_specifier": True,
        "resolution": "unresolved_bare",
        "import_map_key": None,
        "scope": None,
    }


def is_import_map(script: dict):
    return (script.get("script_type") or "").strip().lower() == "importmap"


def load_import_maps(project: Path, manifest: dict):
    resources = {int(r["id"]): r for r in manifest.get("resources", [])}
    maps_by_document = {}
    records = []
    parse_failures = 0

    by_document = defaultdict(list)
    for script in manifest.get("inline_scripts", []):
        if is_import_map(script) and script.get("output_path"):
            by_document[int(script["parent_resource_id"])].append(script)

    for document_id, scripts in by_document.items():
        resource = resources.get(document_id, {})
        base_url = resource.get("url")
        merged = {"imports": {}, "scopes": {}, "integrity": {}}
        for script in sorted(scripts, key=lambda s: int(s.get("ordinal", 0))):
            warnings = []
            path = project / script["output_path"]
            try:
                payload = json.loads(path.read_text())
                parsed = parse_import_map(base_url, payload, warnings)
                merged = merge_import_map(merged, parsed)
                status = "parsed"
            except (OSError, json.JSONDecodeError, UnicodeDecodeError) as error:
                parsed = {"imports": {}, "scopes": {}, "integrity": {}}
                warnings.append(str(error))
                parse_failures += 1
                status = "error"
            records.append(
                {
                    "document_resource_id": document_id,
                    "pageref": resource.get("pageref"),
                    "base_url": base_url,
                    "ordinal": script.get("ordinal"),
                    "raw_path": script.get("output_path"),
                    "status": status,
                    "warnings": warnings,
                    "imports": parsed["imports"],
                    "scopes": parsed["scopes"],
                    "integrity": parsed["integrity"],
                }
            )
        maps_by_document[document_id] = merged

    analysis = {
        "schema": "browser-import-maps/v0",
        "maps": records,
        "documents": {
            str(document_id): import_map
            for document_id, import_map in maps_by_document.items()
        },
        "summary": {
            "import_map_scripts": len(records),
            "documents_with_import_maps": len(maps_by_document),
            "parse_failures": parse_failures,
            "imports": sum(len(m.get("imports", {})) for m in maps_by_document.values()),
            "scopes": sum(len(m.get("scopes", {})) for m in maps_by_document.values()),
        },
        "limitation": (
            "Multiple import maps are merged with standard first-definition-wins conflict "
            "semantics, but runtime resolved-module-set timing is not reconstructed."
        ),
    }
    (project / "analysis/import-maps.json").write_text(
        json.dumps(analysis, indent=2) + "\n"
    )
    return maps_by_document, analysis


def main():
    ap = argparse.ArgumentParser(
        description="Extract literal JS references and resolve document import maps"
    )
    ap.add_argument("project", type=Path)
    ap.add_argument("--extractor", type=Path, default=DEFAULT_EXTRACTOR)
    args = ap.parse_args()

    project = args.project.resolve()
    manifest = json.loads((project / "har-manifest.json").read_text())
    source_index = json.loads((project / "analysis/source-index.json").read_text())
    import_maps, import_map_analysis = load_import_maps(project, manifest)

    rows = []
    failures = 0
    total_refs = 0
    units_by_url = defaultdict(list)
    units_by_raw = {}

    for unit in source_index.get("units", []):
        if unit.get("kind") != "javascript":
            continue
        source_path = unit.get("source_path")
        if not source_path:
            continue
        source = project / source_path
        cp = subprocess.run(
            [str(args.extractor), str(source)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=120,
        )
        row = {
            "resource_id": unit.get("resource_id"),
            "url": unit.get("url"),
            "raw_path": unit.get("raw_path"),
            "source_path": source_path,
            "extractor_exit": cp.returncode,
            "document_resource_ids": [],
            "references": [],
        }
        if cp.returncode:
            failures += 1
            row["error"] = cp.stderr[-3000:]
        else:
            row["references"] = json.loads(cp.stdout)
            total_refs += len(row["references"])
        row_id = len(rows)
        rows.append(row)
        if row.get("url"):
            units_by_url[row["url"]].append(row_id)
        if row.get("raw_path"):
            units_by_raw[row["raw_path"]] = row_id
    # Seed document execution contexts from actual <script> records. Import maps are
    # document state and intentionally do not flow into Worker/worklet graphs.
    queue = deque()
    contexts = defaultdict(set)
    for script in manifest.get("inline_scripts", []):
        if is_import_map(script):
            continue
        document_id = int(script["parent_resource_id"])
        if document_id not in import_maps:
            continue
        if script.get("output_path") in units_by_raw:
            row_id = units_by_raw[script["output_path"]]
            if document_id not in contexts[row_id]:
                contexts[row_id].add(document_id)
                queue.append((row_id, document_id))
        resolved_src = script.get("resolved_src")
        if resolved_src:
            for row_id in units_by_url.get(resolved_src, []):
                if document_id not in contexts[row_id]:
                    contexts[row_id].add(document_id)
                    queue.append((row_id, document_id))

    # Resolve imports and propagate the document import-map context through the
    # captured module graph. This avoids incorrectly applying a document import
    # map to workers merely because their HAR pageref is the same.
    per_ref_candidates = defaultdict(dict)
    seen_context = set()
    while queue:
        row_id, document_id = queue.popleft()
        state = (row_id, document_id)
        if state in seen_context:
            continue
        seen_context.add(state)
        row = rows[row_id]
        import_map = import_maps.get(document_id)
        for ref_index, ref in enumerate(row["references"]):
            if ref.get("kind") not in IMPORT_KINDS:
                continue
            result = resolve_with_import_map(
                row.get("url"), ref["specifier"], import_map
            )
            candidate = {
                "document_resource_id": document_id,
                **result,
            }
            per_ref_candidates[(row_id, ref_index)][document_id] = candidate
            resolved = result.get("resolved_url")
            if not resolved:
                continue
            for target_row_id in units_by_url.get(resolved, []):
                if document_id not in contexts[target_row_id]:
                    contexts[target_row_id].add(document_id)
                    queue.append((target_row_id, document_id))

    resolved_by_import_map = 0
    unresolved_bare = 0
    ambiguous = 0
    for row_id, row in enumerate(rows):
        row["document_resource_ids"] = sorted(contexts.get(row_id, set()))
        for ref_index, ref in enumerate(row["references"]):
            candidates = list(per_ref_candidates.get((row_id, ref_index), {}).values())
            if ref.get("kind") not in IMPORT_KINDS or not candidates:
                result = resolve_with_import_map(row.get("url"), ref["specifier"], None)
                ref.update(result)
                if result["resolution"] == "unresolved_bare":
                    unresolved_bare += 1
                continue

            ref["resolution_candidates"] = sorted(
                candidates, key=lambda c: c["document_resource_id"]
            )
            resolutions = {
                (
                    candidate.get("resolved_url"),
                    candidate.get("resolution"),
                    candidate.get("import_map_key"),
                    candidate.get("scope"),
                )
                for candidate in candidates
            }
            if len(resolutions) == 1:
                only = candidates[0]
                ref.update(
                    {
                        key: only.get(key)
                        for key in (
                            "resolved_url",
                            "bare_specifier",
                            "resolution",
                            "import_map_key",
                            "scope",
                        )
                    }
                )
                if str(ref.get("resolution", "")).startswith("import_map") and ref.get(
                    "resolved_url"
                ):
                    resolved_by_import_map += 1
                if ref.get("resolution") == "unresolved_bare":
                    unresolved_bare += 1
            else:
                ref["resolved_url"] = None
                ref["bare_specifier"] = all(
                    candidate.get("bare_specifier") for candidate in candidates
                )
                ref["resolution"] = "ambiguous_document_context"
                ref["import_map_key"] = None
                ref["scope"] = None
                ambiguous += 1

    out = {
        "schema": "har-js-references/v1",
        "extractor": str(args.extractor),
        "import_maps": "analysis/import-maps.json",
        "code_units": rows,
        "summary": {
            "javascript_units": len(rows),
            "references": total_refs,
            "failures": failures,
            "import_map_scripts": import_map_analysis["summary"]["import_map_scripts"],
            "resolved_by_import_map": resolved_by_import_map,
            "unresolved_bare_specifiers": unresolved_bare,
            "ambiguous_document_contexts": ambiguous,
        },
    }
    path = project / "analysis/js-references.json"
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(
        f"JavaScript references: {len(rows)} units, {total_refs} literal references, "
        f"{resolved_by_import_map} import-map resolutions, {unresolved_bare} unresolved bare, "
        f"{ambiguous} ambiguous contexts, {failures} failures"
    )


if __name__ == "__main__":
    main()
