#!/usr/bin/env python3
import argparse
import copy
import json
import re
import subprocess
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urljoin, urlsplit

from analysis_artifacts import IMPORT_MAPS, JS_REFERENCES, SOURCE_INDEX, load_artifact, write_artifact

from browser_script_types import is_executable_script
from content_dedup import default_jobs, sha256_path
from capture_project import load_manifest

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EXTRACTOR = ROOT / ".cargo-target-nodebug/debug/js-refs"
IMPORT_KINDS = {"import_static", "import_dynamic"}
DYNAMIC_GLOB_KIND = "import_dynamic_glob"


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


def decode_dynamic_glob_literals(pattern: str):
    # rolldown_redox emits conventional glob escapes for literal metacharacters.
    # Our matcher treats only `*` as special, so restore the literal characters first.
    return (
        pattern.replace("[[]", "[")
        .replace("[]]", "]")
        .replace("[{]", "{")
        .replace("[}]", "}")
        .replace("[?]", "?")
    )


def dynamic_glob_regex(pattern: str):
    parts = ["^"]
    for character in pattern:
        parts.append("[^/]*" if character == "*" else re.escape(character))
    parts.append("$")
    return re.compile("".join(parts))


def captured_dynamic_glob_matches(base_url: str | None, pattern: str, captured_urls):
    if not base_url:
        return None, []
    decoded = decode_dynamic_glob_literals(pattern)
    absolute_pattern = urljoin(base_url, decoded)
    matcher = dynamic_glob_regex(absolute_pattern)
    return absolute_pattern, sorted(url for url in captured_urls if matcher.fullmatch(url))


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
        "schema": IMPORT_MAPS.schema,
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
    write_artifact(project, IMPORT_MAPS, analysis)
    return maps_by_document, analysis


def main():
    ap = argparse.ArgumentParser(
        description="Extract literal JS references and resolve document import maps"
    )
    ap.add_argument("project", type=Path)
    ap.add_argument("--extractor", type=Path, default=DEFAULT_EXTRACTOR)
    ap.add_argument("--jobs", type=int, default=default_jobs())
    args = ap.parse_args()
    jobs = max(1, args.jobs)

    project = args.project.resolve()
    manifest = load_manifest(project)
    source_index = load_artifact(project, SOURCE_INDEX)
    import_maps, import_map_analysis = load_import_maps(project, manifest)

    rows = []
    failures = 0
    total_refs = 0
    units_by_url = defaultdict(list)
    units_by_raw = {}

    javascript_units = []
    extraction_groups = {}
    for unit in source_index.get("units", []):
        if unit.get("kind") != "javascript":
            continue
        source_path = unit.get("source_path")
        if not source_path:
            continue
        source = project / source_path
        digest = sha256_path(source)
        item = {
            "unit": unit,
            "source": source,
            "source_path": source_path,
            "content_sha256": digest,
        }
        javascript_units.append(item)
        extraction_groups.setdefault(digest, []).append(item)

    def extract_group(digest, group):
        canonical = group[0]
        cp = subprocess.run(
            [str(args.extractor), str(canonical["source"])],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=120,
        )
        references = json.loads(cp.stdout) if cp.returncode == 0 else []
        return {
            "content_sha256": digest,
            "canonical_source_path": canonical["source_path"],
            "group_size": len(group),
            "exit": cp.returncode,
            "references": references,
            "error": cp.stderr[-3000:] if cp.returncode else None,
        }

    extraction_results = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {
            pool.submit(extract_group, digest, group): digest
            for digest, group in extraction_groups.items()
        }
        for future in as_completed(futures):
            result = future.result()
            extraction_results[result["content_sha256"]] = result

    seen_per_digest = defaultdict(int)
    for item in javascript_units:
        unit = item["unit"]
        result = extraction_results[item["content_sha256"]]
        occurrence = seen_per_digest[item["content_sha256"]]
        seen_per_digest[item["content_sha256"]] += 1
        row = {
            "resource_id": unit.get("resource_id"),
            "url": unit.get("url"),
            "raw_path": unit.get("raw_path"),
            "source_path": item["source_path"],
            "content_sha256": item["content_sha256"],
            "content_group_size": result["group_size"],
            "deduplicated": occurrence > 0,
            "deduplicated_from": (
                result["canonical_source_path"] if occurrence > 0 else None
            ),
            "extractor_exit": result["exit"],
            "document_resource_ids": [],
            "references": copy.deepcopy(result["references"]),
        }
        if result["exit"]:
            failures += 1
            row["error"] = result["error"]
        else:
            total_refs += len(row["references"])
        row_id = len(rows)
        rows.append(row)
        if row.get("url"):
            units_by_url[row["url"]].append(row_id)
        if row.get("raw_path"):
            units_by_raw[row["raw_path"]] = row_id

    dynamic_glob_matches = {}
    dynamic_glob_patterns = 0
    for row_id, row in enumerate(rows):
        for ref_index, ref in enumerate(row["references"]):
            if ref.get("kind") != DYNAMIC_GLOB_KIND:
                continue
            dynamic_glob_patterns += 1
            absolute_pattern, matches = captured_dynamic_glob_matches(
                row.get("url"), ref.get("glob") or "", units_by_url.keys()
            )
            ref["absolute_glob"] = absolute_pattern
            dynamic_glob_matches[(row_id, ref_index)] = matches

    # Seed document execution contexts from actual <script> records. Import maps are
    # document state and intentionally do not flow into Worker/worklet graphs.
    queue = deque()
    contexts = defaultdict(set)
    for script in manifest.get("inline_scripts", []):
        if is_import_map(script) or not is_executable_script(script.get("script_type")):
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
            kind = ref.get("kind")
            if kind == DYNAMIC_GLOB_KIND:
                matched_urls = dynamic_glob_matches.get((row_id, ref_index), [])
                for matched_url in matched_urls:
                    result = resolve_with_import_map(row.get("url"), matched_url, import_map)
                    resolution = result.get("resolution")
                    if resolution == "url":
                        result["resolution"] = "captured_dynamic_glob"
                    elif resolution:
                        result["resolution"] = f"captured_dynamic_glob_{resolution}"
                    candidate = {
                        "document_resource_id": document_id,
                        "glob_match_url": matched_url,
                        **result,
                    }
                    candidate_key = (
                        document_id,
                        candidate.get("glob_match_url"),
                        candidate.get("resolved_url"),
                        candidate.get("resolution"),
                        candidate.get("import_map_key"),
                        candidate.get("scope"),
                    )
                    per_ref_candidates[(row_id, ref_index)][candidate_key] = candidate
                    resolved = result.get("resolved_url")
                    if not resolved:
                        continue
                    for target_row_id in units_by_url.get(resolved, []):
                        if document_id not in contexts[target_row_id]:
                            contexts[target_row_id].add(document_id)
                            queue.append((target_row_id, document_id))
                continue

            if kind not in IMPORT_KINDS:
                continue
            result = resolve_with_import_map(row.get("url"), ref["specifier"], import_map)
            candidate = {
                "document_resource_id": document_id,
                **result,
            }
            candidate_key = (
                document_id,
                candidate.get("resolved_url"),
                candidate.get("resolution"),
                candidate.get("import_map_key"),
                candidate.get("scope"),
            )
            per_ref_candidates[(row_id, ref_index)][candidate_key] = candidate
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
            if ref.get("kind") == DYNAMIC_GLOB_KIND:
                raw_matches = dynamic_glob_matches.get((row_id, ref_index), [])
                if not candidates:
                    candidates = [
                        {
                            "document_resource_id": None,
                            "glob_match_url": matched_url,
                            "resolved_url": matched_url,
                            "bare_specifier": False,
                            "resolution": "captured_dynamic_glob",
                            "import_map_key": None,
                            "scope": None,
                        }
                        for matched_url in raw_matches
                    ]
                candidates = sorted(
                    candidates,
                    key=lambda candidate: (
                        candidate.get("document_resource_id") is not None,
                        candidate.get("document_resource_id") or -1,
                        candidate.get("resolved_url") or "",
                        candidate.get("glob_match_url") or "",
                    ),
                )
                ref["resolution_candidates"] = candidates
                resolved_urls = sorted(
                    {
                        candidate["resolved_url"]
                        for candidate in candidates
                        if candidate.get("resolved_url")
                    }
                )
                ref["candidate_count"] = len(resolved_urls)
                ref["resolved_url"] = resolved_urls[0] if len(resolved_urls) == 1 else None
                ref["bare_specifier"] = False
                ref["resolution"] = (
                    "captured_dynamic_glob" if raw_matches else "captured_dynamic_glob_unmatched"
                )
                ref["import_map_key"] = None
                ref["scope"] = None
                continue

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
        "schema": JS_REFERENCES.schema,
        "extractor": str(args.extractor),
        "import_maps": str(IMPORT_MAPS.relative_path),
        "code_units": rows,
        "summary": {
            "javascript_units": len(rows),
            "unique_input_bodies": len(extraction_groups),
            "deduplicated_units": len(rows) - len(extraction_groups),
            "extractor_invocations": len(extraction_groups),
            "jobs": jobs,
            "references": total_refs,
            "failures": failures,
            "import_map_scripts": import_map_analysis["summary"]["import_map_scripts"],
            "resolved_by_import_map": resolved_by_import_map,
            "unresolved_bare_specifiers": unresolved_bare,
            "ambiguous_document_contexts": ambiguous,
            "dynamic_import_globs": dynamic_glob_patterns,
            "dynamic_import_candidate_urls": sum(
                len(set(matches)) for matches in dynamic_glob_matches.values()
            ),
            "dynamic_import_unmatched": sum(
                not matches for matches in dynamic_glob_matches.values()
            ),
        },
    }
    write_artifact(project, JS_REFERENCES, out)
    dynamic_candidates = sum(len(set(matches)) for matches in dynamic_glob_matches.values())
    print(
        f"JavaScript references: {len(rows)} units, {total_refs} references, "
        f"{dynamic_glob_patterns} dynamic glob(s) / {dynamic_candidates} captured candidate URL(s), "
        f"{resolved_by_import_map} import-map resolutions, {unresolved_bare} unresolved bare, "
        f"{ambiguous} ambiguous contexts, {failures} failures"
    )


if __name__ == "__main__":
    main()
