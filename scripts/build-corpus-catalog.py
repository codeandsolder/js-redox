#!/usr/bin/env python3
"""Build an incremental hash-keyed preclassification catalog for recorder corpora."""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sqlite3
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = ROOT / "work/scum-corpus-20261007"
SCHEMA_VERSION = 1
SCAN_VERSION = 1

TRIVIAL_ANONYMOUS = {
    "", "[]", "{}", "({})", "null", "undefined", "true", "false", "0", "1",
    '""', "''", "void 0", "void(0)",
}
DATA_RESOURCE_TYPES = {"xhr", "fetch", "ping", "eventsource"}
XSSI_PREFIXES = ("for (;;);", "for(;;);", "while (1);", "while(1);", ")]}'")
CHARSET_RE = re.compile(r"charset\s*=\s*['\"]?([^;'\"\s]+)", re.IGNORECASE)
WEB_CHARSET_ALIASES = {
    "iso-8859-1": "cp1252", "iso8859-1": "cp1252", "latin1": "cp1252",
    "latin-1": "cp1252", "windows-1252": "cp1252", "utf8": "utf-8",
}

FEATURES = {
    "source_map_ref": re.compile(br"sourceMappingURL\s*="),
    "source_url_ref": re.compile(br"sourceURL\s*="),
    "eval_call": re.compile(br"(?<![\w$])eval\s*\("),
    "function_constructor": re.compile(br"(?:new\s+)?Function\s*\("),
    "dynamic_import": re.compile(br"(?<![\w$])import\s*\("),
    "worker_constructor": re.compile(br"(?:new\s+)?(?:Shared)?Worker\s*\("),
    "webassembly_api": re.compile(br"WebAssembly\s*\."),
    "wasm_base64_magic": re.compile(br"AGFzbQ"),
    "atob": re.compile(br"(?<![\w$])atob\s*\("),
    "btoa": re.compile(br"(?<![\w$])btoa\s*\("),
    "from_char_code": re.compile(br"String\s*\.\s*fromCharCode\s*\("),
    "char_code_at": re.compile(br"\.\s*charCodeAt\s*\("),
    "unescape_call": re.compile(br"(?<![\w$])unescape\s*\("),
    "decode_uri_component": re.compile(br"decodeURIComponent\s*\("),
    "proxy_constructor": re.compile(br"(?:new\s+)?Proxy\s*\("),
    "debugger_statement": re.compile(br"(?<![\w$])debugger\s*;"),
    "webpack_runtime": re.compile(br"__webpack_require__|webpackChunk|webpackJsonp"),
    "amd_loader": re.compile(br"define\s*\.\s*amd|define\s*\(\s*\["),
    "browserify_runtime": re.compile(br"function\s+r\s*\(\s*e\s*,\s*n\s*,\s*t\s*\)|browserify", re.I),
    "javascript_obfuscator_names": re.compile(br"\b_0x[0-9a-fA-F]{3,}\b"),
    "packer_eval": re.compile(br"eval\s*\(\s*function\s*\(\s*p\s*,\s*a\s*,\s*c\s*,\s*k\s*,\s*e\s*,"),
    "anti_debug_interval": re.compile(br"setInterval\s*\([^)]*(?:debugger|constructor)"),
    "inline_sourcemap": re.compile(br"sourceMappingURL\s*=\s*data:application/json"),
    "switch_statement": re.compile(br"\bswitch\s*\("),
    "while_true": re.compile(br"\bwhile\s*\(\s*(?:true|1)\s*\)"),
    "for_ever": re.compile(br"\bfor\s*\(\s*;\s*;\s*\)"),
    "define_property": re.compile(br"Object\s*\.\s*definePropert(?:y|ies)\s*\("),
    "reflect_apply": re.compile(br"Reflect\s*\.\s*apply\s*\("),
    "regexp_constructor": re.compile(br"(?:new\s+)?RegExp\s*\("),
    "to_string_call": re.compile(br"\.\s*toString\s*\("),
    "base64_blob": re.compile(br"[A-Za-z0-9+/]{256,}={0,2}"),
    "hex_escape_blob": re.compile(br"(?:\\x[0-9a-fA-F]{2}){32,}"),
    "unicode_escape_blob": re.compile(br"(?:\\u[0-9a-fA-F]{4}){16,}"),
    "push_call": re.compile(br"\.\s*push\s*\("),
    "shift_call": re.compile(br"\.\s*shift\s*\("),
}

CANDIDATE_QUERIES = {
    "javascript": """
        SELECT c.representative_path FROM current_body c JOIN body_scan s USING (sha256)
        WHERE s.content_kind LIKE 'javascript%' AND s.nuisance IS NULL ORDER BY c.sha256
    """,
    "runtime-confirmed": """
        SELECT c.representative_path FROM current_body c JOIN body_scan s USING (sha256)
        WHERE c.runtime_present = 1 AND s.nuisance IS NULL ORDER BY c.sha256
    """,
    "network-only-javascript": """
        SELECT c.representative_path FROM current_body c JOIN body_scan s USING (sha256)
        WHERE c.network_present = 1 AND c.runtime_present = 0 AND s.content_kind = 'javascript'
          AND s.nuisance IS NULL ORDER BY c.sha256
    """,
    "dynamic-code": """
        SELECT DISTINCT c.representative_path FROM current_body c JOIN body_scan s USING (sha256)
        JOIN body_feature f USING (sha256)
        WHERE s.nuisance IS NULL AND f.feature IN ('eval_call','function_constructor','dynamic_import','dynamic_code_shape')
        ORDER BY c.sha256
    """,
    "obfuscation": """
        SELECT DISTINCT c.representative_path FROM current_body c JOIN body_scan s USING (sha256)
        JOIN body_feature f USING (sha256)
        WHERE s.nuisance IS NULL AND f.feature IN (
          'javascript_obfuscator_names','packer_eval','anti_debug_interval','flattening_shape',
          'self_defending_shape','string_table_rotation_shape','encoded_payload_shape')
        ORDER BY c.sha256
    """,
    "flattening": """
        SELECT c.representative_path FROM current_body c JOIN body_feature f USING (sha256)
        WHERE f.feature = 'flattening_shape' ORDER BY c.sha256
    """,
    "encoded-payload": """
        SELECT c.representative_path FROM current_body c JOIN body_feature f USING (sha256)
        WHERE f.feature = 'encoded_payload_shape' ORDER BY c.sha256
    """,
    "wasm": """
        SELECT DISTINCT c.representative_path FROM current_body c LEFT JOIN body_scan s USING (sha256)
        LEFT JOIN body_feature f USING (sha256)
        WHERE s.content_kind = 'wasm' OR f.feature IN ('webassembly_api','wasm_base64_magic','wasm_carrier_shape')
        ORDER BY c.sha256
    """,
    "workers": """
        SELECT c.representative_path FROM current_body c JOIN body_feature f USING (sha256)
        WHERE f.feature = 'worker_constructor' ORDER BY c.sha256
    """,
    "source-maps": """
        SELECT DISTINCT c.representative_path FROM current_body c JOIN body_feature f USING (sha256)
        WHERE f.feature IN ('source_map_ref','inline_sourcemap') ORDER BY c.sha256
    """,
    "large-minified": """
        SELECT c.representative_path FROM current_body c JOIN body_feature f USING (sha256)
        WHERE f.feature = 'large_minified' ORDER BY c.sha256
    """,
    "rare-javascript": """
        SELECT c.representative_path FROM current_body c JOIN body_scan s USING (sha256)
        WHERE s.content_kind LIKE 'javascript%' AND s.nuisance IS NULL
          AND c.cohort_count = 1 AND c.domain_count <= 2
        ORDER BY c.capture_count ASC, c.bytes DESC, c.sha256
    """,
    "interesting": """
        SELECT DISTINCT c.representative_path FROM current_body c JOIN body_scan s USING (sha256)
        JOIN body_feature f USING (sha256)
        WHERE s.nuisance IS NULL AND s.content_kind LIKE 'javascript%' AND (
          f.feature IN ('dynamic_code_shape','flattening_shape','encoded_payload_shape','self_defending_shape',
                        'string_table_rotation_shape','wasm_carrier_shape','javascript_obfuscator_names',
                        'packer_eval','anti_debug_interval','worker_constructor')
          OR (f.feature = 'large_minified' AND c.cohort_count = 1)
        )
        ORDER BY c.cohort_count ASC, c.domain_count ASC, c.bytes DESC, c.sha256
    """,
}


def header_value(headers: dict, name: str) -> str | None:
    wanted = name.lower()
    for key, value in (headers or {}).items():
        if str(key).lower() == wanted:
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
    encodings: list[str] = []
    for encoding in (declared_charset(row), "utf-8", "cp1252", "latin1"):
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
            return stripped[len(prefix):].lstrip("\r\n \t"), prefix
    return stripped, None


def looks_like_plain_text_error(text: str) -> bool:
    value = text.strip()
    if not value or len(value) > 512:
        return False
    if any(ord(char) < 32 and char not in "\t\r\n" for char in value):
        return False
    if 16 <= len(value) <= 128 and all(char in "0123456789abcdefABCDEF" for char in value):
        return True
    if any(char in value for char in "{}[]();="):
        return False
    return len(value.split()) >= 2


def transport_javascript(row: dict) -> bool:
    resource_type = (row.get("resourceType") or "").lower()
    mime = (row.get("mimeType") or "").lower()
    path = urlparse(row.get("url") or "").path.lower()
    return resource_type == "script" or "javascript" in mime or "ecmascript" in mime or path.endswith((".js", ".mjs", ".cjs"))


def transport_wasm(row: dict) -> bool:
    resource_type = (row.get("resourceType") or "").lower()
    mime = (row.get("mimeType") or "").lower()
    path = urlparse(row.get("url") or "").path.lower()
    return resource_type == "wasm" or "application/wasm" in mime or path.endswith(".wasm")


def classify_network_body(raw: bytes, row: dict) -> str:
    if not transport_javascript(row):
        return "not_javascript_transport"
    try:
        text, _, _ = decode_text(raw, row)
    except UnicodeDecodeError:
        return "javascript_binary_or_undecodable"
    candidate, xssi = strip_xssi_prefix(text)
    lower_prefix = candidate[:256].lower()
    if lower_prefix.startswith(("<!doctype", "<html", "<head", "<body", "<script")):
        return "html"
    if lower_prefix.startswith(("<?xml", "<svg")):
        return "text"
    if xssi or candidate.startswith(("{", "[")):
        try:
            json.loads(candidate)
        except json.JSONDecodeError:
            pass
        else:
            return "json"
    if (row.get("resourceType") or "").lower() in DATA_RESOURCE_TYPES:
        return "data_text"
    if looks_like_plain_text_error(candidate):
        return "plain_text"
    if row.get("failure"):
        return "incomplete_javascript"
    return "javascript"


def instrumentation_kind(source: str) -> str | None:
    if "// packages/injected/src/utilityScript.ts" in source or "utilityScript.evaluate" in source:
        return "playwright-utility"
    if "// packages/injected/src/storageScript.ts" in source:
        return "playwright-storage"
    if source.lstrip().startswith("(phrases) => {") and "document.querySelectorAll" in source:
        return "recorder-consent-fallback"
    if "detectedCmps" in source and "heuristicPatterns" in source:
        return "recorder-autoconsent-probe"
    if "localStorage: dump(localStorage)" in source and "sessionStorage: dump(sessionStorage)" in source:
        return "recorder-storage-dump"
    if "XMLSerializer().serializeToString(document.doctype)" in source:
        return "recorder-html-snapshot"
    if len(source) <= 4096 and "document.documentElement.scrollHeight" in source and (
        "scrollY" in source or "scrollTo({ top:" in source or source.lstrip().startswith("() => Math.max(")
    ):
        return "recorder-scroll"
    return None


def cohort_name(capture: Path) -> str:
    for name in ("search-result.json", "batch-result.json"):
        path = capture / name
        if path.is_file():
            try:
                value = json.loads(path.read_text(encoding="utf-8")).get("query_id")
            except (OSError, json.JSONDecodeError):
                value = None
            if value:
                return str(value)
    match = re.fullmatch(r"\d+-(.+)-[0-9a-f]{10}", capture.name)
    return match.group(1) if match else capture.name


def compact_network_row(row: dict) -> dict:
    return {
        "url": row.get("url"),
        "resourceType": row.get("resourceType"),
        "mimeType": row.get("mimeType"),
        "responseHeaders": row.get("responseHeaders") or {},
        "failure": row.get("failure"),
    }


def new_group(digest: str, path: Path, size: int) -> dict:
    return {
        "sha256": digest,
        "path": str(path),
        "bytes": size,
        "network_occurrences": 0,
        "network_script_occurrences": 0,
        "runtime_occurrences": 0,
        "runtime_captures": set(),
        "captures": set(),
        "cohorts": set(),
        "domains": set(),
        "classification_rows": [],
        "classification_signatures": set(),
        "wasm_transport": False,
    }


def collect_metadata(capture_root: Path) -> tuple[dict[str, dict], int, list[dict]]:
    groups: dict[str, dict] = {}
    bad_inputs: list[dict] = []
    manifests = sorted(capture_root.glob("*/recorder-manifest.json"))
    for index, manifest in enumerate(manifests, 1):
        capture = manifest.parent
        cohort = cohort_name(capture)
        network_path = capture / "network.json"
        if network_path.is_file():
            try:
                network_rows = json.loads(network_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                bad_inputs.append({"capture": capture.name, "file": "network.json", "error": repr(exc)})
                network_rows = []
            for row in network_rows:
                body = row.get("body") or {}
                digest, rel = body.get("sha256"), body.get("path")
                if not digest or not rel:
                    continue
                path = capture / rel
                if not path.is_file():
                    bad_inputs.append({"capture": capture.name, "file": rel, "error": "missing body"})
                    continue
                group = groups.setdefault(digest, new_group(digest, path, int(body.get("size") or path.stat().st_size)))
                group["network_occurrences"] += 1
                group["captures"].add(capture.name)
                group["cohorts"].add(cohort)
                if (row.get("resourceType") or "").lower() == "script":
                    group["network_script_occurrences"] += 1
                url = row.get("url") or ""
                domain = urlparse(url).netloc.lower()
                if domain:
                    group["domains"].add(domain)
                if transport_wasm(row):
                    group["wasm_transport"] = True
                if transport_javascript(row):
                    signature = (
                        row.get("resourceType"), row.get("mimeType"), declared_charset(row),
                        bool(row.get("failure")), urlparse(url).path.rsplit(".", 1)[-1].lower(),
                    )
                    if signature not in group["classification_signatures"] and len(group["classification_rows"]) < 12:
                        group["classification_signatures"].add(signature)
                        group["classification_rows"].append(compact_network_row(row))

        runtime_path = capture / "runtime-scripts.json"
        if runtime_path.is_file():
            try:
                runtime_rows = json.loads(runtime_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                bad_inputs.append({"capture": capture.name, "file": "runtime-scripts.json", "error": repr(exc)})
                runtime_rows = []
            for row in runtime_rows:
                body = row.get("captured") or {}
                if body.get("kind") != "javascript":
                    continue
                digest, rel = body.get("sha256") or row.get("hash"), body.get("path")
                if not digest or not rel:
                    continue
                path = capture / rel
                if not path.is_file():
                    bad_inputs.append({"capture": capture.name, "file": rel, "error": "missing runtime script"})
                    continue
                group = groups.setdefault(digest, new_group(digest, path, int(body.get("size") or path.stat().st_size)))
                group["runtime_occurrences"] += 1
                group["runtime_captures"].add(capture.name)
                group["captures"].add(capture.name)
                group["cohorts"].add(cohort)
                url = row.get("url") or ""
                domain = urlparse(url).netloc.lower()
                if domain:
                    group["domains"].add(domain)
        if index % 500 == 0:
            print(f"metadata {index}/{len(manifests)} captures; {len(groups)} unique bodies", flush=True)
    return groups, len(manifests), bad_inputs


def scan_body(item: tuple[str, str, bool, bool, bool, list[dict]]) -> dict:
    digest, path_str, network_present, runtime_present, wasm_transport, classification_rows = item
    path = Path(path_str)
    try:
        raw = path.read_bytes()
    except OSError as exc:
        return {"sha256": digest, "error": repr(exc), "features": {}}

    if runtime_present:
        content_kind = "javascript_runtime_confirmed" if network_present else "javascript_runtime_only"
    elif wasm_transport or raw.startswith(b"\x00asm"):
        content_kind = "wasm"
    elif classification_rows:
        categories = [classify_network_body(raw, row) for row in classification_rows]
        content_kind = "javascript" if "javascript" in categories else categories[0]
    else:
        content_kind = "other"

    should_scan_text = content_kind.startswith("javascript")
    nuisance = None
    if should_scan_text and not network_present:
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            text = None
        if text is not None:
            helper = instrumentation_kind(text)
            if helper:
                nuisance = f"capture_instrumentation:{helper}"
            elif text.strip() in TRIVIAL_ANONYMOUS:
                nuisance = "trivial_anonymous_expression"

    features: dict[str, int] = {}
    line_count = None
    max_line_bytes = None
    likely_minified = None
    if should_scan_text and nuisance is None:
        lines = raw.splitlines() or [b""]
        line_count = len(lines)
        max_line_bytes = max(map(len, lines))
        likely_minified = len(raw) >= 1024 and (line_count <= 4 or max_line_bytes >= 4096)
        for name, pattern in FEATURES.items():
            count = len(pattern.findall(raw))
            if count:
                features[name] = count
        if features.get("eval_call") or features.get("function_constructor") or features.get("dynamic_import"):
            features["dynamic_code_shape"] = 1
        if features.get("switch_statement") and (features.get("while_true") or features.get("for_ever")):
            features["flattening_shape"] = 1
        if (
            (features.get("base64_blob") and (features.get("atob") or features.get("decode_uri_component")))
            or (features.get("hex_escape_blob") and (features.get("from_char_code") or features.get("unescape_call")))
            or (features.get("unicode_escape_blob") and features.get("decode_uri_component"))
        ):
            features["encoded_payload_shape"] = 1
        if features.get("debugger_statement") and features.get("to_string_call") and features.get("regexp_constructor"):
            features["self_defending_shape"] = 1
        if features.get("javascript_obfuscator_names") and features.get("push_call") and features.get("shift_call"):
            features["string_table_rotation_shape"] = 1
        if features.get("wasm_base64_magic") and (features.get("atob") or features.get("from_char_code")):
            features["wasm_carrier_shape"] = 1
        if likely_minified and len(raw) >= 65536:
            features["large_minified"] = 1
    elif content_kind == "wasm" and raw.startswith(b"\x00asm"):
        features["wasm_binary_magic"] = 1

    return {
        "sha256": digest,
        "content_kind": content_kind,
        "nuisance": nuisance,
        "bytes": len(raw),
        "line_count": line_count,
        "max_line_bytes": max_line_bytes,
        "likely_minified": int(likely_minified) if likely_minified is not None else None,
        "features": features,
        "error": None,
    }


def open_database(path: Path) -> sqlite3.Connection:
    path.parent.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(path)
    db.execute("PRAGMA journal_mode=WAL")
    db.execute("PRAGMA synchronous=NORMAL")
    db.executescript("""
        CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS current_body (
          sha256 TEXT PRIMARY KEY, representative_path TEXT NOT NULL, bytes INTEGER NOT NULL,
          network_occurrences INTEGER NOT NULL, network_script_occurrences INTEGER NOT NULL,
          runtime_occurrences INTEGER NOT NULL, capture_count INTEGER NOT NULL,
          cohort_count INTEGER NOT NULL, domain_count INTEGER NOT NULL,
          network_present INTEGER NOT NULL, runtime_present INTEGER NOT NULL, wasm_transport INTEGER NOT NULL
        );
        CREATE TABLE IF NOT EXISTS body_cohort (
          sha256 TEXT NOT NULL, cohort TEXT NOT NULL, PRIMARY KEY (sha256, cohort)
        ) WITHOUT ROWID;
        CREATE TABLE IF NOT EXISTS body_domain (
          sha256 TEXT NOT NULL, domain TEXT NOT NULL, PRIMARY KEY (sha256, domain)
        ) WITHOUT ROWID;
        CREATE TABLE IF NOT EXISTS body_scan (
          sha256 TEXT PRIMARY KEY, scan_version INTEGER NOT NULL, content_kind TEXT NOT NULL,
          nuisance TEXT, bytes INTEGER NOT NULL, line_count INTEGER, max_line_bytes INTEGER,
          likely_minified INTEGER, scan_error TEXT
        );
        CREATE TABLE IF NOT EXISTS body_feature (
          sha256 TEXT NOT NULL, feature TEXT NOT NULL, count INTEGER NOT NULL,
          PRIMARY KEY (sha256, feature)
        ) WITHOUT ROWID;
        CREATE INDEX IF NOT EXISTS current_runtime_idx ON current_body(runtime_present);
        CREATE INDEX IF NOT EXISTS current_network_idx ON current_body(network_present);
        CREATE INDEX IF NOT EXISTS scan_kind_idx ON body_scan(content_kind);
        CREATE INDEX IF NOT EXISTS scan_nuisance_idx ON body_scan(nuisance);
        CREATE INDEX IF NOT EXISTS feature_name_idx ON body_feature(feature);
        CREATE INDEX IF NOT EXISTS cohort_name_idx ON body_cohort(cohort);
        CREATE INDEX IF NOT EXISTS domain_name_idx ON body_domain(domain);
    """)
    return db


def emit_candidates(db: sqlite3.Connection, directory: Path) -> dict[str, int]:
    directory.mkdir(parents=True, exist_ok=True)
    counts = {}
    for name, query in CANDIDATE_QUERIES.items():
        rows = [str(row[0]) for row in db.execute(query)]
        (directory / f"{name}.txt").write_text("".join(f"{path}\n" for path in rows), encoding="utf-8")
        counts[name] = len(rows)
    return counts


def build(args: argparse.Namespace) -> dict:
    groups, capture_count, bad_inputs = collect_metadata(args.captures)
    db = open_database(args.database)
    cached = {
        row[0]
        for row in db.execute("SELECT sha256 FROM body_scan WHERE scan_version = ? AND scan_error IS NULL", (SCAN_VERSION,))
    }
    scan_items = []
    for digest, group in groups.items():
        should_scan = bool(group["runtime_occurrences"] or group["classification_rows"] or group["wasm_transport"])
        if should_scan and digest not in cached:
            scan_items.append((
                digest, group["path"], bool(group["network_occurrences"]), bool(group["runtime_occurrences"]),
                bool(group["wasm_transport"]), group["classification_rows"],
            ))
    print(f"catalog current={len(groups)} cached_scans={len(cached & groups.keys())} new_scans={len(scan_items)}", flush=True)

    scan_results = []
    if scan_items:
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            for index, result in enumerate(pool.map(scan_body, scan_items, chunksize=64), 1):
                scan_results.append(result)
                if index % 10000 == 0:
                    print(f"scanned {index}/{len(scan_items)} new bodies", flush=True)

    with db:
        db.execute("DELETE FROM current_body")
        db.execute("DELETE FROM body_cohort")
        db.execute("DELETE FROM body_domain")
        for digest, group in groups.items():
            db.execute(
                "INSERT INTO current_body VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                (digest, group["path"], group["bytes"], group["network_occurrences"], group["network_script_occurrences"],
                 group["runtime_occurrences"], len(group["captures"]), len(group["cohorts"]), len(group["domains"]),
                 int(bool(group["network_occurrences"])), int(bool(group["runtime_occurrences"])), int(group["wasm_transport"])),
            )
            db.executemany("INSERT INTO body_cohort VALUES (?,?)", ((digest, value) for value in sorted(group["cohorts"])))
            db.executemany("INSERT INTO body_domain VALUES (?,?)", ((digest, value) for value in sorted(group["domains"])))
        for result in scan_results:
            digest = result["sha256"]
            db.execute("DELETE FROM body_feature WHERE sha256 = ?", (digest,))
            if result["error"]:
                db.execute(
                    "INSERT INTO body_scan VALUES (?,?,?,?,?,?,?,?,?) ON CONFLICT(sha256) DO UPDATE SET scan_version=excluded.scan_version, content_kind=excluded.content_kind, nuisance=excluded.nuisance, bytes=excluded.bytes, line_count=excluded.line_count, max_line_bytes=excluded.max_line_bytes, likely_minified=excluded.likely_minified, scan_error=excluded.scan_error",
                    (digest, SCAN_VERSION, "scan_error", None, 0, None, None, None, result["error"]),
                )
                continue
            db.execute(
                "INSERT INTO body_scan VALUES (?,?,?,?,?,?,?,?,?) ON CONFLICT(sha256) DO UPDATE SET scan_version=excluded.scan_version, content_kind=excluded.content_kind, nuisance=excluded.nuisance, bytes=excluded.bytes, line_count=excluded.line_count, max_line_bytes=excluded.max_line_bytes, likely_minified=excluded.likely_minified, scan_error=excluded.scan_error",
                (digest, SCAN_VERSION, result["content_kind"], result["nuisance"], result["bytes"], result["line_count"],
                 result["max_line_bytes"], result["likely_minified"], None),
            )
            db.executemany(
                "INSERT INTO body_feature VALUES (?,?,?)",
                ((digest, name, count) for name, count in sorted(result["features"].items())),
            )
        db.execute("INSERT OR REPLACE INTO meta VALUES ('schema_version', ?)", (str(SCHEMA_VERSION),))
        db.execute("INSERT OR REPLACE INTO meta VALUES ('scan_version', ?)", (str(SCAN_VERSION),))
        db.execute("INSERT OR REPLACE INTO meta VALUES ('capture_count', ?)", (str(capture_count),))
        db.execute("INSERT OR REPLACE INTO meta VALUES ('current_body_count', ?)", (str(len(groups)),))

    candidates = emit_candidates(db, args.candidate_dir)
    feature_counts = dict(db.execute(
        "SELECT feature, COUNT(*) FROM body_feature f JOIN current_body c USING (sha256) GROUP BY feature ORDER BY COUNT(*) DESC, feature"
    ))
    kind_counts = dict(db.execute(
        "SELECT content_kind, COUNT(*) FROM body_scan s JOIN current_body c USING (sha256) GROUP BY content_kind ORDER BY COUNT(*) DESC, content_kind"
    ))
    nuisance_counts = dict(db.execute(
        "SELECT nuisance, COUNT(*) FROM body_scan s JOIN current_body c USING (sha256) WHERE nuisance IS NOT NULL GROUP BY nuisance ORDER BY COUNT(*) DESC, nuisance"
    ))
    summary = {
        "schema": "js-redox-corpus-catalog/v1",
        "schema_version": SCHEMA_VERSION,
        "scan_version": SCAN_VERSION,
        "captures": capture_count,
        "current_unique_bodies": len(groups),
        "cached_scans_reused": len(cached & groups.keys()),
        "new_scans": len(scan_items),
        "bad_inputs": len(bad_inputs),
        "content_kinds": kind_counts,
        "nuisance": nuisance_counts,
        "features": feature_counts,
        "candidates": candidates,
        "database": str(args.database),
        "candidate_dir": str(args.candidate_dir),
    }
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2), flush=True)
    db.close()
    return summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--captures", type=Path, default=DEFAULT_CORPUS / "captures")
    parser.add_argument("--database", type=Path, default=DEFAULT_CORPUS / "preclass" / "corpus.sqlite")
    parser.add_argument("--candidate-dir", type=Path, default=DEFAULT_CORPUS / "preclass" / "candidates")
    parser.add_argument("--summary", type=Path, default=DEFAULT_CORPUS / "preclass" / "summary.json")
    parser.add_argument("--jobs", type=int, default=max(1, min(8, os.cpu_count() or 4)))
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.jobs < 1:
        raise SystemExit("--jobs must be >= 1")
    build(args)


if __name__ == "__main__":
    main()
