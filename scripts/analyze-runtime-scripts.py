#!/usr/bin/env python3
"""Classify Debugger-captured runtime scripts from a CloakBrowser recorder bundle.

The raw recorder intentionally captures every script Chromium exposes, including
network scripts, inline scripts, generated code, and automation-world helpers.
This stage turns that superset into provenance instead of pretending every
Debugger.scriptParsed event is an independent application source file.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import re
from collections import Counter, defaultdict
from html.parser import HTMLParser
from pathlib import Path
from typing import Iterable

ALPINE_PREFIX = "(async function anonymous(__self,scope\n) {\nwith (scope) { __self.result = "
ALPINE_SUFFIX = " }; __self.finished = true; return __self.result;\n})"
ALPINE_IIFE_RE = re.compile(r"^\(async\(\)=>\{ (?P<body>.*) \}\)\(\)$", re.DOTALL)
STRING_SINGLE_RE = re.compile(r"'(?:\\.|[^'\\])*'")
STRING_DOUBLE_RE = re.compile(r'"(?:\\.|[^"\\])*"')
NUMBER_RE = re.compile(r"(?<![\w$])(?:\d+(?:\.\d+)?)(?![\w$])")
XFOR_RE = re.compile(r"\s+(?:in|of)\s+", re.IGNORECASE)


class ScriptHTMLParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=False)
        self._in_script = False
        self._script_parts: list[str] = []
        self._script_attrs: dict[str, str] = {}
        self.scripts: list[tuple[str, dict[str, str]]] = []
        self.directives: list[tuple[int, str, str, str]] = []
        self._tag_ordinal = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self._tag_ordinal += 1
        attrs_dict = {key: value or "" for key, value in attrs}
        if tag.lower() == "script":
            self._in_script = True
            self._script_parts = []
            self._script_attrs = attrs_dict
        for key, value in attrs:
            if value is None:
                continue
            if key.startswith("x-") or key.startswith("@") or key.startswith(":"):
                self.directives.append((self._tag_ordinal, tag, key, value))

    def handle_endtag(self, tag: str) -> None:
        if tag.lower() == "script" and self._in_script:
            self.scripts.append(("".join(self._script_parts), self._script_attrs))
            self._in_script = False
            self._script_parts = []
            self._script_attrs = {}

    def handle_data(self, data: str) -> None:
        if self._in_script:
            self._script_parts.append(data)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def load_har_html(capture: Path) -> Iterable[tuple[str, str, int]]:
    har_path = capture / "capture.har"
    if not har_path.is_file():
        return []
    har = json.loads(har_path.read_text())
    rows: list[tuple[str, str, int]] = []
    for index, entry in enumerate(har.get("log", {}).get("entries", [])):
        response = entry.get("response", {})
        content = response.get("content", {})
        mime = str(content.get("mimeType") or "").lower()
        if "html" not in mime:
            continue
        text = content.get("text")
        if not isinstance(text, str):
            continue
        if content.get("encoding") == "base64":
            try:
                text = base64.b64decode(text).decode("utf-8", errors="replace")
            except (ValueError, UnicodeDecodeError):
                continue
        rows.append((entry.get("request", {}).get("url", ""), text, index))
    return rows


def html_provenance(capture: Path) -> tuple[dict[str, list[dict]], dict[str, list[dict]]]:
    inline_by_hash: dict[str, list[dict]] = defaultdict(list)
    directives_by_value: dict[str, list[dict]] = defaultdict(list)

    def ingest_html(text: str, provenance: dict, include_directives: bool) -> None:
        parser = ScriptHTMLParser()
        parser.feed(text)
        for script_index, (source, attrs) in enumerate(parser.scripts):
            if not source.strip():
                continue
            inline_by_hash[sha256_text(source)].append(
                {**provenance, "script_index": script_index, "attrs": attrs}
            )
        if include_directives:
            for tag_ordinal, tag, attr, value in parser.directives:
                directives_by_value[value].append(
                    {
                        **provenance,
                        "tag_ordinal": tag_ordinal,
                        "tag": tag,
                        "attribute": attr,
                    }
                )

    for url, text, entry_index in load_har_html(capture):
        ingest_html(
            text,
            {"source": "har_html", "url": url, "entry_index": entry_index},
            False,
        )
    frames = capture / "frames"
    if frames.is_dir():
        for frame in sorted(frames.glob("*.html")):
            ingest_html(
                frame.read_text(errors="replace"),
                {"source": "final_frame", "path": str(frame.relative_to(capture))},
                True,
            )
    return inline_by_hash, directives_by_value


def recover_alpine_expression(source: str) -> tuple[str, str] | None:
    if not (source.startswith(ALPINE_PREFIX) and source.endswith(ALPINE_SUFFIX)):
        return None
    compiled = source[len(ALPINE_PREFIX) : -len(ALPINE_SUFFIX)]
    match = ALPINE_IIFE_RE.fullmatch(compiled)
    original = match.group("body") if match else compiled
    return compiled, original


def normalize_expression_shape(expression: str) -> str:
    value = STRING_SINGLE_RE.sub("'<str>'", expression)
    value = STRING_DOUBLE_RE.sub('"<str>"', value)
    value = NUMBER_RE.sub("<num>", value)
    return re.sub(r"\s+", " ", value).strip()


def recover_gtm_custom_javascript(source: str) -> str | None:
    value = source.strip()
    if not (value.startswith("(function(){") or value.startswith("(function () {")):
        return None
    if "google_tag_manager" not in value and "googletagmanager" not in value.lower():
        return None
    return normalize_expression_shape(value)


def match_directives(expression: str, directives: dict[str, list[dict]]) -> tuple[str, list[dict]]:
    exact = directives.get(expression)
    if exact:
        return "exact", exact

    placeholder = " = __placeholder"
    if expression.endswith(placeholder):
        target = expression[: -len(placeholder)]
        matches = [row for row in directives.get(target, []) if row["attribute"] == "x-model"]
        if matches:
            return "x-model-setter", matches

    matches: list[dict] = []
    for value, rows in directives.items():
        xfor_rows = [row for row in rows if row["attribute"] == "x-for"]
        if not xfor_rows:
            continue
        split = XFOR_RE.split(value, maxsplit=1)
        if len(split) == 2 and split[1].strip() == expression.strip():
            matches.extend(xfor_rows)
    if matches:
        return "x-for-rhs", matches
    return "unmatched", []


def event_cdp_session(event: dict) -> str:
    return str(event.get("cdpSession") or "main")


def generation_origins(
    event_rows: list[dict], events_by_script_id: dict[tuple[str, str], dict], max_depth: int = 32
) -> list[dict]:
    origins: list[dict] = []
    seen_origins: set[str] = set()
    for event in event_rows:
        cdp_session = event_cdp_session(event)
        child_script_id = str(event.get("scriptId") or "")
        current = event
        visited = {child_script_id} if child_script_id else set()
        chain: list[dict] = []
        for _ in range(max_depth):
            stack = current.get("stackTrace") or {}
            frames = stack.get("callFrames") or []
            if not frames:
                break
            frame = frames[0]
            parent_script_id = str(frame.get("scriptId") or "")
            if not parent_script_id or parent_script_id in visited:
                break
            parent = events_by_script_id.get((cdp_session, parent_script_id))
            captured = (parent or {}).get("captured") or {}
            chain.append(
                {
                    "cdp_session": cdp_session,
                    "script_id": parent_script_id,
                    "sha256": captured.get("sha256"),
                    "url": (parent or {}).get("url") or frame.get("url") or "",
                    "function_name": frame.get("functionName") or "",
                    "line_number": frame.get("lineNumber"),
                    "column_number": frame.get("columnNumber"),
                }
            )
            visited.add(parent_script_id)
            if parent is None:
                break
            current = parent
        if not chain:
            continue
        origin = {"cdp_session": cdp_session, "child_script_id": child_script_id, "chain": chain}
        frozen = json.dumps(origin, sort_keys=True, separators=(",", ":"))
        if frozen not in seen_origins:
            seen_origins.add(frozen)
            origins.append(origin)
    return origins


def document_inline_origins(event_rows: list[dict]) -> list[dict]:
    origins: list[dict] = []
    for event in event_rows:
        url = str(event.get("url") or "")
        if not (url in {"about:blank", "about:srcdoc"} or url.startswith("data:text/html")):
            continue
        if event.get("stackTrace"):
            continue
        aux = event.get("executionContextAuxData") or {}
        if aux.get("isDefault") is not True:
            continue
        start_line = event.get("startLine") or 0
        start_column = event.get("startColumn") or 0
        if url != "about:srcdoc" and start_line == 0 and start_column == 0:
            continue
        origins.append(
            {
                "cdp_session": event_cdp_session(event),
                "script_id": event.get("scriptId"),
                "url": url,
                "frame_id": aux.get("frameId"),
                "start_line": event.get("startLine"),
                "start_column": event.get("startColumn"),
                "end_line": event.get("endLine"),
                "end_column": event.get("endColumn"),
                "embedder_name": event.get("embedderName"),
            }
        )
    return origins


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
    if "document.documentElement.scrollHeight" in source and (
        "scrollY" in source or "scrollTo({ top:" in source or source.lstrip().startswith("() => Math.max(")
    ):
        return "recorder-scroll"
    return None


def analyze(capture: Path) -> dict:
    runtime_manifest_path = capture / "runtime-scripts.json"
    runtime_dir = capture / "runtime-scripts"
    if not runtime_manifest_path.is_file() or not runtime_dir.is_dir():
        raise SystemExit(f"not a recorder runtime-script bundle: {capture}")

    events = json.loads(runtime_manifest_path.read_text())
    inline_by_hash, directives = html_provenance(capture)
    body_hashes = {path.name for path in (capture / "bodies").iterdir()} if (capture / "bodies").is_dir() else set()
    network_urls: set[str] = set()
    network_path = capture / "network.json"
    if network_path.is_file():
        try:
            for record in json.loads(network_path.read_text()):
                url = record.get("url")
                if isinstance(url, str) and url:
                    network_urls.add(url)
        except (json.JSONDecodeError, OSError):
            pass
    har_path = capture / "capture.har"
    if har_path.is_file():
        try:
            for entry in json.loads(har_path.read_text()).get("log", {}).get("entries", []):
                url = entry.get("request", {}).get("url")
                if isinstance(url, str) and url:
                    network_urls.add(url)
        except (json.JSONDecodeError, OSError):
            pass

    events_by_hash: dict[str, list[dict]] = defaultdict(list)
    events_by_script_id = {
        (event_cdp_session(event), str(event.get("scriptId"))): event
        for event in events
        if event.get("scriptId") is not None
    }
    for event in events:
        captured = event.get("captured")
        if captured and captured.get("kind") == "javascript" and captured.get("sha256"):
            events_by_hash[captured["sha256"]].append(event)

    sources = []
    class_counts = Counter()
    class_bytes = Counter()
    instrumentation_counts = Counter()
    alpine_shapes: dict[str, list[str]] = defaultdict(list)
    gtm_shapes: dict[str, list[str]] = defaultdict(list)
    alpine_dom_mapped = 0
    alpine_dom_matches = 0

    for source_path in sorted(runtime_dir.glob("*.js")):
        raw_source = source_path.read_bytes()
        digest = hashlib.sha256(raw_source).hexdigest()
        source = raw_source.decode("utf-8", errors="replace")
        event_rows = events_by_hash.get(digest, [])
        urls = sorted({row.get("url") or "" for row in event_rows if row.get("url")})
        row: dict = {
            "sha256": digest,
            "size": len(raw_source),
            "path": str(source_path.relative_to(capture)),
            "event_count": len(event_rows),
            "script_ids": [event.get("scriptId") for event in event_rows],
            "cdp_sessions": sorted({event_cdp_session(event) for event in event_rows}),
            "execution_context_ids": sorted({event.get("executionContextId") for event in event_rows}),
            "script_instances": [
                {
                    "cdp_session": event_cdp_session(event),
                    "script_id": event.get("scriptId"),
                    "execution_context_id": event.get("executionContextId"),
                }
                for event in event_rows
            ],
            "urls": urls,
        }
        origins = generation_origins(event_rows, events_by_script_id)
        inline_runtime_origins = document_inline_origins(event_rows)
        if inline_runtime_origins:
            row["document_inline_origins"] = inline_runtime_origins
        if origins:
            roots = [origin["chain"][-1] for origin in origins if origin.get("chain")]
            row["generated"] = {
                "origins": origins,
                "root_sha256s": sorted(
                    {root.get("sha256") for root in roots if root.get("sha256")}
                ),
                "root_urls": sorted({root.get("url") for root in roots if root.get("url")}),
                "max_depth": max(len(origin["chain"]) for origin in origins),
            }

        if digest in body_hashes:
            classification = "network_response"
        elif digest in inline_by_hash:
            classification = "inline_script"
            row["inline_origins"] = inline_by_hash[digest]
        elif urls and any(url in network_urls for url in urls):
            classification = "network_observed"
        elif inline_runtime_origins:
            classification = "document_inline_script"
        else:
            alpine = recover_alpine_expression(source)
            if alpine:
                classification = "alpine_expression"
                compiled, expression = alpine
                mapping_kind, matches = match_directives(expression, directives)
                shape = normalize_expression_shape(expression)
                row["alpine"] = {
                    "compiled_expression": compiled,
                    "expression": expression,
                    "shape": shape,
                    "dom_mapping_kind": mapping_kind,
                    "dom_matches": matches,
                }
                alpine_shapes[shape].append(digest)
                if matches:
                    alpine_dom_mapped += 1
                    alpine_dom_matches += len(matches)
            else:
                gtm_shape = recover_gtm_custom_javascript(source)
                if gtm_shape:
                    classification = "gtm_custom_javascript"
                    row["gtm"] = {"shape": gtm_shape}
                    gtm_shapes[gtm_shape].append(digest)
                else:
                    helper = instrumentation_kind(source)
                    if helper:
                        classification = "capture_instrumentation"
                        row["instrumentation_kind"] = helper
                        instrumentation_counts[helper] += 1
                    elif origins:
                        classification = "generated_runtime"
                    else:
                        classification = "anonymous_runtime"
        row["classification"] = classification
        class_counts[classification] += 1
        class_bytes[classification] += row["size"]
        sources.append(row)

    families = [
        {
            "shape": shape,
            "source_count": len(hashes),
            "source_hashes": hashes,
        }
        for shape, hashes in sorted(alpine_shapes.items(), key=lambda item: (-len(item[1]), item[0]))
    ]

    gtm_families = [
        {
            "shape": shape,
            "source_count": len(hashes),
            "source_hashes": hashes,
        }
        for shape, hashes in sorted(gtm_shapes.items(), key=lambda item: (-len(item[1]), item[0]))
    ]

    return {
        "schema": "js-redox-runtime-scripts/v1",
        "capture": str(capture),
        "summary": {
            "script_parsed_events": len(events),
            "captured_javascript_events": sum(len(rows) for rows in events_by_hash.values()),
            "unique_javascript_sources": len(sources),
            "unique_javascript_bytes": sum(row["size"] for row in sources),
            "classifications": dict(sorted(class_counts.items())),
            "classification_bytes": dict(sorted(class_bytes.items())),
            "alpine_dom_mapped_sources": alpine_dom_mapped,
            "alpine_dom_match_occurrences": alpine_dom_matches,
            "alpine_expression_shapes": len(alpine_shapes),
            "gtm_expression_shapes": len(gtm_shapes),
            "capture_instrumentation_kinds": dict(sorted(instrumentation_counts.items())),
            "generated_runtime_sources": class_counts["generated_runtime"],
            "anonymous_runtime_sources": class_counts["anonymous_runtime"],
        },
        "alpine_families": families,
        "gtm_families": gtm_families,
        "sources": sources,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("capture", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    capture = args.capture.resolve()
    report = analyze(capture)
    output = args.output or capture / "runtime-analysis.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    summary = report["summary"]
    classes = ", ".join(f"{key}={value}" for key, value in summary["classifications"].items())
    print(
        f"runtime scripts: {summary['script_parsed_events']} scriptParsed events -> "
        f"{summary['unique_javascript_sources']} unique JS sources; {classes}; "
        f"Alpine DOM mapped={summary['alpine_dom_mapped_sources']}, "
        f"anonymous={summary['anonymous_runtime_sources']}"
    )
    print(f"wrote {output}")


if __name__ == "__main__":
    main()
