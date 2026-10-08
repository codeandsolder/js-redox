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

    events_by_hash: dict[str, list[dict]] = defaultdict(list)
    for event in events:
        captured = event.get("captured")
        if captured and captured.get("kind") == "javascript" and captured.get("sha256"):
            events_by_hash[captured["sha256"]].append(event)

    sources = []
    class_counts = Counter()
    class_bytes = Counter()
    instrumentation_counts = Counter()
    alpine_shapes: dict[str, list[str]] = defaultdict(list)
    alpine_dom_mapped = 0
    alpine_dom_matches = 0

    for source_path in sorted(runtime_dir.glob("*.js")):
        source = source_path.read_text(errors="replace")
        digest = hashlib.sha256(source.encode()).hexdigest()
        event_rows = events_by_hash.get(digest, [])
        urls = sorted({row.get("url") or "" for row in event_rows if row.get("url")})
        row: dict = {
            "sha256": digest,
            "size": len(source.encode()),
            "path": str(source_path.relative_to(capture)),
            "event_count": len(event_rows),
            "script_ids": [event.get("scriptId") for event in event_rows],
            "execution_context_ids": sorted({event.get("executionContextId") for event in event_rows}),
            "urls": urls,
        }

        if digest in body_hashes:
            classification = "network_response"
        elif digest in inline_by_hash:
            classification = "inline_script"
            row["inline_origins"] = inline_by_hash[digest]
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
                helper = instrumentation_kind(source)
                if helper:
                    classification = "capture_instrumentation"
                    row["instrumentation_kind"] = helper
                    instrumentation_counts[helper] += 1
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
            "capture_instrumentation_kinds": dict(sorted(instrumentation_counts.items())),
            "anonymous_runtime_sources": class_counts["anonymous_runtime"],
        },
        "alpine_families": families,
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
