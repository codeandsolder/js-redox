#!/usr/bin/env python3
import argparse
import json
import re
import shutil
import subprocess
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from analysis_artifacts import SOURCE_INDEX, write_artifact

from browser_script_types import inline_script_kind
from content_dedup import default_jobs, link_or_copy, sha256_path
from capture_project import load_manifest

ROOT = Path(__file__).resolve().parents[1]
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


def src_path(raw_path: str) -> str:
    prefix = "resources/"
    if raw_path.startswith(prefix):
        return "src/" + raw_path[len(prefix):]
    return "src/" + raw_path


def declared_charset(resource: dict | None) -> str | None:
    if not resource:
        return None
    candidates = [resource.get("mime_type") or ""]
    for header in resource.get("response_headers") or []:
        if str(header.get("name", "")).lower() == "content-type":
            candidates.append(str(header.get("value", "")))
    for value in candidates:
        match = CHARSET_RE.search(value)
        if match:
            label = match.group(1).strip().lower()
            return WEB_CHARSET_ALIASES.get(label, label)
    return None


def decode_text_bytes(raw: bytes, resource: dict | None) -> tuple[str, str, bool]:
    declared = declared_charset(resource)
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


def materialize_text(source: Path, dest: Path, kind: str, resource: dict | None) -> dict:
    raw = source.read_bytes()
    text, encoding, encoding_fallback = decode_text_bytes(raw, resource)
    transform = "identity_utf8" if encoding == "utf-8" and not encoding_fallback else "text_transcoded_utf8"

    if kind == "json":
        candidate, prefix = strip_xssi_prefix(text)
        try:
            value = json.loads(candidate)
        except json.JSONDecodeError:
            pass
        else:
            text = json.dumps(value, indent=2, ensure_ascii=False) + "\n"
            transform = "json_xssi_unwrapped" if prefix else "json_pretty"

    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(text, encoding="utf-8")
    return {
        "transform": transform,
        "formatted": kind == "json" and transform.startswith("json_"),
        "source_encoding": encoding,
        "encoding_fallback": encoding_fallback,
    }


def format_javascript(formatter: Path, source: Path, dest: Path, resource: dict | None):
    dest.parent.mkdir(parents=True, exist_ok=True)
    raw = source.read_bytes()
    text, encoding, encoding_fallback = decode_text_bytes(raw, resource)
    formatter_source = source
    temp_path = None
    if encoding != "utf-8" or encoding_fallback:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            suffix=".js",
            prefix="js-redox-decoded-",
            dir=dest.parent,
            delete=False,
        ) as temp:
            temp.write(text)
            temp_path = Path(temp.name)
        formatter_source = temp_path
    try:
        cp = subprocess.run(
            [str(formatter), str(formatter_source), str(dest)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=120,
        )
    finally:
        if temp_path is not None:
            temp_path.unlink(missing_ok=True)

    if cp.returncode == 0:
        return {
            "transform": "oxc_parse_codegen",
            "formatted": True,
            "format_error": None,
            "source_encoding": encoding,
            "encoding_fallback": encoding_fallback,
        }
    dest.write_text(text, encoding="utf-8")
    return {
        "transform": "utf8_raw_fallback",
        "formatted": False,
        "format_error": cp.stderr[-1000:],
        "source_encoding": encoding,
        "encoding_fallback": encoding_fallback,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("project", type=Path)
    ap.add_argument(
        "--formatter",
        type=Path,
        default=ROOT / ".cargo-target-nodebug/debug/js-format",
    )
    ap.add_argument("--jobs", type=int, default=default_jobs())
    args = ap.parse_args()
    jobs = max(1, args.jobs)

    project = args.project.resolve()
    manifest = load_manifest(project)

    units = []
    seen = set()
    for resource in manifest["resources"]:
        raw = resource.get("output_path")
        if not raw or raw in seen:
            continue
        if resource["kind"] not in {"javascript", "html", "json", "css", "text"}:
            continue
        seen.add(raw)
        if not resource.get("body_complete", True):
            units.append(
                {
                    "kind": "incomplete",
                    "captured_kind": resource["kind"],
                    "transport_kind": resource.get("transport_kind", resource["kind"]),
                    "raw_path": raw,
                    "source_path": None,
                    "resource_id": resource["id"],
                    "url": resource["url"],
                    "transform": "skipped_incomplete_network_response",
                    "formatted": False,
                }
            )
            continue
        units.append(
            {
                "kind": resource["kind"],
                "captured_kind": resource["kind"],
                "transport_kind": resource.get("transport_kind", resource["kind"]),
                "raw_path": raw,
                "resource_id": resource["id"],
                "url": resource["url"],
                "resource": resource,
            }
        )

    for script in manifest["inline_scripts"]:
        raw = script.get("output_path")
        if raw and raw not in seen:
            seen.add(raw)
            kind = inline_script_kind(script.get("script_type"))
            parent = manifest["resources"][script["parent_resource_id"]]
            units.append(
                {
                    "kind": kind,
                    "captured_kind": kind,
                    "transport_kind": "inline_script",
                    "raw_path": raw,
                    "resource_id": script["parent_resource_id"],
                    "url": parent["url"],
                    "resource": None,
                }
            )

    rows = []
    js_groups = {}
    for unit in units:
        if unit["kind"] == "incomplete":
            rows.append(unit)
            continue
        raw = unit["raw_path"]
        source = project / raw
        dest_rel = src_path(raw)
        dest = project / dest_rel
        row = {key: value for key, value in unit.items() if key != "resource"}
        row["source_path"] = dest_rel
        index = len(rows)
        rows.append(row)
        if unit["kind"] == "javascript":
            digest = sha256_path(source)
            row["input_sha256"] = digest
            charset = declared_charset(unit["resource"])
            group_key = (digest, charset)
            js_groups.setdefault(group_key, []).append(
                {
                    "index": index,
                    "source": source,
                    "dest": dest,
                    "raw_path": raw,
                    "resource": unit["resource"],
                }
            )
        else:
            row.update(materialize_text(source, dest, unit["kind"], unit["resource"]))

    # Derived duplicate outputs may be hardlinks from a previous run. Break all
    # old links before parallel writers start so a changed capture cannot make
    # two now-distinct content groups race through the same inode.
    for group in js_groups.values():
        for item in group:
            dest = item["dest"]
            if dest.exists() or dest.is_symlink():
                dest.unlink()

    def run_group(group_key, group):
        canonical = group[0]
        result = format_javascript(
            args.formatter,
            canonical["source"],
            canonical["dest"],
            canonical["resource"],
        )
        return group_key, group, canonical, result

    futures = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for group_key, group in js_groups.items():
            futures.append(pool.submit(run_group, group_key, group))
        for future in as_completed(futures):
            group_key, group, canonical, result = future.result()
            digest, charset_hint = group_key
            for occurrence, item in enumerate(group):
                row = rows[item["index"]]
                row.update(
                    {
                        "transform": result["transform"],
                        "formatted": result["formatted"],
                        "source_encoding": result["source_encoding"],
                        "encoding_fallback": result["encoding_fallback"],
                        "declared_charset": charset_hint,
                        "content_sha256": digest,
                        "content_group_size": len(group),
                        "deduplicated": occurrence > 0,
                        "deduplicated_from": canonical["raw_path"] if occurrence > 0 else None,
                    }
                )
                if result["format_error"]:
                    row["format_error"] = result["format_error"]
                    row["kind"] = "javascript_unparsed"
                if occurrence == 0:
                    row["materialization"] = "canonical"
                else:
                    row["materialization"] = link_or_copy(
                        canonical["dest"], item["dest"]
                    )

    analysis = project / "analysis"
    analysis.mkdir(parents=True, exist_ok=True)
    js_units = sum(row["kind"] == "javascript" for row in rows)
    unparsed_js_units = sum(row["kind"] == "javascript_unparsed" for row in rows)
    captured_js_units = js_units + unparsed_js_units
    unique_js_inputs = sum(
        row["kind"] == "javascript" and row.get("materialization") == "canonical"
        for row in rows
    )
    captured_unique_js_inputs = len(js_groups)
    incomplete_units = sum(row["kind"] == "incomplete" for row in rows)
    source_index = {
        "schema": SOURCE_INDEX.schema,
        "units": rows,
        "summary": {
            "units": len(rows),
            "javascript_units": js_units,
            "captured_javascript_units": captured_js_units,
            "unparsed_javascript_units": unparsed_js_units,
            "unique_javascript_inputs": unique_js_inputs,
            "captured_unique_javascript_inputs": captured_unique_js_inputs,
            "deduplicated_javascript_units": js_units - unique_js_inputs,
            "incomplete_network_units": incomplete_units,
            "formatter_jobs": jobs,
        },
    }
    write_artifact(project, SOURCE_INDEX, source_index)

    formatted = sum(r.get("transform") == "oxc_parse_codegen" for r in rows)
    fallbacks = sum(r.get("transform") == "utf8_raw_fallback" for r in rows)
    transcoded = sum(r.get("source_encoding") not in {None, "utf-8"} for r in rows)
    print(
        f"materialized {len(rows) - incomplete_units} readable text/code units under src/: "
        f"{formatted} JS formatted, {fallbacks} JS fallbacks, {transcoded} non-UTF-8 inputs normalized; "
        f"{incomplete_units} incomplete responses retained only as raw provenance; "
        f"{js_units} JS occurrences / {unique_js_inputs} unique bodies "
        f"({js_units - unique_js_inputs} reused), jobs={jobs}"
    )


if __name__ == "__main__":
    main()
