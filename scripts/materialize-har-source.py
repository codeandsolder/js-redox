#!/usr/bin/env python3
import argparse
import json
import shutil
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from browser_script_types import inline_script_kind
from content_dedup import default_jobs, link_or_copy, sha256_path

ROOT = Path(__file__).resolve().parents[1]


def src_path(raw_path: str) -> str:
    prefix = "resources/"
    if raw_path.startswith(prefix):
        return "src/" + raw_path[len(prefix):]
    return "src/" + raw_path


def format_javascript(formatter: Path, source: Path, dest: Path):
    dest.parent.mkdir(parents=True, exist_ok=True)
    cp = subprocess.run(
        [str(formatter), str(source), str(dest)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=120,
    )
    if cp.returncode == 0:
        return {
            "transform": "oxc_parse_codegen",
            "formatted": True,
            "format_error": None,
        }
    shutil.copyfile(source, dest)
    return {
        "transform": "raw_fallback",
        "formatted": False,
        "format_error": cp.stderr[-1000:],
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
    manifest = json.loads((project / "har-manifest.json").read_text())

    units = []
    seen = set()
    for r in manifest["resources"]:
        raw = r.get("output_path")
        if (
            raw
            and raw not in seen
            and r["kind"] in {"javascript", "html", "json", "css", "text"}
        ):
            seen.add(raw)
            units.append((r["kind"], raw, r["url"], r["id"]))
    for s in manifest["inline_scripts"]:
        raw = s.get("output_path")
        if raw and raw not in seen:
            seen.add(raw)
            kind = inline_script_kind(s.get("script_type"))
            parent = manifest["resources"][s["parent_resource_id"]]
            units.append((kind, raw, parent["url"], s["parent_resource_id"]))

    rows = [None] * len(units)
    js_groups = {}
    for index, (kind, raw, url, resource_id) in enumerate(units):
        source = project / raw
        dest_rel = src_path(raw)
        dest = project / dest_rel
        row = {
            "kind": kind,
            "raw_path": raw,
            "source_path": dest_rel,
            "resource_id": resource_id,
            "url": url,
        }
        rows[index] = row
        if kind == "javascript":
            digest = sha256_path(source)
            row["input_sha256"] = digest
            js_groups.setdefault(digest, []).append(
                {
                    "index": index,
                    "source": source,
                    "dest": dest,
                    "raw_path": raw,
                }
            )
        else:
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, dest)
            row["transform"] = "identity"
            row["formatted"] = False

    # Derived duplicate outputs may be hardlinks from a previous run. Break all
    # old links before parallel writers start so a changed capture cannot make
    # two now-distinct content groups race through the same inode.
    for group in js_groups.values():
        for item in group:
            dest = item["dest"]
            if dest.exists() or dest.is_symlink():
                dest.unlink()

    def run_group(digest, group):
        canonical = group[0]
        result = format_javascript(args.formatter, canonical["source"], canonical["dest"])
        return digest, group, canonical, result

    futures = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for digest, group in js_groups.items():
            futures.append(pool.submit(run_group, digest, group))
        for future in as_completed(futures):
            digest, group, canonical, result = future.result()
            for occurrence, item in enumerate(group):
                row = rows[item["index"]]
                row.update(
                    {
                        "transform": result["transform"],
                        "formatted": result["formatted"],
                        "content_sha256": digest,
                        "content_group_size": len(group),
                        "deduplicated": occurrence > 0,
                        "deduplicated_from": canonical["raw_path"] if occurrence > 0 else None,
                    }
                )
                if result["format_error"]:
                    row["format_error"] = result["format_error"]
                if occurrence == 0:
                    row["materialization"] = "canonical"
                else:
                    row["materialization"] = link_or_copy(
                        canonical["dest"], item["dest"]
                    )

    rows = [row for row in rows if row is not None]
    analysis = project / "analysis"
    analysis.mkdir(parents=True, exist_ok=True)
    unique_js_inputs = len(js_groups)
    js_units = sum(row["kind"] == "javascript" for row in rows)
    source_index = {
        "schema": "har-source-index/v1",
        "units": rows,
        "summary": {
            "units": len(rows),
            "javascript_units": js_units,
            "unique_javascript_inputs": unique_js_inputs,
            "deduplicated_javascript_units": js_units - unique_js_inputs,
            "formatter_jobs": jobs,
        },
    }
    (analysis / "source-index.json").write_text(
        json.dumps(source_index, indent=2) + "\n"
    )

    formatted = sum(r["transform"] == "oxc_parse_codegen" for r in rows)
    fallbacks = sum(r["transform"] == "raw_fallback" for r in rows)
    print(
        f"materialized {len(rows)} readable text/code units under src/: "
        f"{formatted} JS formatted, {fallbacks} JS fallbacks; "
        f"{js_units} JS occurrences / {unique_js_inputs} unique bodies "
        f"({js_units - unique_js_inputs} reused), jobs={jobs}"
    )


if __name__ == "__main__":
    main()
