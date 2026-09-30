#!/usr/bin/env python3
import argparse
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def src_path(raw_path: str) -> str:
    prefix = "resources/"
    if raw_path.startswith(prefix):
        return "src/" + raw_path[len(prefix):]
    return "src/" + raw_path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("project", type=Path)
    ap.add_argument(
        "--formatter",
        type=Path,
        default=ROOT / ".cargo-target-nodebug/debug/js-format",
    )
    args = ap.parse_args()

    project = args.project.resolve()
    manifest = json.loads((project / "har-manifest.json").read_text())
    rows = []
    seen = set()

    units = []
    for r in manifest["resources"]:
        raw = r.get("output_path")
        if raw and r["kind"] in {"javascript", "html", "json", "css", "text"}:
            units.append((r["kind"], raw, r["url"], r["id"]))
    for s in manifest["inline_scripts"]:
        raw = s.get("output_path")
        if raw:
            kind = "json" if raw.endswith(".json") else "javascript"
            parent = manifest["resources"][s["parent_resource_id"]]
            units.append((kind, raw, parent["url"], s["parent_resource_id"]))

    for kind, raw, url, resource_id in units:
        if raw in seen:
            continue
        seen.add(raw)
        source = project / raw
        dest_rel = src_path(raw)
        dest = project / dest_rel
        dest.parent.mkdir(parents=True, exist_ok=True)

        row = {
            "kind": kind,
            "raw_path": raw,
            "source_path": dest_rel,
            "resource_id": resource_id,
            "url": url,
        }
        if kind == "javascript":
            cp = subprocess.run(
                [str(args.formatter), str(source), str(dest)],
                cwd=ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=120,
            )
            if cp.returncode == 0:
                row["transform"] = "oxc_parse_codegen"
                row["formatted"] = True
            else:
                shutil.copyfile(source, dest)
                row["transform"] = "raw_fallback"
                row["formatted"] = False
                row["format_error"] = cp.stderr[-1000:]
        else:
            shutil.copyfile(source, dest)
            row["transform"] = "identity"
            row["formatted"] = False
        rows.append(row)

    analysis = project / "analysis"
    analysis.mkdir(parents=True, exist_ok=True)
    (analysis / "source-index.json").write_text(
        json.dumps({"schema": "har-source-index/v0", "units": rows}, indent=2) + "\n"
    )

    formatted = sum(r["transform"] == "oxc_parse_codegen" for r in rows)
    fallbacks = sum(r["transform"] == "raw_fallback" for r in rows)
    print(
        f"materialized {len(rows)} readable text/code units under src/: "
        f"{formatted} JS formatted, {fallbacks} JS fallbacks"
    )


if __name__ == "__main__":
    main()
