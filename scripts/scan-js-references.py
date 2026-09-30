#!/usr/bin/env python3
import argparse
import json
import subprocess
from pathlib import Path
from urllib.parse import urljoin, urlsplit

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EXTRACTOR = ROOT / ".cargo-target-nodebug/debug/js-refs"


def resolve_specifier(base_url: str | None, specifier: str):
    specifier = specifier.strip()
    if not specifier:
        return None, True

    parsed = urlsplit(specifier)
    if parsed.scheme:
        return specifier, False
    if specifier.startswith("//"):
        if base_url:
            scheme = urlsplit(base_url).scheme or "https"
            return f"{scheme}:{specifier}", False
        return None, False
    if specifier.startswith(("./", "../", "/")):
        return (urljoin(base_url, specifier) if base_url else None), False

    # Bare specifiers require an import map/bundler/Node resolution context.
    return None, True


def main():
    ap = argparse.ArgumentParser(
        description="Extract literal JS import/worker references from a HAR project"
    )
    ap.add_argument("project", type=Path)
    ap.add_argument("--extractor", type=Path, default=DEFAULT_EXTRACTOR)
    args = ap.parse_args()

    project = args.project.resolve()
    source_index = json.loads((project / "analysis/source-index.json").read_text())
    rows = []
    failures = 0
    total_refs = 0

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
            "references": [],
        }
        if cp.returncode:
            failures += 1
            row["error"] = cp.stderr[-3000:]
            rows.append(row)
            continue

        refs = json.loads(cp.stdout)
        for ref in refs:
            resolved, bare = resolve_specifier(unit.get("url"), ref["specifier"])
            ref["resolved_url"] = resolved
            ref["bare_specifier"] = bare
        row["references"] = refs
        total_refs += len(refs)
        rows.append(row)

    out = {
        "schema": "har-js-references/v0",
        "extractor": str(args.extractor),
        "code_units": rows,
        "summary": {
            "javascript_units": len(rows),
            "references": total_refs,
            "failures": failures,
        },
    }
    path = project / "analysis/js-references.json"
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(
        f"JavaScript references: {len(rows)} units, "
        f"{total_refs} literal references, {failures} failures"
    )


if __name__ == "__main__":
    main()
