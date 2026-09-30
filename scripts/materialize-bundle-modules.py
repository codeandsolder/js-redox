#!/usr/bin/env python3
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INVENTORY = ROOT / ".cargo-target-nodebug/debug/bundle-unpack"
DEFAULT_FORMATTER = ROOT / ".cargo-target-nodebug/debug/js-format"


def safe_component(value: str, cap: int = 96) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9._-]+", "_", value).strip("._") or "module"
    if len(cleaned) <= cap:
        return cleaned
    digest = hashlib.sha256(value.encode()).hexdigest()[:12]
    return f"{cleaned[:cap-13]}-{digest}"


def run(argv, timeout=180):
    return subprocess.run(
        [str(x) for x in argv],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
    )


def module_output_path(parent: Path, chunk_ids: list[str], module_id: str) -> Path:
    parts = list(parent.parts)
    prefix = ["src", "_deobfuscated"]
    if parts[:2] == prefix:
        parts = parts[2:]
    elif parts and parts[0] == "src":
        parts = parts[1:]
    source_rel = Path(*parts)
    stem_dir = source_rel.with_name(source_rel.name + ".modules")
    chunk = "chunk-" + "-".join(safe_component(x, 24) for x in chunk_ids)
    return Path("src/_modules") / stem_dir / chunk / f"module-{safe_component(module_id)}.js"


def build_module_source(source: str, module: dict, provenance: str) -> str:
    ps = int(module["property_start"])
    pe = int(module["property_end"])
    vs = int(module["value_start"])
    ve = int(module["value_end"])
    prop = source[ps:pe]
    value = source[vs:ve]
    header = (
        "/* Statically extracted Webpack/Next module wrapper.\n"
        f" * {provenance}\n"
        " * The wrapper body is preserved from the parent analyst view.\n"
        " */\n"
    )
    if module.get("method"):
        key = json.dumps(str(module["id"]))
        return (
            header
            + "const __webpack_module_table__ = {\n"
            + prop
            + "\n};\n"
            + f"const __webpack_module__ = __webpack_module_table__[{key}];\n"
        )
    return header + "const __webpack_module__ = " + value + ";\n"


def main():
    ap = argparse.ArgumentParser(
        description="Materialize statically explicit Webpack/Next chunk modules as readable source files"
    )
    ap.add_argument("project", type=Path)
    ap.add_argument("--inventory", type=Path, default=DEFAULT_INVENTORY)
    ap.add_argument("--formatter", type=Path, default=DEFAULT_FORMATTER)
    args = ap.parse_args()

    project = args.project.resolve()
    deob_path = project / "analysis/deobfuscation.json"
    if not deob_path.exists():
        raise SystemExit("analysis/deobfuscation.json is required; run safe source recovery first")
    deob = json.loads(deob_path.read_text())

    bundles = []
    modules = []
    failures = []
    tmp_root = ROOT / "work/test-tmp/bundle-module-materialization"
    tmp_root.mkdir(parents=True, exist_ok=True)

    for unit in deob.get("units", []):
        if unit.get("exit") or not unit.get("output_path"):
            continue
        parent_rel = Path(unit["output_path"])
        parent = project / parent_rel
        if not parent.is_file():
            continue
        cp = run([args.inventory, parent])
        if cp.returncode:
            failures.append(
                {
                    "ordinal": unit.get("ordinal"),
                    "path": str(parent_rel),
                    "error": (cp.stdout + cp.stderr)[-3000:],
                }
            )
            continue
        report = json.loads(cp.stdout)
        source = parent.read_text()
        for bundle_ordinal, bundle in enumerate(report.get("bundles", [])):
            bundle_id = len(bundles)
            bundle_row = {
                "bundle_id": bundle_id,
                "parent_ordinal": unit.get("ordinal"),
                "resource_id": unit.get("resource_id"),
                "parent_path": str(parent_rel),
                "kind": bundle.get("kind"),
                "chunk_ids": bundle.get("chunk_ids", []),
                "start": bundle.get("start"),
                "end": bundle.get("end"),
                "module_table_start": bundle.get("module_table_start"),
                "module_table_end": bundle.get("module_table_end"),
                "module_count": len(bundle.get("modules", [])),
                "module_ids": [m.get("id") for m in bundle.get("modules", [])],
            }
            bundles.append(bundle_row)

            for module_ordinal, module in enumerate(bundle.get("modules", [])):
                rel = module_output_path(parent_rel, bundle.get("chunk_ids", []), str(module["id"]))
                dest = project / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                provenance = (
                    f"parent={parent_rel} bundle_span={bundle['start']}..{bundle['end']} "
                    f"module={module['id']} property_span={module['property_start']}..{module['property_end']}"
                )
                raw = build_module_source(source, module, provenance)
                tmp = tmp_root / f"bundle-{bundle_id}-module-{module_ordinal}.js"
                tmp.write_text(raw)
                fmt = run([args.formatter, tmp, dest], timeout=120)
                formatted = fmt.returncode == 0
                if not formatted:
                    dest.write_text(raw)
                modules.append(
                    {
                        "bundle_id": bundle_id,
                        "module_ordinal": module_ordinal,
                        "parent_ordinal": unit.get("ordinal"),
                        "resource_id": unit.get("resource_id"),
                        "parent_path": str(parent_rel),
                        "chunk_ids": bundle.get("chunk_ids", []),
                        "module_id": str(module["id"]),
                        "property_start": module.get("property_start"),
                        "property_end": module.get("property_end"),
                        "value_start": module.get("value_start"),
                        "value_end": module.get("value_end"),
                        "value_kind": module.get("value_kind"),
                        "method": bool(module.get("method")),
                        "source_path": str(rel),
                        "formatted": formatted,
                        "sha256": hashlib.sha256(dest.read_bytes()).hexdigest(),
                    }
                )

    index = {
        "schema": "har-bundle-modules/v1",
        "safe_static_only": True,
        "inventory": str(args.inventory),
        "bundles": bundles,
        "modules": modules,
        "failures": failures,
        "summary": {
            "bundles": len(bundles),
            "modules": len(modules),
            "failed_units": len(failures),
        },
    }
    out = project / "analysis/bundles.json"
    out.write_text(json.dumps(index, indent=2) + "\n")
    print(
        f"bundle modules: {len(bundles)} bundle payload(s), {len(modules)} modules, "
        f"{len(failures)} failed units"
    )


if __name__ == "__main__":
    main()
