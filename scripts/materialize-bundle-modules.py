#!/usr/bin/env python3
import argparse
import hashlib
import json
import re
import shutil
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


def module_output_path(
    parent: Path,
    chunk_ids: list[str],
    module_id: str,
    bundle_id: int,
) -> Path:
    parts = list(parent.parts)
    prefix = ["src", "_deobfuscated"]
    if parts[:2] == prefix:
        parts = parts[2:]
    elif parts and parts[0] == "src":
        parts = parts[1:]
    source_rel = Path(*parts)
    stem_dir = source_rel.with_name(source_rel.name + ".modules")
    group = (
        "chunk-" + "-".join(safe_component(x, 24) for x in chunk_ids)
        if chunk_ids
        else f"module-table-{bundle_id + 1:02d}"
    )
    return Path("src/_modules") / stem_dir / group / f"module-{safe_component(module_id)}.js"


def build_module_source(source: bytes, module: dict, provenance: str) -> str:
    ps = int(module["property_start"])
    pe = int(module["property_end"])
    vs = int(module["value_start"])
    ve = int(module["value_end"])
    prop = source[ps:pe].decode("utf-8")
    value = source[vs:ve].decode("utf-8")
    export_names = [str(name) for name in module.get("export_names", [])]
    export_preview = ", ".join(export_names[:12])
    if len(export_names) > 12:
        export_preview += f", … (+{len(export_names) - 12} more)"
    metadata = ""
    if export_preview:
        metadata += f" * Static export names: {export_preview}\n"
    if module.get("commonjs_export"):
        metadata += " * Static CommonJS module.exports write observed.\n"
    header = (
        "/* Statically extracted Webpack/Next module wrapper.\n"
        f" * {provenance}\n"
        + metadata
        + " * The wrapper body is preserved from the parent analyst view.\n"
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


def markdown_text(value: object) -> str:
    return str(value).replace("\\", "\\\\").replace("|", "\\|").replace("`", "\\`")


def write_module_readme(module_root: Path, bundles: list[dict], modules: list[dict]) -> None:
    module_root.mkdir(parents=True, exist_ok=True)
    by_bundle: dict[int, list[dict]] = {}
    for module in modules:
        by_bundle.setdefault(int(module["bundle_id"]), []).append(module)
    lines = [
        "# Recovered bundle modules",
        "",
        "Module filenames retain the captured Webpack/Next module ID as canonical identity. "
        "Static export names are scope-resolved navigation metadata, not invented filenames.",
        "",
        f"- Bundle payloads: **{len(bundles)}**",
        f"- Modules: **{len(modules)}**",
        f"- Modules with named exports: **{sum(bool(m.get('export_names')) for m in modules)}**",
        f"- Modules with static CommonJS writes: **{sum(bool(m.get('commonjs_export')) for m in modules)}**",
        "",
    ]
    for bundle in bundles:
        bundle_id = int(bundle["bundle_id"])
        rows = by_bundle.get(bundle_id, [])
        named = [row for row in rows if row.get("export_names")]
        commonjs_only = sum(bool(row.get("commonjs_export")) and not row.get("export_names") for row in rows)
        anonymous = len(rows) - len(named) - commonjs_only
        chunk_ids = bundle.get("chunk_ids", [])
        identity = ("chunk " + ", ".join(markdown_text(x) for x in chunk_ids)) if chunk_ids else "direct module table"
        lines.extend([
            f"## Bundle {bundle_id + 1:02d} — {identity}",
            "",
            f"- Parent: `{markdown_text(bundle.get('parent_path', ''))}`",
            f"- Modules: **{len(rows)}**; named: **{len(named)}**; CommonJS-only: **{commonjs_only}**; unlabeled: **{anonymous}**",
        ])
        if named:
            lines.extend(["", "Named-export modules:"])
            for row in named:
                rel = Path(row["source_path"]).relative_to("src/_modules").as_posix()
                names = ", ".join(markdown_text(x) for x in row.get("export_names", []))
                lines.append(f"- [module {markdown_text(row['module_id'])}]({rel}): {names} — {len(row.get('dependencies', []))} literal dep(s)")
        lines.append("")
    (module_root / "README.md").write_text("\n".join(lines))

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

    module_root = project / "src/_modules"
    shutil.rmtree(module_root, ignore_errors=True)

    bundles = []
    modules = []
    failures = []
    tmp_root = ROOT / "work/test-tmp/bundle-module-materialization"
    shutil.rmtree(tmp_root, ignore_errors=True)
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
        source = parent.read_bytes()
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
                rel = module_output_path(
                    parent_rel,
                    bundle.get("chunk_ids", []),
                    str(module["id"]),
                    bundle_ordinal,
                )
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
                        "dependencies": [str(x) for x in module.get("dependencies", [])],
                        "export_names": [str(x) for x in module.get("export_names", [])],
                        "commonjs_export": bool(module.get("commonjs_export")),
                        "source_path": str(rel),
                        "formatted": formatted,
                        "sha256": hashlib.sha256(dest.read_bytes()).hexdigest(),
                    }
                )

    index = {
        "schema": "har-bundle-modules/v2",
        "safe_static_only": True,
        "inventory": str(args.inventory),
        "bundles": bundles,
        "modules": modules,
        "failures": failures,
        "summary": {
            "bundles": len(bundles),
            "modules": len(modules),
            "literal_module_dependencies": sum(
                len(module.get("dependencies", [])) for module in modules
            ),
            "modules_with_named_exports": sum(
                bool(module.get("export_names")) for module in modules
            ),
            "named_exports": sum(
                len(module.get("export_names", [])) for module in modules
            ),
            "commonjs_export_modules": sum(
                bool(module.get("commonjs_export")) for module in modules
            ),
            "failed_units": len(failures),
        },
    }
    out = project / "analysis/bundles.json"
    out.write_text(json.dumps(index, indent=2) + "\n")
    write_module_readme(module_root, bundles, modules)
    print(
        f"bundle modules: {len(bundles)} bundle payload(s), {len(modules)} modules, "
        f"{len(failures)} failed units"
    )


if __name__ == "__main__":
    main()
