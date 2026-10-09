#!/usr/bin/env python3
import argparse
import hashlib
import json
import re
import shutil
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from content_dedup import default_jobs, sha256_path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INVENTORY = ROOT / ".cargo-target-nodebug/debug/bundle-unpack"
DEFAULT_FORMATTER = ROOT / ".cargo-target-nodebug/debug/js-format"
PROVENANCE_PLACEHOLDER = "__JSVM_CAPTURE_PROVENANCE__"


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
    kind: str,
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
    if kind == "amd_named_modules":
        group = "amd-modules"
    elif kind == "member_named_modules":
        group = "member-named-modules"
    elif kind == "browserify_module_table":
        group = "browserify-modules"
    elif chunk_ids:
        group = "chunk-" + "-".join(safe_component(x, 24) for x in chunk_ids)
    else:
        group = f"module-table-{bundle_id + 1:02d}"
    return Path("src/_modules") / stem_dir / group / f"module-{safe_component(module_id)}.js"


def build_module_source(
    source: bytes, module: dict, provenance: str, bundle_kind: str
) -> str:
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
    if bundle_kind == "browserify_module_table":
        dep_map = module.get("dependency_map", {})
        dep_preview = ", ".join(
            f"{name} -> {target}" for name, target in list(dep_map.items())[:12]
        )
        if len(dep_map) > 12:
            dep_preview += f", … (+{len(dep_map) - 12} more)"
        if dep_preview:
            metadata += f" * Static Browserify dependency map: {dep_preview}\n"
        header = (
            "/* Statically extracted Browserify module factory.\n"
            f" * {provenance}\n"
            + metadata
            + " * The factory body is preserved from the parent analyst view.\n"
            " */\n"
        )
        return header + "const __browserify_module_factory__ = " + value + ";\n"
    if bundle_kind in {"amd_named_modules", "member_named_modules"}:
        dep_preview = ", ".join(str(x) for x in module.get("dependencies", [])[:12])
        if len(module.get("dependencies", [])) > 12:
            dep_preview += f", … (+{len(module['dependencies']) - 12} more)"
        if dep_preview:
            dep_label = "AMD" if bundle_kind == "amd_named_modules" else "named-loader"
            metadata += f" * Static {dep_label} dependencies: {dep_preview}\n"
        family = "named AMD" if bundle_kind == "amd_named_modules" else "member-loader named"
        header = (
            f"/* Statically extracted {family} module factory.\n"
            f" * {provenance}\n"
            + metadata
            + " * The factory body is preserved from the parent analyst view.\n"
            " */\n"
        )
        return header + "const __named_module_factory__ = " + value + ";\n"
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
        "# Recovered structured modules",
        "",
        "Module filenames retain captured module identity: explicit AMD names or Webpack/Next module IDs. "
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
        kind = bundle.get("kind")
        if kind == "amd_named_modules":
            identity = "named AMD modules"
        elif kind == "member_named_modules":
            identity = "member-loader named modules"
        elif kind == "browserify_module_table":
            identity = "Browserify module table"
        elif chunk_ids:
            identity = "chunk " + ", ".join(markdown_text(x) for x in chunk_ids)
        else:
            identity = "direct module table"
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
        description="Materialize statically explicit Webpack/Next, Browserify and named AMD modules as readable source files"
    )
    ap.add_argument("project", type=Path)
    ap.add_argument("--inventory", type=Path, default=DEFAULT_INVENTORY)
    ap.add_argument("--formatter", type=Path, default=DEFAULT_FORMATTER)
    ap.add_argument("--jobs", type=int, default=default_jobs())
    args = ap.parse_args()
    jobs = max(1, args.jobs)

    project = args.project.resolve()
    deob_path = project / "analysis/deobfuscation.json"
    if not deob_path.exists():
        raise SystemExit("analysis/deobfuscation.json is required; run safe source recovery first")
    deob = json.loads(deob_path.read_text())

    module_root = project / "src/_modules"
    shutil.rmtree(module_root, ignore_errors=True)

    bundles = []
    modules = []
    module_tasks = []
    failures = []
    # Keep formatter scratch local to this output project. A shared repository-wide
    # scratch directory made concurrent capture pipelines interfere with each other
    # and inherited stale ownership from whichever user ran it first.
    tmp_root = project / "analysis/.tmp/bundle-module-materialization"
    shutil.rmtree(tmp_root, ignore_errors=True)
    tmp_root.mkdir(parents=True, exist_ok=True)

    eligible_units = []
    inventory_groups = {}
    for unit in deob.get("units", []):
        if unit.get("exit") or not unit.get("output_path"):
            continue
        parent_rel = Path(unit["output_path"])
        parent = project / parent_rel
        if not parent.is_file():
            continue
        digest = unit.get("output_sha256") or sha256_path(parent)
        item = {
            "unit": unit,
            "parent_rel": parent_rel,
            "parent": parent,
            "content_sha256": digest,
        }
        eligible_units.append(item)
        inventory_groups.setdefault(digest, []).append(item)

    def inventory_group(digest, group):
        canonical = group[0]
        cp = run([args.inventory, canonical["parent"]])
        if cp.returncode:
            return {
                "content_sha256": digest,
                "exit": cp.returncode,
                "error": (cp.stdout + cp.stderr)[-3000:],
                "report": None,
            }
        return {
            "content_sha256": digest,
            "exit": 0,
            "error": None,
            "report": json.loads(cp.stdout),
        }

    inventory_results = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {
            pool.submit(inventory_group, digest, group): digest
            for digest, group in inventory_groups.items()
        }
        for future in as_completed(futures):
            result = future.result()
            inventory_results[result["content_sha256"]] = result

    seen_digest = {}
    for item in eligible_units:
        unit = item["unit"]
        parent_rel = item["parent_rel"]
        parent = item["parent"]
        digest = item["content_sha256"]
        result = inventory_results[digest]
        occurrence = seen_digest.get(digest, 0)
        seen_digest[digest] = occurrence + 1
        if result["exit"]:
            failures.append(
                {
                    "ordinal": unit.get("ordinal"),
                    "path": str(parent_rel),
                    "content_sha256": digest,
                    "content_group_size": len(inventory_groups[digest]),
                    "deduplicated": occurrence > 0,
                    "error": result["error"],
                }
            )
            continue
        report = result["report"]
        source = parent.read_bytes()
        for bundle_ordinal, bundle in enumerate(report.get("bundles", [])):
            bundle_id = len(bundles)
            bundle_row = {
                "bundle_id": bundle_id,
                "parent_ordinal": unit.get("ordinal"),
                "resource_id": unit.get("resource_id"),
                "parent_path": str(parent_rel),
                "parent_content_sha256": digest,
                "inventory_group_size": len(inventory_groups[digest]),
                "inventory_deduplicated": occurrence > 0,
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
                    str(bundle.get("kind", "")),
                    bundle.get("chunk_ids", []),
                    str(module["id"]),
                    bundle_ordinal,
                )
                dest = project / rel
                provenance = (
                    f"parent={parent_rel} bundle_span={bundle['start']}..{bundle['end']} "
                    f"module={module['id']} property_span={module['property_start']}..{module['property_end']}"
                )
                raw = build_module_source(
                    source,
                    module,
                    PROVENANCE_PLACEHOLDER,
                    str(bundle.get("kind", "")),
                )
                raw_sha = hashlib.sha256(raw.encode()).hexdigest()
                module_index = len(modules)
                modules.append(
                    {
                        "bundle_id": bundle_id,
                        "module_ordinal": module_ordinal,
                        "parent_ordinal": unit.get("ordinal"),
                        "resource_id": unit.get("resource_id"),
                        "parent_path": str(parent_rel),
                        "parent_content_sha256": digest,
                        "bundle_kind": bundle.get("kind"),
                        "chunk_ids": bundle.get("chunk_ids", []),
                        "module_id": str(module["id"]),
                        "property_start": module.get("property_start"),
                        "property_end": module.get("property_end"),
                        "value_start": module.get("value_start"),
                        "value_end": module.get("value_end"),
                        "value_kind": module.get("value_kind"),
                        "method": bool(module.get("method")),
                        "dependencies": [str(x) for x in module.get("dependencies", [])],
                        "dependency_map": {
                            str(k): str(v) for k, v in module.get("dependency_map", {}).items()
                        },
                        "export_names": [str(x) for x in module.get("export_names", [])],
                        "commonjs_export": bool(module.get("commonjs_export")),
                        "source_path": str(rel),
                        "module_input_sha256": raw_sha,
                    }
                )
                module_tasks.append(
                    {
                        "module_index": module_index,
                        "raw": raw,
                        "raw_sha256": raw_sha,
                        "provenance": provenance,
                        "dest": dest,
                    }
                )

    module_format_groups = {}
    for task in module_tasks:
        module_format_groups.setdefault(task["raw_sha256"], []).append(task)

    format_cache = tmp_root / "formatted"
    format_cache.mkdir(parents=True, exist_ok=True)

    def format_module_group(raw_sha, group):
        canonical = group[0]
        source_tmp = tmp_root / "raw" / f"{raw_sha}.js"
        source_tmp.parent.mkdir(parents=True, exist_ok=True)
        source_tmp.write_text(canonical["raw"])
        formatted_tmp = format_cache / f"{raw_sha}.js"
        fmt = run([args.formatter, source_tmp, formatted_tmp], timeout=120)
        formatted = fmt.returncode == 0
        if not formatted:
            formatted_tmp.write_text(canonical["raw"])
        return {
            "raw_sha256": raw_sha,
            "formatted": formatted,
            "formatted_path": formatted_tmp,
            "group": group,
        }

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {
            pool.submit(format_module_group, raw_sha, group): raw_sha
            for raw_sha, group in module_format_groups.items()
        }
        for future in as_completed(futures):
            result = future.result()
            canonical_index = result["group"][0]["module_index"]
            template = result["formatted_path"].read_text()
            if PROVENANCE_PLACEHOLDER not in template:
                raise RuntimeError(
                    f"formatter dropped module provenance placeholder for {result['raw_sha256']}"
                )
            for task in result["group"]:
                record = modules[task["module_index"]]
                rendered = template.replace(
                    PROVENANCE_PLACEHOLDER, task["provenance"], 1
                )
                task["dest"].parent.mkdir(parents=True, exist_ok=True)
                task["dest"].write_text(rendered)
                record["formatted"] = result["formatted"]
                record["sha256"] = hashlib.sha256(rendered.encode()).hexdigest()
                record["format_group_size"] = len(result["group"])
                record["format_deduplicated"] = task["module_index"] != canonical_index
                record["materialization"] = "rendered_content_template"

    index = {
        "schema": "har-bundle-modules/v5",
        "safe_static_only": True,
        "inventory": str(args.inventory),
        "bundles": bundles,
        "modules": modules,
        "failures": failures,
        "summary": {
            "eligible_units": len(eligible_units),
            "unique_input_bodies": len(inventory_groups),
            "deduplicated_units": len(eligible_units) - len(inventory_groups),
            "inventory_invocations": len(inventory_groups),
            "module_format_invocations": len(module_format_groups),
            "deduplicated_module_formats": len(module_tasks) - len(module_format_groups),
            "jobs": jobs,
            "bundles": len(bundles),
            "modules": len(modules),
            "amd_named_modules": sum(
                bundle.get("kind") == "amd_named_modules"
                for bundle in bundles
                for _ in bundle.get("module_ids", [])
            ),
            "member_named_modules": sum(
                bundle.get("kind") == "member_named_modules"
                for bundle in bundles
                for _ in bundle.get("module_ids", [])
            ),
            "browserify_modules": sum(
                bundle.get("kind") == "browserify_module_table"
                for bundle in bundles
                for _ in bundle.get("module_ids", [])
            ),
            "webpack_modules": sum(
                bundle.get("kind")
                not in {"amd_named_modules", "member_named_modules", "browserify_module_table"}
                for bundle in bundles
                for _ in bundle.get("module_ids", [])
            ),
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
    shutil.rmtree(tmp_root, ignore_errors=True)
    print(
        f"bundle modules: {len(bundles)} bundle payload(s), {len(modules)} modules, "
        f"{len(module_format_groups)} formatter invocation(s) / "
        f"{len(module_tasks) - len(module_format_groups)} exact-hash reuse(s), "
        f"{len(failures)} failed units"
    )


if __name__ == "__main__":
    main()
