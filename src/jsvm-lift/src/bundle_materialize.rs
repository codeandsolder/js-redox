use crate::{
    analysis_artifacts::{load_artifact, write_artifact, BUNDLES, DEOBFUSCATION},
    bundle_unpack::{analyze_bundle_source, BundleInventoryReport, ModuleRecord},
    content_dedup::{default_jobs, sha256_path},
    js_format::format_source,
    sha256_hex,
};
use anyhow::{bail, Context, Result};
use rayon::{prelude::*, ThreadPoolBuilder};
use serde_json::{json, Map, Value};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

const PROVENANCE_PLACEHOLDER: &str = "__JSVM_CAPTURE_PROVENANCE__";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BundleMaterializeSummary {
    pub eligible_units: usize,
    pub unique_input_bodies: usize,
    pub bundles: usize,
    pub modules: usize,
    pub failures: usize,
    pub jobs: usize,
}

#[derive(Debug, Clone)]
struct EligibleUnit {
    ordinal: Value,
    resource_id: Value,
    parent_rel: PathBuf,
    parent: PathBuf,
    content_sha256: String,
}

#[derive(Debug)]
struct ModuleTask {
    module_index: usize,
    raw: String,
    raw_sha256: String,
    provenance: String,
    dest: PathBuf,
}

fn safe_component(value: &str, cap: usize) -> String {
    let mut cleaned = String::new();
    let mut pending_underscore = false;
    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() || matches!(ch, '.' | '_' | '-') {
            if pending_underscore && !cleaned.is_empty() {
                cleaned.push('_');
            }
            pending_underscore = false;
            cleaned.push(ch);
        } else {
            pending_underscore = true;
        }
    }
    let cleaned = cleaned.trim_matches(|ch| matches!(ch, '.' | '_'));
    let cleaned = if cleaned.is_empty() {
        "module"
    } else {
        cleaned
    };
    if cleaned.chars().count() <= cap {
        return cleaned.to_owned();
    }
    let digest = &sha256_hex(value.as_bytes())[..12];
    let prefix_len = cap.saturating_sub(13);
    let prefix = cleaned.chars().take(prefix_len).collect::<String>();
    format!("{prefix}-{digest}")
}

fn module_output_path(
    parent: &Path,
    kind: &str,
    chunk_ids: &[String],
    module_id: &str,
    bundle_id: usize,
) -> Result<PathBuf> {
    let parts = parent.components().collect::<Vec<_>>();
    let source_rel = if parts.len() >= 2
        && parts[0].as_os_str() == "src"
        && parts[1].as_os_str() == "_deobfuscated"
    {
        parts[2..].iter().collect::<PathBuf>()
    } else if parts.first().is_some_and(|part| part.as_os_str() == "src") {
        parts[1..].iter().collect::<PathBuf>()
    } else {
        parent.to_path_buf()
    };
    let name = source_rel
        .file_name()
        .and_then(|name| name.to_str())
        .context("bundle parent path has no UTF-8 filename")?;
    let stem_dir = source_rel.with_file_name(format!("{name}.modules"));
    let group = match kind {
        "amd_named_modules" => "amd-modules".to_owned(),
        "member_named_modules" => "member-named-modules".to_owned(),
        "browserify_module_table" => "browserify-modules".to_owned(),
        _ if !chunk_ids.is_empty() => format!(
            "chunk-{}",
            chunk_ids
                .iter()
                .map(|id| safe_component(id, 24))
                .collect::<Vec<_>>()
                .join("-")
        ),
        _ => format!("module-table-{:02}", bundle_id + 1),
    };
    Ok(PathBuf::from("src/_modules")
        .join(stem_dir)
        .join(group)
        .join(format!("module-{}.js", safe_component(module_id, 96))))
}

fn source_span<'a>(source: &'a str, start: u32, end: u32, label: &str) -> Result<&'a str> {
    let start = usize::try_from(start).context("source span start does not fit usize")?;
    let end = usize::try_from(end).context("source span end does not fit usize")?;
    source
        .get(start..end)
        .with_context(|| format!("{label}: invalid UTF-8 source span {start}..{end}"))
}

fn build_module_source(
    source: &str,
    module: &ModuleRecord,
    provenance: &str,
    bundle_kind: &str,
) -> Result<String> {
    let property = source_span(
        source,
        module.property_start,
        module.property_end,
        "module property",
    )?;
    let value = source_span(source, module.value_start, module.value_end, "module value")?;
    let mut metadata = String::new();
    if !module.export_names.is_empty() {
        let mut preview = module
            .export_names
            .iter()
            .take(12)
            .cloned()
            .collect::<Vec<_>>()
            .join(", ");
        if module.export_names.len() > 12 {
            preview.push_str(&format!(", … (+{} more)", module.export_names.len() - 12));
        }
        metadata.push_str(&format!(" * Static export names: {preview}\n"));
    }
    if module.commonjs_export {
        metadata.push_str(" * Static CommonJS module.exports write observed.\n");
    }
    if bundle_kind == "browserify_module_table" {
        let mut dependencies = module
            .dependency_map
            .iter()
            .take(12)
            .map(|(name, target)| format!("{name} -> {target}"))
            .collect::<Vec<_>>()
            .join(", ");
        if module.dependency_map.len() > 12 {
            dependencies.push_str(&format!(", … (+{} more)", module.dependency_map.len() - 12));
        }
        if !dependencies.is_empty() {
            metadata.push_str(&format!(
                " * Static Browserify dependency map: {dependencies}\n"
            ));
        }
        return Ok(format!(
            "/* Statically extracted Browserify module factory.\n * {provenance}\n{metadata} * The factory body is preserved from the parent analyst view.\n */\nconst __browserify_module_factory__ = {value};\n"
        ));
    }
    if matches!(bundle_kind, "amd_named_modules" | "member_named_modules") {
        let mut dependencies = module
            .dependencies
            .iter()
            .take(12)
            .cloned()
            .collect::<Vec<_>>()
            .join(", ");
        if module.dependencies.len() > 12 {
            dependencies.push_str(&format!(", … (+{} more)", module.dependencies.len() - 12));
        }
        if !dependencies.is_empty() {
            let label = if bundle_kind == "amd_named_modules" {
                "AMD"
            } else {
                "named-loader"
            };
            metadata.push_str(&format!(" * Static {label} dependencies: {dependencies}\n"));
        }
        let family = if bundle_kind == "amd_named_modules" {
            "named AMD"
        } else {
            "member-loader named"
        };
        return Ok(format!(
            "/* Statically extracted {family} module factory.\n * {provenance}\n{metadata} * The factory body is preserved from the parent analyst view.\n */\nconst __named_module_factory__ = {value};\n"
        ));
    }
    let header = format!(
        "/* Statically extracted Webpack/Next module wrapper.\n * {provenance}\n{metadata} * The wrapper body is preserved from the parent analyst view.\n */\n"
    );
    if module.method {
        let key = serde_json::to_string(&module.id)?;
        Ok(format!(
            "{header}const __webpack_module_table__ = {{\n{property}\n}};\nconst __webpack_module__ = __webpack_module_table__[{key}];\n"
        ))
    } else {
        Ok(format!("{header}const __webpack_module__ = {value};\n"))
    }
}

fn markdown_text(value: &str) -> String {
    value
        .replace('\\', "\\\\")
        .replace('|', "\\|")
        .replace('`', "\\`")
}

fn string_field<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

fn array_len(value: &Value, key: &str) -> usize {
    value.get(key).and_then(Value::as_array).map_or(0, Vec::len)
}

fn bool_field(value: &Value, key: &str) -> bool {
    value.get(key).and_then(Value::as_bool).unwrap_or(false)
}

fn write_module_readme(module_root: &Path, bundles: &[Value], modules: &[Value]) -> Result<()> {
    fs::create_dir_all(module_root)
        .with_context(|| format!("creating {}", module_root.display()))?;
    let mut by_bundle = BTreeMap::<u64, Vec<&Value>>::new();
    for module in modules {
        let bundle_id = module
            .get("bundle_id")
            .and_then(Value::as_u64)
            .context("module bundle_id must be a non-negative integer")?;
        by_bundle.entry(bundle_id).or_default().push(module);
    }
    let named_count = modules
        .iter()
        .filter(|module| array_len(module, "export_names") > 0)
        .count();
    let commonjs_count = modules
        .iter()
        .filter(|module| bool_field(module, "commonjs_export"))
        .count();
    let mut lines = vec![
        "# Recovered structured modules".to_owned(),
        String::new(),
        "Module filenames retain captured module identity: explicit AMD names or Webpack/Next module IDs. Static export names are scope-resolved navigation metadata, not invented filenames.".to_owned(),
        String::new(),
        format!("- Bundle payloads: **{}**", bundles.len()),
        format!("- Modules: **{}**", modules.len()),
        format!("- Modules with named exports: **{named_count}**"),
        format!("- Modules with static CommonJS writes: **{commonjs_count}**"),
        String::new(),
    ];
    for bundle in bundles {
        let bundle_id = bundle
            .get("bundle_id")
            .and_then(Value::as_u64)
            .context("bundle_id must be a non-negative integer")?;
        let rows = by_bundle.get(&bundle_id).cloned().unwrap_or_default();
        let named = rows
            .iter()
            .filter(|row| array_len(row, "export_names") > 0)
            .copied()
            .collect::<Vec<_>>();
        let commonjs_only = rows
            .iter()
            .filter(|row| bool_field(row, "commonjs_export") && array_len(row, "export_names") == 0)
            .count();
        let anonymous = rows.len().saturating_sub(named.len() + commonjs_only);
        let kind = string_field(bundle, "kind").unwrap_or_default();
        let chunk_ids = bundle
            .get("chunk_ids")
            .and_then(Value::as_array)
            .cloned()
            .unwrap_or_default();
        let identity = match kind {
            "amd_named_modules" => "named AMD modules".to_owned(),
            "member_named_modules" => "member-loader named modules".to_owned(),
            "browserify_module_table" => "Browserify module table".to_owned(),
            _ if !chunk_ids.is_empty() => format!(
                "chunk {}",
                chunk_ids
                    .iter()
                    .filter_map(Value::as_str)
                    .map(markdown_text)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            _ => "direct module table".to_owned(),
        };
        lines.extend([
            format!("## Bundle {:02} — {identity}", bundle_id + 1),
            String::new(),
            format!("- Parent: `{}`", markdown_text(string_field(bundle, "parent_path").unwrap_or_default())),
            format!("- Modules: **{}**; named: **{}**; CommonJS-only: **{commonjs_only}**; unlabeled: **{anonymous}**", rows.len(), named.len()),
        ]);
        if !named.is_empty() {
            lines.extend([String::new(), "Named-export modules:".to_owned()]);
            for row in named {
                let source_path = string_field(row, "source_path").unwrap_or_default();
                let relative = Path::new(source_path)
                    .strip_prefix("src/_modules")
                    .with_context(|| {
                        format!("module path is outside src/_modules: {source_path}")
                    })?;
                let names = row
                    .get("export_names")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .map(markdown_text)
                    .collect::<Vec<_>>()
                    .join(", ");
                lines.push(format!(
                    "- [module {}]({}): {names} — {} literal dep(s)",
                    markdown_text(string_field(row, "module_id").unwrap_or_default()),
                    relative.to_string_lossy(),
                    array_len(row, "dependencies")
                ));
            }
        }
        lines.push(String::new());
    }
    fs::write(module_root.join("README.md"), lines.join("\n"))
        .with_context(|| format!("writing {}/README.md", module_root.display()))
}

fn remove_tree_if_present(path: &Path) -> Result<()> {
    match fs::remove_dir_all(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error).with_context(|| format!("removing {}", path.display())),
    }
}

fn report_for_group(
    digest: &str,
    group: &[usize],
    units: &[EligibleUnit],
) -> (String, Result<BundleInventoryReport, String>) {
    let Some(&index) = group.first() else {
        return (digest.to_owned(), Err("empty inventory group".to_owned()));
    };
    let unit = &units[index];
    let result = fs::read_to_string(&unit.parent)
        .map_err(|error| format!("reading {}: {error}", unit.parent.display()))
        .map(|source| analyze_bundle_source(&source, unit.parent.display().to_string()));
    (digest.to_owned(), result)
}

pub fn materialize_bundle_modules(
    project: &Path,
    jobs: Option<usize>,
) -> Result<BundleMaterializeSummary> {
    let jobs = jobs.unwrap_or_else(|| default_jobs(32)).max(1);
    let deob = load_artifact(project, DEOBFUSCATION, false)?
        .context("safe deobfuscation artifact is missing")?;
    let deob_units = deob
        .get("units")
        .and_then(Value::as_array)
        .context("safe deobfuscation units must be an array")?;
    let module_root = project.join("src/_modules");
    remove_tree_if_present(&module_root)?;

    let mut units = Vec::new();
    let mut groups = BTreeMap::<String, Vec<usize>>::new();
    for unit in deob_units {
        let exit = unit.get("exit").and_then(Value::as_i64).unwrap_or(0);
        if exit != 0 {
            continue;
        }
        let Some(parent_rel) = unit.get("output_path").and_then(Value::as_str) else {
            continue;
        };
        let parent = project.join(parent_rel);
        if !parent.is_file() {
            continue;
        }
        let digest = match unit.get("output_sha256").and_then(Value::as_str) {
            Some(value) => value.to_owned(),
            None => sha256_path(&parent)?,
        };
        let index = units.len();
        units.push(EligibleUnit {
            ordinal: unit.get("ordinal").cloned().unwrap_or(Value::Null),
            resource_id: unit.get("resource_id").cloned().unwrap_or(Value::Null),
            parent_rel: PathBuf::from(parent_rel),
            parent,
            content_sha256: digest.clone(),
        });
        groups.entry(digest).or_default().push(index);
    }

    let pool = ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .context("building bundle-analysis thread pool")?;
    let grouped = groups.iter().collect::<Vec<_>>();
    let inventory_rows = pool.install(|| {
        grouped
            .par_iter()
            .map(|(digest, group)| report_for_group(digest, group, &units))
            .collect::<Vec<_>>()
    });
    let inventory = inventory_rows.into_iter().collect::<BTreeMap<_, _>>();

    let mut bundles = Vec::<Value>::new();
    let mut modules = Vec::<Value>::new();
    let mut tasks = Vec::<ModuleTask>::new();
    let mut failures = Vec::<Value>::new();
    let mut seen_digest = BTreeMap::<String, usize>::new();

    for unit in &units {
        let occurrence = *seen_digest.get(&unit.content_sha256).unwrap_or(&0);
        seen_digest.insert(unit.content_sha256.clone(), occurrence + 1);
        let group_size = groups.get(&unit.content_sha256).map_or(0, Vec::len);
        let report = inventory
            .get(&unit.content_sha256)
            .with_context(|| format!("missing inventory result for {}", unit.content_sha256))?;
        let report = match report {
            Ok(report) => report,
            Err(error) => {
                failures.push(json!({
                    "ordinal": unit.ordinal, "path": unit.parent_rel.to_string_lossy(),
                    "content_sha256": unit.content_sha256, "content_group_size": group_size,
                    "deduplicated": occurrence > 0, "error": error,
                }));
                continue;
            }
        };
        let source = fs::read_to_string(&unit.parent)
            .with_context(|| format!("reading {}", unit.parent.display()))?;
        for (bundle_ordinal, bundle) in report.bundles.iter().enumerate() {
            let bundle_id = bundles.len();
            bundles.push(json!({
                "bundle_id": bundle_id, "parent_ordinal": unit.ordinal, "resource_id": unit.resource_id,
                "parent_path": unit.parent_rel.to_string_lossy(), "parent_content_sha256": unit.content_sha256,
                "inventory_group_size": group_size, "inventory_deduplicated": occurrence > 0,
                "kind": bundle.kind, "chunk_ids": bundle.chunk_ids, "start": bundle.start, "end": bundle.end,
                "module_table_start": bundle.module_table_start, "module_table_end": bundle.module_table_end,
                "module_count": bundle.modules.len(),
                "module_ids": bundle.modules.iter().map(|module| module.id.clone()).collect::<Vec<_>>(),
            }));
            for (module_ordinal, module) in bundle.modules.iter().enumerate() {
                let rel = module_output_path(
                    &unit.parent_rel,
                    &bundle.kind,
                    &bundle.chunk_ids,
                    &module.id,
                    bundle_ordinal,
                )?;
                let provenance = format!(
                    "parent={} bundle_span={}..{} module={} property_span={}..{}",
                    unit.parent_rel.display(),
                    bundle.start,
                    bundle.end,
                    module.id,
                    module.property_start,
                    module.property_end
                );
                let raw =
                    build_module_source(&source, module, PROVENANCE_PLACEHOLDER, &bundle.kind)?;
                let raw_sha = sha256_hex(raw.as_bytes());
                let module_index = modules.len();
                modules.push(json!({
                    "bundle_id": bundle_id, "module_ordinal": module_ordinal, "parent_ordinal": unit.ordinal,
                    "resource_id": unit.resource_id, "parent_path": unit.parent_rel.to_string_lossy(),
                    "parent_content_sha256": unit.content_sha256, "bundle_kind": bundle.kind,
                    "chunk_ids": bundle.chunk_ids, "module_id": module.id, "property_start": module.property_start,
                    "property_end": module.property_end, "value_start": module.value_start, "value_end": module.value_end,
                    "value_kind": module.value_kind, "method": module.method, "dependencies": module.dependencies,
                    "dependency_map": module.dependency_map, "export_names": module.export_names,
                    "commonjs_export": module.commonjs_export, "source_path": rel.to_string_lossy(),
                    "module_input_sha256": raw_sha,
                }));
                tasks.push(ModuleTask {
                    module_index,
                    raw,
                    raw_sha256: raw_sha,
                    provenance,
                    dest: project.join(rel),
                });
            }
        }
    }

    let mut format_groups = BTreeMap::<String, Vec<usize>>::new();
    for (index, task) in tasks.iter().enumerate() {
        format_groups
            .entry(task.raw_sha256.clone())
            .or_default()
            .push(index);
    }
    let grouped_formats = format_groups.iter().collect::<Vec<_>>();
    let formatted = pool.install(|| {
        grouped_formats
            .par_iter()
            .map(|(digest, group)| {
                let Some(&index) = group.first() else {
                    return (digest.to_string(), String::new(), false);
                };
                let raw = &tasks[index].raw;
                match format_source(raw) {
                    Ok(formatted) => (digest.to_string(), formatted, true),
                    Err(_) => (digest.to_string(), raw.clone(), false),
                }
            })
            .collect::<Vec<_>>()
    });
    let formatted = formatted
        .into_iter()
        .map(|(digest, source, ok)| (digest, (source, ok)))
        .collect::<BTreeMap<_, _>>();

    for group in format_groups.values() {
        let Some(&canonical_task) = group.first() else {
            continue;
        };
        let digest = &tasks[canonical_task].raw_sha256;
        let (template, did_format) = formatted
            .get(digest)
            .with_context(|| format!("missing format result for {digest}"))?;
        if !template.contains(PROVENANCE_PLACEHOLDER) {
            bail!("formatter dropped module provenance placeholder for {digest}");
        }
        let canonical_module_index = tasks[canonical_task].module_index;
        for &task_index in group {
            let task = &tasks[task_index];
            let rendered = template.replacen(PROVENANCE_PLACEHOLDER, &task.provenance, 1);
            if let Some(parent) = task.dest.parent() {
                fs::create_dir_all(parent)
                    .with_context(|| format!("creating {}", parent.display()))?;
            }
            fs::write(&task.dest, &rendered)
                .with_context(|| format!("writing {}", task.dest.display()))?;
            let record = modules
                .get_mut(task.module_index)
                .and_then(Value::as_object_mut)
                .context("module record is not an object")?;
            record.insert("formatted".into(), Value::Bool(*did_format));
            record.insert(
                "sha256".into(),
                Value::String(sha256_hex(rendered.as_bytes())),
            );
            record.insert("format_group_size".into(), Value::from(group.len()));
            record.insert(
                "format_deduplicated".into(),
                Value::Bool(task.module_index != canonical_module_index),
            );
            record.insert(
                "materialization".into(),
                Value::String("rendered_content_template".into()),
            );
        }
    }

    let kind_modules = |kind: &str| -> usize {
        bundles
            .iter()
            .filter(|bundle| string_field(bundle, "kind") == Some(kind))
            .map(|bundle| array_len(bundle, "module_ids"))
            .sum()
    };
    let webpack_modules = bundles
        .iter()
        .filter(|bundle| {
            !matches!(
                string_field(bundle, "kind"),
                Some("amd_named_modules" | "member_named_modules" | "browserify_module_table")
            )
        })
        .map(|bundle| array_len(bundle, "module_ids"))
        .sum::<usize>();
    let summary = json!({
        "eligible_units": units.len(), "unique_input_bodies": groups.len(),
        "deduplicated_units": units.len().saturating_sub(groups.len()), "inventory_invocations": groups.len(),
        "module_format_invocations": format_groups.len(), "deduplicated_module_formats": tasks.len().saturating_sub(format_groups.len()),
        "jobs": jobs, "bundles": bundles.len(), "modules": modules.len(),
        "amd_named_modules": kind_modules("amd_named_modules"), "member_named_modules": kind_modules("member_named_modules"),
        "browserify_modules": kind_modules("browserify_module_table"), "webpack_modules": webpack_modules,
        "literal_module_dependencies": modules.iter().map(|module| array_len(module, "dependencies")).sum::<usize>(),
        "modules_with_named_exports": modules.iter().filter(|module| array_len(module, "export_names") > 0).count(),
        "named_exports": modules.iter().map(|module| array_len(module, "export_names")).sum::<usize>(),
        "commonjs_export_modules": modules.iter().filter(|module| bool_field(module, "commonjs_export")).count(),
        "failed_units": failures.len(),
    });
    let mut document = Map::new();
    document.insert("schema".into(), Value::String(BUNDLES.schema.into()));
    document.insert("safe_static_only".into(), Value::Bool(true));
    document.insert(
        "inventory".into(),
        Value::String("jsvm_lift::bundle_unpack".into()),
    );
    document.insert("bundles".into(), Value::Array(bundles.clone()));
    document.insert("modules".into(), Value::Array(modules.clone()));
    document.insert("failures".into(), Value::Array(failures.clone()));
    document.insert("summary".into(), summary);
    write_artifact(project, BUNDLES, &Value::Object(document))?;
    write_module_readme(&module_root, &bundles, &modules)?;

    Ok(BundleMaterializeSummary {
        eligible_units: units.len(),
        unique_input_bodies: groups.len(),
        bundles: bundles.len(),
        modules: modules.len(),
        failures: failures.len(),
        jobs,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis_artifacts::{load_artifact, write_artifact, BUNDLES, DEOBFUSCATION};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn test_project() -> Result<PathBuf> {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let path =
            std::env::temp_dir().join(format!("bundle-materialize-{}-{nonce}", std::process::id()));
        fs::create_dir_all(path.join("src/_deobfuscated"))?;
        Ok(path)
    }

    #[test]
    fn materializes_generated_bundle_fixture_and_deduplicates_identical_units() -> Result<()> {
        let project = test_project()?;
        let result = (|| -> Result<()> {
            let source = include_str!(
                "../../../corpus/generated/reversible-obfuscation/bundle-module-tables.js"
            );
            let first = project.join("src/_deobfuscated/a.js");
            let second = project.join("src/_deobfuscated/b.js");
            fs::write(&first, source)?;
            fs::write(&second, source)?;
            let digest = sha256_hex(source.as_bytes());
            let artifact = json!({
                "schema": DEOBFUSCATION.schema,
                "units": [
                    {"ordinal": 0, "resource_id": 10, "output_path": "src/_deobfuscated/a.js", "output_sha256": digest, "exit": 0},
                    {"ordinal": 1, "resource_id": 11, "output_path": "src/_deobfuscated/b.js", "output_sha256": digest, "exit": 0}
                ],
                "summary": {}
            });
            write_artifact(&project, DEOBFUSCATION, &artifact)?;
            let summary = materialize_bundle_modules(&project, Some(2))?;
            assert_eq!(summary.eligible_units, 2);
            assert_eq!(summary.unique_input_bodies, 1);
            assert!(summary.bundles >= 2);
            assert!(summary.modules >= 2);
            assert_eq!(summary.failures, 0);
            assert!(project.join("src/_modules/README.md").is_file());
            let bundles =
                load_artifact(&project, BUNDLES, false)?.context("bundle artifact missing")?;
            assert_eq!(
                bundles
                    .get("summary")
                    .and_then(|summary| summary.get("inventory_invocations"))
                    .and_then(Value::as_u64),
                Some(1)
            );
            let module_rows = bundles
                .get("modules")
                .and_then(Value::as_array)
                .context("bundle modules missing")?;
            assert!(module_rows.iter().all(|module| module
                .get("source_path")
                .and_then(Value::as_str)
                .is_some_and(|path| project.join(path).is_file())));
            Ok(())
        })();
        let cleanup = fs::remove_dir_all(&project);
        result?;
        cleanup?;
        Ok(())
    }
}
