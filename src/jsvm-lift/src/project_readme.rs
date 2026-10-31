use crate::{
    analysis_artifacts::{
        load_artifact, API_SURFACE, BUNDLES, DEOBFUSCATION, GENERATED_RECOVERY, IMPORT_MAPS,
        JSVM_INDEX, JS_REFERENCES, RUNTIME_SCRIPTS, SOURCEMAPS, SOURCE_GRAPH, SOURCE_INDEX,
        WASM_RESOURCE_PROVENANCE,
    },
    capture_project::load_manifest,
};
use anyhow::{Context, Result};
use serde_json::{json, Value};
use std::{collections::BTreeMap, fs, path::Path};

fn array<'a>(value: &'a Value, key: &str) -> &'a [Value] {
    value
        .get(key)
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .unwrap_or_default()
}

fn object<'a>(value: &'a Value, key: &str) -> Option<&'a serde_json::Map<String, Value>> {
    value.get(key).and_then(Value::as_object)
}

fn usize_field(value: &Value, key: &str) -> usize {
    value
        .get(key)
        .and_then(Value::as_u64)
        .and_then(|v| usize::try_from(v).ok())
        .unwrap_or_default()
}

fn bool_field(value: &Value, key: &str) -> bool {
    value.get(key).and_then(Value::as_bool).unwrap_or(false)
}

fn nonzero_integer_field(value: &Value, key: &str) -> bool {
    value
        .get(key)
        .and_then(Value::as_i64)
        .is_some_and(|number| number != 0)
}

fn str_field<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

fn default_artifact(
    schema: &str,
    fields: impl IntoIterator<Item = (&'static str, Value)>,
) -> Value {
    let mut value = serde_json::Map::new();
    value.insert("schema".into(), Value::String(schema.into()));
    for (key, item) in fields {
        value.insert(key.into(), item);
    }
    Value::Object(value)
}

fn load_or(
    project: &Path,
    spec: crate::analysis_artifacts::ArtifactSpec,
    fallback: Value,
) -> Result<Value> {
    Ok(load_artifact(project, spec, true)?.unwrap_or(fallback))
}

fn compact(value: Option<&Value>) -> String {
    value
        .and_then(|v| serde_json::to_string(v).ok())
        .unwrap_or_else(|| "{}".into())
}

pub fn refresh_project_readme(project: &Path) -> Result<()> {
    let project = project
        .canonicalize()
        .with_context(|| format!("resolving project {}", project.display()))?;
    let manifest = load_manifest(&project)?;
    let manifest_value = serde_json::to_value(&manifest)?;

    let source_index = load_or(
        &project,
        SOURCE_INDEX,
        default_artifact(
            SOURCE_INDEX.schema,
            [("units", json!([])), ("summary", json!({}))],
        ),
    )?;
    let sourcemaps = load_or(
        &project,
        SOURCEMAPS,
        default_artifact(SOURCEMAPS.schema, [("source_maps", json!([]))]),
    )?;
    let jsrefs = load_or(
        &project,
        JS_REFERENCES,
        default_artifact(
            JS_REFERENCES.schema,
            [("code_units", json!([])), ("summary", json!({}))],
        ),
    )?;
    let import_maps = load_or(
        &project,
        IMPORT_MAPS,
        default_artifact(
            IMPORT_MAPS.schema,
            [
                ("maps", json!([])),
                ("documents", json!({})),
                ("summary", json!({})),
            ],
        ),
    )?;
    let deob = load_or(
        &project,
        DEOBFUSCATION,
        default_artifact(
            DEOBFUSCATION.schema,
            [("units", json!([])), ("summary", json!({}))],
        ),
    )?;
    let jsvm = load_or(
        &project,
        JSVM_INDEX,
        default_artifact(
            JSVM_INDEX.schema,
            [
                ("code_units", json!([])),
                ("dynamic_code_units", json!([])),
                ("devirtualized_units", json!([])),
            ],
        ),
    )?;
    let graph = load_or(
        &project,
        SOURCE_GRAPH,
        default_artifact(
            SOURCE_GRAPH.schema,
            [
                ("nodes", json!([])),
                ("edges", json!([])),
                ("summary", json!({})),
            ],
        ),
    )?;
    let api_surface_doc = load_artifact(&project, API_SURFACE, true)?;
    let api_surface = api_surface_doc.clone().unwrap_or_else(|| {
        default_artifact(
            API_SURFACE.schema,
            [
                ("callsites", json!([])),
                ("failures", json!([])),
                ("summary", json!({})),
            ],
        )
    });
    let bundles = load_or(
        &project,
        BUNDLES,
        default_artifact(
            BUNDLES.schema,
            [
                ("bundles", json!([])),
                ("modules", json!([])),
                ("failures", json!([])),
                ("summary", json!({})),
            ],
        ),
    )?;
    let generated_recovery = load_or(
        &project,
        GENERATED_RECOVERY,
        default_artifact(
            GENERATED_RECOVERY.schema,
            [("units", json!([])), ("summary", json!({}))],
        ),
    )?;
    let runtime_scripts = load_or(
        &project,
        RUNTIME_SCRIPTS,
        default_artifact(
            RUNTIME_SCRIPTS.schema,
            [
                ("sources", json!([])),
                ("alpine_families", json!([])),
                ("gtm_families", json!([])),
                ("summary", json!({})),
            ],
        ),
    )?;
    let wasm_resource_provenance = load_artifact(&project, WASM_RESOURCE_PROVENANCE, true)?;

    let resources = array(&manifest_value, "resources");
    let source_units = array(&source_index, "units");
    let js_units = source_units
        .iter()
        .filter(|unit| str_field(unit, "kind") == Some("javascript"))
        .collect::<Vec<_>>();
    let mut source_kinds = BTreeMap::<String, usize>::new();
    for unit in source_units {
        *source_kinds
            .entry(str_field(unit, "kind").unwrap_or("unknown").to_owned())
            .or_default() += 1;
    }

    let mut recovered_originals = 0usize;
    let mut composed_sourcemap_links = 0usize;
    for sm in array(&sourcemaps, "source_maps") {
        let composed = array(sm, "composed_recovered");
        let recovered = if composed.is_empty() {
            array(sm, "recovered")
        } else {
            composed
        };
        recovered_originals += recovered
            .iter()
            .filter(|record| str_field(record, "status") == Some("recovered"))
            .count();
        composed_sourcemap_links += object(sm, "composition")
            .and_then(|o| o.get("composed_links"))
            .and_then(Value::as_u64)
            .and_then(|v| usize::try_from(v).ok())
            .unwrap_or_default();
    }

    let vm_units = array(&jsvm, "code_units");
    let confirmed = vm_units
        .iter()
        .filter(|unit| bool_field(unit, "confirmed_vm_signal"))
        .collect::<Vec<_>>();
    let candidates = vm_units
        .iter()
        .filter(|unit| bool_field(unit, "vm_signal") && !bool_field(unit, "confirmed_vm_signal"))
        .collect::<Vec<_>>();
    let devirtualized = array(&jsvm, "devirtualized_units");
    let dynamic = array(&jsvm, "dynamic_code_units");
    let recursive_generated = vm_units
        .iter()
        .filter(|unit| str_field(unit, "origin") == Some("generated_dynamic_code"))
        .count();
    let large_handler_candidates = candidates
        .iter()
        .copied()
        .filter(|unit| bool_field(unit, "large_handler_table_candidate"))
        .collect::<Vec<_>>();
    let switch_devirtualized = devirtualized
        .iter()
        .filter(|unit| str_field(unit, "vm_kind") == Some("direct_switch"))
        .count();
    let table_devirtualized = devirtualized
        .iter()
        .filter(|unit| str_field(unit, "vm_kind") == Some("function_table"))
        .count();

    let deob_summary = deob.get("summary").unwrap_or(&Value::Null);
    let changed_deob = deob_summary
        .get("changed_units")
        .and_then(Value::as_u64)
        .and_then(|v| usize::try_from(v).ok())
        .unwrap_or_else(|| {
            array(&deob, "units")
                .iter()
                .filter(|unit| bool_field(unit, "changed"))
                .count()
        });
    let deob_failures = deob_summary
        .get("failures")
        .and_then(Value::as_u64)
        .and_then(|v| usize::try_from(v).ok())
        .unwrap_or_else(|| {
            array(&deob, "units")
                .iter()
                .filter(|unit| nonzero_integer_field(unit, "exit"))
                .count()
        });
    let arithmetic_state_proofs = array(&deob, "units")
        .iter()
        .map(|unit| array(unit, "arithmetic_state_proofs").len())
        .sum::<usize>();

    let source = manifest_value
        .get("source")
        .context("capture manifest source missing")?;
    let capture_state = if bool_field(source, "salvaged") {
        "SALVAGED / truncated"
    } else {
        "complete"
    };
    let source_capture = str_field(source, "input").unwrap_or("browser capture");
    let source_kind = str_field(source, "kind").unwrap_or("unknown");
    let original_url = str_field(source, "original_page_url");
    let source_summary = source_index.get("summary").unwrap_or(&Value::Null);
    let jsref_summary = jsrefs.get("summary").unwrap_or(&Value::Null);
    let import_summary = import_maps.get("summary").unwrap_or(&Value::Null);
    let bundle_summary = bundles.get("summary").unwrap_or(&Value::Null);
    let generated_summary = generated_recovery.get("summary").unwrap_or(&Value::Null);
    let runtime_summary = runtime_scripts.get("summary").unwrap_or(&Value::Null);
    let runtime_classes = runtime_summary.get("classifications");
    let api_summary = api_surface.get("summary").unwrap_or(&Value::Null);
    let wasm_runtime_summary = wasm_resource_provenance
        .as_ref()
        .and_then(|doc| doc.get("summary"));

    let mut lines = vec![
        "# Recovered source project".to_owned(),
        String::new(),
        format!("Generated from {source_capture}. Input kind: **{source_kind}**. Capture state: **{capture_state}**."),
    ];
    if let Some(url) = original_url {
        lines.push(format!(
            "Original page URL recorded by the saved page: {url}."
        ));
    }
    lines.extend([
        String::new(),
        "This tree keeps capture truth separate from analyst transformations. Start in src/ for readable code, and use analysis/source-graph.json when you need exact provenance back to the browser capture.".into(),
        String::new(),
        "## Start here".into(),
        String::new(),
        "- [src/](src/) — Oxc-formatted baseline view of captured text/code resources.".into(),
        "- [src/_deobfuscated/](src/_deobfuscated/) — semantics-preserving static recovery run from the exact captured JS bytes; formatting is intentionally left untouched here.".into(),
        "- [src/_readable/](src/_readable/) — formatted analyst view of the safe-deobfuscated result; use this as the normal human reading tree.".into(),
        "- [src/_devirtualized/](src/_devirtualized/) — readable modules/pseudocode for confirmed JavaScript VM interpreters.".into(),
        "- [src/_dynamic/](src/_dynamic/) — formatted analyst views of statically recovered generated-code bodies such as Function(...).".into(),
        "- [src/_dynamic_deobfuscated/](src/_dynamic_deobfuscated/) — proven safe recovery of generated-code children when string/deob passes validate; exact bytes remain the fallback.".into(),
        "- [src/_sourcemap/](src/_sourcemap/) — direct source-map sources plus `final/` views after nested map chains are composed.".into(),
        "- [src/_modules/](src/_modules/) — statically extracted Webpack/Next module wrappers and named AMD factories where module structure is explicit.".into(),
        "- [resources/](resources/) — capture-faithful response bodies or saved-page files.".into(),
        "- [capture-manifest.json](capture-manifest.json) — canonical normalized capture provenance and resource inventory.".into(),
        "- [analysis/import-maps.json](analysis/import-maps.json) — captured import-map definitions, normalized mappings and merge diagnostics.".into(),
        "- [analysis/source-graph.json](analysis/source-graph.json) — machine-readable relationship/provenance graph.".into(),
    ]);
    if api_surface_doc.is_some() {
        lines.push("- [analysis/api-surface.json](analysis/api-surface.json) — proof-gated static browser API callsites with exact URL/method evidence and per-source failures.".into());
    }
    if runtime_summary
        .as_object()
        .is_some_and(|summary| !summary.is_empty())
    {
        lines.push("- [analysis/runtime-scripts.json](analysis/runtime-scripts.json) — Debugger runtime-script provenance, generated-expression recovery, and capture-instrumentation classification.".into());
    }
    if wasm_resource_provenance.is_some() {
        lines.push("- [analysis/wasm-resource-provenance.json](analysis/wasm-resource-provenance.json) — runtime-observed exact WASM responses linked to their CDP script initiators.".into());
    }

    lines.extend([
        String::new(),
        "## Capture summary".into(),
        String::new(),
        format!("- Captured resources: **{}**", resources.len()),
        format!(
            "- Inline scripts: **{}**",
            array(&manifest_value, "inline_scripts").len()
        ),
    ]);
    if runtime_summary
        .as_object()
        .is_some_and(|summary| !summary.is_empty())
    {
        lines.push(format!("- Runtime debugger scripts: **{}** scriptParsed events / **{}** unique JavaScript sources", usize_field(runtime_summary, "script_parsed_events"), usize_field(runtime_summary, "unique_javascript_sources")));
        let class = |key| {
            runtime_classes
                .and_then(|v| v.get(key))
                .and_then(Value::as_u64)
                .unwrap_or_default()
        };
        lines.push(format!("- Runtime provenance: **{}** exact network-body matches, **{}** URL-proven network scripts without exact body bytes, **{}** snapshot/HAR inline, **{}** CDP-proven ephemeral document-inline, **{}** Alpine-generated expressions, **{}** GTM-generated custom JavaScript, **{}** generated by CDP-proven runtime parents, **{}** capture helpers, **{}** unexplained", class("network_response"), class("network_observed"), class("inline_script"), class("document_inline_script"), class("alpine_expression"), class("gtm_custom_javascript"), class("generated_runtime"), class("capture_instrumentation"), usize_field(runtime_summary, "anonymous_runtime_sources")));
        lines.push(format!("- Alpine runtime reduction: **{}** generated sources -> **{}** literal-normalized expression families; **{}** mapped back to captured DOM directives", class("alpine_expression"), usize_field(runtime_summary, "alpine_expression_shapes"), usize_field(runtime_summary, "alpine_dom_mapped_sources")));
        lines.push(format!("- GTM runtime reduction: **{}** generated custom-JavaScript sources -> **{}** literal-normalized families", class("gtm_custom_javascript"), usize_field(runtime_summary, "gtm_expression_shapes")));
    }
    if let Some(summary) = wasm_runtime_summary {
        if bool_field(summary, "applicable") {
            lines.push(format!("- Runtime-observed WASM responses: **{}** exact response observations / **{}** unique module bodies; exact runtime-script initiators: **{}**; identity proof: **{}** CDP-body + **{}** unique-URL/cardinality; unmatched body-bearing WASM events: **{}**; non-body WASM observations: **{}**", usize_field(summary, "observations"), usize_field(summary, "unique_wasm_sha256"), usize_field(summary, "runtime_script_identities"), usize_field(summary, "direct_body_identities"), usize_field(summary, "url_unique_body_identities"), usize_field(summary, "unmatched_wasm_events"), usize_field(summary, "ignored_non_body_wasm_events")));
        } else {
            lines.push(format!(
                "- Runtime WASM provenance unavailable: **{}**",
                str_field(summary, "unavailable_reason").unwrap_or("unknown")
            ));
        }
    }
    let unique_js = usize_field(source_summary, "unique_javascript_inputs");
    let unique_js = if source_summary.get("unique_javascript_inputs").is_some() {
        unique_js
    } else {
        js_units.len()
    };
    let extractor_invocations = if jsref_summary.get("extractor_invocations").is_some() {
        usize_field(jsref_summary, "extractor_invocations")
    } else {
        js_units.len()
    };
    lines.extend([
        format!("- Readable source units: **{}** ({} JavaScript)", source_units.len(), js_units.len()),
        format!("- Exact-content JS reuse: **{unique_js}** unique bodies / **{}** occurrences (**{}** formatter reuses)", js_units.len(), usize_field(source_summary, "deduplicated_javascript_units")),
        format!("- JS-reference extraction: **{extractor_invocations}** parser invocations / **{}** exact-hash reuses", usize_field(jsref_summary, "deduplicated_units")),
        format!("- Source kinds: {}", serde_json::to_string(&source_kinds)?),
        format!("- JS/module/worker references: **{}**", usize_field(jsref_summary, "references")),
    ]);
    if api_surface_doc.is_some() {
        lines.push(format!("- Static browser API callsites: **{}**; callsites with exact absolute network URLs: **{}**; proven invalid methods: **{}**; failed source units: **{}**", usize_field(api_summary, "callsites"), usize_field(api_summary, "absolute_network_urls"), usize_field(api_summary, "invalid_methods"), usize_field(api_summary, "failures")));
        lines.push(format!(
            "- Static browser API sink kinds: {}",
            compact(api_summary.get("kinds"))
        ));
    }
    lines.extend([
        format!("- Bounded dynamic-import patterns: **{}**; captured candidate URLs: **{}**; unmatched patterns: **{}**", usize_field(jsref_summary, "dynamic_import_globs"), usize_field(jsref_summary, "dynamic_import_candidate_urls"), usize_field(jsref_summary, "dynamic_import_unmatched")),
        format!("- Import-map blocks captured: **{}**", usize_field(import_summary, "import_map_scripts")),
        format!("- Imports resolved through import maps: **{}**", usize_field(jsref_summary, "resolved_by_import_map")),
        format!("- Unresolved bare module specifiers: **{}**", usize_field(jsref_summary, "unresolved_bare_specifiers")),
        format!("- Source-map originals recovered: **{recovered_originals}**"),
        format!("- Nested source-map links composed: **{composed_sourcemap_links}**"),
        format!("- Literal generated-code units recovered: **{}**", dynamic.len()),
        format!("- Generated-code units recursively scanned: **{recursive_generated}**"),
        format!("- Generated-code safe recovery: **{}** safe deob, **{}** string-only, **{}** exact fallback", usize_field(generated_summary, "safe_deobfuscation"), usize_field(generated_summary, "string_recovery_only"), usize_field(generated_summary, "exact_fallback")),
        format!("- Generated-child exact-content reuse: **{}** unique bodies / **{}** occurrences (**{}** recovery reuses)", if generated_summary.get("unique_raw_inputs").is_some() { usize_field(generated_summary, "unique_raw_inputs") } else { usize_field(generated_summary, "generated_units") }, usize_field(generated_summary, "generated_units"), usize_field(generated_summary, "deduplicated_units")),
        format!("- Generated children with full safe deobfuscation: **{}**", usize_field(generated_summary, "safe_deobfuscation")),
        format!("- Generated children with string-recovery only: **{}**", usize_field(generated_summary, "string_recovery_only")),
        format!("- Generated children scanned from exact fallback bytes: **{}**", usize_field(generated_summary, "exact_fallback")),
        String::new(),
        "## Safe static deobfuscation".into(),
        String::new(),
        format!("- Changed JavaScript units: **{changed_deob}**"),
        format!("- Failed units: **{deob_failures}**"),
        format!("- Content-addressed work: **{}** unique raw inputs, **{}** safe-deob invocations, **{}** readable-format invocations for **{}** JS occurrences", if deob_summary.get("unique_raw_inputs").is_some() { usize_field(deob_summary, "unique_raw_inputs") } else { js_units.len() }, if deob_summary.get("safe_deob_invocations").is_some() { usize_field(deob_summary, "safe_deob_invocations") } else { js_units.len() }, if deob_summary.get("readable_format_invocations").is_some() { usize_field(deob_summary, "readable_format_invocations") } else { js_units.len() }, if deob_summary.get("javascript_units").is_some() { usize_field(deob_summary, "javascript_units") } else { js_units.len() }),
        format!("- Encoded string-decoder recovery: **{}** call sites across **{}** unit(s)", usize_field(deob_summary, "string_recovery_replacements"), usize_field(deob_summary, "string_recovery_changed_units")),
        format!("- Proven arithmetic-state unflattenings: **{arithmetic_state_proofs}**"),
        "- Encoded string-table proof/provenance: [analysis/string-recovery.json](analysis/string-recovery.json)".into(),
        "- Detailed captured-unit final-view hashes, pass counts and provenance: [analysis/deobfuscation.json](analysis/deobfuscation.json)".into(),
        "- Recursive generated-code recovery/fallback provenance: [analysis/generated-recovery.json](analysis/generated-recovery.json)".into(),
        String::new(),
        "## Structured bundle modules".into(),
        String::new(),
        format!("- Bundle inventory work: **{}** parser invocations for **{}** eligible JS occurrences (**{}** exact-hash reuses)", if bundle_summary.get("inventory_invocations").is_some() { usize_field(bundle_summary, "inventory_invocations") } else { usize_field(bundle_summary, "eligible_units") }, usize_field(bundle_summary, "eligible_units"), usize_field(bundle_summary, "deduplicated_units")),
        format!("- Module-wrapper formatting: **{}** formatter invocations for **{}** outputs (**{}** exact-template reuses)", if bundle_summary.get("module_format_invocations").is_some() { usize_field(bundle_summary, "module_format_invocations") } else { usize_field(bundle_summary, "modules") }, usize_field(bundle_summary, "modules"), usize_field(bundle_summary, "deduplicated_module_formats")),
        format!("- Explicit bundle payloads recovered: **{}**", usize_field(bundle_summary, "bundles")),
        format!("- Readable module wrappers materialized: **{}** (**{}** Webpack/Next, **{}** Browserify, **{}** global named AMD, **{}** member-loader named modules)", usize_field(bundle_summary, "modules"), usize_field(bundle_summary, "webpack_modules"), usize_field(bundle_summary, "browserify_modules"), usize_field(bundle_summary, "amd_named_modules"), usize_field(bundle_summary, "member_named_modules")),
        format!("- Literal intra-bundle/module-loader dependencies recovered: **{}**", usize_field(bundle_summary, "literal_module_dependencies")),
        format!("- Modules with statically named exports: **{}** (**{}** distinct module-local export names observed)", usize_field(bundle_summary, "modules_with_named_exports"), usize_field(bundle_summary, "named_exports")),
        format!("- Modules with a static CommonJS `module.exports` write: **{}**", usize_field(bundle_summary, "commonjs_export_modules")),
        format!("- Bundle-analysis failures: **{}**", usize_field(bundle_summary, "failed_units")),
        "- Module inventory/provenance: [analysis/bundles.json](analysis/bundles.json)".into(),
        String::new(),
        "## VM analysis".into(),
        String::new(),
        format!("- Scanner work: **{}** scanner invocations / **{}** exact-hash reuses", if jsvm.get("scanner_invocations").is_some() { usize_field(&jsvm, "scanner_invocations") } else { vm_units.len() }, usize_field(&jsvm, "deduplicated_scans")),
        format!("- Proven bundle module tables excluded from handler-table candidate scoring: **{}**", vm_units.iter().map(|unit| usize_field(unit, "bundle_module_table_handler_tables")).sum::<usize>()),
        format!("- Confirmed VM-bearing JavaScript units: **{}**", confirmed.len()),
        format!("- Weaker VM candidates: **{}**", candidates.len()),
        format!("- Large unlinked handler-table candidates: **{}**", large_handler_candidates.len()),
        format!("- Materialized devirtualized interpreter modules: **{}** ({switch_devirtualized} direct-switch, {table_devirtualized} function-table)", devirtualized.len()),
    ]);

    if !confirmed.is_empty() {
        lines.extend([
            String::new(),
            "Confirmed VM-bearing resources/code units:".into(),
        ]);
        for unit in confirmed {
            let label = str_field(unit, "path")
                .or_else(|| str_field(unit, "url"))
                .map(ToOwned::to_owned)
                .unwrap_or_else(|| format!("scan {}", usize_field(unit, "scan_id")));
            lines.push(format!(
                "- {label} — {} devirtualized interpreter module(s)",
                array(unit, "devirtualized_units").len()
            ));
        }
    }
    if !large_handler_candidates.is_empty() {
        lines.extend([
            String::new(),
            "Large handler-table candidates not yet linked to a supported dispatcher:".into(),
        ]);
        for unit in large_handler_candidates {
            let label = str_field(unit, "path")
                .or_else(|| str_field(unit, "url"))
                .map(ToOwned::to_owned)
                .unwrap_or_else(|| format!("scan {}", usize_field(unit, "scan_id")));
            let handlers = if unit.get("largest_non_bundle_handler_table").is_some() {
                usize_field(unit, "largest_non_bundle_handler_table")
            } else {
                usize_field(unit, "largest_handler_table")
            };
            lines.push(format!(
                "- {label} — largest static function table {handlers} handlers"
            ));
        }
    }

    if let Some(summary) = graph
        .get("summary")
        .filter(|v| v.as_object().is_some_and(|o| !o.is_empty()))
    {
        lines.extend([
            String::new(),
            "## Provenance graph".into(),
            String::new(),
            format!("- Nodes: **{}**", usize_field(summary, "nodes")),
            format!("- Edges: **{}**", usize_field(summary, "edges")),
            format!(
                "- External uncaptured URLs: **{}**",
                usize_field(summary, "external_urls")
            ),
            format!("- Edge kinds: {}", compact(summary.get("edge_kinds"))),
        ]);
    }

    if bool_field(source, "salvaged") {
        lines.extend([
            String::new(),
            "## Capture caveat".into(),
            String::new(),
            "The input HAR ended before valid JSON completion. Structurally complete entries before the truncation point were salvaged; absence of later resources is not evidence they were never requested.".into(),
        ]);
        if let Some(parse_error) = str_field(source, "parse_error") {
            lines.push(format!("- HAR parse error: {parse_error}"));
        }
    }

    lines.extend([
        String::new(),
        "## Provenance rule".into(),
        String::new(),
        "resources/ is capture truth. Everything under src/, including _deobfuscated/, _readable/, _dynamic_deobfuscated/, _dynamic/, _devirtualized/, _modules/, and _sourcemap/, is a derived analyst view and should be traced through the files in analysis/ before treating it as original captured source.".into(),
        String::new(),
    ]);

    fs::write(project.join("README.md"), lines.join("\n"))
        .with_context(|| format!("writing {}/README.md", project.display()))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capture_project::{validate_manifest_value, write_manifest};
    use serde_json::json;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn renders_minimal_salvaged_project_without_optional_artifacts() -> Result<()> {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
        let project =
            std::env::temp_dir().join(format!("project-readme-{}-{nonce}", std::process::id()));
        fs::create_dir_all(&project)?;
        let result = (|| -> Result<()> {
            let raw = json!({
                "schema": "capture-project/v1",
                "source": {
                    "kind": "har",
                    "input": "fixture.har",
                    "salvaged": true,
                    "parse_error": "truncated input"
                },
                "pages": [],
                "resources": [{
                    "id": 42,
                    "kind": "javascript",
                    "url": "https://fixture.invalid/app.js",
                    "output_path": "resources/app.js"
                }],
                "inline_scripts": [],
                "counts": {}
            });
            let manifest = validate_manifest_value(&raw, "test")?;
            write_manifest(&project.join("capture-manifest.json"), &manifest)?;
            refresh_project_readme(&project)?;
            let readme = fs::read_to_string(project.join("README.md"))?;
            assert!(readme.contains("# Recovered source project"));
            assert!(readme.contains("Capture state: **SALVAGED / truncated**"));
            assert!(readme.contains("## Structured bundle modules"));
            assert!(readme.contains("## VM analysis"));
            assert!(readme.contains("## Capture caveat"));
            assert!(readme.contains("truncated input"));
            Ok(())
        })();
        let cleanup = fs::remove_dir_all(&project);
        result?;
        cleanup?;
        Ok(())
    }
}
