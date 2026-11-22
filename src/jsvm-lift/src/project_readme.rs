use crate::{
    analysis_artifacts::{
        load_optional_artifact, API_SURFACE, BUNDLES, DEOBFUSCATION, GENERATED_RECOVERY,
        IMPORT_MAPS, JSVM_INDEX, JS_REFERENCES, RUNTIME_SCRIPTS, SOURCEMAPS, SOURCE_GRAPH,
        SOURCE_INDEX, WASM_RESOURCE_PROVENANCE,
    },
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    capture_project::load_manifest,
    project_entrypoints::render_entrypoint_index,
    report_markdown::{code_span, literal_text},
};
use anyhow::{Context, Result};
use serde_json::{json, Value};
use std::{collections::BTreeMap, path::Path};

fn array<'a>(value: &'a Value, key: &str) -> &'a [Value] {
    value
        .get(key)
        .and_then(Value::as_array)
        .map_or_default(Vec::as_slice)
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

fn load_empty(
    project: &Path,
    spec: crate::analysis_artifacts::ArtifactSpec,
    arrays: &[&str],
    objects: &[&str],
) -> Result<Value> {
    Ok(load_optional_artifact(project, spec)?.unwrap_or_else(|| {
        let mut value = serde_json::Map::new();
        value.insert("schema".into(), Value::String(spec.schema.into()));
        for key in arrays {
            value.insert((*key).into(), json!([]));
        }
        for key in objects {
            value.insert((*key).into(), json!({}));
        }
        Value::Object(value)
    }))
}

fn summary(value: &Value) -> &Value {
    value.get("summary").unwrap_or(&Value::Null)
}

fn compact(value: Option<&Value>) -> String {
    value
        .and_then(|v| serde_json::to_string(v).ok())
        .unwrap_or_else(|| "{}".into())
}

struct ReadmeArtifacts {
    source_index: Value,
    sourcemaps: Value,
    jsrefs: Value,
    import_maps: Value,
    deob: Value,
    jsvm: Value,
    graph: Value,
    api_surface_doc: Option<Value>,
    bundles: Value,
    generated_recovery: Value,
    runtime_scripts: Value,
    wasm_resource_provenance: Option<Value>,
}

impl ReadmeArtifacts {
    fn load(project: &Path) -> Result<Self> {
        let source_index = load_empty(project, SOURCE_INDEX, &["units"], &["summary"])?;
        let sourcemaps = load_empty(project, SOURCEMAPS, &["source_maps"], &[])?;
        let jsrefs = load_empty(project, JS_REFERENCES, &["code_units"], &["summary"])?;
        let import_maps = load_empty(project, IMPORT_MAPS, &["maps"], &["documents", "summary"])?;
        let deob = load_empty(project, DEOBFUSCATION, &["units"], &["summary"])?;
        let jsvm = load_empty(
            project,
            JSVM_INDEX,
            &["code_units", "dynamic_code_units", "devirtualized_units"],
            &[],
        )?;
        let graph = load_empty(
            project,
            SOURCE_GRAPH,
            &["nodes", "edges", "unresolved_edges"],
            &["summary"],
        )?;
        let api_surface_doc = load_optional_artifact(project, API_SURFACE)?;
        let bundles = load_empty(
            project,
            BUNDLES,
            &["bundles", "modules", "failures"],
            &["summary"],
        )?;
        let generated_recovery = load_empty(project, GENERATED_RECOVERY, &["units"], &["summary"])?;
        let runtime_scripts = load_empty(
            project,
            RUNTIME_SCRIPTS,
            &[
                "sources",
                "alpine_families",
                "gtm_families",
                "script_identity_conflicts",
            ],
            &["summary"],
        )?;
        let wasm_resource_provenance = load_optional_artifact(project, WASM_RESOURCE_PROVENANCE)?;
        Ok(Self {
            source_index,
            sourcemaps,
            jsrefs,
            import_maps,
            deob,
            jsvm,
            graph,
            api_surface_doc,
            bundles,
            generated_recovery,
            runtime_scripts,
            wasm_resource_provenance,
        })
    }
}

struct SourceCounts {
    total: usize,
    javascript: usize,
    kinds: BTreeMap<String, usize>,
}

fn collect_source_counts(
    source_index: &Value,
    budget: &work_budget::WorkBudget,
) -> Result<SourceCounts> {
    let source_units = array(source_index, "units");
    let mut source_kinds = BTreeMap::<String, usize>::new();
    for unit in source_units {
        budget.checkpoint()?;
        *source_kinds
            .entry(str_field(unit, "kind").unwrap_or("unknown").to_owned())
            .or_default() += 1;
    }

    Ok(SourceCounts {
        total: source_units.len(),
        javascript: source_kinds.get("javascript").copied().unwrap_or_default(),
        kinds: source_kinds,
    })
}

fn sourcemap_counts(
    sourcemaps: &Value,
    budget: &work_budget::WorkBudget,
) -> Result<(usize, usize)> {
    let mut recovered_originals = 0usize;
    let mut composed_sourcemap_links = 0usize;
    for sm in array(sourcemaps, "source_maps") {
        budget.checkpoint()?;
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

    Ok((recovered_originals, composed_sourcemap_links))
}

fn render_introduction(
    project: &Path,
    source: &Value,
    artifacts: &ReadmeArtifacts,
    declared_scripts: usize,
) -> Vec<String> {
    let runtime_summary = summary(&artifacts.runtime_scripts);
    let capture_state = if bool_field(source, "salvaged") {
        "SALVAGED / truncated"
    } else {
        "complete"
    };
    let source_capture = str_field(source, "input").unwrap_or("browser capture");
    let source_kind = str_field(source, "kind").unwrap_or("unknown");
    let original_url =
        str_field(source, "original_page_url").or_else(|| str_field(source, "requested_url"));
    let final_url = str_field(source, "final_url");
    let mut lines = vec![
        "# Recovered source project".to_owned(),
        String::new(),
        format!(
            "Generated from {}. Input kind: **{}**. Capture state: **{capture_state}**.",
            code_span(source_capture),
            literal_text(source_kind)
        ),
    ];
    if let Some(url) = original_url.map(code_span) {
        if source_kind.starts_with("saved_page_") {
            lines.push(format!(
                "Original page URL recorded by the saved page: {url}."
            ));
        } else if source_kind == "http_static" {
            lines.push(format!("HTTP requested URL: {url}."));
        } else {
            lines.push(format!("Observed browser entrypoint URL: {url}."));
        }
    }
    if let Some(url) = final_url.map(code_span) {
        lines.push(format!(
            "{}: {url}.",
            if source_kind == "http_static" {
                "Final HTTP URL"
            } else {
                "Browser final navigation URL"
            }
        ));
    }
    lines.extend([
        String::new(),
        "This tree keeps capture truth separate from analyst transformations. Start in src/ for readable code, and use analysis/source-graph.json when you need exact provenance back to the browser capture.".into(),
        String::new(),
        "## Start here".into(),
        String::new(),
        format!("- [src/ENTRYPOINTS.md](src/ENTRYPOINTS.md) — navigable HTML-declared entrypoints and their transitive captured JavaScript dependencies (**{declared_scripts}** script declarations). Start here for the actual code loading structure."),
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
    if artifacts.api_surface_doc.is_some() {
        lines.push("- [analysis/api-surface.json](analysis/api-surface.json) — proof-gated static browser API callsites with exact URL/method evidence and per-source failures.".into());
    }
    if runtime_summary
        .as_object()
        .is_some_and(|summary| !summary.is_empty())
    {
        lines.push("- [analysis/runtime-scripts.json](analysis/runtime-scripts.json) — Debugger runtime-script provenance, generated-expression recovery, and capture-instrumentation classification.".into());
    }
    if project.join("analysis/observed-source.json").is_file() {
        lines.push("- [src/_observed/](src/_observed/) — Oxc-formatted runtime sources with positive V8 execution counters; unlisted code is not necessarily unexecuted.".into());
        lines.push("- [analysis/execution-coverage.json](analysis/execution-coverage.json) — per-session execution witnesses, V8 source offsets and observation mode.".into());
        lines.push("- [analysis/observed-source.json](analysis/observed-source.json) — observed source identity, provenance, and formatting status.".into());
    }
    if project
        .join("src/_observed/invocations/README.md")
        .is_file()
    {
        lines.push("- [src/_observed/invocations/README.md](src/_observed/invocations/README.md) — concrete breakpoint call stacks and bounded observed values with links to exact captured and safe-readable code; these are invocation-specific facts.".into());
    }
    if artifacts.wasm_resource_provenance.is_some() {
        lines.push("- [analysis/wasm-resource-provenance.json](analysis/wasm-resource-provenance.json) — runtime-observed exact WASM responses linked to their CDP script initiators.".into());
    }

    lines
}

fn append_http_acquisition(lines: &mut Vec<String>, source: &Value) {
    if str_field(source, "kind") != Some("http_static") {
        return;
    }
    let capture = source.get("http_static").unwrap_or(&Value::Null);
    lines.extend([
        String::new(),
        "## HTTP-only acquisition".into(),
        String::new(),
        format!("- HTTP responses: **{}**; request failures: **{}**; pending due to limits: **{}**; response bytes: **{}**", usize_field(capture, "resources"), usize_field(capture, "failed_resources"), usize_field(capture, "pending_resources"), usize_field(capture, "bytes")),
        "- [Raw HTTP capture](analysis/http-capture.har) and [fetch details](analysis/http-static.json).".into(),
        "- This is HTTP-discovered source, not a browser execution trace. Runtime-generated scripts may require a browser capture.".into(),
    ]);
    for warning in array(capture, "warnings") {
        if let Some(message) = warning.as_str() {
            lines.push(format!("- Acquisition note: {}", literal_text(message)));
        }
    }
}

fn append_capture_summary(
    lines: &mut Vec<String>,
    manifest_value: &Value,
    artifacts: &ReadmeArtifacts,
) {
    let runtime_summary = summary(&artifacts.runtime_scripts);
    let runtime_classes = runtime_summary.get("classifications");
    let wasm_runtime_summary = artifacts
        .wasm_resource_provenance
        .as_ref()
        .and_then(|doc| doc.get("summary"));
    lines.extend([
        String::new(),
        "## Capture summary".into(),
        String::new(),
        format!(
            "- Captured resources: **{}**",
            array(manifest_value, "resources").len()
        ),
        format!(
            "- Inline scripts: **{}**",
            array(manifest_value, "inline_scripts").len()
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
                literal_text(str_field(summary, "unavailable_reason").unwrap_or("unknown"))
            ));
        }
    }
}

fn append_source_summary(
    lines: &mut Vec<String>,
    artifacts: &ReadmeArtifacts,
    counts: &SourceCounts,
    maps: (usize, usize),
) -> Result<()> {
    let source_summary = summary(&artifacts.source_index);
    let jsref_summary = summary(&artifacts.jsrefs);
    let import_summary = summary(&artifacts.import_maps);
    let api_summary = artifacts
        .api_surface_doc
        .as_ref()
        .map_or(&Value::Null, summary);
    let (recovered_originals, composed_sourcemap_links) = maps;
    let unique_js = usize_field(source_summary, "unique_javascript_inputs");
    let unique_js = if source_summary.get("unique_javascript_inputs").is_some() {
        unique_js
    } else {
        counts.javascript
    };
    let extractor_invocations = if jsref_summary.get("extractor_invocations").is_some() {
        usize_field(jsref_summary, "extractor_invocations")
    } else {
        counts.javascript
    };
    lines.extend([
        format!("- Readable source units: **{}** ({} JavaScript)", counts.total, counts.javascript),
        format!("- Exact-content JS reuse: **{unique_js}** unique bodies / **{}** occurrences (**{}** formatter reuses)", counts.javascript, usize_field(source_summary, "deduplicated_javascript_units")),
        format!("- JS-reference extraction: **{extractor_invocations}** parser invocations / **{}** exact-hash reuses", usize_field(jsref_summary, "deduplicated_units")),
        format!("- Source kinds: {}", code_span(&serde_json::to_string(&counts.kinds)?)),
        format!("- JS/module/worker references: **{}**", usize_field(jsref_summary, "references")),
    ]);
    if artifacts.api_surface_doc.is_some() {
        lines.push(format!("- Static browser API callsites: **{}**; callsites with exact absolute network URLs: **{}**; proven invalid methods: **{}**; failed source units: **{}**", usize_field(api_summary, "callsites"), usize_field(api_summary, "absolute_network_urls"), usize_field(api_summary, "invalid_methods"), usize_field(api_summary, "failures")));
        lines.push(format!(
            "- Static browser API sink kinds: {}",
            code_span(&compact(api_summary.get("kinds")))
        ));
    }
    lines.extend([
        format!("- Bounded dynamic-import patterns: **{}**; captured candidate URLs: **{}**; unmatched patterns: **{}**", usize_field(jsref_summary, "dynamic_import_globs"), usize_field(jsref_summary, "dynamic_import_candidate_urls"), usize_field(jsref_summary, "dynamic_import_unmatched")),
        format!("- Import-map blocks captured: **{}**", usize_field(import_summary, "import_map_scripts")),
        format!("- Imports resolved through import maps: **{}**", usize_field(jsref_summary, "resolved_by_import_map")),
        format!("- Unresolved bare module specifiers: **{}**", usize_field(jsref_summary, "unresolved_bare_specifiers")),
        format!("- Source-map originals recovered: **{recovered_originals}**"),
        format!("- Nested source-map links composed: **{composed_sourcemap_links}**"),
    ]);
    Ok(())
}

fn append_generated_summary(lines: &mut Vec<String>, artifacts: &ReadmeArtifacts) {
    let generated_summary = summary(&artifacts.generated_recovery);
    let dynamic = array(&artifacts.jsvm, "dynamic_code_units");
    let recursive_generated = array(&artifacts.jsvm, "code_units")
        .iter()
        .filter(|unit| str_field(unit, "origin") == Some("generated_dynamic_code"))
        .count();
    lines.extend([
        format!("- Literal generated-code units recovered: **{}**", dynamic.len()),
        format!("- Generated-code units recursively scanned: **{recursive_generated}**"),
        format!("- Generated-code safe recovery: **{}** safe deob, **{}** string-only, **{}** exact fallback", usize_field(generated_summary, "safe_deobfuscation"), usize_field(generated_summary, "string_recovery_only"), usize_field(generated_summary, "exact_fallback")),
        format!("- Generated-child exact-content reuse: **{}** unique bodies / **{}** occurrences (**{}** recovery reuses)", if generated_summary.get("unique_raw_inputs").is_some() { usize_field(generated_summary, "unique_raw_inputs") } else { usize_field(generated_summary, "generated_units") }, usize_field(generated_summary, "generated_units"), usize_field(generated_summary, "deduplicated_units")),
        format!("- Generated children with full safe deobfuscation: **{}**", usize_field(generated_summary, "safe_deobfuscation")),
        format!("- Generated children with string-recovery only: **{}**", usize_field(generated_summary, "string_recovery_only")),
        format!("- Generated children scanned from exact fallback bytes: **{}**", usize_field(generated_summary, "exact_fallback")),
    ]);
}

fn append_deobfuscation(lines: &mut Vec<String>, deob: &Value, javascript_units: usize) {
    let deob_summary = deob.get("summary").unwrap_or(&Value::Null);
    let changed_deob = deob_summary
        .get("changed_units")
        .and_then(Value::as_u64)
        .and_then(|v| usize::try_from(v).ok())
        .unwrap_or_else(|| {
            array(deob, "units")
                .iter()
                .filter(|unit| bool_field(unit, "changed"))
                .count()
        });
    let deob_failures = deob_summary
        .get("failures")
        .and_then(Value::as_u64)
        .and_then(|v| usize::try_from(v).ok())
        .unwrap_or_else(|| {
            array(deob, "units")
                .iter()
                .filter(|unit| nonzero_integer_field(unit, "exit"))
                .count()
        });
    let arithmetic_state_proofs = array(deob, "units")
        .iter()
        .map(|unit| array(unit, "arithmetic_state_proofs").len())
        .sum::<usize>();

    lines.extend([
        String::new(),
        "## Safe static deobfuscation".into(),
        String::new(),
        format!("- Changed JavaScript units: **{changed_deob}**"),
        format!("- Failed units: **{deob_failures}**"),
        format!("- Content-addressed work: **{}** unique raw inputs, **{}** safe-deob invocations, **{}** readable-format invocations for **{}** JS occurrences", if deob_summary.get("unique_raw_inputs").is_some() { usize_field(deob_summary, "unique_raw_inputs") } else { javascript_units }, if deob_summary.get("safe_deob_invocations").is_some() { usize_field(deob_summary, "safe_deob_invocations") } else { javascript_units }, if deob_summary.get("readable_format_invocations").is_some() { usize_field(deob_summary, "readable_format_invocations") } else { javascript_units }, if deob_summary.get("javascript_units").is_some() { usize_field(deob_summary, "javascript_units") } else { javascript_units }),
        format!("- Encoded string-decoder recovery: **{}** call sites across **{}** unit(s)", usize_field(deob_summary, "string_recovery_replacements"), usize_field(deob_summary, "string_recovery_changed_units")),
        format!("- Proven arithmetic-state unflattenings: **{arithmetic_state_proofs}**"),
        "- Encoded string-table proof/provenance: [analysis/string-recovery.json](analysis/string-recovery.json)".into(),
        "- Detailed captured-unit final-view hashes, pass counts and provenance: [analysis/deobfuscation.json](analysis/deobfuscation.json)".into(),
        "- Recursive generated-code recovery/fallback provenance: [analysis/generated-recovery.json](analysis/generated-recovery.json)".into(),
    ]);
}

fn append_bundle_summary(lines: &mut Vec<String>, bundles: &Value) {
    let bundle_summary = summary(bundles);
    lines.extend([
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
    ]);
}

fn append_vm_analysis(lines: &mut Vec<String>, jsvm: &Value) {
    let vm_units = array(jsvm, "code_units");
    let confirmed = vm_units
        .iter()
        .filter(|unit| bool_field(unit, "confirmed_vm_signal"))
        .collect::<Vec<_>>();
    let candidates = vm_units
        .iter()
        .filter(|unit| bool_field(unit, "vm_signal") && !bool_field(unit, "confirmed_vm_signal"))
        .collect::<Vec<_>>();
    let devirtualized = array(jsvm, "devirtualized_units");
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

    lines.extend([
        String::new(),
        "## VM analysis".into(),
        String::new(),
        format!("- Scanner work: **{}** scanner invocations / **{}** exact-hash reuses", if jsvm.get("scanner_invocations").is_some() { usize_field(jsvm, "scanner_invocations") } else { vm_units.len() }, usize_field(jsvm, "deduplicated_scans")),
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
                .map_or_else(
                    || format!("scan {}", usize_field(unit, "scan_id")),
                    ToOwned::to_owned,
                );
            lines.push(format!(
                "- {} — {} devirtualized interpreter module(s)",
                code_span(&label),
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
                .map_or_else(
                    || format!("scan {}", usize_field(unit, "scan_id")),
                    ToOwned::to_owned,
                );
            let handlers = if unit.get("largest_non_bundle_handler_table").is_some() {
                usize_field(unit, "largest_non_bundle_handler_table")
            } else {
                usize_field(unit, "largest_handler_table")
            };
            lines.push(format!(
                "- {} — largest static function table {handlers} handlers",
                code_span(&label)
            ));
        }
    }
}

fn append_provenance(lines: &mut Vec<String>, graph: &Value, source: &Value) {
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
                "- Unresolved link claims (missing graph endpoints): **{}**",
                usize_field(summary, "unresolved_edges")
            ),
            format!(
                "- External uncaptured URLs: **{}**",
                usize_field(summary, "external_urls")
            ),
            format!(
                "- Edge kinds: {}",
                code_span(&compact(summary.get("edge_kinds")))
            ),
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
            lines.push(format!("- HAR parse error: {}", literal_text(parse_error)));
        }
    }

    lines.extend([
        String::new(),
        "## Provenance rule".into(),
        String::new(),
        "resources/ is capture truth. Everything under src/, including _deobfuscated/, _readable/, _dynamic_deobfuscated/, _dynamic/, _devirtualized/, _modules/, and _sourcemap/, is a derived analyst view and should be traced through the files in analysis/ before treating it as original captured source.".into(),
        String::new(),
    ]);
}

/// Regenerate the project README from its durable analysis artifacts.
///
/// # Errors
///
/// Fails if the project cannot be resolved, manifest/artifact data cannot be read or
/// serialized, the README cannot be written, or the analysis budget is exhausted.
pub fn refresh_project_readme(project: &Path, budgets: &AnalysisBudgets) -> Result<()> {
    let budget = budgets.operation(
        AnalysisOperation::ProjectReadme,
        project.display().to_string(),
    );
    budget.checkpoint()?;
    let project = project
        .canonicalize()
        .with_context(|| format!("resolving project {}", project.display()))?;
    let manifest = load_manifest(&project)?;
    let manifest_value = serde_json::to_value(&manifest)?;
    budget.checkpoint()?;

    let artifacts = ReadmeArtifacts::load(&project)?;
    budget.checkpoint()?;
    let counts = collect_source_counts(&artifacts.source_index, &budget)?;
    let maps = sourcemap_counts(&artifacts.sourcemaps, &budget)?;
    let entrypoints = render_entrypoint_index(
        &manifest_value,
        &artifacts.source_index,
        &artifacts.deob,
        &artifacts.jsrefs,
        &budget,
    )?;
    let source = manifest_value
        .get("source")
        .context("capture manifest source missing")?;
    let mut lines = render_introduction(&project, source, &artifacts, entrypoints.declared_scripts);
    append_http_acquisition(&mut lines, source);
    append_capture_summary(&mut lines, &manifest_value, &artifacts);
    append_source_summary(&mut lines, &artifacts, &counts, maps)?;
    append_generated_summary(&mut lines, &artifacts);
    append_deobfuscation(&mut lines, &artifacts.deob, counts.javascript);
    append_bundle_summary(&mut lines, &artifacts.bundles);
    append_vm_analysis(&mut lines, &artifacts.jsvm);
    append_provenance(&mut lines, &artifacts.graph, source);

    // Both documents describe this generation. Render and stage both before
    // either is published, including failures at the second destination.
    let index =
        crate::report_file::stage_text(&project.join("src/ENTRYPOINTS.md"), &entrypoints.markdown)?;
    let readme = crate::report_file::stage_text(&project.join("README.md"), &lines.join("\n"))?;
    budget.checkpoint()?;
    index.publish()?;
    readme.publish()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capture_project::{validate_manifest_value, write_manifest};
    use serde_json::json;
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };

    #[test]
    fn http_project_readme_uses_original_url_and_exposes_entrypoints() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let project = temp.path();
        let document = json!({
            "schema": "capture-project/v1",
            "source": {
                "kind": "http_static",
                "input": "https://fixture.invalid/app/index.html",
                "requested_url": "https://fixture.invalid/app/index.html",
                "final_url": "https://fixture.invalid/app/index.html",
                "http_static": {"resources": 2, "failed_resources": 0, "pending_resources": 0, "bytes": 128, "warnings": []},
                "captured_har": "analysis/http-capture.har",
                "salvaged": false
            },
            "pages": [],
            "resources": [
                {"id": 0, "kind": "html", "url": "https://fixture.invalid/app/index.html", "output_path": "resources/index.html"},
                {"id": 1, "kind": "javascript", "url": "https://fixture.invalid/app/main.js", "output_path": "resources/main.js"}
            ],
            "inline_scripts": [{"parent_resource_id": 0, "ordinal": 1, "src": "main.js", "resolved_src": "https://fixture.invalid/app/main.js", "script_type": "module"}],
            "counts": {}
        });
        let manifest = validate_manifest_value(&document, "HTTP README test")?;
        write_manifest(&project.join("capture-manifest.json"), &manifest)?;
        refresh_project_readme(project, &AnalysisBudgets::standard("HTTP README test"))?;
        let readme = fs::read_to_string(project.join("README.md"))?;
        assert!(readme.contains("Input kind: **http\\_static**"));
        assert!(readme.contains("HTTP requested URL: `https://fixture.invalid/app/index.html`."));
        assert!(readme.contains("Final HTTP URL: `https://fixture.invalid/app/index.html`."));
        assert!(readme.contains("## HTTP-only acquisition"));
        assert!(readme.contains("HTTP responses: **2**"));
        assert!(readme.contains("[src/ENTRYPOINTS.md](src/ENTRYPOINTS.md)"));
        assert!(!readme.contains("Observed browser entrypoint URL"));
        let entrypoints = fs::read_to_string(project.join("src/ENTRYPOINTS.md"))?;
        assert!(entrypoints.contains("https://fixture.invalid/app/main.js"));
        assert!(entrypoints.contains("Source body not present in this capture"));

        // The new entrypoint report is valid and different, but the second
        // destination cannot be published. Do not expose the first report.
        let mut changed = manifest;
        changed.inline_scripts[0]["resolved_src"] = json!("https://fixture.invalid/changed.js");
        write_manifest(&project.join("capture-manifest.json"), &changed)?;
        fs::remove_file(project.join("README.md"))?;
        fs::create_dir(project.join("README.md"))?;
        assert!(
            refresh_project_readme(project, &AnalysisBudgets::standard("unwritable readme"))
                .is_err()
        );
        assert_eq!(
            fs::read_to_string(project.join("src/ENTRYPOINTS.md"))?,
            entrypoints
        );
        assert_eq!(fs::read_dir(project.join("src"))?.count(), 1);
        Ok(())
    }

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
            refresh_project_readme(&project, &AnalysisBudgets::standard("project-readme-test"))?;
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
