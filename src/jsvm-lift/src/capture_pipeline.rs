use crate::{
    bundle_materialize::{materialize_bundle_modules, BundleMaterializeSummary},
    capture_import::{import_capture_project, CaptureImportOptions, CaptureImportSummary},
    capture_project::{read_manifest, MANIFEST_NAME},
    project_api_surface::analyze_project_api_surface,
    project_deob::{materialize_project_deobfuscation, ProjectDeobOptions, ProjectDeobSummary},
    project_js_refs::{scan_project_references, ReferenceScanSummary},
    project_readme::refresh_project_readme,
    project_scan::{scan_project, ProjectScanOptions, ProjectScanSummary},
    project_sourcemaps::{recover_project_sourcemaps, ProjectSourcemapSummary},
    source_graph::{build_source_graph, SourceGraphSummary},
    source_materialize::{materialize_capture_source, SourceMaterializeSummary},
    vm_materialize::{materialize_project as materialize_vm_project, MaterializeSummary},
    wasm_js_boundary::{correlate_project as correlate_wasm_js_boundary, WasmJsBoundarySummary},
    wasm_materialize::{materialize_wasm, WasmMaterializeSummary},
    wasm_resource_provenance::{correlate_wasm_resource_provenance, WasmResourceProvenanceSummary},
};
use anyhow::{ensure, Result};
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct VmPipelineOptions {
    pub repo_root: PathBuf,
    pub switch_ir: PathBuf,
    pub table_ir: PathBuf,
}

#[derive(Debug, Clone)]
pub struct CapturePipelineOptions {
    pub input: PathBuf,
    pub output: PathBuf,
    pub assets_dir: Option<PathBuf>,
    pub overwrite: bool,
    pub jobs: Option<usize>,
    pub safe_deobfuscation: bool,
    pub bundle_materialization: bool,
    pub wasm_analysis: bool,
    pub vm: Option<VmPipelineOptions>,
}

#[derive(Debug)]
pub struct CapturePipelineSummary {
    pub import: CaptureImportSummary,
    pub source: SourceMaterializeSummary,
    pub sourcemaps: ProjectSourcemapSummary,
    pub references: ReferenceScanSummary,
    pub deobfuscation: Option<ProjectDeobSummary>,
    pub bundles: Option<BundleMaterializeSummary>,
    pub wasm: Option<WasmMaterializeSummary>,
    pub wasm_resource_provenance: Option<WasmResourceProvenanceSummary>,
    pub wasm_js_boundary: Option<WasmJsBoundarySummary>,
    pub vm_scan: Option<ProjectScanSummary>,
    pub vm_materialization: Option<MaterializeSummary>,
    pub graph: SourceGraphSummary,
}

/// Recover the durable analysis/project artifacts for one browser capture.
///
/// Pipeline ordering lives here rather than in the CLI so tests and other callers
/// exercise the same supported workflow without spawning sibling Rust binaries.
pub fn recover_capture_project(options: &CapturePipelineOptions) -> Result<CapturePipelineSummary> {
    ensure!(
        !options.bundle_materialization || options.safe_deobfuscation,
        "bundle materialization requires safe deobfuscation"
    );

    let import = import_capture_project(&CaptureImportOptions {
        input: options.input.clone(),
        output: options.output.clone(),
        assets_dir: options.assets_dir.clone(),
        overwrite: options.overwrite,
    })?;
    let project = &options.output;
    let manifest = read_manifest(&project.join(MANIFEST_NAME))?;

    let source = materialize_capture_source(project, options.jobs)?;

    let wasm = options
        .wasm_analysis
        .then(|| materialize_wasm(project, None))
        .transpose()?;
    let wasm_resource_provenance = if options.wasm_analysis && manifest.source.kind == "recorder" {
        Some(correlate_wasm_resource_provenance(project)?)
    } else {
        None
    };

    let sourcemaps = recover_project_sourcemaps(project)?;
    let references = scan_project_references(project, options.jobs)?;

    let deobfuscation = options
        .safe_deobfuscation
        .then(|| {
            materialize_project_deobfuscation(
                project,
                &ProjectDeobOptions {
                    jobs: options.jobs,
                    max_iterations: 16,
                },
            )
        })
        .transpose()?;
    let bundles = options
        .bundle_materialization
        .then(|| materialize_bundle_modules(project, options.jobs))
        .transpose()?;

    let wasm_js_boundary = if options.wasm_analysis && options.safe_deobfuscation {
        Some(correlate_wasm_js_boundary(project)?)
    } else {
        None
    };

    let (vm_scan, vm_materialization) = if let Some(vm) = &options.vm {
        let scan = scan_project(
            project,
            &ProjectScanOptions::with_defaults(
                vm.repo_root.clone(),
                vm.switch_ir.clone(),
                vm.table_ir.clone(),
            ),
        )?;
        let materialized = materialize_vm_project(project)?;
        (Some(scan), Some(materialized))
    } else {
        (None, None)
    };

    analyze_project_api_surface(project)?;
    let graph = build_source_graph(project)?;
    refresh_project_readme(project)?;

    Ok(CapturePipelineSummary {
        import,
        source,
        sourcemaps,
        references,
        deobfuscation,
        bundles,
        wasm,
        wasm_resource_provenance,
        wasm_js_boundary,
        vm_scan,
        vm_materialization,
        graph,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        analysis_artifacts::{load_artifact, BUNDLES, JS_REFERENCES, SOURCEMAPS, SOURCE_GRAPH},
        capture_project::read_manifest,
    };
    use anyhow::Context;
    use base64::{engine::general_purpose::STANDARD, Engine as _};
    use serde_json::{json, Value};
    use std::{fs, path::Path};
    use tempfile::TempDir;

    fn har_entry(url: &str, mime: &str, body: &[u8], binary: bool) -> Value {
        let content = if binary {
            json!({
                "size": body.len(),
                "mimeType": mime,
                "text": STANDARD.encode(body),
                "encoding": "base64",
            })
        } else {
            json!({
                "size": body.len(),
                "mimeType": mime,
                "text": String::from_utf8_lossy(body),
            })
        };
        json!({
            "pageref": "page_1",
            "startedDateTime": "2026-09-29T00:00:00.000Z",
            "time": 1,
            "request": {
                "method": "GET",
                "url": url,
                "httpVersion": "HTTP/2",
                "headers": [],
                "queryString": [],
                "cookies": [],
                "headersSize": -1,
                "bodySize": 0,
            },
            "response": {
                "status": 200,
                "statusText": "OK",
                "httpVersion": "HTTP/2",
                "headers": [{"name": "content-type", "value": mime}],
                "cookies": [],
                "content": content,
                "redirectURL": "",
                "headersSize": -1,
                "bodySize": body.len(),
            },
            "cache": {},
            "timings": {"send": 0, "wait": 1, "receive": 0},
        })
    }

    fn static_options(input: &Path, output: &Path) -> CapturePipelineOptions {
        CapturePipelineOptions {
            input: input.to_path_buf(),
            output: output.to_path_buf(),
            assets_dir: None,
            overwrite: false,
            jobs: Some(2),
            safe_deobfuscation: true,
            bundle_materialization: true,
            wasm_analysis: false,
            vm: None,
        }
    }

    fn artifact(project: &Path, spec: crate::analysis_artifacts::ArtifactSpec) -> Result<Value> {
        load_artifact(project, spec, false)?.context("missing pipeline artifact")
    }

    fn edge_count(graph: &Value, kind: &str) -> u64 {
        graph
            .get("summary")
            .and_then(|summary| summary.get("edge_kinds"))
            .and_then(|kinds| kinds.get(kind))
            .and_then(Value::as_u64)
            .unwrap_or_default()
    }

    fn representative_bundle_assertions(project: &Path) -> Result<()> {
        let bundles = artifact(project, BUNDLES)?;
        let modules = bundles
            .get("modules")
            .and_then(Value::as_array)
            .context("bundle modules missing")?;
        let module = |id: &str| {
            modules
                .iter()
                .find(|row| row.get("module_id").and_then(Value::as_str) == Some(id))
        };
        let module_20001 = module("20001").context("module 20001 missing")?;
        assert_eq!(
            module_20001.get("dependencies"),
            Some(&json!(["20002", "40000"]))
        );
        assert_eq!(
            module_20001.get("export_names"),
            Some(&json!(["name", "named"]))
        );
        let browserify = module("50001").context("Browserify module missing")?;
        assert_eq!(
            browserify.get("bundle_kind").and_then(Value::as_str),
            Some("browserify_module_table")
        );
        let amd = module("amd/alpha").context("AMD module missing")?;
        assert_eq!(amd.get("dependencies"), Some(&json!(["amd/beta"])));
        let member = module("embedded/alpha").context("member-loader module missing")?;
        assert_eq!(
            member.get("bundle_kind").and_then(Value::as_str),
            Some("member_named_modules")
        );
        assert!(modules.iter().all(|row| row
            .get("source_path")
            .and_then(Value::as_str)
            .is_some_and(|path| project.join(path).is_file())));
        Ok(())
    }

    #[test]
    fn har_pipeline_preserves_capture_semantics_across_static_recovery() -> Result<()> {
        let work = TempDir::new()?;
        let har = work.path().join("fixture.har");
        let project = work.path().join("project");
        let truncated_har = work.path().join("fixture-truncated.har");
        let truncated_project = work.path().join("project-truncated");

        let bundle = include_str!(
            "../../../corpus/generated/reversible-obfuscation/bundle-module-tables.js"
        );
        let app = format!(
            "{bundle}\nnew Worker(\"./worker.js\");\n\
             const dynamicName = globalThis.dynamicName; void import(`./chunks/${{dynamicName}}.js`);\n\
             const fakeSourceMap = \"/*# sourceMappingURL=fake-string.js.map */\";\n\
             const fakeRuntimeMap = \"/*# sourceMappingURL=data:application/json;base64,\" + globalThis.payload + \" */\";\n\
             //# sourceMappingURL=app.js.map\n"
        );
        let html = b"<!doctype html><html><head><meta charset=\"windows-1252\"></head><body>\
            <script charset=\"windows-1252\" src=\"/assets/app.js\"></script>\
            <script type=\"80bb470769a376240e5e4e06-text/javascript\">globalThis.inlineHar = \"\xa9\";</script>\
            <script type=\"speculationrules\">{\"prefetch\":[{\"source\":\"list\",\"urls\":[\"/next\"]}]}</script>\
            </body></html>";
        let source_map = json!({
            "version": 3,
            "file": "app.js",
            "sources": ["src/intermediate.js", "src/side.js"],
            "names": [],
            "mappings": "AAAA;ACAA",
            "sourcesContent": [
                "export function intermediateAnswer() { return 42; }\n//# sourceMappingURL=intermediate.js.map\n",
                "export const side = 'preserved';\n"
            ]
        });
        let nested_source_map = json!({
            "version": 3,
            "file": "intermediate.js",
            "sources": ["../original/app-original.ts"],
            "names": [],
            "mappings": "AAAA",
            "sourcesContent": ["export function originalAnswer(): number { return 42; }\n"]
        });
        let fixture = json!({
            "log": {
                "version": "1.2",
                "creator": {"name": "capture pipeline regression", "version": "1"},
                "pages": [{
                    "startedDateTime": "2026-09-29T00:00:00.000Z",
                    "id": "page_1",
                    "title": "capture pipeline fixture",
                    "pageTimings": {}
                }],
                "entries": [
                    har_entry("https://fixture.invalid/index.html", "text/html", html, true),
                    har_entry("https://fixture.invalid/assets/app.js", "application/javascript", app.as_bytes(), false),
                    har_entry("https://fixture.invalid/assets/worker.js", "application/javascript", b"postMessage(\"ready\");\n", false),
                    har_entry("https://fixture.invalid/assets/worker-copy.js", "application/javascript", b"postMessage(\"ready\");\n", false),
                    har_entry("https://fixture.invalid/assets/chunks/en.js", "application/javascript", b"export const language = \"en\";\n", false),
                    har_entry("https://fixture.invalid/assets/chunks/pl.js", "application/javascript", b"export const language = \"pl\";\n", false),
                    har_entry("https://fixture.invalid/assets/chunks/deep/skip.js", "application/javascript", b"export const nested = true;\n", false),
                    har_entry("https://fixture.invalid/assets/app.js.map", "application/json", serde_json::to_string(&source_map)?.as_bytes(), false),
                    har_entry("https://fixture.invalid/assets/src/intermediate.js.map", "application/json", serde_json::to_string(&nested_source_map)?.as_bytes(), false)
                ]
            }
        });
        let raw = serde_json::to_string(&fixture)?;
        fs::write(&har, &raw)?;

        let summary = recover_capture_project(&static_options(&har, &project))?;
        assert_eq!(summary.import.resources, 9);
        assert_eq!(summary.source.javascript_units, 7);
        assert_eq!(summary.source.unique_javascript_inputs, 6);
        assert_eq!(summary.sourcemaps.composed_links, 1);
        assert!(summary.sourcemaps.final_recovered >= 2);
        assert_eq!(summary.references.failures, 0);
        assert_eq!(
            summary.deobfuscation.as_ref().map(|row| row.failed_units),
            Some(0)
        );
        assert!(summary.bundles.as_ref().is_some_and(|row| row.modules >= 2));

        let manifest = read_manifest(&project.join(MANIFEST_NAME))?;
        assert_eq!(manifest.source.kind, "har");
        assert!(!manifest.source.salvaged);
        let page = manifest
            .resources
            .iter()
            .find(|row| {
                row.get("url").and_then(Value::as_str) == Some("https://fixture.invalid/index.html")
            })
            .context("page resource missing")?;
        assert_eq!(
            page.get("document_encoding").and_then(Value::as_str),
            Some("windows-1252")
        );
        let executable_inline = manifest
            .inline_scripts
            .iter()
            .find(|row| {
                row.get("output_path")
                    .and_then(Value::as_str)
                    .is_some_and(|path| path.ends_with(".js"))
            })
            .context("executable inline script missing")?;
        assert_eq!(
            executable_inline.get("script_type").and_then(Value::as_str),
            Some("80bb470769a376240e5e4e06-text/javascript")
        );
        assert_eq!(
            executable_inline
                .get("parent_document_encoding")
                .and_then(Value::as_str),
            Some("windows-1252")
        );
        let inline_path = executable_inline
            .get("output_path")
            .and_then(Value::as_str)
            .context("inline output missing")?;
        assert!(fs::read_to_string(project.join(inline_path))?.contains('©'));

        let references = artifact(&project, JS_REFERENCES)?;
        let code_units = references
            .get("code_units")
            .and_then(Value::as_array)
            .context("JS reference code units missing")?;
        let dynamic = code_units
            .iter()
            .flat_map(|unit| {
                unit.get("references")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
            })
            .find(|row| row.get("kind").and_then(Value::as_str) == Some("import_dynamic_glob"))
            .context("dynamic import glob missing")?;
        assert_eq!(
            dynamic.get("glob").and_then(Value::as_str),
            Some("./chunks/*.js")
        );
        let candidates = dynamic
            .get("resolution_candidates")
            .and_then(Value::as_array)
            .context("dynamic import candidates missing")?;
        assert_eq!(candidates.len(), 2);
        assert!(candidates.iter().all(|row| row
            .get("resolved_url")
            .and_then(Value::as_str)
            .is_some_and(|url| !url.contains("/deep/"))));

        representative_bundle_assertions(&project)?;
        let graph = artifact(&project, SOURCE_GRAPH)?;
        assert_eq!(edge_count(&graph, "source_map_composed"), 1);
        assert_eq!(edge_count(&graph, "js_worker"), 1);
        assert_eq!(edge_count(&graph, "js_import_dynamic_glob"), 2);
        assert!(edge_count(&graph, "safe_deobfuscation") >= 7);
        assert!(edge_count(&graph, "bundle_module") >= 2);
        let readme = fs::read_to_string(project.join("README.md"))?;
        assert!(readme.contains("# Recovered source project"));
        assert!(readme.contains("## Structured bundle modules"));
        assert!(readme.contains("## Provenance graph"));

        let cut_marker = "https://fixture.invalid/assets/app.js.map";
        let cut = raw
            .find(cut_marker)
            .context("HAR cut marker missing")?
            .saturating_add(cut_marker.len() + 32);
        fs::write(&truncated_har, &raw[..cut.min(raw.len())])?;
        let truncated = import_capture_project(&CaptureImportOptions {
            input: truncated_har,
            output: truncated_project.clone(),
            assets_dir: None,
            overwrite: false,
        })?;
        assert_eq!(truncated.resources, 7);
        let truncated_manifest = read_manifest(&truncated_project.join(MANIFEST_NAME))?;
        assert!(truncated_manifest.source.salvaged);
        assert!(truncated_manifest
            .source
            .extra
            .get("parse_error")
            .and_then(Value::as_str)
            .is_some());
        Ok(())
    }

    #[test]
    fn saved_page_pipeline_stays_static_and_preserves_local_provenance() -> Result<()> {
        let work = TempDir::new()?;
        let page = work.path().join("Saved.html");
        let assets = work.path().join("Saved_files");
        let project = work.path().join("project");
        let execution_marker = work.path().join("hostile-js-was-executed.txt");
        fs::create_dir_all(&assets)?;
        fs::write(
            &page,
            b"<!-- saved from url=(0032)https://example.invalid/demo -->\n\
              <!doctype html><html><head><meta charset=\"windows-1252\">\n\
              <link rel=\"stylesheet\" href=\"./Saved_files/site.css\"></head><body>\n\
              <script type=\"text/javascript\" charset=\"windows-1252\" src=\"./Saved_files/app.js\"></script>\n\
              <script type=\"module\">import \"./Saved_files/inline-dep.js\"; console.log(\"\xa9\");</script>\n\
              <script type=\"speculationrules\">{\"prefetch\":[{\"source\":\"list\",\"urls\":[\"/next\"]}]}</script>\n\
              </body></html>\n",
        )?;
        let bundle = include_str!(
            "../../../corpus/generated/reversible-obfuscation/bundle-module-tables.js"
        );
        let app = format!(
            "{bundle}\nnew Worker(\"./worker.js\");\n\
             const fakeSourceMap = \"/*# sourceMappingURL=fake-string.js.map */\";\n\
             const fakeRuntimeMap = \"/*# sourceMappingURL=data:application/json;base64,\" + globalThis.payload + \" */\";\n\
             if (typeof require === \"function\") require(\"node:fs\").writeFileSync({}, \"executed\");\n\
             //# sourceMappingURL=app.js.map\n",
            serde_json::to_string(&execution_marker.to_string_lossy())?
        );
        fs::write(assets.join("app.js"), app)?;
        fs::write(assets.join("worker.js"), "postMessage(\"ready\");\n")?;
        fs::write(assets.join("inline-dep.js"), "export const dep = 42;\n")?;
        fs::write(assets.join("site.css"), "body { color: #123; }\n")?;
        fs::write(
            assets.join("app.js.map"),
            serde_json::to_vec(&json!({
                "version": 3,
                "file": "app.js",
                "sources": ["src/app-original.js"],
                "names": [],
                "mappings": "",
                "sourcesContent": ["export function originalAnswer() { return 42; }\n"]
            }))?,
        )?;

        #[cfg(unix)]
        {
            use std::os::unix::fs::symlink;
            let outside = work.path().join("do-not-ingest.txt");
            fs::write(&outside, "local secret")?;
            symlink(&outside, assets.join("linked-secret.txt"))?;
        }

        let summary = recover_capture_project(&static_options(&page, &project))?;
        assert_eq!(summary.import.resources, 6);
        assert_eq!(summary.source.javascript_units, 4);
        assert_eq!(summary.sourcemaps.direct_recovered, 1);
        assert_eq!(summary.references.failures, 0);
        assert_eq!(
            summary.deobfuscation.as_ref().map(|row| row.failed_units),
            Some(0)
        );
        assert!(summary.bundles.as_ref().is_some_and(|row| row.modules >= 2));

        let manifest = read_manifest(&project.join(MANIFEST_NAME))?;
        assert_eq!(manifest.source.kind, "saved_page_complete");
        assert_eq!(
            manifest
                .source
                .extra
                .get("original_page_url")
                .and_then(Value::as_str),
            Some("https://example.invalid/demo")
        );
        assert_eq!(manifest.resources.len(), 6);
        let page_resource = manifest
            .resources
            .iter()
            .find(|row| {
                row.get("url")
                    .and_then(Value::as_str)
                    .is_some_and(|url| url.ends_with("/Saved.html"))
            })
            .context("saved page resource missing")?;
        assert_eq!(
            page_resource
                .get("document_encoding")
                .and_then(Value::as_str),
            Some("windows-1252")
        );
        let module_inline = manifest
            .inline_scripts
            .iter()
            .find(|row| row.get("script_type").and_then(Value::as_str) == Some("module"))
            .context("module inline script missing")?;
        let module_path = module_inline
            .get("output_path")
            .and_then(Value::as_str)
            .context("module output missing")?;
        assert!(fs::read_to_string(project.join(module_path))?.contains('©'));

        let sourcemaps = artifact(&project, SOURCEMAPS)?;
        assert!(sourcemaps
            .get("source_maps")
            .and_then(Value::as_array)
            .is_some_and(|rows| rows
                .iter()
                .all(|row| row.get("raw_reference").and_then(Value::as_str)
                    != Some("fake-string.js.map"))));
        representative_bundle_assertions(&project)?;
        let graph = artifact(&project, SOURCE_GRAPH)?;
        assert!(edge_count(&graph, "script_src") >= 1);
        assert!(edge_count(&graph, "stylesheet") >= 1);
        assert_eq!(edge_count(&graph, "source_map_source"), 1);
        assert!(edge_count(&graph, "js_worker") >= 1);
        assert!(edge_count(&graph, "js_import_static") >= 1);
        assert!(edge_count(&graph, "bundle_module") >= 2);
        assert!(
            !execution_marker.exists(),
            "static pipeline executed sample JavaScript"
        );
        let readme = fs::read_to_string(project.join("README.md"))?;
        assert!(readme.contains("# Recovered source project"));
        assert!(readme.contains("Original page URL recorded by the saved page"));
        assert!(readme.contains("src/_modules/"));
        Ok(())
    }
}
