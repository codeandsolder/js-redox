use anyhow::{Context, Result};
use jsvm_lift::{
    analysis_budget::AnalysisBudgets,
    capture_import::{import_capture_project, CaptureImportOptions},
    capture_project::{validate_manifest_value, write_manifest},
    document_entrypoints::captured_document_entrypoints,
    project_js_refs::scan_project_references,
    project_readme::refresh_project_readme,
    sha256_hex,
    source_graph::build_source_graph,
    source_materialize::materialize_capture_source,
    static_module_graph::link_static_modules,
};
use serde_json::{json, Value};
use std::{fs, path::Path};
use work_budget::WorkBudget;

#[derive(Debug)]
struct ExpectedResolution {
    pkg: String,
    lib: String,
    extra: String,
    scoped: String,
    scope: String,
    child_specifier: &'static str,
}

fn har_entry(url: &str, mime: &str, text: &str) -> Value {
    let size = text.len();
    json!({
        "pageref": "page_1",
        "startedDateTime": "2026-10-04T00:00:00.000Z",
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
            "content": {"size": size, "mimeType": mime, "text": text},
            "redirectURL": "",
            "headersSize": -1,
            "bodySize": size,
        },
        "cache": {},
        "timings": {"send": 0, "wait": 1, "receive": 0},
    })
}

fn read_json(path: &Path) -> Result<Value> {
    serde_json::from_slice(&fs::read(path).with_context(|| format!("reading {}", path.display()))?)
        .with_context(|| format!("parsing {}", path.display()))
}

fn code_unit<'a>(rows: &'a [Value], url: &str) -> Result<&'a Value> {
    rows.iter()
        .find(|row| row.get("url").and_then(Value::as_str) == Some(url))
        .with_context(|| format!("missing code unit for {url}"))
}

fn reference<'a>(row: &'a Value, specifier: &str) -> Result<&'a Value> {
    row.get("references")
        .and_then(Value::as_array)
        .context("code-unit references missing")?
        .iter()
        .find(|reference| reference.get("specifier").and_then(Value::as_str) == Some(specifier))
        .with_context(|| format!("missing reference {specifier:?}"))
}

fn run_pipeline(input: &Path, project: &Path) -> Result<()> {
    import_capture_project(
        &CaptureImportOptions {
            input: input.to_owned(),
            output: project.to_owned(),
            assets_dir: None,
            overwrite: false,
        },
        &AnalysisBudgets::standard("import-map-capture-import-test"),
    )?;
    materialize_capture_source(
        project,
        Some(2),
        &AnalysisBudgets::standard("import-map-project-test"),
    )?;
    scan_project_references(
        project,
        Some(2),
        &AnalysisBudgets::standard("import-map-reference-test"),
    )?;
    build_source_graph(project, &AnalysisBudgets::standard("import-map-graph-test"))?;
    refresh_project_readme(
        project,
        &AnalysisBudgets::standard("import-map-readme-test"),
    )?;
    Ok(())
}

fn assert_project(
    project: &Path,
    root_url: &str,
    child_url: &str,
    worker_url: &str,
    expected: &ExpectedResolution,
) -> Result<()> {
    let manifest = read_json(&project.join("capture-manifest.json"))?;
    let import_map_paths = manifest
        .get("inline_scripts")
        .and_then(Value::as_array)
        .context("manifest inline_scripts missing")?
        .iter()
        .filter(|script| {
            script
                .get("script_type")
                .and_then(Value::as_str)
                .is_some_and(|script_type| script_type.eq_ignore_ascii_case("importmap"))
        })
        .filter_map(|script| script.get("output_path").and_then(Value::as_str))
        .collect::<Vec<_>>();
    assert_eq!(import_map_paths.len(), 2);

    let source_index = read_json(&project.join("analysis/source-index.json"))?;
    let source_units = source_index
        .get("units")
        .and_then(Value::as_array)
        .context("source-index units missing")?;
    for path in &import_map_paths {
        let unit = source_units
            .iter()
            .find(|unit| unit.get("raw_path").and_then(Value::as_str) == Some(*path))
            .with_context(|| format!("missing source-index unit for import map {path}"))?;
        assert_eq!(unit.get("kind").and_then(Value::as_str), Some("json"));
        assert_eq!(
            unit.get("origin").and_then(Value::as_str),
            Some("inline_script")
        );
    }

    let maps = read_json(&project.join("analysis/import-maps.json"))?;
    assert_eq!(maps["summary"]["import_map_scripts"], 2);
    assert_eq!(maps["summary"]["documents_with_import_maps"], 1);
    assert_eq!(maps["summary"]["parse_failures"], 0);
    assert_eq!(maps["summary"]["imports"], 3);
    assert_eq!(maps["summary"]["scopes"], 1);

    let refs = read_json(&project.join("analysis/js-references.json"))?;
    let rows = refs
        .get("code_units")
        .and_then(Value::as_array)
        .context("js-references code_units missing")?;
    assert!(import_map_paths.iter().all(|path| {
        rows.iter()
            .all(|row| row.get("raw_path").and_then(Value::as_str) != Some(*path))
    }));

    let root = code_unit(rows, root_url)?;
    let child = code_unit(rows, child_url)?;
    let worker = code_unit(rows, worker_url)?;

    let pkg = reference(root, "pkg")?;
    assert_eq!(pkg["resolved_url"], expected.pkg);
    assert_eq!(pkg["resolution"], "import_map");

    let lib = reference(root, "lib/util.js")?;
    assert_eq!(lib["resolved_url"], expected.lib);
    assert_eq!(lib["resolution"], "import_map");

    let extra = reference(root, "extra")?;
    assert_eq!(extra["resolved_url"], expected.extra);
    assert_eq!(extra["resolution"], "import_map");

    let child_link = reference(root, expected.child_specifier)?;
    assert_eq!(child_link["resolved_url"], child_url);
    assert_eq!(child_link["resolution"], "url");

    let child_pkg = reference(child, "pkg")?;
    assert_eq!(child_pkg["resolved_url"], expected.scoped);
    assert_eq!(child_pkg["resolution"], "import_map_scope");
    assert_eq!(child_pkg["scope"], expected.scope);

    let worker_pkg = reference(worker, "pkg")?;
    assert!(worker_pkg["resolved_url"].is_null());
    assert_eq!(worker_pkg["resolution"], "unresolved_bare");
    assert_eq!(worker["document_resource_ids"], json!([]));

    assert_eq!(refs["summary"]["resolved_by_import_map"], 4);
    assert_eq!(refs["summary"]["unresolved_bare_specifiers"], 1);
    assert_eq!(refs["summary"]["ambiguous_document_contexts"], 0);

    let graph = read_json(&project.join("analysis/source-graph.json"))?;
    assert_eq!(graph["summary"]["edge_kinds"]["import_map_entry"], 5);
    assert_eq!(graph["summary"]["edge_kinds"]["js_import_static"], 6);
    let mapped_imports = graph
        .get("edges")
        .and_then(Value::as_array)
        .context("source-graph edges missing")?
        .iter()
        .filter(|edge| {
            edge.get("kind").and_then(Value::as_str) == Some("js_import_static")
                && edge
                    .get("resolution")
                    .and_then(Value::as_str)
                    .is_some_and(|resolution| resolution.starts_with("import_map"))
        })
        .collect::<Vec<_>>();
    assert_eq!(mapped_imports.len(), 4);
    assert!(mapped_imports.iter().all(|edge| edge
        .get("document_resource_id")
        .is_some_and(|value| !value.is_null())));
    Ok(())
}

fn check_har(root: &Path) -> Result<()> {
    let work = root.join("har");
    let project = work.join("project");
    fs::create_dir_all(&work)?;

    let map1 = serde_json::to_string(&json!({
        "imports": {
            "pkg": "/modules/pkg-v1.js",
            "lib/": "/modules/lib/",
        },
        "scopes": {
            "/modules/scoped/": {
                "pkg": "/modules/pkg-scoped.js",
            }
        },
    }))?;
    let map2 = serde_json::to_string(&json!({
        "imports": {
            "pkg": "/modules/pkg-v2-ignored.js",
            "extra": "/modules/extra.js",
        },
    }))?;
    let html = format!(
        "<!doctype html><script type=\"importmap\">{map1}</script><script type=\"importmap\">{map2}</script><script type=\"module\" src=\"/modules/root.js\"></script>"
    );
    let root_source = concat!(
        "import \"pkg\";\n",
        "import \"lib/util.js\";\n",
        "import \"extra\";\n",
        "import \"./scoped/child.js\";\n",
        "new Worker(\"/worker.js\", {type: \"module\"});\n",
    );
    let child = "import \"pkg\"; export const child = true;\n";
    let worker = "import \"pkg\"; postMessage(\"ready\");\n";
    let entries = vec![
        har_entry("https://fixture.invalid/index.html", "text/html", &html),
        har_entry(
            "https://fixture.invalid/modules/root.js",
            "application/javascript",
            root_source,
        ),
        har_entry(
            "https://fixture.invalid/modules/scoped/child.js",
            "application/javascript",
            child,
        ),
        har_entry(
            "https://fixture.invalid/worker.js",
            "application/javascript",
            worker,
        ),
        har_entry(
            "https://fixture.invalid/modules/pkg-v1.js",
            "application/javascript",
            "export default 1;",
        ),
        har_entry(
            "https://fixture.invalid/modules/pkg-scoped.js",
            "application/javascript",
            "export default 2;",
        ),
        har_entry(
            "https://fixture.invalid/modules/lib/util.js",
            "application/javascript",
            "export const util = 1;",
        ),
        har_entry(
            "https://fixture.invalid/modules/extra.js",
            "application/javascript",
            "export const extra = 1;",
        ),
    ];
    let har = json!({
        "log": {
            "version": "1.2",
            "creator": {"name": "import map regression", "version": "1"},
            "pages": [{
                "startedDateTime": "2026-10-04T00:00:00.000Z",
                "id": "page_1",
                "title": "import map regression",
                "pageTimings": {},
            }],
            "entries": entries,
        }
    });
    let input = work.join("fixture.har");
    fs::write(&input, serde_json::to_vec(&har)?)?;
    run_pipeline(&input, &project)?;
    assert_project(
        &project,
        "https://fixture.invalid/modules/root.js",
        "https://fixture.invalid/modules/scoped/child.js",
        "https://fixture.invalid/worker.js",
        &ExpectedResolution {
            pkg: "https://fixture.invalid/modules/pkg-v1.js".into(),
            lib: "https://fixture.invalid/modules/lib/util.js".into(),
            extra: "https://fixture.invalid/modules/extra.js".into(),
            scoped: "https://fixture.invalid/modules/pkg-scoped.js".into(),
            scope: "https://fixture.invalid/modules/scoped/".into(),
            child_specifier: "./scoped/child.js",
        },
    )
}

fn check_saved_page(root: &Path) -> Result<()> {
    let work = root.join("saved");
    let project = work.join("project");
    let assets = work.join("Saved_files");
    fs::create_dir_all(assets.join("scoped"))?;
    fs::create_dir_all(assets.join("lib"))?;

    let map1 = serde_json::to_string(&json!({
        "imports": {
            "pkg": "./Saved_files/pkg-v1.js",
            "lib/": "./Saved_files/lib/",
        },
        "scopes": {
            "./Saved_files/scoped/": {
                "pkg": "./Saved_files/pkg-scoped.js",
            }
        },
    }))?;
    let map2 = serde_json::to_string(&json!({
        "imports": {
            "pkg": "./Saved_files/pkg-v2-ignored.js",
            "extra": "./Saved_files/extra.js",
        },
    }))?;
    let page = work.join("Saved.html");
    fs::write(
        &page,
        format!(
            "<!doctype html><script type=\"importmap\">{map1}</script><script type=\"importmap\">{map2}</script><script type=\"module\" src=\"./Saved_files/root.js\"></script>"
        ),
    )?;
    fs::write(
        assets.join("root.js"),
        concat!(
            "import \"pkg\";\n",
            "import \"lib/util.js\";\n",
            "import \"extra\";\n",
            "import \"./scoped/child.js\";\n",
            "new Worker(\"./worker.js\", {type: \"module\"});\n",
        ),
    )?;
    fs::write(
        assets.join("scoped/child.js"),
        "import \"pkg\"; export const child = true;\n",
    )?;
    fs::write(
        assets.join("worker.js"),
        "import \"pkg\"; postMessage(\"ready\");\n",
    )?;
    fs::write(assets.join("pkg-v1.js"), "export default 1;\n")?;
    fs::write(assets.join("pkg-scoped.js"), "export default 2;\n")?;
    fs::write(assets.join("lib/util.js"), "export const util = 1;\n")?;
    fs::write(assets.join("extra.js"), "export const extra = 1;\n")?;

    run_pipeline(&page, &project)?;
    let base = "https://saved-page.invalid/saved-page/Saved_files/";
    assert_project(
        &project,
        &format!("{base}root.js"),
        &format!("{base}scoped/child.js"),
        &format!("{base}worker.js"),
        &ExpectedResolution {
            pkg: format!("{base}pkg-v1.js"),
            lib: format!("{base}lib/util.js"),
            extra: format!("{base}extra.js"),
            scoped: format!("{base}pkg-scoped.js"),
            scope: format!("{base}scoped/"),
            child_specifier: "./scoped/child.js",
        },
    )
}

fn verify_saved_page_mixed_roles(project: &Path) -> Result<()> {
    let manifest = read_json(&project.join("capture-manifest.json"))?;
    let resources = manifest["resources"]
        .as_array()
        .context("manifest resources missing")?;
    assert_eq!(resources.len(), 2, "one page and one physical asset");
    let asset = resources
        .iter()
        .find(|row| {
            row["url"]
                .as_str()
                .is_some_and(|url| url.ends_with("/Page_files/dual.bin"))
        })
        .context("dual-role saved asset missing")?;
    let id = asset["id"].as_u64().context("missing saved asset ID")?;
    let url = asset["url"].as_str().context("missing dual-role URL")?;
    assert_eq!(
        asset["kind"], "javascript",
        "script analysis must be preserved"
    );
    assert_eq!(asset["mime_type"], "application/javascript");
    assert_eq!(
        asset["saved_page_reference_roles"],
        json!(["css", "javascript"])
    );
    assert_eq!(manifest["counts"]["javascript"], 1);
    assert_eq!(manifest["counts"]["html"], 1);
    assert_eq!(manifest["counts"]["binary"], Value::Null);

    let page_record = resources
        .iter()
        .find(|row| row["kind"] == "html")
        .context("saved page HTML resource missing")?;
    let page_id = page_record["id"]
        .as_u64()
        .context("missing page resource ID")?;
    let refs = page_record["references"]
        .as_array()
        .context("HTML references missing")?;
    for role in ["script_src", "stylesheet"] {
        assert_eq!(
            refs.iter()
                .filter(|entry| entry["kind"] == role && entry["resolved_url"] == url)
                .count(),
            1,
            "HTML must independently retain the {role} reference"
        );
    }
    let asset_refs = asset["references"]
        .as_array()
        .context("asset references missing")?;
    assert_eq!(
        asset_refs
            .iter()
            .filter(|entry| entry["kind"] == "source_map")
            .count(),
        1,
        "JS and CSS scanners must not duplicate source-map references"
    );

    let index = read_json(&project.join("analysis/source-index.json"))?;
    let units = index["units"]
        .as_array()
        .context("source index units missing")?;
    assert_eq!(
        units
            .iter()
            .filter(|row| row["url"] == url && row["kind"] == "javascript")
            .count(),
        1
    );
    let graph = read_json(&project.join("analysis/source-graph.json"))?;
    let node = graph["nodes"]
        .as_array()
        .context("source graph nodes missing")?
        .iter()
        .find(|row| row["id"] == format!("resource:{id}"))
        .context("dual-role resource node missing")?;
    assert_eq!(
        node["saved_page_reference_roles"],
        json!(["css", "javascript"])
    );
    let edges = graph["edges"]
        .as_array()
        .context("source graph edges missing")?;
    for role in ["script_src", "stylesheet"] {
        assert_eq!(
            edges
                .iter()
                .filter(|edge| {
                    edge["from"] == format!("resource:{page_id}")
                        && edge["to"] == format!("resource:{id}")
                        && edge["kind"] == role
                })
                .count(),
            1,
            "graph must keep one explicit {role} edge to the same resource"
        );
    }
    Ok(())
}

#[test]
fn saved_page_mixed_script_and_stylesheet_roles_preserve_both_provenances() -> Result<()> {
    let workspace = tempfile::tempdir()?;
    for script_first in [true, false] {
        let root = workspace.path().join(if script_first {
            "script-first"
        } else {
            "style-first"
        });
        let assets = root.join("Page_files");
        fs::create_dir_all(&assets)?;
        let page = root.join("Page.html");
        let script = r#"<script src="./Page_files/dual.bin"></script>"#;
        let stylesheet = r#"<link rel="stylesheet" href="./Page_files/dual.bin">"#;
        let html = if script_first {
            format!("{script}\n{stylesheet}")
        } else {
            format!("{stylesheet}\n{script}")
        };
        fs::write(&page, html)?;
        fs::write(
            assets.join("dual.bin"),
            "export const value = 7;\n//# sourceMappingURL=dual.map\n",
        )?;
        let project = root.join("capture");
        run_pipeline(&page, &project)?;

        verify_saved_page_mixed_roles(&project)?;
    }
    Ok(())
}

#[test]
fn import_maps_preserve_document_context_and_isolate_workers() -> Result<()> {
    let workspace = tempfile::tempdir()?;
    check_har(workspace.path())?;
    check_saved_page(workspace.path())?;
    Ok(())
}

#[test]
fn html_base_is_shared_by_har_scripts_import_maps_and_module_graph() -> Result<()> {
    let root = tempfile::tempdir()?;
    let input = root.path().join("base.har");
    let project = root.path().join("project");
    let page_url = "https://fixture.invalid/site/page.html";
    let base_url = "https://fixture.invalid/assets/";
    let entry_url = "https://fixture.invalid/assets/entry.js";
    let mapped_url = "https://fixture.invalid/assets/vendor/logic.js";
    let dynamic_url = "https://fixture.invalid/assets/dynamic.js";
    let page = r#"<!doctype html><base href="../assets/">
      <link rel="modulepreload" href="vendor/logic.js">
      <link rel="preload stylesheet" as="script" href="dynamic.js">
      <script type="importmap">{"imports":{"pkg/":"./vendor/"}}</script>
      <script type="module">import {answer} from 'pkg/logic.js'; import('./dynamic.js'); console.log(answer);</script>
      <script src="entry.js" type="module"></script>"#;
    let entries = vec![
        har_entry(page_url, "text/html; charset=utf-8", page),
        har_entry(
            entry_url,
            "application/javascript",
            "import {answer} from 'pkg/logic.js'; console.log(answer);",
        ),
        har_entry(
            mapped_url,
            "application/javascript",
            "export const answer=42;",
        ),
        har_entry(
            dynamic_url,
            "application/javascript",
            "export const dynamic=true;",
        ),
    ];
    fs::write(
        &input,
        serde_json::to_vec(&json!({
            "log": {
                "version": "1.2",
                "creator": {"name":"HTML base resolution regression", "version":"1"},
                "pages": [{"id":"page_1", "title":"HTML base regression", "startedDateTime":"2026-10-04T00:00:00Z"}],
                "entries": entries,
            }
        }))?,
    )?;
    run_pipeline(&input, &project)?;
    let manifest = read_json(&project.join("capture-manifest.json"))?;
    let document = &manifest["resources"][0];
    assert_eq!(document["document_base_url"], base_url);
    let preload_references = document["references"]
        .as_array()
        .context("document references missing")?;
    assert!(preload_references.iter().any(|reference| {
        reference["kind"] == "modulepreload" && reference["resolved_url"] == mapped_url
    }));
    assert!(preload_references.iter().any(|reference| {
        reference["kind"] == "script_preload" && reference["resolved_url"] == dynamic_url
    }));
    let scripts = manifest["inline_scripts"]
        .as_array()
        .context("missing inline scripts")?;
    let external = scripts
        .iter()
        .find(|script| script["src"] == "entry.js")
        .context("external script declaration missing")?;
    assert_eq!(external["resolved_src"], entry_url);

    let maps = read_json(&project.join("analysis/import-maps.json"))?;
    assert_eq!(
        maps["documents"]["0"]["imports"]["pkg/"],
        "https://fixture.invalid/assets/vendor/"
    );
    let refs = read_json(&project.join("analysis/js-references.json"))?;
    let units = refs["code_units"]
        .as_array()
        .context("missing JS reference units")?;
    let external = code_unit(units, entry_url)?;
    assert_eq!(
        reference(external, "pkg/logic.js")?["resolved_url"],
        mapped_url
    );
    assert_eq!(external["document_resource_ids"], json!([0]));
    let inline = units
        .iter()
        .find(|unit| unit["url"] == page_url && unit["origin"] == "inline_script")
        .context("missing inline module reference unit")?;
    assert_eq!(
        reference(inline, "pkg/logic.js")?["resolved_url"],
        mapped_url
    );
    assert_eq!(
        reference(inline, "./dynamic.js")?["resolved_url"],
        dynamic_url
    );
    assert_eq!(inline["document_resource_ids"], json!([0]));

    let index = read_json(&project.join("analysis/source-index.json"))?;
    let source_units = index["units"].as_array().context("missing source units")?;
    let output = source_units
        .iter()
        .find(|unit| unit["url"] == entry_url)
        .context("missing entrypoint source")?;
    let source_path = output["source_path"]
        .as_str()
        .context("missing entrypoint path")?;
    assert!(project.join(source_path).is_file());
    let graph = read_json(&project.join("analysis/source-graph.json"))?;
    assert_eq!(graph["summary"]["edge_kinds"]["js_import_static"], 2);
    assert_eq!(graph["summary"]["edge_kinds"]["js_import_dynamic"], 1);
    assert_eq!(graph["summary"]["edge_kinds"]["modulepreload"], 1);
    assert_eq!(graph["summary"]["edge_kinds"]["script_preload"], 1);
    let entrypoints = fs::read_to_string(project.join("src/ENTRYPOINTS.md"))?;
    assert!(entrypoints.contains("## HTML script preload hints"));
    assert!(entrypoints.contains("`modulepreload`"));
    assert!(entrypoints.contains("`script_preload`"));
    assert!(entrypoints.contains("assets/entry.js"));
    assert!(entrypoints.contains("assets/vendor/logic.js"));
    assert!(entrypoints.contains("assets/dynamic.js"));
    assert!(entrypoints.contains("`import_static` `pkg/logic.js`"));
    assert!(entrypoints.contains("`import_dynamic` `./dynamic.js`"));
    assert!(fs::read_to_string(project.join("README.md"))?
        .contains("[src/ENTRYPOINTS.md](src/ENTRYPOINTS.md)"));
    Ok(())
}

// Shared external module source is observed by one mapped and one unmapped HTML page.
const SHARED_MAPPED_PAGE_URL: &str = "https://fixture.invalid/mapped.html";
const SHARED_PLAIN_PAGE_URL: &str = "https://fixture.invalid/plain.html";
const SHARED_MODULE_URL: &str = "https://fixture.invalid/modules/shared.js";
const SHARED_CHILD_URL: &str = "https://fixture.invalid/modules/child.js";
const SHARED_REEXPORTED_URL: &str = "https://fixture.invalid/modules/reexported.js";
const SHARED_MAPPED_MODULE_URL: &str = "https://fixture.invalid/modules/mapped.js";

fn write_shared_module_context_fixture(input: &Path, project: &Path) -> Result<()> {
    let mapped_html = concat!(
        "<script type=\"importmap\">",
        "{\"imports\":{\"pkg\":\"/modules/mapped.js\"}}",
        "</script><script type=\"module\" src=\"/modules/shared.js\"></script>"
    );
    let plain_html = "<script type=\"module\" src=\"/modules/shared.js\"></script>";
    let entries = vec![
        har_entry(SHARED_MAPPED_PAGE_URL, "text/html", mapped_html),
        har_entry(SHARED_PLAIN_PAGE_URL, "text/html", plain_html),
        har_entry(
            SHARED_MODULE_URL,
            "application/javascript",
            "import 'pkg'; import './child.js'; export * from './reexported.js'; export { mapped } from 'pkg';",
        ),
        har_entry(SHARED_CHILD_URL, "application/javascript", "import 'pkg';"),
        har_entry(
            SHARED_REEXPORTED_URL,
            "application/javascript",
            "import 'pkg'; export const reexported = true;",
        ),
        har_entry(
            SHARED_MAPPED_MODULE_URL,
            "application/javascript",
            "export const mapped = true;",
        ),
    ];
    fs::write(
        input,
        serde_json::to_vec(&json!({
            "log": {
                "version":"1.2",
                "creator":{"name":"two-document module context regression","version":"1"},
                "pages":[{"id":"page_1","title":"shared modules",
                    "startedDateTime":"2026-10-04T00:00:00Z"}],
                "entries":entries
            }
        }))?,
    )?;
    run_pipeline(input, project)?;
    Ok(())
}

#[test]
fn shared_modules_keep_mapped_and_unmapped_document_contexts() -> Result<()> {
    let root = tempfile::tempdir()?;
    let input = root.path().join("shared-contexts.har");
    let project = root.path().join("project");
    write_shared_module_context_fixture(&input, &project)?;
    let manifest = read_json(&project.join("capture-manifest.json"))?;
    let resource_id = |url: &str| -> Result<u64> {
        manifest["resources"]
            .as_array()
            .context("missing resource list")?
            .iter()
            .find(|resource| resource["url"] == url)
            .and_then(|resource| resource["id"].as_u64())
            .with_context(|| format!("missing resource {url}"))
    };
    let mapped_id = resource_id(SHARED_MAPPED_PAGE_URL)?;
    let plain_id = resource_id(SHARED_PLAIN_PAGE_URL)?;
    let shared_id = resource_id(SHARED_MODULE_URL)?;
    let child_id = resource_id(SHARED_CHILD_URL)?;
    let reexported_id = resource_id(SHARED_REEXPORTED_URL)?;
    let mapped_target_id = resource_id(SHARED_MAPPED_MODULE_URL)?;
    let refs = read_json(&project.join("analysis/js-references.json"))?;
    let rows = refs["code_units"]
        .as_array()
        .context("missing JS reference rows")?;
    for (url, expected_resource_id) in [
        (SHARED_MODULE_URL, shared_id),
        (SHARED_CHILD_URL, child_id),
        (SHARED_REEXPORTED_URL, reexported_id),
    ] {
        let unit = code_unit(rows, url)?;
        assert_eq!(unit["resource_id"], expected_resource_id);
        assert_eq!(
            unit["document_resource_ids"],
            json!([mapped_id, plain_id]),
            "both pages must contribute an execution context to {url}"
        );
        let pkg = reference(unit, "pkg")?;
        assert_eq!(pkg["resolution"], "ambiguous_document_context");
        assert!(pkg["resolved_url"].is_null());
        let choices = pkg["resolution_candidates"]
            .as_array()
            .context("missing contextual resolution candidates")?;
        assert_eq!(choices.len(), 2);
        assert!(choices.iter().any(|choice| {
            choice["document_resource_id"] == mapped_id
                && choice["resolved_url"] == SHARED_MAPPED_MODULE_URL
                && choice["resolution"] == "import_map"
        }));
        assert!(choices.iter().any(|choice| {
            choice["document_resource_id"] == plain_id
                && choice["resolved_url"].is_null()
                && choice["resolution"] == "unresolved_bare"
        }));
    }
    // A module reached only through a re-export must inherit every document
    // context. A named re-export must also retain mapped and unmapped choices.
    let shared_references = code_unit(rows, SHARED_MODULE_URL)?["references"]
        .as_array()
        .context("missing shared module reference inventory")?;
    let wildcard = shared_references
        .iter()
        .find(|reference| reference["kind"] == "reexport_all")
        .context("missing wildcard re-export")?;
    assert_eq!(wildcard["resolved_url"], SHARED_REEXPORTED_URL);
    assert_eq!(
        wildcard["resolution_candidates"].as_array().map(Vec::len),
        Some(2)
    );
    let named = shared_references
        .iter()
        .find(|reference| reference["kind"] == "reexport_named")
        .context("missing named re-export")?;
    assert_eq!(named["resolution"], "ambiguous_document_context");
    assert!(named["resolved_url"].is_null());
    assert_eq!(
        named["resolution_candidates"].as_array().map(Vec::len),
        Some(2)
    );

    let child_import = reference(code_unit(rows, SHARED_MODULE_URL)?, "./child.js")?;
    assert_eq!(child_import["resolved_url"], SHARED_CHILD_URL);
    assert_eq!(
        child_import["resolution_candidates"]
            .as_array()
            .context("child import contexts missing")?
            .len(),
        2
    );

    let graph = read_json(&project.join("analysis/source-graph.json"))?;
    let edges = graph["edges"]
        .as_array()
        .context("source graph edges missing")?;
    for source_id in [shared_id, child_id, reexported_id] {
        let source = format!("resource:{source_id}");
        let pkg_edges = edges
            .iter()
            .filter(|edge| {
                edge["from"] == source
                    && edge["kind"] == "js_import_static"
                    && edge["specifier"] == "pkg"
            })
            .collect::<Vec<_>>();
        assert_eq!(pkg_edges.len(), 2);
        assert!(pkg_edges.iter().any(|edge| {
            edge["to"] == format!("resource:{mapped_target_id}")
                && edge["document_resource_id"] == mapped_id
                && edge["resolution"] == "import_map"
        }));
        assert!(pkg_edges.iter().any(|edge| {
            edge["to"]
                .as_str()
                .is_some_and(|id| id.starts_with("specifier:"))
                && edge["document_resource_id"] == plain_id
                && edge["resolution"] == "unresolved_bare"
                && edge["resolved_url"].is_null()
        }));
    }
    Ok(())
}

fn shared_alias_capture_fixture(project: &Path) -> Result<()> {
    fs::create_dir_all(project.join("resources"))?;
    let html = "<script type=\"module\" src=\"./entry.js\"></script><script type=\"module\">import './next.js';</script>";
    let external = "import './next.js';";
    let inline = "import './next.js';";
    let next_a = "export const a=1;";
    let next_b = "export const b=2;";
    for (name, bytes) in [
        ("alpha.html", html),
        ("beta.html", html),
        ("shared.js", external),
        ("shared-inline.js", inline),
        ("alpha-next.js", next_a),
        ("beta-next.js", next_b),
    ] {
        fs::write(project.join("resources").join(name), bytes)?;
    }
    let html_sha = sha256_hex(html.as_bytes());
    let ext_sha = sha256_hex(external.as_bytes());
    let inline_sha = sha256_hex(inline.as_bytes());
    let manifest = validate_manifest_value(
        &json!({
            "schema":"capture-project/v1",
            "source":{"kind":"synthetic","input":"shared-raw-capture-aliases","salvaged":false},
            "pages":[],
            "resources":[
                {"id":10,"kind":"html","url":"https://fixture.invalid/alpha/page.html",
                 "output_path":"resources/alpha.html","sha256":html_sha},
                {"id":11,"kind":"html","url":"https://fixture.invalid/beta/page.html",
                 "output_path":"resources/beta.html","sha256":html_sha},
                {"id":20,"kind":"javascript","url":"https://fixture.invalid/alpha/entry.js",
                 "output_path":"resources/shared.js","sha256":ext_sha},
                {"id":21,"kind":"javascript","url":"https://fixture.invalid/beta/entry.js",
                 "output_path":"resources/shared.js","sha256":ext_sha},
                {"id":30,"kind":"javascript","url":"https://fixture.invalid/alpha/next.js",
                 "output_path":"resources/alpha-next.js","sha256":sha256_hex(next_a.as_bytes())},
                {"id":31,"kind":"javascript","url":"https://fixture.invalid/beta/next.js",
                 "output_path":"resources/beta-next.js","sha256":sha256_hex(next_b.as_bytes())}
            ],
            "inline_scripts":[
                {"parent_resource_id":10,"ordinal":1,"script_type":"module",
                 "src":"./entry.js","resolved_src":"https://fixture.invalid/alpha/entry.js"},
                {"parent_resource_id":10,"ordinal":2,"script_type":"module",
                 "output_path":"resources/shared-inline.js","sha256":inline_sha},
                {"parent_resource_id":11,"ordinal":1,"script_type":"module",
                 "src":"./entry.js","resolved_src":"https://fixture.invalid/beta/entry.js"},
                {"parent_resource_id":11,"ordinal":2,"script_type":"module",
                 "output_path":"resources/shared-inline.js","sha256":inline_sha}
            ],
            "counts":{}
        }),
        "shared capture alias fixture",
    )?;
    write_manifest(&project.join("capture-manifest.json"), &manifest)?;
    materialize_capture_source(
        project,
        Some(2),
        &AnalysisBudgets::standard("shared-capture-alias-materialize"),
    )?;
    scan_project_references(
        project,
        Some(2),
        &AnalysisBudgets::standard("shared-capture-alias-refs"),
    )?;
    build_source_graph(
        project,
        &AnalysisBudgets::standard("shared-capture-alias-graph"),
    )?;
    Ok(())
}

fn assert_alias_source_inventory(project: &Path) -> Result<()> {
    let source_index = read_json(&project.join("analysis/source-index.json"))?;
    let source_units = source_index["units"]
        .as_array()
        .context("missing source units")?;
    let refs = read_json(&project.join("analysis/js-references.json"))?;
    let rows = refs["code_units"]
        .as_array()
        .context("missing JS code units")?;
    for (raw, origins) in [
        ("resources/shared.js", [(20, "resource"), (21, "resource")]),
        (
            "resources/shared-inline.js",
            [(10, "inline_script"), (11, "inline_script")],
        ),
    ] {
        let aliases = source_units
            .iter()
            .filter(|unit| unit["raw_path"] == raw)
            .collect::<Vec<_>>();
        assert_eq!(
            aliases.len(),
            2,
            "source index lost a capture identity for {raw}"
        );
        assert_ne!(aliases[0]["source_path"], aliases[1]["source_path"]);
        for (id, origin) in origins {
            assert!(aliases
                .iter()
                .any(|unit| unit["resource_id"] == id && unit["origin"] == origin));
        }
    }
    for (raw, resource_id, expected_url, document_id) in [
        (
            "resources/shared.js",
            20,
            "https://fixture.invalid/alpha/next.js",
            10,
        ),
        (
            "resources/shared.js",
            21,
            "https://fixture.invalid/beta/next.js",
            11,
        ),
        (
            "resources/shared-inline.js",
            10,
            "https://fixture.invalid/alpha/next.js",
            10,
        ),
        (
            "resources/shared-inline.js",
            11,
            "https://fixture.invalid/beta/next.js",
            11,
        ),
    ] {
        let row = rows
            .iter()
            .find(|row| row["raw_path"] == raw && row["resource_id"] == resource_id)
            .with_context(|| format!("missing reference row for {raw} / {resource_id}"))?;
        assert_eq!(row["document_resource_ids"], json!([document_id]));
        let reference = reference(row, "./next.js")?;
        assert_eq!(reference["resolved_url"], expected_url);
        assert_eq!(
            reference["resolution_candidates"][0]["document_resource_id"],
            document_id
        );
    }
    Ok(())
}

fn assert_alias_source_graph(project: &Path) -> Result<()> {
    let graph = read_json(&project.join("analysis/source-graph.json"))?;
    let edges = graph["edges"]
        .as_array()
        .context("missing source graph edges")?;
    for (src, target, doc) in [
        ("resource:20", "resource:30", 10),
        ("resource:21", "resource:31", 11),
        ("inline:10:2", "resource:30", 10),
        ("inline:11:2", "resource:31", 11),
    ] {
        let from_source = edges
            .iter()
            .filter(|edge| edge["from"] == src && edge["kind"] == "js_import_static")
            .collect::<Vec<_>>();
        assert_eq!(from_source.len(), 1, "unexpected edges from {src}");
        assert_eq!(from_source[0]["to"], target);
        assert_eq!(from_source[0]["document_resource_id"], doc);
    }

    Ok(())
}

fn assert_alias_static_module_graph(project: &Path) -> Result<()> {
    let source_index = read_json(&project.join("analysis/source-index.json"))?;
    let refs = read_json(&project.join("analysis/js-references.json"))?;
    let manifest = jsvm_lift::capture_project::load_manifest(project)?;
    let budget = WorkBudget::unlimited("shared-alias-static-module-test");
    let documents = captured_document_entrypoints(project, &manifest, &budget)?;
    let static_graph = link_static_modules(
        project,
        &documents,
        &source_index,
        &refs,
        &manifest,
        &budget,
    )?;
    assert_eq!(static_graph.roots.len(), 4);
    assert!(static_graph.unmatched_module_roots.is_empty());
    for (doc, raw, expected_id) in [
        (10, "resources/shared.js", 20),
        (11, "resources/shared.js", 21),
    ] {
        let root = static_graph
            .roots
            .iter()
            .find(|root| root.document_resource_id == doc && root.source.raw_path == raw)
            .context("missing exact captured script root")?;
        assert_eq!(root.source.capture_manifest_resource_ids, vec![expected_id]);
    }
    for dep in static_graph
        .dependencies
        .iter()
        .filter(|dep| dep.specifier == "./next.js")
    {
        let expected_id = if dep.document_resource_id == 10 {
            30
        } else {
            31
        };
        assert_eq!(dep.target_candidates.len(), 1);
        assert_eq!(
            dep.target_candidates[0].capture_manifest_resource_ids,
            vec![expected_id]
        );
    }
    Ok(())
}

#[test]
fn reused_capture_bytes_retain_each_exact_script_origin_and_url() -> Result<()> {
    let root = tempfile::tempdir()?;
    let project = root.path();
    shared_alias_capture_fixture(project)?;
    assert_alias_source_inventory(project)?;
    assert_alias_source_graph(project)?;
    assert_alias_static_module_graph(project)?;
    Ok(())
}
