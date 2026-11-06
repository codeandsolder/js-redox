use anyhow::{Context, Result};
use jsvm_lift::{
    analysis_budget::AnalysisBudgets,
    capture_import::{import_capture_project, CaptureImportOptions},
    project_js_refs::scan_project_references,
    project_readme::refresh_project_readme,
    source_graph::build_source_graph,
    source_materialize::materialize_capture_source,
};
use serde_json::{json, Value};
use std::{fs, path::Path};

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
