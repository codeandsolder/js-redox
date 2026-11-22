use anyhow::Result;
use std::path::PathBuf;
use work_budget::WorkBudget;

pub mod html;
mod materialize;
mod parse;
pub mod resource;

use materialize::materialize_project;
use parse::read_har;

/// Inputs controlling one HAR-to-capture-project import.
#[derive(Debug)]
pub struct HarProjectOptions {
    pub har: PathBuf,
    pub output: PathBuf,
}

/// Small import result for callers that need counts without decoding the manifest again.
#[derive(Debug)]
pub struct HarProjectSummary {
    pub(crate) resources: usize,
    pub(crate) script_records: usize,
}

/// Materialize a HAR capture into an isolated, empty project staging directory.
pub fn import_har_project(
    args: &HarProjectOptions,
    budget: &WorkBudget,
) -> Result<HarProjectSummary> {
    budget.checkpoint()?;
    let (har, salvaged, parse_error, parse_warnings) = read_har(&args.har, budget)?;
    budget.checkpoint()?;
    materialize_project(args, har, salvaged, parse_error, parse_warnings, budget)
}
#[cfg(test)]
mod tests {
    use super::resource::output_path_for;

    #[test]
    fn har_archive_preserves_colliding_file_and_directory_paths() -> anyhow::Result<()> {
        use crate::{
            analysis_budget::AnalysisBudgets,
            capture_import::{import_capture_project, CaptureImportOptions},
            capture_project::load_manifest,
            sha256_hex,
        };
        use anyhow::Context;
        use serde_json::json;
        use std::fs;
        let root = tempfile::tempdir()?;
        let har = root.path().join("fixture.har");
        let output = root.path().join("project");
        let bodies = [
            (
                "https://fixture.invalid/assets.js",
                "application/javascript",
                "const value=42;",
            ),
            (
                "https://fixture.invalid/assets.js/index.html",
                "text/html",
                "<script>const inline=1;</script>",
            ),
            (
                "https://fixture.invalid/assets.js",
                "application/javascript",
                "const value=43;",
            ),
            (
                "https://fixture.invalid/assets.js",
                "application/javascript",
                "const value=42;",
            ),
        ];
        let entries = bodies
            .iter()
            .map(|(url, mime, body)| {
                json!({
                    "request":{"method":"GET","url":url},
                    "response":{"status":200,"content":{"mimeType":mime,"text":body}}
                })
            })
            .collect::<Vec<_>>();
        fs::write(
            &har,
            serde_json::to_vec(&json!({"log":{"entries":entries}}))?,
        )?;
        import_capture_project(
            &CaptureImportOptions {
                input: har,
                output: output.clone(),
                assets_dir: None,
                overwrite: false,
            },
            &AnalysisBudgets::standard("archive collision fixture"),
        )?;
        let manifest = load_manifest(&output)?;
        assert_eq!(manifest.resources.len(), bodies.len());
        for (row, (_, _, body)) in manifest.resources.iter().zip(bodies) {
            let path = row["output_path"].as_str().context("resource path")?;
            assert_eq!(fs::read_to_string(output.join(path))?, body);
            assert_eq!(row["sha256"], sha256_hex(body.as_bytes()));
        }
        assert_eq!(
            manifest.resources[0]["output_path"],
            manifest.resources[3]["output_path"]
        );
        assert_eq!(manifest.resources[3]["reused_body"], true);
        let page = manifest.resources[1]["output_path"]
            .as_str()
            .context("page path")?;
        let inline = manifest.inline_scripts[0]["output_path"]
            .as_str()
            .context("inline path")?;
        assert!(
            inline.starts_with(&format!("{page}.inline/")),
            "{page} vs {inline}"
        );
        assert_eq!(fs::read_to_string(output.join(inline))?, "const inline=1;");
        Ok(())
    }

    #[test]
    fn version_like_url_component_gets_resource_extension() {
        assert_eq!(
            output_path_for(
                "https://esm.glass.adidas.com/@adl/typography@2.0.0",
                "javascript",
                "application/javascript",
            ),
            "resources/https/esm.glass.adidas.com/adl/typography_2.0.0.js"
        );
        assert_eq!(
            output_path_for(
                "https://esm.glass.adidas.com/@adl/typography@2.0.0/fonts/AdihausDIN-Regular.woff2",
                "binary",
                "font/woff2",
            ),
            "resources/https/esm.glass.adidas.com/adl/typography_2.0.0/fonts/AdihausDIN-Regular.woff2"
        );
    }
}
