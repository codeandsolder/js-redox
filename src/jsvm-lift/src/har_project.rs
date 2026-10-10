use anyhow::{bail, Result};
use std::{collections::BTreeMap, fs, path::PathBuf};

mod html;
mod materialize;
mod parse;
mod resource;

use materialize::materialize_project;
use parse::read_har;

/// Inputs controlling one HAR-to-capture-project import.
#[derive(Debug)]
pub struct HarProjectOptions {
    pub har: PathBuf,
    pub output: PathBuf,
    pub overwrite: bool,
}

/// Small import result for callers that need counts without decoding the manifest again.
#[derive(Debug)]
pub struct HarProjectSummary {
    pub resources: usize,
    pub script_records: usize,
    pub counts: BTreeMap<String, usize>,
}

fn prepare_output(args: &HarProjectOptions) -> Result<()> {
    if args.output.exists() {
        if !args.overwrite {
            bail!(
                "output directory already exists: {} (use --overwrite)",
                args.output.display()
            );
        }
        fs::remove_dir_all(&args.output)?;
    }
    fs::create_dir_all(&args.output)?;
    Ok(())
}

/// Materialize a HAR capture as a canonical capture project.
pub fn import_har_project(args: &HarProjectOptions) -> Result<HarProjectSummary> {
    prepare_output(args)?;
    let (har, salvaged, parse_error) = read_har(&args.har)?;
    materialize_project(args, har, salvaged, parse_error)
}
#[cfg(test)]
mod tests {
    use super::resource::output_path_for;

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
