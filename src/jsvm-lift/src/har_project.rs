use crate::capture_project::prepare_project_output;
use anyhow::Result;
use std::path::PathBuf;

pub(crate) mod html;
mod materialize;
mod parse;
pub(crate) mod resource;

use materialize::materialize_project;
use parse::read_har;

/// Inputs controlling one HAR-to-capture-project import.
#[derive(Debug)]
pub(crate) struct HarProjectOptions {
    pub har: PathBuf,
    pub output: PathBuf,
    pub overwrite: bool,
}

/// Small import result for callers that need counts without decoding the manifest again.
#[derive(Debug)]
pub(crate) struct HarProjectSummary {
    pub(crate) resources: usize,
    pub(crate) script_records: usize,
}

/// Materialize a HAR capture as a canonical capture project.
pub(crate) fn import_har_project(args: &HarProjectOptions) -> Result<HarProjectSummary> {
    prepare_project_output(&args.output, args.overwrite)?;
    let (har, salvaged, parse_error, parse_warnings) = read_har(&args.har)?;
    materialize_project(args, har, salvaged, parse_error, parse_warnings)
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
