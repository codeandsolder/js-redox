use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, HashMap},
    fs,
    path::PathBuf,
};

mod html;
mod materialize;
mod parse;
mod resource;

use materialize::{build_manifest, write_project_metadata};
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

#[derive(Debug, Deserialize)]
struct Har {
    log: HarLog,
}

#[derive(Debug, Deserialize)]
struct HarLog {
    #[serde(default)]
    version: String,
    #[serde(default)]
    pages: Vec<HarPage>,
    entries: Vec<HarEntry>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HarPage {
    #[serde(default)]
    id: String,
    #[serde(default)]
    title: String,
    #[serde(default)]
    started_date_time: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HarEntry {
    #[serde(default)]
    pageref: Option<String>,
    #[serde(default)]
    started_date_time: String,
    #[serde(default)]
    time: f64,
    request: HarRequest,
    response: HarResponse,
    #[serde(default, rename = "_resourceType")]
    resource_type: Option<String>,
    #[serde(default, rename = "_failure")]
    failure: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
struct HarRequest {
    #[serde(default)]
    method: String,
    #[serde(default)]
    url: String,
    #[serde(default)]
    headers: Vec<NameValue>,
}

#[derive(Debug, Deserialize)]
struct HarResponse {
    #[serde(default)]
    status: i64,
    #[serde(default)]
    status_text: String,
    #[serde(default)]
    headers: Vec<NameValue>,
    content: HarContent,
    #[serde(default, rename = "_jsRedoxBody")]
    js_redox_body: Option<JsRedoxBodyRef>,
    #[serde(default, rename = "_jsRedoxBodyCapture")]
    js_redox_body_capture: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
struct JsRedoxBodyRef {
    path: String,
    sha256: String,
    size: usize,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
struct HarContent {
    #[serde(default)]
    size: i64,
    #[serde(default)]
    mime_type: String,
    #[serde(default)]
    text: Option<String>,
    #[serde(default)]
    encoding: Option<String>,
}

#[derive(Debug, Deserialize)]
struct NameValue {
    #[serde(default)]
    name: String,
    #[serde(default)]
    value: String,
}

#[derive(Debug, Clone, Serialize)]
struct PageMeta {
    id: String,
    title: String,
    started_date_time: String,
}

#[derive(Debug, Clone, Serialize)]
struct HeaderMeta {
    name: String,
    value: String,
}

#[derive(Debug, Clone, Serialize)]
struct Reference {
    kind: String,
    raw: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    resolved_url: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct ResourceMeta {
    id: usize,
    pageref: Option<String>,
    started_date_time: String,
    time_ms: f64,
    method: String,
    url: String,
    status: i64,
    status_text: String,
    mime_type: String,
    resource_type: Option<String>,
    declared_size: i64,
    encoding: Option<String>,
    body_present: bool,
    body_complete: bool,
    body_bytes: usize,
    sha256: Option<String>,
    transport_kind: String,
    kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    network_failure: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    body_capture: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    output_path: Option<String>,
    reused_body: bool,
    request_headers: Vec<HeaderMeta>,
    response_headers: Vec<HeaderMeta>,
    references: Vec<Reference>,
}

#[derive(Debug, Clone, Serialize)]
struct InlineScriptMeta {
    parent_resource_id: usize,
    ordinal: usize,
    script_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    src: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    resolved_src: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    output_path: Option<String>,
    body_bytes: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    sha256: Option<String>,
}

#[derive(Debug, Serialize)]
struct CaptureSource {
    kind: &'static str,
    input: String,
    har_version: String,
    salvaged: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    parse_error: Option<String>,
}

#[derive(Debug, Serialize)]
struct ProjectManifest {
    schema: &'static str,
    source: CaptureSource,
    pages: Vec<PageMeta>,
    resources: Vec<ResourceMeta>,
    inline_scripts: Vec<InlineScriptMeta>,
    counts: BTreeMap<String, usize>,
}

#[derive(Debug)]
struct ScriptTag {
    attrs: HashMap<String, String>,
    body: String,
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
    let manifest = build_manifest(args, har, salvaged, parse_error)?;
    write_project_metadata(args, &manifest)?;
    Ok(HarProjectSummary {
        resources: manifest.resources.len(),
        script_records: manifest.inline_scripts.len(),
        counts: manifest.counts,
    })
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
