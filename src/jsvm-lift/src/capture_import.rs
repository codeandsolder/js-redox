mod execution_coverage;
mod runtime_scripts;
mod saved_page;

use crate::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    capture_project::{load_manifest, write_manifest, CaptureManifest},
    har_project::{import_har_project, HarProjectOptions},
};
use anyhow::{bail, Context, Result};
use runtime_scripts::analyze_recorder_runtime_scripts;
use saved_page::{import_saved_page, SavedPageOptions};
use serde_json::Value;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaptureInputKind {
    Har,
    Recorder,
    SavedPage,
}

impl CaptureInputKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Har => "har",
            Self::Recorder => "recorder",
            Self::SavedPage => "saved_page",
        }
    }
}

#[derive(Debug, Clone)]
pub struct CaptureImportOptions {
    pub input: PathBuf,
    pub output: PathBuf,
    pub assets_dir: Option<PathBuf>,
    pub overwrite: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaptureImportSummary {
    pub kind: CaptureInputKind,
    pub resources: usize,
    pub script_records: usize,
}

pub fn detect_capture_input(path: &Path) -> Result<CaptureInputKind> {
    if path.is_dir() {
        if path.join("recorder-manifest.json").is_file() && path.join("capture.har").is_file() {
            return Ok(CaptureInputKind::Recorder);
        }
        bail!(
            "unsupported capture directory: {}; expected a recorder bundle containing recorder-manifest.json and capture.har",
            path.display()
        );
    }
    let suffix = path
        .extension()
        .and_then(|value| value.to_str())
        .unwrap_or_default()
        .to_ascii_lowercase();
    match suffix.as_str() {
        "html" | "htm" | "xhtml" => Ok(CaptureInputKind::SavedPage),
        "har" | "json" => Ok(CaptureInputKind::Har),
        _ => bail!(
            "unsupported capture input: {}; expected recorder bundle, HAR/JSON HAR, or saved HTML",
            path.display()
        ),
    }
}

/// Retain the actual browser entrypoint even when a recorder HAR omits log.pages.
/// These values are observed navigation metadata, not recovered JS semantics.
fn add_recorder_navigation(manifest: &mut CaptureManifest, recorder_manifest: &Value) {
    let requested = recorder_manifest
        .get("requestedUrl")
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty());
    let final_url = recorder_manifest
        .get("finalUrl")
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty());
    if let Some(value) = requested {
        manifest
            .source
            .extra
            .insert("requested_url".into(), Value::String(value.into()));
    }
    if let Some(value) = final_url {
        manifest
            .source
            .extra
            .insert("final_url".into(), Value::String(value.into()));
    }
    if let Some(created) = recorder_manifest.get("createdAt").and_then(Value::as_str) {
        manifest
            .source
            .extra
            .insert("capture_created_at".into(), Value::String(created.into()));
    }
    if requested.is_some() || final_url.is_some() {
        manifest.pages.push(serde_json::json!({
            "kind": "recorder_navigation",
            "requested_url": requested,
            "final_url": final_url,
        }));
    }
}

pub fn import_capture_project(
    options: &CaptureImportOptions,
    budgets: &AnalysisBudgets,
) -> Result<CaptureImportSummary> {
    let budget = budgets.operation(
        AnalysisOperation::CaptureImport,
        options.input.display().to_string(),
    );
    budget.checkpoint()?;
    let input = options
        .input
        .canonicalize()
        .with_context(|| format!("capture input does not exist: {}", options.input.display()))?;
    let kind = detect_capture_input(&input)?;
    match kind {
        CaptureInputKind::SavedPage => {
            let summary = import_saved_page(
                &input,
                &options.output,
                &SavedPageOptions {
                    assets_dir: options.assets_dir.clone(),
                    overwrite: options.overwrite,
                },
                &budget,
            )?;
            Ok(CaptureImportSummary {
                kind,
                resources: summary.resources,
                script_records: summary.script_records,
            })
        }
        CaptureInputKind::Har | CaptureInputKind::Recorder => {
            if options.assets_dir.is_some() {
                bail!("--assets-dir is only valid for saved-page captures");
            }
            let har = if kind == CaptureInputKind::Recorder {
                input.join("capture.har")
            } else {
                input.clone()
            };
            let summary = import_har_project(
                &HarProjectOptions {
                    har: har.clone(),
                    output: options.output.clone(),
                    overwrite: options.overwrite,
                },
                &budget,
            )?;
            if kind == CaptureInputKind::Recorder {
                let mut manifest = load_manifest(&options.output)?;
                manifest.source.kind = "recorder".into();
                manifest.source.input = input.display().to_string();
                manifest
                    .source
                    .extra
                    .insert("har_input".into(), Value::String(har.display().to_string()));
                let recorder_manifest_path = input.join("recorder-manifest.json");
                let recorder_metadata: Value =
                    serde_json::from_slice(&std::fs::read(&recorder_manifest_path)?)
                        .with_context(|| format!("parsing {}", recorder_manifest_path.display()))?;
                add_recorder_navigation(&mut manifest, &recorder_metadata);
                write_manifest(&options.output.join("capture-manifest.json"), &manifest)?;
                analyze_recorder_runtime_scripts(&input, &options.output, &manifest, &budget)?;
            }
            Ok(CaptureImportSummary {
                kind,
                resources: summary.resources,
                script_records: summary.script_records,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recorder_navigation_survives_har_without_pages() {
        use crate::capture_project::{CaptureManifest, CaptureSource};
        use serde_json::{json, Map};
        use std::collections::BTreeMap;

        let mut manifest = CaptureManifest {
            schema: "capture-project/v1".into(),
            source: CaptureSource {
                kind: "recorder".into(),
                input: "capture".into(),
                salvaged: false,
                extra: Map::new(),
            },
            pages: vec![],
            resources: vec![],
            inline_scripts: vec![],
            counts: BTreeMap::new(),
            extra: Map::new(),
        };
        add_recorder_navigation(
            &mut manifest,
            &json!({
                "requestedUrl":"https://example.test/a",
                "finalUrl":"https://example.test/b",
                "createdAt":"2026-11-04T01:00:00Z",
            }),
        );
        assert_eq!(manifest.pages.len(), 1);
        assert_eq!(manifest.pages[0]["requested_url"], "https://example.test/a");
        assert_eq!(manifest.pages[0]["final_url"], "https://example.test/b");
        assert_eq!(
            manifest.source.extra["requested_url"],
            "https://example.test/a"
        );
        assert_eq!(manifest.source.extra["final_url"], "https://example.test/b");
        assert_eq!(
            manifest.source.extra["capture_created_at"],
            "2026-11-04T01:00:00Z"
        );
    }

    #[test]
    fn detects_supported_file_inputs_without_parsing_them() -> Result<()> {
        assert_eq!(
            detect_capture_input(Path::new("capture.har"))?,
            CaptureInputKind::Har
        );
        assert_eq!(
            detect_capture_input(Path::new("capture.json"))?,
            CaptureInputKind::Har
        );
        assert_eq!(
            detect_capture_input(Path::new("Saved.html"))?,
            CaptureInputKind::SavedPage
        );
        Ok(())
    }
}
