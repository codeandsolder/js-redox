mod saved_page;

use crate::{
    capture_project::{load_manifest, write_manifest},
    har_project::{import_har_project, HarProjectOptions},
};
use anyhow::{bail, Context, Result};
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

pub fn import_capture_project(options: &CaptureImportOptions) -> Result<CaptureImportSummary> {
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
            let summary = import_har_project(&HarProjectOptions {
                har: har.clone(),
                output: options.output.clone(),
                overwrite: options.overwrite,
            })?;
            if kind == CaptureInputKind::Recorder {
                let mut manifest = load_manifest(&options.output)?;
                manifest.source.kind = "recorder".into();
                manifest.source.input = input.display().to_string();
                manifest
                    .source
                    .extra
                    .insert("har_input".into(), Value::String(har.display().to_string()));
                write_manifest(&options.output.join("capture-manifest.json"), &manifest)?;
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
