use anyhow::{bail, Context, Result};
use serde::Deserialize;
use std::{fs, path::Path};

#[derive(Debug, Deserialize)]
pub(super) struct Har {
    pub(super) log: HarLog,
}

#[derive(Debug, Deserialize)]
pub(super) struct HarLog {
    #[serde(default)]
    pub(super) version: String,
    #[serde(default)]
    pub(super) pages: Vec<HarPage>,
    pub(super) entries: Vec<HarEntry>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct HarPage {
    #[serde(default)]
    pub(super) id: String,
    #[serde(default)]
    pub(super) title: String,
    #[serde(default)]
    pub(super) started_date_time: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct HarEntry {
    #[serde(default)]
    pub(super) pageref: Option<String>,
    #[serde(default)]
    pub(super) started_date_time: String,
    #[serde(default)]
    pub(super) time: f64,
    pub(super) request: HarRequest,
    pub(super) response: HarResponse,
    #[serde(default, rename = "_resourceType")]
    pub(super) resource_type: Option<String>,
    #[serde(default, rename = "_failure")]
    pub(super) failure: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
pub(super) struct HarRequest {
    #[serde(default)]
    pub(super) method: String,
    #[serde(default)]
    pub(super) url: String,
    #[serde(default)]
    pub(super) headers: Vec<NameValue>,
}

#[derive(Debug, Deserialize)]
pub(super) struct HarResponse {
    #[serde(default)]
    pub(super) status: i64,
    #[serde(default)]
    pub(super) status_text: String,
    #[serde(default)]
    pub(super) headers: Vec<NameValue>,
    pub(super) content: HarContent,
    #[serde(default, rename = "_jsRedoxBody")]
    pub(super) js_redox_body: Option<JsRedoxBodyRef>,
    #[serde(default, rename = "_jsRedoxBodyCapture")]
    pub(super) js_redox_body_capture: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
pub(super) struct JsRedoxBodyRef {
    pub(super) path: String,
    pub(super) sha256: String,
    pub(super) size: usize,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct HarContent {
    #[serde(default)]
    pub(super) size: i64,
    #[serde(default)]
    pub(super) mime_type: String,
    #[serde(default)]
    pub(super) text: Option<String>,
    #[serde(default)]
    pub(super) encoding: Option<String>,
}

#[derive(Debug, Deserialize)]
pub(super) struct NameValue {
    #[serde(default)]
    pub(super) name: String,
    #[serde(default)]
    pub(super) value: String,
}

fn salvage_har(raw: &[u8]) -> Result<Har> {
    let text = std::str::from_utf8(raw).context("HAR is not valid UTF-8")?;
    let marker = text
        .find("\"entries\"")
        .context("could not locate HAR log.entries for salvage")?;
    let array_rel = text[marker..]
        .find('[')
        .context("could not locate HAR log.entries array")?;
    let array_start = marker + array_rel;
    let bytes = text.as_bytes();

    let mut entries = Vec::new();
    let mut in_string = false;
    let mut escaped = false;
    let mut object_depth = 0usize;
    let mut array_depth = 1usize;
    let mut entry_start = None;

    for i in (array_start + 1)..bytes.len() {
        let byte = bytes[i];
        if in_string {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                in_string = false;
            }
            continue;
        }

        match byte {
            b'"' => in_string = true,
            b'{' => {
                if object_depth == 0 && array_depth == 1 {
                    entry_start = Some(i);
                }
                object_depth += 1;
            }
            b'}' => {
                if object_depth == 0 {
                    continue;
                }
                object_depth -= 1;
                if object_depth == 0 && array_depth == 1 {
                    if let Some(start) = entry_start.take() {
                        match serde_json::from_str::<HarEntry>(&text[start..=i]) {
                            Ok(entry) => entries.push(entry),
                            Err(error) => {
                                eprintln!(
                                    "warning: skipping malformed salvaged HAR entry at bytes {start}..={i}: {error}"
                                );
                            }
                        }
                    }
                }
            }
            b'[' => array_depth += 1,
            b']' => {
                if array_depth == 1 && object_depth == 0 {
                    break;
                }
                array_depth = array_depth.saturating_sub(1);
            }
            _ => {}
        }
    }

    if entries.is_empty() {
        bail!("no complete HAR entries could be salvaged");
    }

    Ok(Har {
        log: HarLog {
            version: "1.2-salvaged".into(),
            pages: Vec::new(),
            entries,
        },
    })
}

pub(super) fn read_har(path: &Path) -> Result<(Har, bool, Option<String>)> {
    let raw = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
    let first = raw.iter().copied().find(|byte| !byte.is_ascii_whitespace());
    if first != Some(b'{') {
        bail!(
            "{} is not HAR JSON (first non-whitespace byte {:?})",
            path.display(),
            first
        );
    }
    let parsed = match serde_json::from_slice::<Har>(&raw) {
        Ok(har) => (har, false, None),
        Err(error) => {
            let message = error.to_string();
            eprintln!("warning: full HAR JSON parse failed; salvaging complete entries: {message}");
            (
                salvage_har(&raw)
                    .with_context(|| format!("salvaging truncated HAR {}", path.display()))?,
                true,
                Some(message),
            )
        }
    };
    if parsed.0.log.entries.is_empty() {
        bail!("HAR contains no log.entries");
    }
    Ok(parsed)
}
