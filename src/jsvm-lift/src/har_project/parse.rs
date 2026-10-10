use super::{Har, HarEntry, HarLog};
use anyhow::{bail, Context, Result};
use std::{fs, path::Path};

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
