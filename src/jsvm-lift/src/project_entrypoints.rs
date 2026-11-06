//! Navigable document-to-module source index for a recovered capture project.
//! Kept independent of runtime evidence: HTML declarations and import edges
//! describe statically reachable code, not necessarily executed functions.
use crate::browser_script_types::is_executable_script;
use anyhow::{Context, Result};
use serde_json::Value;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    path::Path,
};

fn fields<'a>(value: &'a Value, key: &str) -> &'a [Value] {
    value
        .get(key)
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .unwrap_or_default()
}

fn string<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

fn display(text: &str) -> String {
    text.replace('\\', "\\\\")
        .replace('`', "\\`")
        .replace(['\n', '\r'], " ")
}

fn path_link(unit: &Value, readable: &BTreeMap<&str, &str>) -> String {
    let raw = string(unit, "raw_path").unwrap_or_default();
    let source = string(unit, "source_path").unwrap_or_default();
    let preferred = readable.get(raw).copied().unwrap_or(source);
    // Links originate inside src/; all source paths are validated project paths.
    let relative = preferred.strip_prefix("src/").unwrap_or(preferred);
    let escaped = relative
        .replace('%', "%25")
        .replace('#', "%23")
        .replace(' ', "%20")
        .replace('(', "%28")
        .replace(')', "%29");
    format!("[`{}`]({escaped})", display(relative))
}

fn append_reachable<'a>(
    lines: &mut Vec<String>,
    roots: Vec<(&'a Value, String)>,
    by_url: &BTreeMap<&str, Vec<&'a Value>>,
    references: &BTreeMap<&str, &[Value]>,
    readable: &BTreeMap<&str, &str>,
    global_seen: &mut BTreeSet<&'a str>,
) {
    let mut queue = VecDeque::from(roots);
    let mut visited = BTreeSet::<&str>::new();
    while let Some((unit, why)) = queue.pop_front() {
        let Some(raw) = string(unit, "raw_path") else {
            continue;
        };
        if !visited.insert(raw) {
            continue;
        }
        global_seen.insert(raw);
        lines.push(format!("- {} — {why}", path_link(unit, readable)));
        for reference in references.get(raw).copied().unwrap_or_default() {
            let specifier = string(reference, "specifier").unwrap_or("unknown");
            let kind = string(reference, "kind").unwrap_or("reference");
            let Some(destination) = string(reference, "resolved_url") else {
                if !specifier.is_empty() {
                    lines.push(format!(
                        "  - `{kind}` `{}` — unresolved",
                        display(specifier)
                    ));
                }
                continue;
            };
            let Some(targets) = by_url.get(destination) else {
                lines.push(format!(
                    "  - `{kind}` `{}` — not captured (`{}`)",
                    display(specifier),
                    display(destination)
                ));
                continue;
            };
            for target in targets {
                queue.push_back((
                    target,
                    format!(
                        "`{kind}` `{}` from {}",
                        display(specifier),
                        path_link(unit, readable)
                    ),
                ));
            }
        }
    }
}

/// Materializes a complete navigator of HTML-declared scripts and their
/// statically resolved transitive JavaScript imports. Returns the number of
/// distinct declared script entries; an empty index is still useful for
/// explaining why there is no HTML-root code path in a capture.
pub(crate) fn write_entrypoint_index(
    project: &Path,
    manifest: &Value,
    source_index: &Value,
    deob: &Value,
    references: &Value,
) -> Result<usize> {
    let js_units = fields(source_index, "units")
        .iter()
        .filter(|unit| string(unit, "kind") == Some("javascript"))
        .collect::<Vec<_>>();
    let mut by_url = BTreeMap::<&str, Vec<&Value>>::new();
    let mut by_raw = BTreeMap::<&str, &Value>::new();
    for unit in &js_units {
        // Inline script bodies share their document URL but must not be treated
        // as importable modules at that URL.
        if string(unit, "origin") != Some("inline_script") {
            if let Some(url) = string(unit, "url") {
                by_url.entry(url).or_default().push(unit);
            }
        }
        if let Some(raw) = string(unit, "raw_path") {
            by_raw.insert(raw, unit);
        }
    }
    let readable = fields(deob, "units")
        .iter()
        .filter_map(|row| {
            Some((
                string(row, "raw_path")?,
                string(row, "readable_output_path")?,
            ))
        })
        .collect::<BTreeMap<_, _>>();
    let references = fields(references, "code_units")
        .iter()
        .filter_map(|unit| Some((string(unit, "raw_path")?, fields(unit, "references"))))
        .collect::<BTreeMap<_, _>>();
    let documents = fields(manifest, "resources")
        .iter()
        .filter_map(|row| Some((row.get("id")?.as_u64()?, string(row, "url")?)))
        .collect::<BTreeMap<_, _>>();
    let mut lines = vec![
        "# JavaScript source entrypoints".to_owned(),
        String::new(),
        "These are the HTML-declared scripts from the captured documents, with the statically resolvable JavaScript import/worker dependencies. This is an index of available source, **not an execution trace**. A missing edge does not mean an import never happened.".into(),
        String::new(),
    ];
    let mut global_seen = BTreeSet::<&str>::new();
    let mut roots = 0;
    for script in fields(manifest, "inline_scripts") {
        if !is_executable_script(string(script, "script_type")) {
            continue;
        }
        roots += 1;
        let document = script
            .get("parent_resource_id")
            .and_then(Value::as_u64)
            .and_then(|id| documents.get(&id).copied())
            .unwrap_or("unknown document");
        let ordinal = script.get("ordinal").and_then(Value::as_u64).unwrap_or(0);
        lines.push(format!("## {} — script {ordinal}", display(document)));
        lines.push(String::new());
        let roots_for_script = if let Some(src) = string(script, "resolved_src") {
            lines.push(format!("HTML `src`: `{}`", display(src)));
            by_url.get(src).cloned().unwrap_or_default()
        } else if let Some(raw) = string(script, "output_path") {
            by_raw.get(raw).copied().into_iter().collect()
        } else {
            Vec::new()
        };
        if roots_for_script.is_empty() {
            lines.push("Source body not present in this capture.".into());
            lines.push(String::new());
            continue;
        }
        append_reachable(
            &mut lines,
            roots_for_script
                .into_iter()
                .map(|unit| (unit, "declared entrypoint".to_owned()))
                .collect(),
            &by_url,
            &references,
            &readable,
            &mut global_seen,
        );
        lines.push(String::new());
    }
    if roots == 0 {
        lines.push("No executable HTML script declarations were found in this capture.".into());
        lines.push(String::new());
    }
    let preloads = fields(manifest, "resources")
        .iter()
        .flat_map(|document| {
            fields(document, "references")
                .iter()
                .filter(|reference| {
                    matches!(
                        string(reference, "kind"),
                        Some("modulepreload" | "script_preload")
                    )
                })
                .map(move |reference| (document, reference))
        })
        .collect::<Vec<_>>();
    if !preloads.is_empty() {
        lines.extend([
            "## HTML script preload hints".into(),
            String::new(),
            "These resources were declared in HTML `<link rel=modulepreload>` or `<link rel=preload as=script>` tags. Preloading is not proof of execution; the listed dependencies are statically discoverable source code.".into(),
            String::new(),
        ]);
        for (document, reference) in preloads {
            let document_url = string(document, "url").unwrap_or("unknown document");
            let kind = string(reference, "kind").unwrap_or("preload");
            let url = string(reference, "resolved_url").unwrap_or_default();
            lines.push(format!(
                "### {} — `{}` `{}`",
                display(document_url),
                kind,
                display(url)
            ));
            lines.push(String::new());
            if let Some(units) = by_url.get(url) {
                append_reachable(
                    &mut lines,
                    units
                        .iter()
                        .copied()
                        .map(|unit| (unit, format!("HTML `{kind}` hint")))
                        .collect(),
                    &by_url,
                    &references,
                    &readable,
                    &mut global_seen,
                );
            } else {
                lines.push("Preloaded script body not present in this capture.".into());
            }
            lines.push(String::new());
        }
    }
    let unlinked = js_units
        .iter()
        .filter(|unit| string(unit, "raw_path").is_some_and(|path| !global_seen.contains(path)))
        .collect::<Vec<_>>();
    if !unlinked.is_empty() {
        lines.extend([
            "## Other captured JavaScript".into(),
            String::new(),
            "These files are not reached from an HTML-declared script through the statically resolved edges above. They may be preloads, workers, runtime-loaded resources or unrelated captured pages.".into(),
            String::new(),
        ]);
        for unit in unlinked {
            lines.push(format!("- {}", path_link(unit, &readable)));
        }
        lines.push(String::new());
    }
    let output = project.join("src/ENTRYPOINTS.md");
    fs::create_dir_all(output.parent().context("entrypoint index has no parent")?)?;
    fs::write(&output, lines.join("\n"))
        .with_context(|| format!("writing {}", output.display()))?;
    Ok(roots)
}
