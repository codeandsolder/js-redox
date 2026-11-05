//! Static document script roots, before any JS execution assumptions.
//!
//! Script source links are matched against captured resource URLs, not guessed
//! from filenames. DOM-inserted scripts, import-map resolution and runtime
//! network choices are separate work and explicitly left unresolved.
use crate::{
    browser_script_types::{is_executable_script, script_type_essence},
    capture_project::CaptureManifest,
    har_project::html::{extract_script_tags, find_tag_end, parse_attrs},
    sha256_hex,
};
use anyhow::{Context, Result};
use serde::Serialize;
use serde_json::Value;
use std::{collections::BTreeMap, fs, path::Path};
use url::Url;
use work_budget::WorkBudget;

#[derive(Debug, Clone, Serialize)]
pub struct CapturedScriptSource {
    pub resource_id: Option<u64>,
    pub output_path: String,
    pub sha256: String,
    pub matches_manifest_sha256: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct DocumentScriptRoot {
    pub ordinal: usize,
    pub script_type: String,
    pub executable: bool,
    pub is_module: bool,
    pub async_attribute: bool,
    pub defer_attribute: bool,
    pub nomodule_attribute: bool,
    /// parser_blocking, deferred, asynchronous, or inert.
    pub scheduling_class: &'static str,
    pub src: Option<String>,
    pub resolved_url: Option<String>,
    /// One per captured response; identical URL does not mean unique bytes.
    pub captured_sources: Vec<CapturedScriptSource>,
    /// Source claims here are static candidates, not browser execution proof.
    pub execution_observed: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct DocumentEntrypoints {
    pub document_resource_id: u64,
    pub document_url: String,
    pub document_source_sha256: String,
    pub document_matches_manifest_sha256: bool,
    pub static_base_url: String,
    pub scripts: Vec<DocumentScriptRoot>,
}

fn str_field<'a>(entry: &'a Value, name: &str) -> Option<&'a str> {
    entry.get(name).and_then(Value::as_str)
}

fn first_base_href(html: &str) -> Option<String> {
    // Reuse the same tag-boundary and attribute parser as capture import.
    // This is the initial markup, not a DOM after script execution.
    let lower = html.to_ascii_lowercase();
    let bytes = html.as_bytes();
    let mut cursor = 0;
    while let Some(offset) = lower[cursor..].find("<base") {
        let start = cursor + offset;
        cursor = start + 5;
        if !bytes
            .get(cursor)
            .is_some_and(|byte| byte.is_ascii_whitespace() || matches!(byte, b'>' | b'/'))
        {
            continue;
        }
        let end = find_tag_end(bytes, cursor)?;
        let attrs = parse_attrs(&html[start..=end]);
        if let Some(href) = attrs.get("href") {
            return Some(href.clone());
        }
        cursor = end + 1;
    }
    None
}

fn scheduling_class(
    executable: bool,
    module: bool,
    src: bool,
    is_async: bool,
    is_defer: bool,
) -> &'static str {
    if !executable {
        "inert"
    } else if is_async && src {
        "asynchronous"
    } else if module || (is_defer && src) {
        "deferred"
    } else {
        "parser_blocking"
    }
}

/// Enumerate parser-visible initial script roots and *candidate* scheduling
/// classes. The ordinal is source markup order, not an actual runtime sequence.
pub fn static_document_scripts(
    html: &str,
    document_url: &str,
    budget: &WorkBudget,
) -> Result<(String, Vec<DocumentScriptRoot>)> {
    let doc_url = Url::parse(document_url)
        .with_context(|| format!("invalid document base URL: {document_url}"))?;
    let base = first_base_href(html)
        .and_then(|href| doc_url.join(&href).ok())
        .unwrap_or(doc_url);
    let mut scripts = Vec::new();
    for (ordinal0, tag) in extract_script_tags(html).into_iter().enumerate() {
        budget.consume(1)?;
        let script_type = script_type_essence(tag.attrs.get("type").map(String::as_str));
        let is_module = script_type == "module";
        let executable = is_executable_script(Some(&script_type));
        let src = tag.attrs.get("src").cloned();
        let resolved_url = src
            .as_deref()
            .and_then(|raw| base.join(raw).ok())
            .map(|url| url.to_string());
        let is_async = tag.attrs.contains_key("async");
        let is_defer = tag.attrs.contains_key("defer");
        scripts.push(DocumentScriptRoot {
            ordinal: ordinal0 + 1,
            script_type,
            executable,
            is_module,
            async_attribute: is_async,
            defer_attribute: is_defer,
            nomodule_attribute: tag.attrs.contains_key("nomodule"),
            scheduling_class: scheduling_class(
                executable,
                is_module,
                src.is_some(),
                is_async,
                is_defer,
            ),
            src,
            resolved_url,
            captured_sources: Vec::new(),
            execution_observed: false,
        });
    }
    Ok((base.to_string(), scripts))
}

/// Resolve source-linked HTML roots in an already validated capture project.
/// Ambiguous repeated network responses remain separate candidate sources.
pub fn captured_document_entrypoints(
    project: &Path,
    manifest: &CaptureManifest,
    budget: &WorkBudget,
) -> Result<Vec<DocumentEntrypoints>> {
    let mut resources_by_url = BTreeMap::<String, Vec<&Value>>::new();
    let mut inline_by_document = BTreeMap::<(u64, usize), &Value>::new();
    for resource in &manifest.resources {
        budget.consume(1)?;
        if let Some(url) = str_field(resource, "url") {
            resources_by_url
                .entry(url.to_string())
                .or_default()
                .push(resource);
        }
    }
    for script in &manifest.inline_scripts {
        budget.consume(1)?;
        if let (Some(parent), Some(ordinal)) = (
            script.get("parent_resource_id").and_then(Value::as_u64),
            script.get("ordinal").and_then(Value::as_u64),
        ) {
            let Ok(ordinal) = usize::try_from(ordinal) else {
                continue;
            };
            inline_by_document.insert((parent, ordinal), script);
        }
    }

    let captured = |record: &Value| -> Result<Option<CapturedScriptSource>> {
        let Some(output_path) = str_field(record, "output_path") else {
            return Ok(None);
        };
        let bytes = fs::read(project.join(output_path))
            .with_context(|| format!("reading captured script {output_path}"))?;
        let digest = sha256_hex(&bytes);
        Ok(Some(CapturedScriptSource {
            resource_id: record.get("id").and_then(Value::as_u64),
            output_path: output_path.to_string(),
            matches_manifest_sha256: str_field(record, "sha256") == Some(digest.as_str()),
            sha256: digest,
        }))
    };

    let mut documents = Vec::new();
    for resource in &manifest.resources {
        budget.consume(1)?;
        if str_field(resource, "kind") != Some("html") {
            continue;
        }
        let (Some(document_resource_id), Some(document_url), Some(output_path)) = (
            resource.get("id").and_then(Value::as_u64),
            str_field(resource, "url"),
            str_field(resource, "output_path"),
        ) else {
            continue;
        };
        let html = fs::read_to_string(project.join(output_path))
            .with_context(|| format!("reading captured HTML {output_path}"))?;
        let document_source_sha256 = sha256_hex(html.as_bytes());
        let (base, mut scripts) = static_document_scripts(&html, document_url, budget)?;
        for script in &mut scripts {
            budget.consume(1)?;
            if let Some(url) = script.resolved_url.as_ref() {
                if script.executable {
                    for record in resources_by_url.get(url).into_iter().flatten() {
                        if let Some(source) = captured(record)? {
                            script.captured_sources.push(source);
                        }
                    }
                }
            } else if script.executable {
                if let Some(record) =
                    inline_by_document.get(&(document_resource_id, script.ordinal))
                {
                    if let Some(source) = captured(record)? {
                        script.captured_sources.push(source);
                    }
                }
            }
        }
        documents.push(DocumentEntrypoints {
            document_resource_id,
            document_url: document_url.to_string(),
            document_source_sha256: document_source_sha256.clone(),
            document_matches_manifest_sha256: str_field(resource, "sha256")
                == Some(document_source_sha256.as_str()),
            static_base_url: base,
            scripts,
        });
    }
    Ok(documents)
}

#[cfg(test)]
mod tests {
    use super::static_document_scripts;
    use work_budget::WorkBudget;

    #[test]
    fn html_root_order_base_and_script_scheduling_are_explicit() -> anyhow::Result<()> {
        let html = r#"
            <base href="/assets/">
            <script>run()</script>
            <script type="module" src="main.mjs"></script>
            <script src="slow.js" defer></script>
            <script src="fast.js" async></script>
            <script type="application/json">{"ok":true}</script>
            <script src="legacy.js" nomodule></script>
        "#;
        let (base, scripts) = static_document_scripts(
            html,
            "https://example.test/docs/index.html",
            &WorkBudget::unlimited("test-doc-scripts"),
        )?;
        assert_eq!(base, "https://example.test/assets/");
        assert_eq!(scripts.len(), 6);
        assert_eq!(scripts[0].scheduling_class, "parser_blocking");
        assert_eq!(scripts[1].scheduling_class, "deferred");
        assert_eq!(
            scripts[1].resolved_url.as_deref(),
            Some("https://example.test/assets/main.mjs")
        );
        assert_eq!(scripts[2].scheduling_class, "deferred");
        assert_eq!(scripts[3].scheduling_class, "asynchronous");
        assert_eq!(scripts[4].scheduling_class, "inert");
        assert!(scripts[5].nomodule_attribute);
        assert!(!scripts[5].execution_observed);
        Ok(())
    }
}
