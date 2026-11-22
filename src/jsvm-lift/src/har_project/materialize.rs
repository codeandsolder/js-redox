use super::html::{
    document_base, extract_script_tags, inline_script_extension, is_executable_script_type,
    is_json_script_type, resolve_ref, script_preload_links, script_type, source_refs,
};
use super::parse::{Har, HarEntry, NameValue};
use super::resource::{
    decode_body, format_json_if_possible, output_path_for, refine_resource_kind, resource_kind,
};
use super::{HarProjectOptions, HarProjectSummary};
use crate::{
    archive_storage::ResourceStore,
    browser_decode::decode_html,
    capture_project::{write_manifest, CaptureManifest, CaptureSource, MANIFEST_NAME, SCHEMA},
};
use anyhow::{Context, Result};
use serde::Serialize;
use serde_json::{Map, Value};
use std::{collections::BTreeMap, fmt::Write as _, path::Path};
use url::Url;

use work_budget::WorkBudget;

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
pub(super) struct Reference {
    pub(super) kind: String,
    pub(super) raw: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) resolved_url: Option<String>,
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
    body_expected: bool,
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
    #[serde(skip_serializing_if = "Option::is_none")]
    document_encoding: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    document_base_url: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    document_decode_source: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    document_decode_had_errors: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    document_decode_uncertain: Option<bool>,
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
    #[serde(skip_serializing_if = "Option::is_none")]
    charset: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    parent_document_encoding: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    parent_decode_source: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    parent_decode_uncertain: Option<bool>,
}

fn headers(src: &[NameValue]) -> Vec<HeaderMeta> {
    src.iter()
        .map(|header| HeaderMeta {
            name: header.name.clone(),
            value: header.value.clone(),
        })
        .collect()
}

fn header_value<'a>(headers: &'a [NameValue], name: &str) -> Option<&'a str> {
    headers
        .iter()
        .find(|header| header.name.eq_ignore_ascii_case(name))
        .map(|header| header.value.as_str())
}

fn page_metadata(har: &Har) -> Vec<PageMeta> {
    har.log
        .pages
        .iter()
        .map(|page| PageMeta {
            id: page.id.clone(),
            title: page.title.clone(),
            started_date_time: page.started_date_time.clone(),
        })
        .collect()
}

#[expect(
    clippy::too_many_arguments,
    reason = "materialization keeps the per-resource context explicit at this boundary"
)]
fn materialize_inline_scripts(
    parent_resource_id: usize,
    base_url: &str,
    html: &str,
    inline_base: &str,
    store: &mut ResourceStore<'_>,
    counts: &mut BTreeMap<String, usize>,
    references: &mut Vec<Reference>,
    inline_scripts: &mut Vec<InlineScriptMeta>,
    document_encoding: &str,
    document_decode_source: &str,
    document_decode_uncertain: bool,
) -> Result<()> {
    for (ordinal0, script) in extract_script_tags(html).into_iter().enumerate() {
        let ordinal = ordinal0 + 1;
        let ty = script_type(&script.attrs);
        let src = script.attrs.get("src").cloned();
        let resolved_src = src.as_deref().and_then(|src| resolve_ref(base_url, src));
        if let Some(raw_src) = src.as_ref() {
            if is_executable_script_type(&ty) {
                references.push(Reference {
                    kind: "script_src".into(),
                    raw: raw_src.clone(),
                    resolved_url: resolved_src.clone(),
                });
            }
            inline_scripts.push(InlineScriptMeta {
                parent_resource_id,
                ordinal,
                script_type: ty,
                src,
                resolved_src,
                output_path: None,
                body_bytes: 0,
                sha256: None,
                charset: script.attrs.get("charset").cloned(),
                parent_document_encoding: Some(document_encoding.to_string()),
                parent_decode_source: Some(document_decode_source.to_string()),
                parent_decode_uncertain: Some(document_decode_uncertain),
            });
            continue;
        }

        let body = if is_json_script_type(&ty) {
            format_json_if_possible(script.body.as_bytes())
        } else {
            script.body.into_bytes()
        };
        if body.iter().all(u8::is_ascii_whitespace) {
            continue;
        }
        let ext = inline_script_extension(&ty);
        let desired = format!("{inline_base}.inline/script-{ordinal:03}.{ext}");
        let stored = store.write(&desired, &body)?;
        *counts.entry("inline_scripts".into()).or_insert(0) += 1;
        inline_scripts.push(InlineScriptMeta {
            parent_resource_id,
            ordinal,
            script_type: ty,
            src: None,
            resolved_src: None,
            output_path: Some(stored.path),
            body_bytes: body.len(),
            sha256: Some(stored.sha256),
            charset: script.attrs.get("charset").cloned(),
            parent_document_encoding: Some(document_encoding.to_string()),
            parent_decode_source: Some(document_decode_source.to_string()),
            parent_decode_uncertain: Some(document_decode_uncertain),
        });
    }
    Ok(())
}

fn response_body_expected(method: &str, status: i64) -> bool {
    if method.eq_ignore_ascii_case("HEAD") {
        return false;
    }
    !((100..200).contains(&status) || (300..400).contains(&status) || matches!(status, 204 | 205))
}

const fn response_body_complete(body_expected: bool, network_failed: bool) -> bool {
    !body_expected || !network_failed
}

fn materialize_entry(
    id: usize,
    entry: &HarEntry,
    har_root: &Path,
    store: &mut ResourceStore<'_>,
    counts: &mut BTreeMap<String, usize>,
    inline_scripts: &mut Vec<InlineScriptMeta>,
) -> Result<ResourceMeta> {
    let transport_kind =
        resource_kind(&entry.request.url, &entry.response.content.mime_type).to_string();
    let body = decode_body(
        &entry.response.content,
        entry.response.js_redox_body.as_ref(),
        har_root,
    )
    .with_context(|| format!("entry {id}: {}", entry.request.url))?;
    let body_expected = response_body_expected(&entry.request.method, entry.response.status);
    let body_present = body.is_some();
    let body_complete = response_body_complete(body_expected, entry.failure.is_some());
    let mut kind = transport_kind.clone();
    let mut output_path = None;
    let mut body_bytes = 0;
    let mut sha256 = None;
    let mut reused_body = false;
    let mut references = Vec::new();
    let mut document_encoding = None;
    let mut document_base_url = None;
    let mut document_decode_source = None;
    let mut document_decode_had_errors = None;
    let mut document_decode_uncertain = None;

    if let Some(body) = body {
        body_bytes = body.len();
        kind = refine_resource_kind(
            &transport_kind,
            entry.resource_type.as_deref(),
            &entry.response.content.mime_type,
            &body,
        );
        if kind != transport_kind {
            *counts
                .entry("resources_content_reclassified".into())
                .or_insert(0) += 1;
        }
        if kind == "javascript" && body_complete {
            if let Ok(source) = std::str::from_utf8(&body) {
                references.extend(source_refs(source, &entry.request.url));
            }
        }
        let desired = output_path_for(&entry.request.url, &kind, &entry.response.content.mime_type);
        let stored = store.write(&desired, &body)?;
        let written = stored.path;
        output_path = Some(written.clone());
        reused_body = stored.reused;
        sha256 = Some(stored.sha256);
        if kind == "html" && body_complete {
            let transport_content_type = header_value(&entry.response.headers, "content-type")
                .or_else(|| {
                    (!entry.response.content.mime_type.is_empty())
                        .then_some(entry.response.content.mime_type.as_str())
                });
            let decoded = decode_html(&body, transport_content_type, None);
            document_encoding = Some(decoded.encoding.clone());
            document_base_url = Url::parse(&entry.request.url)
                .ok()
                .map(|url| document_base(&decoded.source, &url).to_string());
            document_decode_source = Some(decoded.decode_source.as_str().to_string());
            document_decode_had_errors = Some(decoded.had_errors);
            document_decode_uncertain = Some(decoded.uncertain);
            let base_url = document_base_url.as_deref().unwrap_or(&entry.request.url);
            for (href, kind) in script_preload_links(&decoded.source) {
                references.push(Reference {
                    kind: kind.into(),
                    resolved_url: resolve_ref(base_url, &href),
                    raw: href,
                });
            }
            // The store maps logical directories to physical directories. Keep
            // the original logical parent and the allocated leaf name so an
            // inline body remains adjacent to its document even after a collision.
            let (logical_parent, _) = desired.rsplit_once('/').context("resource parent")?;
            let (_, physical_leaf) = written.rsplit_once('/').context("resource filename")?;
            let inline_base = format!("{logical_parent}/{physical_leaf}");
            materialize_inline_scripts(
                id,
                document_base_url.as_deref().unwrap_or(&entry.request.url),
                &decoded.source,
                &inline_base,
                store,
                counts,
                &mut references,
                inline_scripts,
                &decoded.encoding,
                decoded.decode_source.as_str(),
                decoded.uncertain,
            )?;
        }
    } else {
        *counts.entry("resources_without_body".into()).or_insert(0) += 1;
    }
    *counts.entry(format!("resource_{kind}")).or_insert(0) += 1;
    if !body_complete {
        *counts.entry("resources_incomplete".into()).or_insert(0) += 1;
    }

    Ok(ResourceMeta {
        id,
        pageref: entry.pageref.clone(),
        started_date_time: entry.started_date_time.clone(),
        time_ms: entry.time,
        method: entry.request.method.clone(),
        url: entry.request.url.clone(),
        status: entry.response.status,
        status_text: entry.response.status_text.clone(),
        mime_type: entry.response.content.mime_type.clone(),
        resource_type: entry.resource_type.clone(),
        declared_size: entry.response.content.size,
        encoding: entry.response.content.encoding.clone(),
        body_expected,
        body_present,
        body_complete,
        body_bytes,
        sha256,
        transport_kind,
        kind,
        network_failure: entry.failure.clone(),
        body_capture: entry.response.js_redox_body_capture.clone(),
        output_path,
        reused_body,
        request_headers: headers(&entry.request.headers),
        response_headers: headers(&entry.response.headers),
        references,
        document_encoding,
        document_base_url,
        document_decode_source,
        document_decode_had_errors,
        document_decode_uncertain,
    })
}

fn build_manifest(
    args: &HarProjectOptions,
    har: Har,
    salvaged: bool,
    parse_error: Option<String>,
    parse_warnings: Vec<String>,
    budget: &WorkBudget,
) -> Result<CaptureManifest> {
    budget.checkpoint()?;
    let pages = page_metadata(&har)
        .into_iter()
        .map(serde_json::to_value)
        .collect::<serde_json::Result<Vec<_>>>()?;
    let mut store = ResourceStore::new(&args.output, budget);
    let mut counts = BTreeMap::new();
    let mut inline_scripts = Vec::new();
    let mut resources = Vec::with_capacity(har.log.entries.len());
    let har_root = args.har.parent().unwrap_or_else(|| Path::new("."));
    for (id, entry) in har.log.entries.into_iter().enumerate() {
        budget.checkpoint()?;
        resources.push(serde_json::to_value(materialize_entry(
            id,
            &entry,
            har_root,
            &mut store,
            &mut counts,
            &mut inline_scripts,
        )?)?);
    }
    counts.insert("resources_total".into(), resources.len());
    counts.insert("pages".into(), pages.len());
    let inline_scripts = inline_scripts
        .into_iter()
        .map(serde_json::to_value)
        .collect::<serde_json::Result<Vec<_>>>()?;
    let mut extra = Map::new();
    extra.insert("har_version".into(), Value::String(har.log.version));
    if let Some(error) = parse_error {
        extra.insert("parse_error".into(), Value::String(error));
    }
    if !parse_warnings.is_empty() {
        extra.insert(
            "parse_warnings".into(),
            serde_json::to_value(parse_warnings)?,
        );
    }
    Ok(CaptureManifest {
        schema: SCHEMA.into(),
        source: CaptureSource {
            kind: "har".into(),
            input: args.har.display().to_string(),
            salvaged,
            extra,
        },
        pages,
        resources,
        inline_scripts,
        counts,
        extra: Map::new(),
    })
}

fn write_project_metadata(args: &HarProjectOptions, manifest: &CaptureManifest) -> Result<()> {
    write_manifest(&args.output.join(MANIFEST_NAME), manifest)?;
    crate::capture_project::write_editor_settings(&args.output)?;
    let mut summary = String::new();
    for (kind, count) in &manifest.counts {
        let _ = writeln!(summary, "- {kind}: {count}");
    }
    crate::report_file::write_text(
        &args.output.join("README.md"),
        &format!(
            "# Capture source project\n\nGenerated from {}.\n\nResponse bodies are preserved by URL under resources/. Inline script bodies are extracted beside their parent HTML. capture-manifest.json keeps capture provenance and discovered script/source-map references.\n\n## Counts\n\n{}",
            crate::report_markdown::code_span(&args.har.to_string_lossy()),
            summary
        ),
    )?;
    Ok(())
}

pub(super) fn materialize_project(
    args: &HarProjectOptions,
    har: Har,
    salvaged: bool,
    parse_error: Option<String>,
    parse_warnings: Vec<String>,
    budget: &WorkBudget,
) -> Result<HarProjectSummary> {
    let manifest = build_manifest(args, har, salvaged, parse_error, parse_warnings, budget)?;
    budget.checkpoint()?;
    write_project_metadata(args, &manifest)?;
    budget.checkpoint()?;
    Ok(HarProjectSummary {
        resources: manifest.resources.len(),
        script_records: manifest.inline_scripts.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::{response_body_complete, response_body_expected};

    #[test]
    fn response_body_expectation_matches_capture_semantics() {
        assert!(!response_body_expected("HEAD", 200));
        assert!(!response_body_expected("head", 404));
        assert!(!response_body_expected("GET", 101));
        assert!(!response_body_expected("GET", 204));
        assert!(!response_body_expected("GET", 205));
        assert!(!response_body_expected("GET", 304));
        assert!(response_body_expected("CONNECT", 200));
        assert!(response_body_expected("CONNECT", 407));
        assert!(response_body_expected("GET", 200));
        assert!(!response_body_expected("POST", 302));
    }

    #[test]
    fn response_body_completion_ignores_failures_when_no_body_is_expected() {
        assert!(response_body_complete(false, true));
        assert!(response_body_complete(false, false));
        assert!(response_body_complete(true, false));
        assert!(!response_body_complete(true, true));
    }
}
