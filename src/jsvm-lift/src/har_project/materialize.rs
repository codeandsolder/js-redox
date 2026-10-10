use super::html::{
    extract_script_tags, inline_script_extension, is_executable_script_type, is_json_script_type,
    resolve_ref, script_type, source_refs,
};
use super::parse::{Har, HarEntry, NameValue};
use super::resource::{
    decode_body, format_json_if_possible, output_path_for, refine_resource_kind, resource_kind,
    write_resource,
};
use super::{HarProjectOptions, HarProjectSummary};
use crate::sha256_hex;
use anyhow::{Context, Result};
use serde::Serialize;
use std::{
    collections::{BTreeMap, HashMap},
    fmt::Write as _,
    fs,
    path::Path,
};

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

fn headers(src: &[NameValue]) -> Vec<HeaderMeta> {
    src.iter()
        .map(|header| HeaderMeta {
            name: header.name.clone(),
            value: header.value.clone(),
        })
        .collect()
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

#[allow(clippy::too_many_arguments)]
fn materialize_inline_scripts(
    parent_resource_id: usize,
    base_url: &str,
    html: &str,
    written: &str,
    output_root: &Path,
    seen: &mut HashMap<String, String>,
    counts: &mut BTreeMap<String, usize>,
    references: &mut Vec<Reference>,
    inline_scripts: &mut Vec<InlineScriptMeta>,
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
        let desired = format!("{written}.inline/script-{ordinal:03}.{ext}");
        let (script_path, _) = write_resource(output_root, desired, &body, seen)?;
        *counts.entry("inline_scripts".into()).or_insert(0) += 1;
        inline_scripts.push(InlineScriptMeta {
            parent_resource_id,
            ordinal,
            script_type: ty,
            src: None,
            resolved_src: None,
            output_path: Some(script_path),
            body_bytes: body.len(),
            sha256: Some(sha256_hex(&body)),
        });
    }
    Ok(())
}

fn materialize_entry(
    id: usize,
    entry: &HarEntry,
    har_root: &Path,
    output_root: &Path,
    seen: &mut HashMap<String, String>,
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
    let body_present = body.is_some();
    let body_complete = entry.failure.is_none();
    let mut kind = transport_kind.clone();
    let mut output_path = None;
    let mut body_bytes = 0;
    let mut sha256 = None;
    let mut reused_body = false;
    let mut references = Vec::new();

    if let Some(body) = body {
        body_bytes = body.len();
        sha256 = Some(sha256_hex(&body));
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
        let (written, reused) = write_resource(output_root, desired, &body, seen)?;
        output_path = Some(written.clone());
        reused_body = reused;
        if kind == "html" && body_complete {
            if let Ok(html) = std::str::from_utf8(&body) {
                materialize_inline_scripts(
                    id,
                    &entry.request.url,
                    html,
                    &written,
                    output_root,
                    seen,
                    counts,
                    &mut references,
                    inline_scripts,
                )?;
            }
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
    })
}

fn build_manifest(
    args: &HarProjectOptions,
    har: Har,
    salvaged: bool,
    parse_error: Option<String>,
) -> Result<ProjectManifest> {
    let pages = page_metadata(&har);
    let mut seen = HashMap::new();
    let mut counts = BTreeMap::new();
    let mut inline_scripts = Vec::new();
    let mut resources = Vec::with_capacity(har.log.entries.len());
    let har_root = args.har.parent().unwrap_or_else(|| Path::new("."));
    for (id, entry) in har.log.entries.iter().enumerate() {
        resources.push(materialize_entry(
            id,
            entry,
            har_root,
            &args.output,
            &mut seen,
            &mut counts,
            &mut inline_scripts,
        )?);
    }
    counts.insert("resources_total".into(), resources.len());
    counts.insert("pages".into(), pages.len());
    Ok(ProjectManifest {
        schema: "capture-project/v1",
        source: CaptureSource {
            kind: "har",
            input: args.har.display().to_string(),
            har_version: har.log.version,
            salvaged,
            parse_error,
        },
        pages,
        resources,
        inline_scripts,
        counts,
    })
}

fn write_project_metadata(args: &HarProjectOptions, manifest: &ProjectManifest) -> Result<()> {
    fs::write(
        args.output.join("capture-manifest.json"),
        format!("{}\n", serde_json::to_string_pretty(manifest)?),
    )?;
    fs::create_dir_all(args.output.join(".vscode"))?;
    fs::write(
        args.output.join(".vscode/settings.json"),
        "{\n  \"editor.maxTokenizationLineLength\": 200000\n}\n",
    )?;
    let mut summary = String::new();
    for (kind, count) in &manifest.counts {
        let _ = writeln!(summary, "- {kind}: {count}");
    }
    fs::write(
        args.output.join("README.md"),
        format!(
            "# Capture source project\n\nGenerated from {}.\n\nResponse bodies are preserved by URL under resources/. Inline script bodies are extracted beside their parent HTML. capture-manifest.json keeps capture provenance and discovered script/source-map references.\n\n## Counts\n\n{}",
            args.har.display(),
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
) -> Result<HarProjectSummary> {
    let manifest = build_manifest(args, har, salvaged, parse_error)?;
    write_project_metadata(args, &manifest)?;
    Ok(HarProjectSummary {
        resources: manifest.resources.len(),
        script_records: manifest.inline_scripts.len(),
        counts: manifest.counts,
    })
}
