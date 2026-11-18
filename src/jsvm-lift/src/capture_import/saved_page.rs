use crate::{
    browser_decode::{decode_html, DecodedHtml},
    browser_script_types::{inline_script_extension, is_executable_script, script_type_essence},
    capture_project::{
        prepare_project_output, write_manifest, CaptureManifest, CaptureSource, MANIFEST_NAME,
        SCHEMA,
    },
    har_project::{
        html::{extract_script_tags, find_tag_end, parse_attrs},
        resource::resource_kind,
    },
    sha256_hex,
    source_directive::source_directives,
};
use anyhow::{bail, Context, Result};
use encoding_rs::{Encoding, WINDOWS_1252};
use html_escape::decode_html_entities;
use regex::Regex;
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    ffi::OsStr,
    fs,
    path::{Component, Path, PathBuf},
};
use url::Url;
use work_budget::WorkBudget;

const SAVED_ORIGIN: &str = "https://saved-page.invalid/";

#[derive(Debug, Clone, Default)]
pub(super) struct SavedPageOptions {
    pub assets_dir: Option<PathBuf>,
    pub overwrite: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct SavedPageSummary {
    pub(super) resources: usize,
    pub(super) script_records: usize,
}

fn path_text(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

fn canonical_url(relative: &Path) -> Result<String> {
    let mut url = Url::parse(SAVED_ORIGIN)?;
    {
        let mut segments = url
            .path_segments_mut()
            .map_err(|()| anyhow::anyhow!("saved-page base URL cannot be a base"))?;
        segments.clear();
        for component in relative.components() {
            if let Component::Normal(segment) = component {
                let text = segment.to_str().with_context(|| {
                    format!(
                        "saved-page path cannot be represented in UTF-8: {}",
                        relative.display()
                    )
                })?;
                segments.push(text);
            }
        }
    }
    Ok(url.to_string())
}

fn guess_mime(path: &Path) -> String {
    match path
        .extension()
        .and_then(OsStr::to_str)
        .map(str::to_ascii_lowercase)
    {
        Some(extension) if extension == "map" => "application/json".into(),
        Some(extension) if extension == "wasm" => "application/wasm".into(),
        _ => mime_guess::from_path(path)
            .first_raw()
            .unwrap_or("application/octet-stream")
            .to_owned(),
    }
}

fn read_text_lossless(path: &Path) -> Result<Option<String>> {
    let data = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
    if let Some((encoding, bom_len)) = Encoding::for_bom(&data) {
        let (decoded, _, had_errors) = encoding.decode(&data[bom_len..]);
        return Ok((!had_errors).then(|| decoded.into_owned()));
    }

    let head = String::from_utf8_lossy(&data[..data.len().min(8192)]);
    let charset = Regex::new(r#"(?i)charset\s*=\s*[\"']?([A-Za-z0-9._:-]+)"#)?;
    if let Some(label) = charset
        .captures(&head)
        .and_then(|captures| captures.get(1))
        .and_then(|capture| Encoding::for_label(capture.as_str().as_bytes()))
    {
        let (decoded, _, had_errors) = label.decode(&data);
        if !had_errors {
            return Ok(Some(decoded.into_owned()));
        }
    }
    if let Ok(text) = std::str::from_utf8(&data) {
        return Ok(Some(text.to_owned()));
    }
    if data
        .iter()
        .any(|byte| matches!(*byte, 0x81 | 0x8d | 0x8f | 0x90 | 0x9d))
    {
        return Ok(None);
    }
    let (decoded, _, had_errors) = WINDOWS_1252.decode(&data);
    Ok((!had_errors).then(|| decoded.into_owned()))
}

fn clean_ref(raw: &str) -> Option<String> {
    // HTML attributes have already had character references decoded by
    // parse_attrs. Source-map directives are not HTML; decoding them here
    // would be equally incorrect and could bind a different captured URL.
    let cleaned = raw.trim();
    if cleaned.is_empty() || cleaned.starts_with('#') {
        return None;
    }
    if let Ok(parsed) = Url::parse(cleaned) {
        if matches!(
            parsed.scheme(),
            "data" | "blob" | "javascript" | "mailto" | "tel" | "about"
        ) {
            return None;
        }
    }
    Some(cleaned.replace('\\', "/"))
}

fn reference(base: &str, kind: &str, raw: &str) -> Option<Value> {
    let cleaned = clean_ref(raw)?;
    let resolved = Url::parse(base).ok()?.join(&cleaned).ok()?.to_string();
    Some(json!({"kind": kind, "raw": cleaned, "resolved_url": resolved}))
}

fn html_references(html: &str, base: &str) -> Result<Vec<Value>> {
    let pattern = Regex::new(r"(?is)<(script|link|img|iframe|source|video|audio|object|embed)\b")?;
    let mut references = Vec::new();
    for capture in pattern.captures_iter(html) {
        let Some(matched) = capture.get(0) else {
            continue;
        };
        let Some(tag_name) = capture
            .get(1)
            .map(|capture| capture.as_str().to_ascii_lowercase())
        else {
            continue;
        };
        let Some(end) = find_tag_end(html.as_bytes(), matched.end()) else {
            continue;
        };
        let attrs = parse_attrs(&html[matched.start()..=end]);
        let mut candidates = Vec::<(String, String)>::new();
        if tag_name == "script" {
            // Browsers do not fetch src on data-block scripts (including
            // JSON-LD and import maps). Never classify them as executable.
            if is_executable_script(attrs.get("type").map(String::as_str)) {
                if let Some(src) = attrs.get("src").filter(|src| !src.is_empty()) {
                    candidates.push(("script_src".into(), src.clone()));
                }
            }
        } else if tag_name == "link" && attrs.get("href").is_some_and(|href| !href.is_empty()) {
            let rel = attrs.get("rel").map_or("", String::as_str);
            let rel_has = |token: &str| {
                rel.split_ascii_whitespace()
                    .any(|part| part.eq_ignore_ascii_case(token))
            };
            let kind = if rel_has("stylesheet") {
                "stylesheet"
            } else if rel_has("modulepreload")
                || (rel_has("preload")
                    && attrs
                        .get("as")
                        .is_some_and(|value| value.eq_ignore_ascii_case("script")))
            {
                "script_preload"
            } else {
                "link_href"
            };
            if let Some(href) = attrs.get("href") {
                candidates.push((kind.into(), href.clone()));
            }
        } else {
            for attribute in ["src", "data"] {
                if let Some(value) = attrs.get(attribute).filter(|value| !value.is_empty()) {
                    candidates.push((format!("{tag_name}_{attribute}"), value.clone()));
                }
            }
        }
        if let Some(srcset) = attrs.get("srcset") {
            for item in srcset.split(',') {
                if let Some(url) = item.split_whitespace().next().filter(|url| !url.is_empty()) {
                    candidates.push((format!("{tag_name}_srcset"), url.to_owned()));
                }
            }
        }
        for (kind, raw) in candidates {
            if let Some(row) = reference(base, &kind, &raw) {
                references.push(row);
            }
        }
    }
    Ok(references)
}

fn css_source_references(source: &str, base: &str) -> Result<Vec<Value>> {
    let pattern =
        Regex::new(r"(?m)(?://[#@]|/\*[#@])\s*(sourceMappingURL|sourceURL)\s*=\s*([^\s*]+)")?;
    let mut references = Vec::new();
    for capture in pattern.captures_iter(source) {
        let Some(kind) = capture.get(1).map(|value| value.as_str()) else {
            continue;
        };
        let Some(raw) = capture
            .get(2)
            .map(|value| value.as_str().trim_matches(['\'', '"', ';']))
        else {
            continue;
        };
        if let Some(row) = reference(
            base,
            if kind == "sourceMappingURL" {
                "source_map"
            } else {
                "source_url"
            },
            raw,
        ) {
            references.push(row);
        }
    }
    Ok(references)
}

fn js_source_references(source: &str, base: &str) -> Vec<Value> {
    source_directives(source)
        .into_iter()
        .filter_map(|directive| reference(base, &directive.kind, &directive.raw))
        .collect()
}

fn infer_original_url(html: &str) -> Result<Option<String>> {
    let pattern = Regex::new(r"(?is)saved\s+from\s+url=\(\d+\)(.*?)\s*-->")?;
    let Some(candidate) = pattern
        .captures(html)
        .and_then(|captures| captures.get(1))
        .map(|capture| decode_html_entities(capture.as_str().trim()).into_owned())
    else {
        return Ok(None);
    };
    let Ok(url) = Url::parse(&candidate) else {
        return Ok(None);
    };
    Ok(matches!(url.scheme(), "http" | "https").then_some(candidate))
}

fn discover_assets_dir(page: &Path) -> Result<Option<PathBuf>> {
    let parent = page
        .parent()
        .context("saved page has no parent directory")?
        .canonicalize()?;
    let file_name = page
        .file_name()
        .and_then(OsStr::to_str)
        .context("saved page name is not UTF-8")?;
    let stem = page
        .file_stem()
        .and_then(OsStr::to_str)
        .context("saved page stem is not UTF-8")?;
    let candidates = [
        format!("{stem}_files"),
        format!("{stem}.files"),
        format!("{file_name}_files"),
    ];
    let mut seen = HashSet::new();
    for candidate_name in candidates {
        let candidate = parent.join(candidate_name);
        let Ok(metadata) = fs::symlink_metadata(&candidate) else {
            continue;
        };
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            continue;
        }
        let resolved = candidate.canonicalize()?;
        if resolved.parent() != Some(parent.as_path()) || !seen.insert(resolved.clone()) {
            continue;
        }
        return Ok(Some(resolved));
    }
    Ok(None)
}

fn collect_asset_files(root: &Path, budget: &WorkBudget) -> Result<Vec<(PathBuf, PathBuf)>> {
    fn visit(
        root: &Path,
        directory: &Path,
        output: &mut Vec<(PathBuf, PathBuf)>,
        budget: &WorkBudget,
    ) -> Result<()> {
        budget.checkpoint()?;
        for entry in
            fs::read_dir(directory).with_context(|| format!("reading {}", directory.display()))?
        {
            budget.checkpoint()?;
            let entry = entry?;
            let file_type = entry.file_type()?;
            if file_type.is_symlink() {
                continue;
            }
            let path = entry.path();
            if file_type.is_dir() {
                visit(root, &path, output, budget)?;
            } else if file_type.is_file() {
                let resolved = path.canonicalize()?;
                let Ok(relative) = resolved.strip_prefix(root) else {
                    continue;
                };
                output.push((resolved.clone(), relative.to_owned()));
            }
        }
        Ok(())
    }
    let mut output = Vec::new();
    visit(root, root, &mut output, budget)?;
    output.sort_by(|left, right| left.1.cmp(&right.1));
    Ok(output)
}

fn write_copy(source: &Path, destination: &Path) -> Result<Vec<u8>> {
    let data = fs::read(source).with_context(|| format!("reading {}", source.display()))?;
    if let Some(parent) = destination.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(destination, &data).with_context(|| format!("writing {}", destination.display()))?;
    Ok(data)
}

fn index_saved_urls(resources: &[Value]) -> Result<HashMap<String, usize>> {
    let mut by_url = HashMap::with_capacity(resources.len());
    for (index, resource) in resources.iter().enumerate() {
        let url = resource
            .get("url")
            .and_then(Value::as_str)
            .context("saved resource URL missing")?;
        if let Some(previous) = by_url.insert(url.to_owned(), index) {
            bail!("saved resources {previous} and {index} resolve to the same URL: {url}");
        }
    }
    Ok(by_url)
}

fn collect_saved_page_files(
    page: &Path,
    assets: Option<&Path>,
    budget: &WorkBudget,
) -> Result<(PathBuf, Vec<(PathBuf, PathBuf)>)> {
    let page_name = page
        .file_name()
        .context("saved page has no filename")?
        .to_owned();
    let page_rel = PathBuf::from("saved-page").join(&page_name);
    let mut files = vec![(page.to_path_buf(), page_rel.clone())];
    if let Some(assets_root) = assets {
        let assets_name = assets_root
            .file_name()
            .context("assets directory has no name")?;
        for (source, relative) in collect_asset_files(assets_root, budget)? {
            files.push((
                source,
                PathBuf::from("saved-page").join(assets_name).join(relative),
            ));
        }
    }

    Ok((page_rel, files))
}

fn materialize_saved_resources(
    page: &Path,
    output: &Path,
    files: &[(PathBuf, PathBuf)],
    decoded: &DecodedHtml,
    budget: &WorkBudget,
) -> Result<(Vec<Value>, HashMap<PathBuf, u64>)> {
    let mut resources = Vec::<Value>::new();
    let mut rel_to_id = HashMap::<PathBuf, u64>::new();
    for (id, (source, capture_rel)) in files.iter().enumerate() {
        budget.checkpoint()?;
        let resource_id = u64::try_from(id).context("too many saved-page resources")?;
        // Manifest paths must preserve native filenames exactly, never
        // replace path bytes with U+FFFD and alias distinct inputs.
        source.to_str().with_context(|| {
            format!("saved-page source path is not UTF-8: {}", source.display())
        })?;
        let output_rel = PathBuf::from("resources").join(capture_rel);
        let url = canonical_url(capture_rel)?;
        let data = write_copy(source, &output.join(&output_rel))?;
        let mime = guess_mime(source);
        let kind = resource_kind(&url, &mime);
        let mut object = Map::new();
        object.insert("id".into(), json!(resource_id));
        object.insert("pageref".into(), json!("saved-page"));
        object.insert("started_date_time".into(), json!(""));
        object.insert("time_ms".into(), json!(0.0));
        object.insert("method".into(), json!("SAVED"));
        object.insert("url".into(), json!(url));
        object.insert("status".into(), json!(200));
        object.insert("status_text".into(), json!("Saved locally"));
        object.insert("mime_type".into(), json!(mime));
        object.insert("declared_size".into(), json!(data.len()));
        object.insert("encoding".into(), Value::Null);
        object.insert("body_present".into(), json!(true));
        object.insert("body_bytes".into(), json!(data.len()));
        object.insert("sha256".into(), json!(sha256_hex(&data)));
        object.insert("kind".into(), json!(kind));
        object.insert("output_path".into(), json!(path_text(&output_rel)));
        object.insert("reused_body".into(), json!(false));
        object.insert("request_headers".into(), json!([]));
        object.insert("response_headers".into(), json!([]));
        object.insert("references".into(), json!([]));
        object.insert("saved_source_path".into(), json!(path_text(source)));
        if source.as_path() == page {
            object.insert("document_encoding".into(), json!(decoded.encoding.clone()));
            object.insert(
                "document_decode_source".into(),
                json!(decoded.decode_source.as_str()),
            );
            object.insert(
                "document_decode_had_errors".into(),
                json!(decoded.had_errors),
            );
            object.insert("document_decode_uncertain".into(), json!(decoded.uncertain));
        }
        resources.push(Value::Object(object));
        rel_to_id.insert(capture_rel.clone(), resource_id);
    }

    Ok((resources, rel_to_id))
}

fn reconcile_saved_reference_roles(
    resources: &mut [Value],
    page_refs: &[Value],
    budget: &WorkBudget,
) -> Result<()> {
    // A saved-page file path must identify one resource. Reject collisions
    // rather than silently choosing the last matching entry.
    let by_url = index_saved_urls(&resources)?;
    // HTML declarations describe roles, not distinct captured bodies. Gather
    // every role before choosing a stable primary kind for single-kind consumers.
    let mut roles_by_resource = vec![BTreeSet::<&str>::new(); resources.len()];
    for reference in page_refs {
        budget.checkpoint()?;
        let Some(url) = reference.get("resolved_url").and_then(Value::as_str) else {
            continue;
        };
        let Some(&index) = by_url.get(url) else {
            continue;
        };
        match reference.get("kind").and_then(Value::as_str) {
            Some("script_src" | "script_preload") => {
                roles_by_resource[index].insert("javascript");
            }
            Some("stylesheet") => {
                roles_by_resource[index].insert("css");
            }
            _ => {}
        }
    }
    for (resource, roles) in resources.iter_mut().zip(&roles_by_resource) {
        budget.checkpoint()?;
        if roles.is_empty() {
            continue;
        }
        // Prefer JavaScript when both roles are declared, so the same bytes
        // remain indexable as a script. Both independent declarations stay
        // explicit in saved_page_reference_roles and in the page's references.
        let (kind, mime) = if roles.contains("javascript") {
            ("javascript", "application/javascript")
        } else {
            ("css", "text/css")
        };
        resource["kind"] = json!(kind);
        resource["mime_type"] = json!(mime);
        resource["saved_page_reference_roles"] = json!(roles);
    }

    Ok(())
}

fn saved_reference_key(item: &Value) -> (String, String, String) {
    let field = |name| {
        item.get(name)
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_owned()
    };
    (field("kind"), field("raw"), field("resolved_url"))
}

fn collect_saved_resource_references(resources: &mut [Value], budget: &WorkBudget) -> Result<()> {
    for resource in resources.iter_mut() {
        budget.checkpoint()?;
        let Some(kind) = resource.get("kind").and_then(Value::as_str) else {
            continue;
        };
        let parse_javascript = kind == "javascript";
        let parse_css = kind == "css"
            || resource["saved_page_reference_roles"]
                .as_array()
                .is_some_and(|roles| roles.iter().any(|role| role == "css"));
        if !parse_javascript && !parse_css {
            continue;
        }
        let Some(source_path) = resource.get("saved_source_path").and_then(Value::as_str) else {
            continue;
        };
        let Some(source) = read_text_lossless(Path::new(source_path))? else {
            continue;
        };
        let Some(base_url) = resource.get("url").and_then(Value::as_str) else {
            continue;
        };
        let mut items = Vec::new();
        if parse_javascript {
            items.extend(js_source_references(&source, base_url));
        }
        if parse_css {
            items.extend(css_source_references(&source, base_url)?);
        }
        let references = resource
            .get_mut("references")
            .and_then(Value::as_array_mut)
            .context("saved resource references are not an array")?;
        let mut known = references
            .iter()
            .map(saved_reference_key)
            .collect::<HashSet<_>>();
        for item in items {
            if known.insert(saved_reference_key(&item)) {
                references.push(item);
            }
        }
    }

    Ok(())
}

fn materialize_saved_inline_scripts(
    page_text: &str,
    page_rel: &Path,
    page_url: &str,
    page_id: u64,
    decoded: &DecodedHtml,
    output: &Path,
    budget: &WorkBudget,
) -> Result<Vec<Value>> {
    let mut inline_scripts = Vec::<Value>::new();
    let mut inline_seen = HashMap::<String, String>::new();
    budget.checkpoint()?;
    for (offset, script) in extract_script_tags(&page_text).into_iter().enumerate() {
        budget.checkpoint()?;
        let ordinal = offset + 1;
        let script_type = script_type_essence(script.attrs.get("type").map(String::as_str));
        let src = script.attrs.get("src").and_then(|value| clean_ref(value));
        if let Some(src) = src {
            let resolved = Url::parse(&page_url)?.join(&src)?.to_string();
            inline_scripts.push(json!({
                "parent_resource_id": page_id,
                "ordinal": ordinal,
                "script_type": script_type,
                "src": src,
                "resolved_src": resolved,
                "output_path": null,
                "body_bytes": 0,
                "sha256": null,
                "charset": script.attrs.get("charset").cloned(),
                "parent_document_encoding": decoded.encoding,
                "parent_decode_source": decoded.decode_source.as_str(),
                "parent_decode_uncertain": decoded.uncertain,
            }));
            continue;
        }
        if script.body.trim().is_empty() {
            continue;
        }
        let bytes = script.body.as_bytes();
        let extension = inline_script_extension(Some(&script_type));
        let digest = sha256_hex(bytes);
        let desired = PathBuf::from("resources")
            .join(page_rel.parent().unwrap_or_else(|| Path::new("")))
            .join(format!(
                "{}.inline",
                page_rel
                    .file_name()
                    .and_then(OsStr::to_str)
                    .unwrap_or("page")
            ))
            .join(format!("script-{ordinal:03}.{extension}"));
        let mut output_rel = desired.clone();
        if let Some(existing) = inline_seen.get(&path_text(&output_rel)) {
            if existing != &digest {
                let stem = desired
                    .file_stem()
                    .and_then(OsStr::to_str)
                    .unwrap_or("script");
                output_rel =
                    desired.with_file_name(format!("{stem}-{}.{}", &digest[..10], extension));
            }
        }
        let output_key = path_text(&output_rel);
        if let std::collections::hash_map::Entry::Vacant(entry) = inline_seen.entry(output_key) {
            if let Some(parent) = output.join(&output_rel).parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(output.join(&output_rel), bytes)?;
            entry.insert(digest.clone());
        }
        inline_scripts.push(json!({
            "parent_resource_id": page_id,
            "ordinal": ordinal,
            "script_type": script_type,
            "src": null,
            "resolved_src": null,
            "output_path": path_text(&output_rel),
            "body_bytes": bytes.len(),
            "sha256": digest,
            "charset": script.attrs.get("charset").cloned(),
            "parent_document_encoding": decoded.encoding,
            "parent_decode_source": decoded.decode_source.as_str(),
            "parent_decode_uncertain": decoded.uncertain,
        }));
    }

    Ok(inline_scripts)
}

fn saved_page_manifest(
    page: &Path,
    page_text: &str,
    assets: Option<&Path>,
    resources: Vec<Value>,
    inline_scripts: Vec<Value>,
    budget: &WorkBudget,
) -> Result<CaptureManifest> {
    // Count the final classified resources, not the pre-reference filename
    // guesses (which can differ for e.g. a .bin used as a script).
    let mut counts = BTreeMap::<String, usize>::new();
    for resource in &resources {
        budget.checkpoint()?;
        let kind = resource["kind"]
            .as_str()
            .context("saved resource kind missing")?;
        *counts.entry(kind.to_owned()).or_default() += 1;
    }
    counts.insert("resources_total".into(), resources.len());
    counts.insert("pages".into(), 1);
    counts.insert(
        "inline_scripts".into(),
        inline_scripts
            .iter()
            .filter(|script| !script["output_path"].is_null())
            .count(),
    );
    let original_url = infer_original_url(&page_text)?;
    let mut source_extra = Map::new();
    source_extra.insert("parse_error".into(), Value::Null);
    source_extra.insert(
        "original_page_url".into(),
        original_url.clone().map_or(Value::Null, Value::String),
    );
    source_extra.insert(
        "assets_dir".into(),
        assets
            .as_ref()
            .map_or(Value::Null, |path| Value::String(path_text(path))),
    );
    let manifest = CaptureManifest {
        schema: SCHEMA.into(),
        source: CaptureSource {
            kind: if assets.is_some() {
                "saved_page_complete"
            } else {
                "saved_page_html"
            }
            .into(),
            input: path_text(&page),
            salvaged: false,
            extra: source_extra,
        },
        pages: vec![json!({
            "id": "saved-page",
            "title": page.file_stem().and_then(OsStr::to_str).unwrap_or_default(),
            "started_date_time": "",
            "original_url": original_url,
        })],
        resources,
        inline_scripts,
        counts,
        extra: Map::new(),
    };

    Ok(manifest)
}

pub(super) fn import_saved_page(
    page: &Path,
    output: &Path,
    options: &SavedPageOptions,
    budget: &WorkBudget,
) -> Result<SavedPageSummary> {
    budget.checkpoint()?;
    let page = page
        .canonicalize()
        .with_context(|| format!("saved page HTML does not exist: {}", page.display()))?;
    if !page.is_file() {
        bail!("saved page HTML does not exist: {}", page.display());
    }
    let output = if output.is_absolute() {
        output.to_owned()
    } else {
        std::env::current_dir()?.join(output)
    };
    prepare_project_output(&output, options.overwrite)?;

    let page_bytes = fs::read(&page)?;
    let decoded = decode_html(&page_bytes, None, None);
    budget.checkpoint()?;
    let page_text = &decoded.source;
    let assets = if let Some(explicit) = &options.assets_dir {
        let resolved = explicit
            .canonicalize()
            .with_context(|| format!("assets directory does not exist: {}", explicit.display()))?;
        if !resolved.is_dir() {
            bail!("assets directory does not exist: {}", resolved.display());
        }
        Some(resolved)
    } else {
        discover_assets_dir(&page)?
    };

    if let Some(root) = assets.as_ref() {
        root.to_str().with_context(|| {
            format!(
                "saved-page assets directory is not UTF-8: {}",
                root.display()
            )
        })?;
    }

    let (page_rel, files) = collect_saved_page_files(&page, assets.as_deref(), budget)?;
    let (mut resources, rel_to_id) =
        materialize_saved_resources(&page, &output, &files, &decoded, budget)?;
    let page_id = *rel_to_id
        .get(&page_rel)
        .context("saved page resource disappeared")?;
    let page_index =
        usize::try_from(page_id).context("saved page resource ID does not fit usize")?;
    let page_url = resources[page_index]["url"]
        .as_str()
        .context("saved page resource URL missing")?
        .to_owned();
    budget.checkpoint()?;
    let page_refs = html_references(page_text, &page_url)?;
    budget.checkpoint()?;
    resources[page_index]["references"] = Value::Array(page_refs.clone());

    reconcile_saved_reference_roles(&mut resources, &page_refs, budget)?;
    collect_saved_resource_references(&mut resources, budget)?;
    let inline_scripts = materialize_saved_inline_scripts(
        page_text, &page_rel, &page_url, page_id, &decoded, &output, budget,
    )?;
    let manifest = saved_page_manifest(
        &page,
        page_text,
        assets.as_deref(),
        resources,
        inline_scripts,
        budget,
    )?;
    budget.checkpoint()?;
    write_manifest(&output.join(MANIFEST_NAME), &manifest)?;
    budget.checkpoint()?;
    fs::create_dir_all(output.join(".vscode"))?;
    fs::write(
        output.join(".vscode/settings.json"),
        "{\n  \"editor.maxTokenizationLineLength\": 200000\n}\n",
    )?;

    Ok(SavedPageSummary {
        resources: manifest.resources.len(),
        script_records: manifest.inline_scripts.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reference_cleaning_rejects_non_network_inline_schemes() {
        assert!(clean_ref(" data:text/plain,hello ").is_none());
        assert!(clean_ref("javascript:alert(1)").is_none());
        assert_eq!(clean_ref(" ./a&amp;b.js ").as_deref(), Some("./a&amp;b.js"));
    }

    #[test]
    fn inert_script_sources_and_invalid_link_rel_tokens_do_not_promote_assets() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let root = temp.path();
        let page = root.join("Example.html");
        let assets = root.join("Example_files");
        fs::create_dir_all(&assets)?;
        fs::write(
            &page,
            r#"<script type="application/ld+json" src="./Example_files/data.bin"></script>
            <script type="text/x-template" src="./Example_files/template.bin"></script>
            <script type="module" src="./Example_files/runtime.bin"></script>
            <script src="./Example_files/amp&amp;amp;name.bin"></script>
            <link rel="modulepreload" href="./Example_files/module.bin">
            <link rel="notstylesheet" href="./Example_files/false-style.bin">
            <link rel="stylesheet alternate" href="./Example_files/style.bin">
            <link rel="notmodulepreload" href="./Example_files/false-preload.bin">
            <link rel="PRELOAD" as="SCRIPT" href="./Example_files/preload.bin">"#,
        )?;
        for name in [
            "data.bin",
            "template.bin",
            "runtime.bin",
            "amp&amp;name.bin",
            "amp&name.bin",
            "module.bin",
            "false-style.bin",
            "style.bin",
            "false-preload.bin",
            "preload.bin",
        ] {
            fs::write(assets.join(name), "var x = 1;")?;
        }

        let project = root.join("capture");
        let budget = WorkBudget::new(
            "saved-page-classification",
            work_budget::BudgetLimits::unlimited(),
        );
        import_saved_page(&page, &project, &SavedPageOptions::default(), &budget)?;
        let manifest = crate::capture_project::load_manifest(&project)?;
        let resource = |name: &str| {
            manifest
                .resources
                .iter()
                .find(|resource| {
                    resource["url"]
                        .as_str()
                        .is_some_and(|url| url.rsplit('/').next() == Some(name))
                })
                .with_context(|| format!("missing fixture resource: {name}"))
        };
        for name in [
            "data.bin",
            "template.bin",
            "false-style.bin",
            "false-preload.bin",
            "amp&name.bin",
        ] {
            assert_eq!(
                resource(name)?["kind"],
                "binary",
                "{name} must remain inert"
            );
        }
        for name in [
            "runtime.bin",
            "amp&amp;name.bin",
            "module.bin",
            "preload.bin",
        ] {
            assert_eq!(
                resource(name)?["kind"],
                "javascript",
                "{name} must be JavaScript"
            );
        }
        assert_eq!(resource("style.bin")?["kind"], "css");
        assert_eq!(resource("amp&name.bin")?["kind"], "binary");
        let page_record = resource("Example.html")?;
        let references = page_record["references"]
            .as_array()
            .context("missing page references")?;
        assert!(!references.iter().any(|reference| {
            reference["kind"] == "script_src"
                && reference["resolved_url"]
                    .as_str()
                    .is_some_and(|url| url.ends_with("data.bin") || url.ends_with("template.bin"))
        }));
        assert!(references.iter().any(|reference| {
            reference["kind"] == "script_src"
                && reference["resolved_url"]
                    .as_str()
                    .is_some_and(|url| url.ends_with("runtime.bin"))
        }));
        assert!(references.iter().any(|reference| {
            reference["raw"] == "./Example_files/amp&amp;name.bin"
                && reference["resolved_url"]
                    .as_str()
                    .is_some_and(|url| url.ends_with("amp&amp;name.bin"))
        }));
        Ok(())
    }

    #[test]
    fn duplicate_canonical_saved_urls_are_rejected() -> Result<()> {
        let url = "https://saved-page.invalid/saved-page/example.js";
        let resources = vec![json!({"url":url,"id":3}), json!({"url":url,"id":4})];
        let Err(error) = index_saved_urls(&resources) else {
            bail!("duplicate saved-page URLs must never select a single resource");
        };
        assert!(error.to_string().contains("resources 0 and 1"));
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn non_utf8_saved_path_cannot_alias_a_valid_filename() {
        use std::os::unix::ffi::OsStringExt;
        let bad = PathBuf::from("saved-page")
            .join(std::ffi::OsString::from_vec(b"asset-\xff.bin".to_vec()));
        assert!(canonical_url(&bad).is_err());
    }

    #[test]
    fn canonical_saved_urls_are_browser_safe() -> Result<()> {
        assert_eq!(
            canonical_url(Path::new("saved-page/a b.js"))?,
            "https://saved-page.invalid/saved-page/a%20b.js"
        );
        assert_ne!(
            canonical_url(Path::new("saved-page/a b.js"))?,
            canonical_url(Path::new("saved-page/a%20b.js"))?,
            "escaped and literal source names must remain distinguishable"
        );
        Ok(())
    }
}
