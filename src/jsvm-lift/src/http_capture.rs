//! Lightweight HTTP-root acquisition for the existing capture-project pipeline.
//! This does not run JavaScript. It walks declared HTML scripts, module imports,
//! static worker references and source directives, then emits a normal HAR.
use crate::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    browser_decode::decode_html,
    browser_script_types::is_executable_script,
    har_project::html::{extract_script_tags, find_tag_end, parse_attrs},
    js_refs::extract_js_references,
    project_js_refs::{merge_import_map, parse_import_map, resolve_with_import_map, ImportMap},
};
use anyhow::{bail, ensure, Context, Result};
use base64::Engine;
use reqwest::{
    blocking::Client,
    header::{ACCEPT, ACCEPT_LANGUAGE, CONTENT_TYPE, REFERER},
};
use serde::Serialize;
use serde_json::{json, Value};
use std::{
    collections::{BTreeSet, VecDeque},
    fs,
    io::Read,
    path::Path,
    time::Duration,
};
use url::Url;

#[derive(Debug, Clone, Copy)]
pub struct HttpCaptureLimits {
    pub max_resources: usize,
    pub max_resource_bytes: usize,
    pub max_total_bytes: usize,
}

impl Default for HttpCaptureLimits {
    fn default() -> Self {
        Self {
            max_resources: 128,
            max_resource_bytes: 8 * 1024 * 1024,
            max_total_bytes: 64 * 1024 * 1024,
        }
    }
}

#[derive(Debug, Serialize)]
pub struct HttpCaptureSummary {
    pub requested_url: String,
    pub final_url: String,
    pub resources: usize,
    pub failed_resources: usize,
    pub bytes: usize,
    pub pending_resources: usize,
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Document,
    Script,
    Asset,
}

impl Kind {
    const fn resource_type(self) -> &'static str {
        match self {
            Self::Document => "document",
            Self::Script => "script",
            Self::Asset => "other",
        }
    }
}

#[derive(Debug)]
struct Pending {
    url: Url,
    referer: Option<Url>,
    kind: Kind,
}

fn fetchable_url(url: Url) -> Option<Url> {
    matches!(url.scheme(), "http" | "https").then_some(url)
}

fn queue_url(
    queue: &mut VecDeque<Pending>,
    known: &mut BTreeSet<String>,
    url: Url,
    referer: &Url,
    kind: Kind,
) {
    let Some(mut url) = fetchable_url(url) else {
        return;
    };
    url.set_fragment(None);
    if known.insert(url.as_str().to_owned()) {
        queue.push_back(Pending {
            url,
            referer: Some(referer.clone()),
            kind,
        });
    }
}

fn document_base(html: &str, final_url: &Url) -> Url {
    let lower = html.to_ascii_lowercase();
    let mut from = 0;
    while let Some(relative) = lower[from..].find("<base") {
        let start = from + relative;
        if !html
            .as_bytes()
            .get(start + 5)
            .is_some_and(|c| c.is_ascii_whitespace() || *c == b'>')
        {
            from = start + 5;
            continue;
        }
        let Some(end) = find_tag_end(html.as_bytes(), start + 5) else {
            break;
        };
        let attrs = parse_attrs(&html[start..=end]);
        if let Some(href) = attrs.get("href") {
            if let Ok(candidate) = final_url.join(href) {
                if let Some(url) = fetchable_url(candidate) {
                    return url;
                }
            }
        }
        from = end + 1;
    }
    final_url.clone()
}

fn link_script_urls(html: &str) -> Vec<String> {
    let lower = html.to_ascii_lowercase();
    let mut from = 0;
    let mut urls = Vec::new();
    while let Some(relative) = lower[from..].find("<link") {
        let start = from + relative;
        if !html
            .as_bytes()
            .get(start + 5)
            .is_some_and(|c| c.is_ascii_whitespace() || *c == b'>')
        {
            from = start + 5;
            continue;
        }
        let Some(end) = find_tag_end(html.as_bytes(), start + 5) else {
            break;
        };
        let attrs = parse_attrs(&html[start..=end]);
        let rel = attrs.get("rel").map(String::as_str).unwrap_or_default();
        let modulepreload = rel
            .split_ascii_whitespace()
            .any(|word| word.eq_ignore_ascii_case("modulepreload"));
        let script_preload = rel
            .split_ascii_whitespace()
            .any(|word| word.eq_ignore_ascii_case("preload"))
            && attrs
                .get("as")
                .is_some_and(|value| value.eq_ignore_ascii_case("script"));
        if modulepreload || script_preload {
            if let Some(url) = attrs.get("href") {
                urls.push(url.clone());
            }
        }
        from = end + 1;
    }
    urls
}

fn add_code_references(
    source: &str,
    from: &Url,
    import_map: &ImportMap,
    queue: &mut VecDeque<Pending>,
    known: &mut BTreeSet<String>,
    warnings: &mut Vec<String>,
    budgets: &AnalysisBudgets,
) {
    let budget = budgets.operation(AnalysisOperation::ReferenceScan, from.as_str());
    let references = match extract_js_references(source, &budget) {
        Ok(refs) => refs,
        Err(error) => {
            warnings.push(format!("{}: JavaScript reference parse: {error}", from));
            return;
        }
    };
    for reference in references {
        let kind = match reference.kind.as_str() {
            "import_static"
            | "import_dynamic"
            | "reexport_named"
            | "reexport_all"
            | "worker"
            | "shared_worker"
            | "service_worker_register"
            | "import_scripts"
            | "require" => Kind::Script,
            "module_url" => Kind::Asset,
            _ => continue,
        };
        let resolved =
            resolve_with_import_map(Some(from.as_str()), &reference.specifier, Some(import_map));
        if let Some(raw_url) = resolved.get("resolved_url").and_then(Value::as_str) {
            if let Ok(url) = Url::parse(raw_url) {
                queue_url(queue, known, url, from, kind);
            }
        } else if reference.kind != "require" {
            warnings.push(format!(
                "{}: unresolved {} {}",
                from, reference.kind, reference.specifier
            ));
        }
    }
}

fn add_document_references(
    html: &str,
    final_url: &Url,
    queue: &mut VecDeque<Pending>,
    known: &mut BTreeSet<String>,
    import_map: &mut ImportMap,
    warnings: &mut Vec<String>,
    budgets: &AnalysisBudgets,
) {
    let base = document_base(html, final_url);
    let tags = extract_script_tags(html);
    // Import maps are document-level, including maps following module tags.
    for tag in &tags {
        if tag
            .attrs
            .get("type")
            .is_some_and(|ty| ty.trim().eq_ignore_ascii_case("importmap"))
        {
            match serde_json::from_str::<Value>(&tag.body) {
                Ok(payload) => {
                    let parsed = parse_import_map(base.as_str(), &payload, warnings);
                    *import_map = merge_import_map(import_map, &parsed);
                }
                Err(error) => warnings.push(format!("{}: import map: {error}", final_url)),
            }
        }
    }
    for tag in tags {
        if !is_executable_script(tag.attrs.get("type").map(String::as_str)) {
            continue;
        }
        if let Some(src) = tag.attrs.get("src") {
            if let Ok(url) = base.join(src) {
                queue_url(queue, known, url, final_url, Kind::Script);
            }
        } else if !tag.body.trim().is_empty() {
            add_code_references(
                &tag.body, &base, import_map, queue, known, warnings, budgets,
            );
        }
    }
    for href in link_script_urls(html) {
        if let Ok(url) = base.join(&href) {
            queue_url(queue, known, url, final_url, Kind::Script);
        }
    }
}

fn har_entry(
    requested_url: &Url,
    actual_url: &Url,
    kind: Kind,
    status: u16,
    mime: &str,
    body: &[u8],
    referer: Option<&Url>,
) -> Value {
    let request_headers = referer.map_or_else(Vec::new, |url| {
        vec![json!({"name":"Referer","value":url.as_str()})]
    });
    json!({
        "pageref": "page_0",
        "_resourceType": kind.resource_type(),
        "request": {"method":"GET","url":actual_url.as_str(),"headers":request_headers,
            "_requestedUrl":requested_url.as_str()},
        "response": {
            "status":status,
            "statusText":"",
            "headers":[{"name":"Content-Type","value":mime}],
            "content":{"size":body.len(),"mimeType":mime,
                "encoding":"base64",
                "text":base64::engine::general_purpose::STANDARD.encode(body)}
        }
    })
}

/// Obtain a static HTTP graph and write its captured responses in standard HAR form.
///
/// Fails if the root HTML cannot be fetched. Individual dependency failures are
/// represented in the HAR and in the returned summary without aborting the graph.
pub fn capture_url_to_har(
    requested: &str,
    har_path: &Path,
    limits: HttpCaptureLimits,
) -> Result<HttpCaptureSummary> {
    ensure!(
        limits.max_resources > 0 && limits.max_resource_bytes > 0 && limits.max_total_bytes > 0,
        "HTTP capture limits must be positive"
    );
    let root = Url::parse(requested).context("expected a full http(s) URL")?;
    ensure!(
        fetchable_url(root.clone()).is_some(),
        "only http(s) URLs are supported"
    );
    let client = Client::builder()
        .cookie_store(true)
        .redirect(reqwest::redirect::Policy::limited(10))
        .user_agent("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")
        .timeout(Duration::from_secs(15))
        .build()?;
    let mut queue = VecDeque::from([Pending {
        url: root.clone(),
        referer: None,
        kind: Kind::Document,
    }]);
    let mut known = BTreeSet::from([root.as_str().to_owned()]);
    let mut entries = Vec::new();
    let mut warnings = Vec::new();
    let mut failures = 0_usize;
    let mut total_bytes = 0_usize;
    let mut final_root = None;
    let mut import_map = ImportMap::default();
    let budgets = AnalysisBudgets::standard("http-static-capture");

    while let Some(pending) = queue.pop_front() {
        if entries.len() >= limits.max_resources || total_bytes >= limits.max_total_bytes {
            queue.push_front(pending);
            break;
        }
        let mut request = client
            .get(pending.url.clone())
            .header(
                ACCEPT,
                if pending.kind == Kind::Document {
                    "text/html,application/xhtml+xml;q=0.9,*/*;q=0.8"
                } else {
                    "*/*"
                },
            )
            .header(ACCEPT_LANGUAGE, "en-US,en;q=0.8");
        if let Some(referrer) = &pending.referer {
            request = request.header(REFERER, referrer.as_str());
        }
        let outcome: Result<(Url, u16, String, Vec<u8>)> = (|| {
            let mut response = request
                .send()
                .with_context(|| format!("GET {}", pending.url))?;
            let final_url = response.url().clone();
            let status = response.status().as_u16();
            let mime = response
                .headers()
                .get(CONTENT_TYPE)
                .and_then(|value| value.to_str().ok())
                .unwrap_or(if pending.kind == Kind::Script {
                    "application/javascript"
                } else {
                    "application/octet-stream"
                })
                .to_owned();
            let left = limits.max_total_bytes.saturating_sub(total_bytes);
            let cap = limits.max_resource_bytes.min(left);
            let mut body = Vec::new();
            response
                .take(u64::try_from(cap)?.saturating_add(1))
                .read_to_end(&mut body)?;
            ensure!(
                body.len() <= cap,
                "response exceeds HTTP capture byte limit"
            );
            Ok((final_url, status, mime, body))
        })();

        match outcome {
            Ok((actual_url, status, mime, body)) => {
                known.insert(actual_url.as_str().to_owned());
                if pending.kind == Kind::Document {
                    final_root = Some(actual_url.clone());
                    ensure!(
                        (200..300).contains(&status),
                        "root document returned HTTP {status}"
                    );
                    let decoded = decode_html(&body, Some(&mime), None);
                    add_document_references(
                        &decoded.source,
                        &actual_url,
                        &mut queue,
                        &mut known,
                        &mut import_map,
                        &mut warnings,
                        &budgets,
                    );
                } else if (200..300).contains(&status) && pending.kind == Kind::Script {
                    // Browser JS text decoder handles BOMs and legacy charset responses.
                    let decoded = crate::browser_decode::decode_script(
                        &body,
                        crate::browser_decode::ScriptDecodeContext::classic_unknown(),
                    );
                    add_code_references(
                        &decoded.source,
                        &actual_url,
                        &import_map,
                        &mut queue,
                        &mut known,
                        &mut warnings,
                        &budgets,
                    );
                }
                total_bytes += body.len();
                entries.push(har_entry(
                    &pending.url,
                    &actual_url,
                    pending.kind,
                    status,
                    &mime,
                    &body,
                    pending.referer.as_ref(),
                ));
            }
            Err(error) => {
                if pending.kind == Kind::Document {
                    return Err(error).context("could not acquire root document");
                }
                failures += 1;
                warnings.push(format!("{}: {error:#}", pending.url));
                let mut failure = har_entry(
                    &pending.url,
                    &pending.url,
                    pending.kind,
                    0,
                    "",
                    &[],
                    pending.referer.as_ref(),
                );
                failure["response"]["content"]["text"] = Value::Null;
                failure["_failure"] = json!({"errorText":error.to_string()});
                entries.push(failure);
            }
        }
    }
    let final_url = final_root.context("root document missing")?;
    let summary = HttpCaptureSummary {
        requested_url: root.to_string(),
        final_url: final_url.to_string(),
        resources: entries.len(),
        failed_resources: failures,
        bytes: total_bytes,
        pending_resources: queue.len(),
        warnings,
    };
    let har = json!({"log":{"version":"1.2","creator":{"name":"js-redox","version":"1"},
        "pages":[{"id":"page_0","title":final_url.as_str(),"startedDateTime":""}],
        "entries":entries,
        "_httpStaticCapture":&summary}});
    if let Some(parent) = har_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(har_path, serde_json::to_vec_pretty(&har)?)
        .with_context(|| format!("writing {}", har_path.display()))?;
    Ok(summary)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fetches_real_http_root_and_transitive_module() -> Result<()> {
        use std::{io::Write as _, net::TcpListener, thread, time::Instant};
        let listener = TcpListener::bind("127.0.0.1:0")?;
        let addr = listener.local_addr()?;
        listener.set_nonblocking(true)?;
        let server = thread::spawn(move || -> Result<usize> {
            let mut served = 0;
            let deadline = Instant::now() + Duration::from_secs(6);
            while served < 3 && Instant::now() < deadline {
                let (mut stream, _) = match listener.accept() {
                    Ok(pair) => pair,
                    Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(10));
                        continue;
                    }
                    Err(error) => return Err(error.into()),
                };
                stream.set_read_timeout(Some(Duration::from_secs(1)))?;
                let mut request = [0_u8; 4096];
                let count = stream.read(&mut request)?;
                let text = String::from_utf8_lossy(&request[..count]);
                let (mime, body) = if text.starts_with("GET /entry.js ") {
                    (
                        "application/javascript",
                        "import './dep.js'; console.log(1);",
                    )
                } else if text.starts_with("GET /dep.js ") {
                    ("application/javascript", "export const answer=42;")
                } else {
                    (
                        "text/html",
                        "<!doctype html><script type='module' src='/entry.js'></script>",
                    )
                };
                write!(stream, "HTTP/1.1 200 OK\r\nContent-Type: {mime}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}", body.len())?;
                served += 1;
            }
            Ok(served)
        });
        let tmp = tempfile::tempdir()?;
        let har = tmp.path().join("capture.har");
        let summary = capture_url_to_har(
            &format!("http://{addr}/"),
            &har,
            HttpCaptureLimits::default(),
        )?;
        let served = server
            .join()
            .map_err(|_| anyhow::anyhow!("fixture HTTP server panicked"))??;
        assert_eq!(served, 3);
        assert_eq!(summary.resources, 3);
        assert_eq!(summary.failed_resources, 0);
        let document: Value = serde_json::from_slice(&fs::read(har)?)?;
        let entries = document["log"]["entries"]
            .as_array()
            .context("HAR entries")?;
        assert_eq!(entries.len(), 3);
        assert!(entries.iter().any(|entry| entry["request"]["url"]
            .as_str()
            .is_some_and(|url| url.ends_with("/dep.js"))));
        Ok(())
    }

    #[test]
    fn html_base_links_and_import_maps() -> Result<()> {
        let html = r#"<base href="/app/"><link rel="modulepreload" href="chunk.js">
          <script type="importmap">{"imports":{"lib":"./lib.js"}}</script>
          <script type="module">import "lib"; import("./later.js");</script>
          <script src="main.js"></script>"#;
        let page =
            Url::parse("https://example.test/original/").unwrap_or_else(|e| unreachable!("{e}"));
        let mut queue = VecDeque::new();
        let mut known = BTreeSet::new();
        let mut map = ImportMap::default();
        let mut warnings = Vec::new();
        add_document_references(
            html,
            &page,
            &mut queue,
            &mut known,
            &mut map,
            &mut warnings,
            &AnalysisBudgets::standard("http-test"),
        );
        let urls: BTreeSet<_> = queue.iter().map(|p| p.url.as_str()).collect();
        assert!(urls.contains("https://example.test/app/chunk.js"));
        assert!(urls.contains("https://example.test/app/lib.js"));
        assert!(urls.contains("https://example.test/app/later.js"));
        assert!(urls.contains("https://example.test/app/main.js"));
        assert!(warnings.is_empty(), "{warnings:?}");
        Ok(())
    }
}
