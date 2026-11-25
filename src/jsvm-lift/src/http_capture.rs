//! Lightweight HTTP-root acquisition for the existing capture-project pipeline.
//!
//! This does not run JavaScript. It walks declared HTML scripts, module imports,
//! static worker references and source directives, then emits a normal HAR.
use crate::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    browser_decode::decode_html,
    browser_script_types::is_executable_script,
    har_project::html::{document_base, extract_script_tags, script_preload_links},
    import_map::{merge_import_map, parse_import_map, resolve_with_import_map, ImportMap},
    js_refs::extract_js_references,
};
use anyhow::{ensure, Context, Result};
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
    pub resources: usize,
    pub per_resource_bytes: usize,
    pub total_bytes: usize,
}

impl Default for HttpCaptureLimits {
    fn default() -> Self {
        Self {
            resources: 128,
            per_resource_bytes: 8 * 1024 * 1024,
            total_bytes: 64 * 1024 * 1024,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
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

struct CaptureGraph {
    queue: VecDeque<Pending>,
    known: BTreeSet<String>,
    import_map: ImportMap,
    warnings: Vec<String>,
    budgets: AnalysisBudgets,
}

impl CaptureGraph {
    fn new(root: &Url) -> Self {
        Self {
            queue: VecDeque::from([Pending {
                url: root.clone(),
                referer: None,
                kind: Kind::Document,
            }]),
            known: BTreeSet::from([root.as_str().to_owned()]),
            import_map: ImportMap::default(),
            warnings: Vec::new(),
            budgets: AnalysisBudgets::standard("http-static-capture"),
        }
    }

    fn enqueue(&mut self, url: Url, referer: &Url, kind: Kind) {
        let Some(mut url) = fetchable_url(url) else {
            return;
        };
        url.set_fragment(None);
        if self.known.insert(url.as_str().to_owned()) {
            self.queue.push_back(Pending {
                url,
                referer: Some(referer.clone()),
                kind,
            });
        }
    }

    fn discover_code(&mut self, source: &str, from: &Url) {
        let budget = self
            .budgets
            .operation(AnalysisOperation::ReferenceScan, from.as_str());
        let references = match extract_js_references(source, &budget) {
            Ok(refs) => refs,
            Err(error) => {
                self.warnings
                    .push(format!("{from}: JavaScript reference parse: {error}"));
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
            let resolved = resolve_with_import_map(
                Some(from.as_str()),
                &reference.specifier,
                Some(&self.import_map),
            );
            if let Some(raw_url) = resolved.get("resolved_url").and_then(Value::as_str) {
                if let Ok(url) = Url::parse(raw_url) {
                    self.enqueue(url, from, kind);
                }
            } else if reference.kind != "require" {
                self.warnings.push(format!(
                    "{from}: unresolved {} {}",
                    reference.kind, reference.specifier
                ));
            }
        }
    }

    fn discover_document(&mut self, html: &str, final_url: &Url) {
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
                        let parsed = parse_import_map(base.as_str(), &payload, &mut self.warnings);
                        self.import_map = merge_import_map(&self.import_map, &parsed);
                    }
                    Err(error) => self
                        .warnings
                        .push(format!("{final_url}: import map: {error}")),
                }
            }
        }
        for tag in tags {
            if !is_executable_script(tag.attrs.get("type").map(String::as_str)) {
                continue;
            }
            if let Some(src) = tag.attrs.get("src") {
                if let Ok(url) = base.join(src) {
                    self.enqueue(url, final_url, Kind::Script);
                }
            } else if !tag.body.trim().is_empty() {
                self.discover_code(&tag.body, &base);
            }
        }
        for (href, _) in script_preload_links(html) {
            if let Ok(url) = base.join(&href) {
                self.enqueue(url, final_url, Kind::Script);
            }
        }
    }
}

struct CapturedResponse {
    url: Url,
    status: u16,
    mime: String,
    body: Vec<u8>,
}

impl CapturedResponse {
    fn har_entry(&self, pending: &Pending) -> Value {
        let request_headers = pending.referer.as_ref().map_or_else(Vec::new, |url| {
            vec![json!({"name":"Referer","value":url.as_str()})]
        });
        json!({
            "pageref": "page_0",
            "_resourceType": pending.kind.resource_type(),
            "request": {"method":"GET","url":self.url.as_str(),"headers":request_headers,
                "_requestedUrl":pending.url.as_str()},
            "response": {
                "status":self.status,
                "statusText":"",
                "headers":[{"name":"Content-Type","value":self.mime}],
                "content":{"size":self.body.len(),"mimeType":self.mime,
                    "encoding":"base64",
                    "text":base64::engine::general_purpose::STANDARD.encode(&self.body)}
            }
        })
    }
}

fn fetch_response(client: &Client, pending: &Pending, cap: usize) -> Result<CapturedResponse> {
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
    let response = request
        .send()
        .with_context(|| format!("GET {}", pending.url))?;
    let final_url = response.url().clone();
    let status = response.status().as_u16();
    let mime = response
        .headers()
        .get(CONTENT_TYPE)
        .and_then(|value| value.to_str().ok())
        .unwrap_or(match pending.kind {
            Kind::Document => "text/html",
            Kind::Script => "application/javascript",
            Kind::Asset => "application/octet-stream",
        })
        .to_owned();
    let mut body = Vec::new();
    response
        .take(u64::try_from(cap)?.saturating_add(1))
        .read_to_end(&mut body)?;
    ensure!(
        body.len() <= cap,
        "response exceeds HTTP capture byte limit"
    );
    Ok(CapturedResponse {
        url: final_url,
        status,
        mime,
        body,
    })
}

struct Acquisition {
    graph: CaptureGraph,
    entries: Vec<Value>,
    failures: usize,
    total_bytes: usize,
    final_root: Option<Url>,
}

impl Acquisition {
    fn new(root: &Url) -> Self {
        Self {
            graph: CaptureGraph::new(root),
            entries: Vec::new(),
            failures: 0,
            total_bytes: 0,
            final_root: None,
        }
    }

    fn run(&mut self, client: &Client, limits: HttpCaptureLimits) -> Result<()> {
        while let Some(pending) = self.graph.queue.pop_front() {
            if self.entries.len() >= limits.resources || self.total_bytes >= limits.total_bytes {
                self.graph.queue.push_front(pending);
                break;
            }
            let cap = limits
                .per_resource_bytes
                .min(limits.total_bytes.saturating_sub(self.total_bytes));
            match fetch_response(client, &pending, cap) {
                Ok(response) => self.record_response(&pending, &response)?,
                Err(error) => self.record_failure(&pending, error)?,
            }
        }
        Ok(())
    }

    fn record_response(&mut self, pending: &Pending, response: &CapturedResponse) -> Result<()> {
        self.graph.known.insert(response.url.as_str().to_owned());
        if pending.kind == Kind::Document {
            self.final_root = Some(response.url.clone());
            ensure!(
                (200..300).contains(&response.status),
                "root document returned HTTP {}",
                response.status
            );
            let decoded = decode_html(&response.body, Some(&response.mime), None);
            self.graph.discover_document(&decoded.source, &response.url);
        } else if (200..300).contains(&response.status) && pending.kind == Kind::Script {
            // Browser JS text decoder handles BOMs and legacy charset responses.
            let decoded = crate::browser_decode::decode_script(
                &response.body,
                crate::browser_decode::ScriptDecodeContext::classic_unknown(),
            );
            self.graph.discover_code(&decoded.source, &response.url);
        }
        self.total_bytes += response.body.len();
        self.entries.push(response.har_entry(pending));
        Ok(())
    }

    fn record_failure(&mut self, pending: &Pending, error: anyhow::Error) -> Result<()> {
        if pending.kind == Kind::Document {
            return Err(error).context("could not acquire root document");
        }
        self.failures += 1;
        self.graph
            .warnings
            .push(format!("{}: {error:#}", pending.url));
        let response = CapturedResponse {
            url: pending.url.clone(),
            status: 0,
            mime: String::new(),
            body: Vec::new(),
        };
        let mut failure = response.har_entry(pending);
        failure["response"]["content"]["text"] = Value::Null;
        failure["_failure"] = json!({"errorText": error.to_string()});
        self.entries.push(failure);
        Ok(())
    }

    fn publish(self, root: &Url, har_path: &Path) -> Result<HttpCaptureSummary> {
        let final_url = self.final_root.context("root document missing")?;
        let summary = HttpCaptureSummary {
            requested_url: root.to_string(),
            final_url: final_url.to_string(),
            resources: self.entries.len(),
            failed_resources: self.failures,
            bytes: self.total_bytes,
            pending_resources: self.graph.queue.len(),
            warnings: self.graph.warnings,
        };
        let har = json!({"log":{"version":"1.2","creator":{"name":"js-redox","version":"1"},
            "pages":[{"id":"page_0","title":final_url.as_str(),"startedDateTime":""}],
            "entries":self.entries,
            "_httpStaticCapture":&summary}});
        if let Some(parent) = har_path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(har_path, serde_json::to_vec_pretty(&har)?)
            .with_context(|| format!("writing {}", har_path.display()))?;
        Ok(summary)
    }
}

/// Obtain a static HTTP graph and write its captured responses in standard HAR form.
///
/// Fails if the root HTML cannot be fetched. Individual dependency failures are
/// represented in the HAR and in the returned summary without aborting the graph.
///
/// # Errors
///
/// Rejects nonpositive capture limits, invalid or non-HTTP(S) root URLs, failed root requests
/// and non-successful root responses. Client construction, HAR serialization and filesystem
/// writes can also fail; individual dependency failures are recorded without aborting the
/// capture.
pub fn capture_url_to_har(
    requested: &str,
    har_path: &Path,
    limits: HttpCaptureLimits,
) -> Result<HttpCaptureSummary> {
    ensure!(
        limits.resources > 0 && limits.per_resource_bytes > 0 && limits.total_bytes > 0,
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
    let mut acquisition = Acquisition::new(&root);
    acquisition.run(&client, limits)?;
    acquisition.publish(&root, har_path)
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
        let server_thread = thread::spawn(move || -> Result<usize> {
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
        let served_requests = server_thread
            .join()
            .map_err(|_| anyhow::anyhow!("fixture HTTP server panicked"))??;
        assert_eq!(served_requests, 3);
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
    fn dependency_failure_preserves_har_identity_and_does_not_charge_body_bytes() -> Result<()> {
        let root = Url::parse("https://example.test/")?;
        let mut capture = Acquisition::new(&root);
        let document = capture.graph.queue.pop_front().context("root request")?;
        let response = CapturedResponse {
            url: root.clone(),
            status: 200,
            mime: "text/html".into(),
            body: b"<script src='missing.js'></script>".to_vec(),
        };
        capture.record_response(&document, &response)?;
        let dependency = capture
            .graph
            .queue
            .pop_front()
            .context("dependency request")?;
        capture.record_failure(&dependency, anyhow::anyhow!("fixture read failure"))?;
        assert_eq!(capture.total_bytes, response.body.len());
        assert_eq!(capture.failures, 1);
        let failure = &capture.entries[1];
        assert_eq!(failure["request"]["url"], "https://example.test/missing.js");
        assert_eq!(failure["request"]["headers"][0]["value"], root.as_str());
        assert_eq!(failure["response"]["status"], 0);
        assert_eq!(failure["response"]["content"]["text"], Value::Null);
        assert_eq!(failure["_failure"]["errorText"], "fixture read failure");
        assert_eq!(capture.graph.warnings.len(), 1);
        let mut root_failure = Acquisition::new(&root);
        let document = root_failure
            .graph
            .queue
            .pop_front()
            .context("root request")?;
        assert!(root_failure
            .record_failure(&document, anyhow::anyhow!("fixture root failure"))
            .is_err());
        assert_eq!(root_failure.entries, [] as [Value; 0]);
        Ok(())
    }

    #[test]
    fn html_base_links_and_import_maps() {
        let html = r#"<base href="/app/"><link rel="modulepreload" href="chunk.js">
          <script type="importmap">{"imports":{"lib":"./lib.js"}}</script>
          <script type="module">import "lib"; import("./later.js");</script>
          <script src="main.js"></script>"#;
        let page =
            Url::parse("https://example.test/original/").unwrap_or_else(|e| unreachable!("{e}"));
        let mut graph = CaptureGraph::new(&page);
        graph.queue.clear();
        graph.discover_document(html, &page);
        let urls: BTreeSet<_> = graph.queue.iter().map(|p| p.url.as_str()).collect();
        assert!(urls.contains("https://example.test/app/chunk.js"));
        assert!(urls.contains("https://example.test/app/lib.js"));
        assert!(urls.contains("https://example.test/app/later.js"));
        assert!(urls.contains("https://example.test/app/main.js"));
        assert!(graph.warnings.is_empty(), "{:?}", graph.warnings);
    }
}
