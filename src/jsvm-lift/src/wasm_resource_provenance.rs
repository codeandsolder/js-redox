use crate::{
    analysis_artifacts::{write_artifact, WASM_RESOURCE_PROVENANCE},
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    capture_project::load_manifest,
};
use anyhow::{Context, Result};
use serde_json::{json, Map, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
};
use work_budget::WorkBudget;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmResourceProvenanceSummary {
    pub observations: usize,
    pub runtime_script_identities: usize,
    pub unmatched_wasm_events: usize,
    pub ignored_non_body_wasm_events: usize,
    pub applicable: bool,
}

fn text(value: Option<&Value>) -> Option<&str> {
    value.and_then(Value::as_str)
}

fn stringish(value: Option<&Value>) -> String {
    match value {
        None | Some(Value::Null) => String::new(),
        Some(Value::String(value)) => value.clone(),
        Some(value) => value.to_string(),
    }
}

fn status_code(value: Option<&Value>) -> i64 {
    value
        .and_then(|value| {
            value
                .as_i64()
                .or_else(|| value.as_u64().and_then(|n| i64::try_from(n).ok()))
                .or_else(|| value.as_str().and_then(|s| s.parse::<i64>().ok()))
        })
        .unwrap_or_default()
}

fn cdp_session(row: &Map<String, Value>) -> String {
    text(row.get("cdpSession"))
        .filter(|value| !value.is_empty())
        .unwrap_or("main")
        .to_owned()
}

fn is_wasm_response(url: Option<&Value>, mime_type: Option<&Value>) -> bool {
    let Some(url) = text(url) else {
        return false;
    };
    let mime = stringish(mime_type).to_ascii_lowercase();
    mime == "application/wasm"
        || url
            .split_once('#')
            .map_or(url, |(without_fragment, _)| without_fragment)
            .to_ascii_lowercase()
            .contains(".wasm")
}

fn response_body_expected(method: Option<&Value>, status: Option<&Value>) -> bool {
    if stringish(method).eq_ignore_ascii_case("HEAD") {
        return false;
    }
    let status = status_code(status);
    !((100..200).contains(&status) || (300..400).contains(&status) || matches!(status, 204 | 205))
}

fn resource_body_expected(resource: &Map<String, Value>) -> bool {
    resource
        .get("body_expected")
        .and_then(Value::as_bool)
        .unwrap_or_else(|| response_body_expected(resource.get("method"), resource.get("status")))
}

fn non_body_reason(method: Option<&Value>, status: Option<&Value>) -> String {
    if stringish(method).eq_ignore_ascii_case("HEAD") {
        "method_HEAD".to_owned()
    } else {
        format!("status_{}", status_code(status))
    }
}

fn load_json(path: &Path) -> Result<Value> {
    let bytes = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
    serde_json::from_slice(&bytes).with_context(|| format!("parsing {}", path.display()))
}

fn runtime_script_identities(capture: &Path) -> HashMap<(String, String), Value> {
    let path = capture.join("runtime-scripts.json");
    let Ok(document) = load_json(&path) else {
        return HashMap::new();
    };
    let Some(events) = document.as_array() else {
        return HashMap::new();
    };
    let mut identities: HashMap<(String, String), Value> = HashMap::new();
    let mut conflicts = HashSet::new();
    for event in events {
        let Some(event) = event.as_object() else {
            continue;
        };
        let Some(script_id) = event.get("scriptId") else {
            continue;
        };
        let Some(captured) = event.get("captured").and_then(Value::as_object) else {
            continue;
        };
        if text(captured.get("kind")) != Some("javascript") {
            continue;
        }
        let Some(digest) = text(captured.get("sha256")).filter(|digest| !digest.is_empty()) else {
            continue;
        };
        let key = (cdp_session(event), stringish(Some(script_id)));
        let candidate = json!({
            "sha256": digest,
            "path": captured.get("path").cloned().unwrap_or(Value::Null),
            "url": event.get("url").cloned().unwrap_or(Value::Null),
        });
        if conflicts.contains(&key) {
            continue;
        }
        if let Some(previous) = identities.get(&key) {
            if previous.get("sha256") != candidate.get("sha256") {
                conflicts.insert(key.clone());
                identities.remove(&key);
                continue;
            }
        }
        identities.insert(key, candidate);
    }
    identities
}

fn normalized_frames(initiator: &Map<String, Value>) -> Vec<Value> {
    initiator
        .get("stack")
        .and_then(Value::as_object)
        .and_then(|stack| stack.get("callFrames"))
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_object)
        .map(|frame| {
            json!({
                "function_name": frame.get("functionName").cloned().unwrap_or(Value::Null),
                "script_id": frame.get("scriptId").map_or(Value::Null, |id| Value::String(stringish(Some(id)))),
                "url": text(frame.get("url")).filter(|url| !url.is_empty()).map_or(Value::Null, |url| Value::String(url.to_owned())),
                "line_number": frame.get("lineNumber").cloned().unwrap_or(Value::Null),
                "column_number": frame.get("columnNumber").cloned().unwrap_or(Value::Null),
            })
        })
        .collect()
}

fn unavailable(reason: &str) -> Value {
    json!({
        "schema": WASM_RESOURCE_PROVENANCE.schema,
        "observations": [],
        "unmatched": [],
        "ignored_non_body": [],
        "summary": {
            "observations": 0,
            "unique_wasm_sha256": 0,
            "script_initiators": 0,
            "runtime_script_identities": 0,
            "captured_script_url_matches": 0,
            "direct_body_identities": 0,
            "url_unique_body_identities": 0,
            "unmatched_wasm_events": 0,
            "unmatched_reasons": {},
            "ignored_non_body_wasm_events": 0,
            "applicable": false,
            "unavailable_reason": reason,
        }
    })
}

fn current_dir_resolve(path: &str) -> Result<PathBuf> {
    let path = PathBuf::from(path);
    if path.is_absolute() {
        Ok(path)
    } else {
        Ok(std::env::current_dir()?.join(path))
    }
}

fn observation_key(row: &Value) -> (String, String, String, String) {
    let Some(row) = row.as_object() else {
        return (String::new(), String::new(), String::new(), String::new());
    };
    (
        text(row.get("cdp_session")).unwrap_or_default().to_owned(),
        stringish(row.get("request_id")),
        text(row.get("url")).unwrap_or_default().to_owned(),
        text(row.get("sha256")).unwrap_or_default().to_owned(),
    )
}

struct ResponseEvidenceIndex<'r> {
    /// Body-present, complete, exact URL + SHA-256 identities.
    wasm_resources: HashMap<(String, String), Vec<u64>>,
    /// All body-expected project WASM responses for URL/cardinality proofs.
    wasm_resources_by_url: HashMap<String, Vec<&'r Map<String, Value>>>,
    js_resources_by_url: HashMap<String, Vec<u64>>,
    cdp_wasm_counts: HashMap<String, usize>,
}

struct ResolvedResponse {
    digest: String,
    resource_ids: Vec<u64>,
    identity_basis: &'static str,
    byte_len: Value,
}

#[derive(Default)]
struct CorrelatedResponses {
    observations: Vec<Value>,
    unmatched: Vec<Value>,
    ignored_non_body: Vec<Value>,
}

impl<'r> ResponseEvidenceIndex<'r> {
    fn build(resources: &'r [Value], cdp_rows: &[Value], budget: &WorkBudget) -> Result<Self> {
        budget.checkpoint()?;
        let mut wasm_resources: HashMap<(String, String), Vec<u64>> = HashMap::new();
        let mut wasm_resources_by_url: HashMap<String, Vec<&Map<String, Value>>> = HashMap::new();
        let mut js_resources_by_url: HashMap<String, Vec<u64>> = HashMap::new();
        for resource in resources {
            budget.checkpoint()?;
            let Some(resource) = resource.as_object() else {
                continue;
            };
            let url = text(resource.get("url"));
            let digest = text(resource.get("sha256"));
            if text(resource.get("kind")) == Some("wasm")
                && url.is_some()
                && resource_body_expected(resource)
            {
                let url = url.unwrap_or_default().to_owned();
                wasm_resources_by_url
                    .entry(url.clone())
                    .or_default()
                    .push(resource);
                if resource.get("body_present").and_then(Value::as_bool) == Some(true)
                    && resource.get("body_complete").and_then(Value::as_bool) == Some(true)
                {
                    if let (Some(digest), Some(id)) =
                        (digest, resource.get("id").and_then(Value::as_u64))
                    {
                        wasm_resources
                            .entry((url, digest.to_owned()))
                            .or_default()
                            .push(id);
                    }
                }
            }
            if text(resource.get("kind")) == Some("javascript") {
                if let (Some(url), Some(id)) = (url, resource.get("id").and_then(Value::as_u64)) {
                    js_resources_by_url
                        .entry(url.to_owned())
                        .or_default()
                        .push(id);
                }
            }
        }

        let mut cdp_wasm_counts: HashMap<String, usize> = HashMap::new();
        for row in cdp_rows {
            budget.checkpoint()?;
            let Some(row) = row.as_object() else {
                continue;
            };
            if is_wasm_response(row.get("url"), row.get("mimeType"))
                && response_body_expected(row.get("method"), row.get("status"))
            {
                if let Some(url) = text(row.get("url")) {
                    *cdp_wasm_counts.entry(url.to_owned()).or_default() += 1;
                }
            }
        }
        Ok(Self {
            wasm_resources,
            wasm_resources_by_url,
            js_resources_by_url,
            cdp_wasm_counts,
        })
    }

    /// A directly observed body hash is sufficient only with an exact captured
    /// resource. Without that hash, require identical cardinality, all complete
    /// bodies and a single distinct project-side digest for the URL.
    fn resolve(
        &self,
        url: &str,
        body: Option<&Map<String, Value>>,
    ) -> std::result::Result<ResolvedResponse, &'static str> {
        if let Some(digest) = body.and_then(|body| text(body.get("sha256"))) {
            let mut resource_ids = self
                .wasm_resources
                .get(&(url.to_owned(), digest.to_owned()))
                .cloned()
                .unwrap_or_default();
            resource_ids.sort_unstable();
            resource_ids.dedup();
            if resource_ids.is_empty() {
                return Err("no_exact_project_wasm_resource");
            }
            return Ok(ResolvedResponse {
                digest: digest.to_owned(),
                resource_ids,
                identity_basis: "cdp_body_sha256",
                byte_len: body
                    .and_then(|body| body.get("size"))
                    .cloned()
                    .unwrap_or(Value::Null),
            });
        }

        let project_rows = self
            .wasm_resources_by_url
            .get(url)
            .map_or(&[][..], Vec::as_slice);
        if project_rows.is_empty() {
            return Err("no_project_wasm_resource_for_url");
        }
        if self.cdp_wasm_counts.get(url).copied().unwrap_or_default() != project_rows.len() {
            return Err("request_cardinality_mismatch");
        }
        if project_rows.iter().any(|resource| {
            resource.get("body_present").and_then(Value::as_bool) != Some(true)
                || resource.get("body_complete").and_then(Value::as_bool) != Some(true)
                || text(resource.get("sha256")).is_none()
        }) {
            return Err("incomplete_project_wasm_body_capture");
        }
        let digests = project_rows
            .iter()
            .filter_map(|resource| text(resource.get("sha256")))
            .collect::<BTreeSet<_>>();
        if digests.len() != 1 {
            return Err("ambiguous_project_wasm_bodies_for_url");
        }
        let Some(digest) = digests.first() else {
            return Err("ambiguous_project_wasm_bodies_for_url");
        };
        let digest = (*digest).to_owned();
        let mut resource_ids = project_rows
            .iter()
            .filter_map(|resource| resource.get("id").and_then(Value::as_u64))
            .collect::<Vec<_>>();
        resource_ids.sort_unstable();
        let byte_len = body
            .and_then(|body| body.get("size"))
            .cloned()
            .filter(|value| !value.is_null())
            .unwrap_or_else(|| {
                project_rows[0]
                    .get("body_bytes")
                    .cloned()
                    .unwrap_or(Value::Null)
            });
        Ok(ResolvedResponse {
            digest,
            resource_ids,
            identity_basis: "unique_url_body_and_request_cardinality",
            byte_len,
        })
    }

    fn observation(
        &self,
        row: &Map<String, Value>,
        session: &str,
        url: &str,
        resolved: ResolvedResponse,
        runtime_scripts: &HashMap<(String, String), Value>,
    ) -> Value {
        let initiator = row.get("initiator").and_then(Value::as_object);
        let frames = initiator.map_or_else(Vec::new, normalized_frames);
        let primary = frames.first().cloned();
        let mut runtime_identity = None;
        let mut initiator_resource_ids = Vec::new();
        if let Some(primary_object) = primary.as_ref().and_then(Value::as_object) {
            if let Some(script_id) = text(primary_object.get("script_id")) {
                runtime_identity = runtime_scripts.get(&(session.to_owned(), script_id.to_owned()));
            }
            if let Some(primary_url) = text(primary_object.get("url")) {
                initiator_resource_ids = self
                    .js_resources_by_url
                    .get(primary_url)
                    .cloned()
                    .unwrap_or_default();
                initiator_resource_ids.sort_unstable();
                initiator_resource_ids.dedup();
            }
        }
        json!({
            "cdp_session": session,
            "request_id": row.get("requestId").cloned().unwrap_or(Value::Null),
            "url": url,
            "sha256": resolved.digest,
            "byte_len": resolved.byte_len,
            "wasm_resource_ids": resolved.resource_ids,
            "initiator_type": initiator.and_then(|value| value.get("type")).cloned().unwrap_or(Value::Null),
            "initiator_frames": frames,
            "primary_initiator": primary.unwrap_or(Value::Null),
            "initiator_runtime_sha256": runtime_identity.and_then(|value| value.get("sha256")).cloned().unwrap_or(Value::Null),
            "initiator_runtime_path": runtime_identity.and_then(|value| value.get("path")).cloned().unwrap_or(Value::Null),
            "initiator_resource_ids": initiator_resource_ids,
            "evidence": "cdp_network_response_initiator",
            "response_identity_basis": resolved.identity_basis,
            "runtime_observed": true,
            "exact_response_identity": true,
        })
    }

    fn correlate(
        &self,
        cdp_rows: &[Value],
        runtime_scripts: &HashMap<(String, String), Value>,
        budget: &WorkBudget,
    ) -> Result<CorrelatedResponses> {
        let mut results = CorrelatedResponses::default();
        for row in cdp_rows {
            budget.checkpoint()?;
            let Some(row) = row.as_object() else {
                continue;
            };
            let Some(url) = text(row.get("url")) else {
                continue;
            };
            if !is_wasm_response(row.get("url"), row.get("mimeType")) {
                continue;
            }
            let session = cdp_session(row);
            if !response_body_expected(row.get("method"), row.get("status")) {
                results.ignored_non_body.push(json!({
                    "cdp_session": session,
                    "request_id": row.get("requestId").cloned().unwrap_or(Value::Null),
                    "url": url,
                    "method": row.get("method").cloned().unwrap_or(Value::Null),
                    "status": row.get("status").cloned().unwrap_or(Value::Null),
                    "reason": non_body_reason(row.get("method"), row.get("status")),
                }));
                continue;
            }

            let body = row.get("body").and_then(Value::as_object);
            match self.resolve(url, body) {
                Ok(resolved) => results.observations.push(self.observation(
                    row,
                    &session,
                    url,
                    resolved,
                    runtime_scripts,
                )),
                Err(reason) => results.unmatched.push(json!({
                    "cdp_session": session,
                    "request_id": row.get("requestId").cloned().unwrap_or(Value::Null),
                    "url": url,
                    "sha256": body.and_then(|body| text(body.get("sha256"))),
                    "reason": reason,
                })),
            }
        }
        Ok(results)
    }
}

impl CorrelatedResponses {
    fn into_report(self) -> (WasmResourceProvenanceSummary, Value) {
        let Self {
            mut observations,
            mut unmatched,
            ignored_non_body,
        } = self;
        observations.sort_by_key(observation_key);
        unmatched.sort_by_key(|row| {
            let Some(row) = row.as_object() else {
                return (String::new(), String::new(), String::new());
            };
            (
                text(row.get("cdp_session")).unwrap_or_default().to_owned(),
                stringish(row.get("request_id")),
                text(row.get("url")).unwrap_or_default().to_owned(),
            )
        });
        let unique_digests = observations
            .iter()
            .filter_map(|row| text(row.get("sha256")))
            .collect::<BTreeSet<_>>()
            .len();
        let script_initiators = observations
            .iter()
            .filter(|row| text(row.get("initiator_type")) == Some("script"))
            .count();
        let runtime_script_count = observations
            .iter()
            .filter(|row| text(row.get("initiator_runtime_sha256")).is_some())
            .count();
        let captured_script_url_matches = observations
            .iter()
            .filter(|row| {
                row.get("initiator_resource_ids")
                    .and_then(Value::as_array)
                    .is_some_and(|ids| !ids.is_empty())
            })
            .count();
        let direct_body_identities = observations
            .iter()
            .filter(|row| text(row.get("response_identity_basis")) == Some("cdp_body_sha256"))
            .count();
        let url_unique_body_identities = observations
            .iter()
            .filter(|row| {
                text(row.get("response_identity_basis"))
                    == Some("unique_url_body_and_request_cardinality")
            })
            .count();
        let mut unmatched_reasons = BTreeMap::<String, usize>::new();
        for row in &unmatched {
            if let Some(reason) = text(row.get("reason")) {
                *unmatched_reasons.entry(reason.to_owned()).or_default() += 1;
            }
        }

        let observation_count = observations.len();
        let unmatched_count = unmatched.len();
        let ignored_non_body_count = ignored_non_body.len();
        let summary = WasmResourceProvenanceSummary {
            observations: observation_count,
            runtime_script_identities: runtime_script_count,
            unmatched_wasm_events: unmatched_count,
            ignored_non_body_wasm_events: ignored_non_body_count,
            applicable: true,
        };
        let document = json!({
            "schema": WASM_RESOURCE_PROVENANCE.schema,
            "observations": observations,
            "unmatched": unmatched,
            "ignored_non_body": ignored_non_body,
            "summary": {
                "observations": observation_count,
                "unique_wasm_sha256": unique_digests,
                "script_initiators": script_initiators,
                "runtime_script_identities": runtime_script_count,
                "captured_script_url_matches": captured_script_url_matches,
                "direct_body_identities": direct_body_identities,
                "url_unique_body_identities": url_unique_body_identities,
                "unmatched_wasm_events": unmatched_count,
                "unmatched_reasons": unmatched_reasons,
                "ignored_non_body_wasm_events": ignored_non_body_count,
                "applicable": true,
            },
        });
        (summary, document)
    }
}

fn unavailable_result(project: &Path, reason: &str) -> Result<WasmResourceProvenanceSummary> {
    write_artifact(project, WASM_RESOURCE_PROVENANCE, &unavailable(reason))?;
    Ok(WasmResourceProvenanceSummary {
        observations: 0,
        runtime_script_identities: 0,
        unmatched_wasm_events: 0,
        ignored_non_body_wasm_events: 0,
        applicable: false,
    })
}

/// Correlate captured runtime WebAssembly resources with module provenance.
///
/// # Errors
///
/// Fails on invalid project path or capture manifest, failed artifact loading/persistence, or
/// exhaustion of the runtime analysis budget.
pub fn correlate_wasm_resource_provenance(
    project: &Path,
    budgets: &AnalysisBudgets,
) -> Result<WasmResourceProvenanceSummary> {
    let project = project
        .canonicalize()
        .with_context(|| format!("resolving project {}", project.display()))?;
    let budget = budgets.operation(
        AnalysisOperation::RuntimeAnalysis,
        project.display().to_string(),
    );
    budget.checkpoint()?;
    let manifest = load_manifest(&project)?;
    if manifest.source.kind != "recorder" {
        budget.checkpoint()?;
        return unavailable_result(&project, "not_recorder_capture");
    }

    let capture = current_dir_resolve(&manifest.source.input)?;
    let cdp_path = capture.join("cdp-streams.json");
    if !cdp_path.is_file() {
        return unavailable_result(&project, "missing_cdp_stream");
    }
    budget.checkpoint()?;
    let cdp_document = match load_json(&cdp_path) {
        Ok(document) => document,
        Err(_) => return unavailable_result(&project, "invalid_cdp_stream"),
    };
    let Some(cdp_rows) = cdp_document.as_array() else {
        return unavailable_result(&project, "invalid_cdp_stream_shape");
    };

    let index = ResponseEvidenceIndex::build(&manifest.resources, cdp_rows, &budget)?;
    let runtime_scripts = runtime_script_identities(&capture);
    let results = index.correlate(cdp_rows, &runtime_scripts, &budget)?;
    budget.checkpoint()?;
    let (summary, document) = results.into_report();
    write_artifact(&project, WASM_RESOURCE_PROVENANCE, &document)?;
    Ok(summary)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn body_expectation_matches_http_no_body_cases() {
        assert!(!response_body_expected(
            Some(&Value::String("HEAD".into())),
            Some(&json!(200))
        ));
        assert!(!response_body_expected(
            Some(&Value::String("GET".into())),
            Some(&json!(204))
        ));
        assert!(!response_body_expected(
            Some(&Value::String("GET".into())),
            Some(&json!(302))
        ));
        assert!(response_body_expected(
            Some(&Value::String("GET".into())),
            Some(&json!(200))
        ));
        assert!(response_body_expected(
            None,
            Some(&Value::String("200".into()))
        ));
    }

    #[test]
    fn resolves_only_exact_or_unique_complete_wasm_body_evidence() -> Result<()> {
        const URL: &str = "https://example.test/module.wasm";
        let budget = WorkBudget::unlimited("wasm-response-evidence-test");
        let request = json!({"url":URL, "status":200, "method":"GET"});
        let resource = |id: u64, digest: &str| {
            json!({
                "id": id,
                "url": URL,
                "kind": "wasm",
                "status": 200,
                "body_expected": true,
                "body_present": true,
                "body_complete": true,
                "sha256": digest,
                "body_bytes": 8,
            })
        };
        let resources = vec![resource(2, "same"), resource(1, "same")];
        let requests = vec![request.clone(), request.clone()];
        let index = ResponseEvidenceIndex::build(&resources, &requests, &budget)?;

        let Some(exact) = index
            .resolve(URL, json!({"sha256":"same","size":5}).as_object())
            .ok()
        else {
            anyhow::bail!("exact URL+body digest should resolve");
        };
        assert_eq!(exact.identity_basis, "cdp_body_sha256");
        assert_eq!(exact.resource_ids, [1, 2]);
        assert_eq!(exact.byte_len, json!(5));
        assert_eq!(exact.digest, "same");
        assert_eq!(
            index
                .resolve(URL, json!({"sha256":"different"}).as_object())
                .err(),
            Some("no_exact_project_wasm_resource")
        );

        let Some(fallback) = index.resolve(URL, None).ok() else {
            anyhow::bail!(
                "two complete bodies with one digest and equal request count should resolve"
            );
        };
        assert_eq!(
            fallback.identity_basis,
            "unique_url_body_and_request_cardinality"
        );
        assert_eq!(fallback.resource_ids, [1, 2]);
        assert_eq!(fallback.byte_len, json!(8));
        assert_eq!(fallback.digest, "same");

        let short_requests = vec![request.clone()];
        let index = ResponseEvidenceIndex::build(&resources, &short_requests, &budget)?;
        assert_eq!(
            index.resolve(URL, None).err(),
            Some("request_cardinality_mismatch")
        );

        let conflicting = vec![resource(2, "other"), resource(1, "same")];
        let index = ResponseEvidenceIndex::build(&conflicting, &requests, &budget)?;
        assert_eq!(
            index.resolve(URL, None).err(),
            Some("ambiguous_project_wasm_bodies_for_url")
        );

        let mut incomplete = resource(2, "same");
        incomplete["body_complete"] = json!(false);
        let incomplete_resources = vec![incomplete];
        let index = ResponseEvidenceIndex::build(&incomplete_resources, &short_requests, &budget)?;
        assert_eq!(
            index.resolve(URL, None).err(),
            Some("incomplete_project_wasm_body_capture")
        );

        let index = ResponseEvidenceIndex::build(&[], &short_requests, &budget)?;
        assert_eq!(
            index.resolve(URL, None).err(),
            Some("no_project_wasm_resource_for_url")
        );
        Ok(())
    }

    #[test]
    fn wasm_detection_accepts_mime_or_url_before_fragment() {
        assert!(is_wasm_response(
            Some(&json!("https://x.test/a.bin")),
            Some(&json!("application/wasm"))
        ));
        assert!(is_wasm_response(
            Some(&json!("https://x.test/a.wasm?v=1#x")),
            None
        ));
        assert!(!is_wasm_response(
            Some(&json!("https://x.test/a.js#.wasm")),
            None
        ));
    }
}
