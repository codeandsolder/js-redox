//! Join a capture's initial HTML script source candidates to existing
//! counter-positive V8 source instances, without inferring handler calls or
//! asserting which HTML tag necessarily scheduled a same-byte script.
use crate::document_entrypoints::DocumentEntrypoints;
use serde::Serialize;
use serde_json::Value;
use std::collections::BTreeMap;
use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PositiveScriptInstance {
    pub cdp_session: String,
    pub script_id: String,
    pub execution_context_id: Option<u64>,
    pub script_url: Option<String>,
    pub url_correlates_with_html_root: bool,
    pub positive_functions: u64,
    pub positive_ranges: u64,
    pub counter_offset_units: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct RootSourceExecutionWitness {
    pub document_resource_id: u64,
    pub script_ordinal: usize,
    pub source_raw_path: String,
    pub source_raw_sha256: String,
    /// The source hash is present in captured V8 scriptParsed events.
    pub source_bytes_parsed: bool,
    /// A strictly positive V8 counter exists for the exact source bytes.
    pub source_bytes_positively_executed: bool,
    /// Positive script instances, NOT a proof the particular HTML tag executed.
    pub positive_instances: Vec<PositiveScriptInstance>,
    pub runtime_script_body_classifications: Vec<String>,
    pub exact_html_tag_execution_proven: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct InitialSourceCoverageJoin {
    pub schema: &'static str,
    pub roots: Vec<RootSourceExecutionWitness>,
    pub candidate_sources: usize,
    pub positively_executed_source_matches: usize,
    pub source_parsed_matches: usize,
    pub url_correlated_positive_instances: usize,
    pub coverage_proves_specific_function_calls: bool,
    pub coverage_offset_contract: &'static str,
}

fn field<'a>(row: &'a Value, name: &str) -> Option<&'a str> {
    row.get(name).and_then(Value::as_str)
}

fn positive_instance(
    instance: &Value,
    expected_url: Option<&str>,
) -> Option<PositiveScriptInstance> {
    let execution = instance.get("execution")?;
    if field(execution, "status") != Some("positive") {
        return None;
    }
    let functions = execution
        .get("positive_functions")
        .and_then(Value::as_u64)
        .unwrap_or(0);
    let ranges = execution
        .get("positive_ranges")
        .and_then(Value::as_u64)
        .unwrap_or(0);
    if functions == 0 && ranges == 0 {
        return None;
    }
    let url = field(instance, "script_url")
        .or_else(|| field(execution, "source_url"))
        .map(str::to_owned);
    let id = instance.get("script_id")?;
    let script_id = match id {
        Value::String(value) => value.clone(),
        Value::Number(value) => value.to_string(),
        _ => return None,
    };
    let cdp_session = field(instance, "cdp_session").unwrap_or("main").to_string();
    Some(PositiveScriptInstance {
        cdp_session,
        script_id,
        execution_context_id: instance.get("execution_context_id").and_then(Value::as_u64),
        url_correlates_with_html_root: expected_url
            .is_some_and(|expected| url.as_deref() == Some(expected)),
        script_url: url,
        positive_functions: functions,
        positive_ranges: ranges,
        counter_offset_units: field(execution, "offset_units")
            .unwrap_or("unknown")
            .to_owned(),
    })
}

/// Correlate initial HTML source *bytes* with counter-positive JS script
/// instances. Identical bytes in separate tags/frames or injected scripts
/// mean that an exact digest match is NOT proof a specific tag executed.
pub fn join_initial_source_coverage(
    documents: &[DocumentEntrypoints],
    runtime_scripts: &Value,
    budget: &WorkBudget,
) -> Result<InitialSourceCoverageJoin, BudgetExceeded> {
    let mut by_digest = BTreeMap::<String, Vec<&Value>>::new();
    if let Some(sources) = runtime_scripts.get("sources").and_then(Value::as_array) {
        for source in sources {
            budget.consume(1)?;
            if field(source, "classification") == Some("capture_instrumentation") {
                continue;
            }
            if let Some(sha) = field(source, "sha256") {
                by_digest.entry(sha.to_string()).or_default().push(source);
            }
        }
    }
    let mut roots = Vec::new();
    let mut positive = 0;
    let mut parsed = 0;
    let mut url_correlated = 0;
    for doc in documents {
        for script in &doc.scripts {
            budget.consume(1)?;
            if !script.executable {
                continue;
            }
            let expected_url = script.resolved_url.as_deref().unwrap_or(&doc.document_url);
            for body in &script.captured_sources {
                budget.consume(1)?;
                let matches = by_digest.get(&body.sha256);
                let mut positive_instances = Vec::new();
                let mut classifications = Vec::new();
                if let Some(matches) = matches {
                    for row in matches {
                        budget.consume(1)?;
                        if let Some(classification) = field(row, "classification") {
                            classifications.push(classification.to_owned());
                        }
                        for instance in row
                            .get("script_instances")
                            .and_then(Value::as_array)
                            .into_iter()
                            .flatten()
                        {
                            budget.consume(1)?;
                            if let Some(witness) = positive_instance(instance, Some(expected_url)) {
                                if witness.url_correlates_with_html_root {
                                    url_correlated += 1;
                                }
                                positive_instances.push(witness);
                            }
                        }
                    }
                }
                positive_instances.sort_by(|left, right| {
                    (&left.cdp_session, &left.script_id, &left.script_url).cmp(&(
                        &right.cdp_session,
                        &right.script_id,
                        &right.script_url,
                    ))
                });
                positive_instances.dedup();
                classifications.sort();
                classifications.dedup();
                let source_bytes_positively_executed =
                    !positive_instances.is_empty() && body.matches_manifest_sha256;
                if source_bytes_positively_executed {
                    positive += 1;
                }
                if matches.is_some() && body.matches_manifest_sha256 {
                    parsed += 1;
                }
                roots.push(RootSourceExecutionWitness {
                    document_resource_id: doc.document_resource_id,
                    script_ordinal: script.ordinal,
                    source_raw_path: body.output_path.clone(),
                    source_raw_sha256: body.sha256.clone(),
                    source_bytes_parsed: matches.is_some() && body.matches_manifest_sha256,
                    source_bytes_positively_executed,
                    positive_instances,
                    runtime_script_body_classifications: classifications,
                    exact_html_tag_execution_proven: false,
                });
            }
        }
    }
    Ok(InitialSourceCoverageJoin {
        schema: "jsvm-html-source-coverage-join/v1",
        candidate_sources: roots.len(),
        positively_executed_source_matches: positive,
        source_parsed_matches: parsed,
        url_correlated_positive_instances: url_correlated,
        roots,
        coverage_proves_specific_function_calls: false,
        coverage_offset_contract: "V8 counter offsets, when available, are UTF-16 positions in original parsed JS; no implicit conversion to source graph UTF-8 byte offsets",
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::document_entrypoints::{
        CapturedScriptSource, DocumentEntrypoints, DocumentScriptRoot,
    };
    use serde_json::json;

    #[test]
    fn exact_bytes_and_positive_counters_not_false_tag_witnesses() -> anyhow::Result<()> {
        let doc = DocumentEntrypoints {
            document_resource_id: 9,
            document_url: "https://example.test/page".into(),
            static_base_url: "https://example.test/page".into(),
            document_source_sha256: String::new(),
            document_matches_manifest_sha256: true,
            scripts: vec![DocumentScriptRoot {
                ordinal: 1,
                script_type: "text/javascript".into(),
                executable: true,
                is_module: false,
                async_attribute: false,
                defer_attribute: false,
                nomodule_attribute: false,
                scheduling_class: "parser_blocking",
                src: None,
                resolved_url: None,
                execution_observed: false,
                captured_sources: vec![CapturedScriptSource {
                    resource_id: None,
                    output_path: "resources/s.js".into(),
                    sha256: "abc".into(),
                    matches_manifest_sha256: true,
                }],
            }],
        };
        let runtime = json!({"sources":[
            {
                "sha256":"abc", "classification":"inline_script",
                "observed_executed":true,
                "script_instances":[
                    {"cdp_session":"main","script_id":"7",
                     "script_url":"https://example.test/page",
                     "execution_context_id":4,
                     "execution":{"status":"positive","positive_functions":1,"positive_ranges":2,"offset_units":"utf16"}},
                    {"cdp_session":"main","script_id":"8","execution":{"status":"zero","positive_functions":0}}
                ]
            },
            {"sha256":"other","classification":"inline_script",
             "observed_executed":true,"script_instances":[{"script_id":"9","execution":{"status":"positive","positive_functions":3}}]},
            {"sha256":"abc","classification":"capture_instrumentation",
             "script_instances":[{"script_id":"10","execution":{"status":"positive","positive_functions":5}}]}
        ]});
        let got = join_initial_source_coverage(
            &[doc],
            &runtime,
            &WorkBudget::unlimited("coverage-test"),
        )?;
        assert_eq!(got.candidate_sources, 1);
        assert_eq!(got.positively_executed_source_matches, 1);
        assert_eq!(got.source_parsed_matches, 1);
        assert_eq!(got.url_correlated_positive_instances, 1);
        assert!(!got.coverage_proves_specific_function_calls);
        let only = &got.roots[0];
        assert!(only.source_bytes_positively_executed);
        assert!(!only.exact_html_tag_execution_proven);
        assert_eq!(only.positive_instances.len(), 1);
        assert_eq!(only.positive_instances[0].script_id, "7");
        assert_eq!(only.positive_instances[0].counter_offset_units, "utf16");
        Ok(())
    }
}
