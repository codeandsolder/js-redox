//! Positive coverage of exact captured source bytes. Raw profiles and event
//! occurrences remain separate from deduplicated session/script witnesses.
use crate::runtime_identity::ScriptIdentityIndex;
use anyhow::Result;
use serde::Serialize;
use serde_json::Value;
use std::collections::BTreeMap;
use work_budget::WorkBudget;

#[derive(Clone, Debug, PartialEq, Eq)]
struct PositiveCounters {
    positive_functions: u64,
    positive_ranges: u64,
    offset_units: String,
}

impl PositiveCounters {
    fn from_instance(instance: &Value) -> Option<Self> {
        let execution = instance.get("execution")?;
        if execution.get("status").and_then(Value::as_str) != Some("positive") {
            return None;
        }
        let positive_functions = execution
            .get("positive_functions")
            .and_then(Value::as_u64)
            .unwrap_or_default();
        let positive_ranges = execution
            .get("positive_ranges")
            .and_then(Value::as_u64)
            .unwrap_or_default();
        (positive_functions > 0 || positive_ranges > 0).then(|| Self {
            positive_functions,
            positive_ranges,
            offset_units: execution
                .get("offset_units")
                .and_then(Value::as_str)
                .unwrap_or("unknown")
                .to_owned(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PositiveCoverageWitness {
    pub cdp_session: String,
    pub script_id: String,
    pub execution_context_id: Option<u64>,
    pub script_url: Option<String>,
    pub positive_functions: u64,
    pub positive_ranges: u64,
    pub counter_offset_units: String,
    pub capture_instrumentation: bool,
}

#[derive(Default)]
pub(crate) struct RuntimeCoverageIndex {
    by_digest: BTreeMap<String, Vec<PositiveCoverageWitness>>,
}

impl RuntimeCoverageIndex {
    pub(crate) fn build(runtime: &Value, budget: &WorkBudget) -> Result<Self> {
        // Register negative/missing profiles as well: disagreement is not a
        // positive witness. The global raw-event conflict list also applies.
        let profiles =
            ScriptIdentityIndex::from_runtime_report(runtime, budget, |sha, source, instance| {
                Some((
                    sha.to_owned(),
                    PositiveCounters::from_instance(instance),
                    source["classification"] == "capture_instrumentation",
                ))
            })?;
        // Contextual disagreement must not erase agreement on executed bytes.
        // Conversely, never pick an arbitrary URL or context from aliases.
        let urls = ScriptIdentityIndex::from_runtime_report(runtime, budget, |_, _, instance| {
            Some(
                instance
                    .get("script_url")
                    .and_then(Value::as_str)
                    .filter(|s| !s.is_empty())
                    .or_else(|| {
                        instance
                            .pointer("/execution/source_url")
                            .and_then(Value::as_str)
                            .filter(|url| !url.is_empty())
                    })
                    .map(ToOwned::to_owned),
            )
        })?;
        let contexts =
            ScriptIdentityIndex::from_runtime_report(runtime, budget, |_, _, instance| {
                Some(instance.get("execution_context_id").and_then(Value::as_u64))
            })?;
        let mut by_digest = BTreeMap::<String, Vec<PositiveCoverageWitness>>::new();
        for (session, script, (sha, profile, instrumentation)) in profiles.unique_entries() {
            budget.consume(1)?;
            let Some(profile) = profile else {
                continue;
            };
            by_digest
                .entry(sha.clone())
                .or_default()
                .push(PositiveCoverageWitness {
                    cdp_session: session.to_owned(),
                    script_id: script.to_owned(),
                    execution_context_id: contexts.get(session, script).copied().flatten(),
                    script_url: urls.get(session, script).cloned().flatten(),
                    positive_functions: profile.positive_functions,
                    positive_ranges: profile.positive_ranges,
                    counter_offset_units: profile.offset_units.clone(),
                    capture_instrumentation: *instrumentation,
                });
        }
        Ok(Self { by_digest })
    }

    pub(crate) fn witnesses(&self, digest: &str) -> &[PositiveCoverageWitness] {
        self.by_digest.get(digest).map_or_default(Vec::as_slice)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn coverage_requires_unambiguous_source_and_counters_not_unambiguous_url() -> Result<()> {
        let profile = json!({"status":"positive","positive_functions":2,"positive_ranges":3,"offset_units":"utf16"});
        let instance = |session: &str, script: &str, url: &str, execution: &Value| json!({"cdp_session":session,"script_id":script,"script_url":url,"execution_context_id":1,"execution":execution});
        let one = instance("main", "1", "a", &profile);
        let two = instance("main", "2", "a", &profile);
        let mut worker_profile = profile.clone();
        worker_profile["source_url"] = json!("w");
        let runtime = json!({"sources":[{"sha256":"body","script_instances":[
            one.clone(),one,instance("main","1","b",&profile),
            two.clone(),instance("main","2","a",&json!({"status":"zero_only"})),
            instance("main","3","a",&profile),instance("worker","3","",&worker_profile),
            instance("main","4","a",&json!({"status":"positive"})),
            instance("main","5","a",&profile)
        ]},{"sha256":"other","script_instances":[instance("main","5","a",&profile)]}],
            "script_identity_conflicts":[{"cdp_session":"main","script_id":"3","sha256_claims":["body","missing"]}]});
        let index =
            RuntimeCoverageIndex::build(&runtime, &WorkBudget::unlimited("coverage-evidence"))?;
        let witnesses = index.witnesses("body");
        assert_eq!(witnesses.len(), 2);
        assert_eq!(witnesses[0].script_id, "1");
        assert_eq!(witnesses[0].script_url, None);
        assert_eq!(witnesses[0].execution_context_id, Some(1));
        assert_eq!(witnesses[0].positive_ranges, 3);
        assert_eq!(witnesses[1].cdp_session, "worker");
        assert_eq!(witnesses[1].script_url.as_deref(), Some("w"));
        assert!(index.witnesses("other").is_empty());
        Ok(())
    }
}
