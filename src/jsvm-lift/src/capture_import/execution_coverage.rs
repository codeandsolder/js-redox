//! Join V8 best-effort or precise coverage by (CDP target session, script ID).
//! A positive range is a witness that code ran in the recorded interval.
//! Zero/absent coverage is deliberately not evidence of non-execution.
use crate::analysis_artifacts::{write_artifact, EXECUTION_COVERAGE};
use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::{
    collections::{HashMap, HashSet},
    fs,
    path::Path,
};
use work_budget::WorkBudget;

pub(super) struct CoverageIndex {
    by_script: HashMap<(String, String), Value>,
    available_sessions: HashSet<String>,
    mode: String,
}

fn nonempty_text(value: Option<&Value>) -> Option<&str> {
    value
        .and_then(Value::as_str)
        .filter(|text| !text.is_empty())
}

impl CoverageIndex {
    pub(super) fn load(
        capture: &Path,
        project: &Path,
        budget: &WorkBudget,
    ) -> Result<Option<Self>> {
        let path = capture.join("execution-coverage.json");
        if !path.is_file() {
            return Ok(None);
        }
        let root: Value = serde_json::from_slice(&fs::read(&path)?)
            .with_context(|| format!("parsing {}", path.display()))?;
        if root.get("schema").and_then(Value::as_str) != Some("js-redox/execution-coverage/v2")
            || root.get("offsetUnits").and_then(Value::as_str) != Some("utf16")
        {
            bail!(
                "unsupported execution coverage schema or offset unit in {}",
                path.display()
            );
        }
        let mode = nonempty_text(root.get("mode"))
            .context("execution coverage missing observation mode")?;
        if !matches!(mode, "none" | "best-effort" | "precise") {
            bail!("unsupported execution coverage mode: {mode}");
        }
        let sessions = root
            .get("sessions")
            .and_then(Value::as_array)
            .context("execution coverage requires sessions[]")?;
        let mut by_script = HashMap::new();
        let mut available_sessions = HashSet::new();
        let mut seen_sessions = HashSet::new();
        let mut duplicate_keys = HashSet::new();
        let mut script_rows = Vec::new();
        for session in sessions {
            budget.consume(1)?;
            let name = nonempty_text(session.get("cdpSession"))
                .context("execution coverage session missing cdpSession")?;
            if !seen_sessions.insert(name.to_owned()) {
                bail!("duplicate execution coverage session: {name}");
            }
            let status = session.get("status").and_then(Value::as_str);
            if mode == "none" {
                if status != Some("disabled") {
                    bail!("coverage mode none must contain only disabled sessions");
                }
                continue;
            }
            if status != Some("captured") {
                if status != Some("unavailable") {
                    bail!("unsupported execution coverage session status: {status:?}");
                }
                continue;
            }
            if !available_sessions.insert(name.to_owned()) {
                bail!("duplicate captured execution coverage session: {name}");
            }
            let scripts = session
                .get("scripts")
                .and_then(Value::as_array)
                .context("captured execution coverage missing scripts[]")?;
            for script in scripts {
                budget.consume(1)?;
                let Some(script_id) = nonempty_text(script.get("scriptId")) else {
                    continue;
                };
                let mut positive_functions = 0usize;
                let mut positive_ranges = 0usize;
                let functions = script
                    .get("functions")
                    .and_then(Value::as_array)
                    .context("coverage script missing functions[]")?;
                for function in functions {
                    budget.consume(1)?;
                    let ranges = function
                        .get("ranges")
                        .and_then(Value::as_array)
                        .context("coverage function missing ranges[]")?;
                    let mut positive = false;
                    for range in ranges {
                        budget.consume(1)?;
                        if range
                            .get("count")
                            .and_then(Value::as_u64)
                            .is_some_and(|count| count > 0)
                        {
                            positive_ranges += 1;
                            positive = true;
                        }
                    }
                    if positive {
                        positive_functions += 1;
                    }
                }
                let row = json!({
                    "cdp_session": name,
                    "script_id": script_id,
                    "coverage_mode": mode,
                    "status": if positive_ranges > 0 { "positive" } else { "zero_only" },
                    "positive_functions": positive_functions,
                    "positive_ranges": positive_ranges,
                    "function_profiles": functions.len(),
                    "offset_units": "utf16",
                    "source_url": script.get("url").cloned().unwrap_or(Value::Null),
                });
                let key = (name.to_owned(), script_id.to_owned());
                if by_script.insert(key.clone(), row.clone()).is_some() {
                    duplicate_keys.insert(key);
                }
                script_rows.push(row);
            }
        }
        for key in duplicate_keys {
            by_script.remove(&key);
        }
        let document = json!({
            "schema": EXECUTION_COVERAGE.schema,
            "capture": capture.display().to_string(),
            "mode": mode,
            "summary": {
                "mode": mode,
                "captured_sessions": available_sessions.len(),
                "script_profiles": script_rows.len(),
                "positive_script_profiles": script_rows.iter().filter(|row| row["status"] == "positive").count(),
                "zero_only_script_profiles": script_rows.iter().filter(|row| row["status"] == "zero_only").count(),
                "notes": "Positive V8 function coverage is evidence of execution in the recorded mode; zero, missing, and unavailable coverage are inconclusive. Precise coverage disables optimization.",
            },
            "scripts": script_rows,
        });
        write_artifact(project, EXECUTION_COVERAGE, &document)?;
        Ok(Some(Self {
            by_script,
            available_sessions,
            mode: mode.to_owned(),
        }))
    }

    pub(super) fn mode(&self) -> &str {
        &self.mode
    }

    pub(super) fn for_script(&self, session: &str, script_id: &str) -> Value {
        self.by_script
            .get(&(session.to_owned(), script_id.to_owned()))
            .cloned()
            .unwrap_or_else(|| {
                json!({
                    "status": if self.mode == "none" {
                        "disabled"
                    } else if self.available_sessions.contains(session) {
                        "not_reported"
                    } else {
                        "unavailable"
                    },
                    "coverage_mode": self.mode
                })
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn best_effort_positive_function_evidence_preserves_mode() -> Result<()> {
        let root = TempDir::new()?;
        let capture = root.path().join("capture");
        let project = root.path().join("project");
        fs::create_dir_all(&capture)?;
        fs::create_dir_all(&project)?;
        let fixture = json!({
            "schema":"js-redox/execution-coverage/v2",
            "mode":"best-effort", "offsetUnits":"utf16",
            "sessions":[
                {"cdpSession":"main","status":"captured","scripts":[
                    {"scriptId":"11","functions":[{"ranges":[
                        {"startOffset":0,"endOffset":10,"count":1}
                    ]}]},
                    {"scriptId":"12","functions":[]}
                ]},
                {"cdpSession":"worker-1","status":"unavailable","scripts":[]}
            ]
        });
        fs::write(
            capture.join("execution-coverage.json"),
            serde_json::to_vec(&fixture)?,
        )?;
        let index = CoverageIndex::load(&capture, &project, &WorkBudget::unlimited("best effort"))?
            .context("missing coverage")?;
        assert_eq!(index.mode(), "best-effort");
        assert_eq!(index.for_script("main", "11")["status"], "positive");
        assert_eq!(
            index.for_script("main", "11")["coverage_mode"],
            "best-effort"
        );
        assert_eq!(index.for_script("main", "12")["status"], "zero_only");
        assert_eq!(index.for_script("main", "13")["status"], "not_reported");
        assert_eq!(index.for_script("worker-1", "11")["status"], "unavailable");
        let output: Value =
            serde_json::from_slice(&fs::read(project.join("analysis/execution-coverage.json"))?)?;
        assert_eq!(output["summary"]["mode"], "best-effort");
        assert_eq!(output["scripts"][0]["coverage_mode"], "best-effort");
        Ok(())
    }

    #[test]
    fn disabled_coverage_is_explicitly_not_an_execution_witness() -> Result<()> {
        let root = TempDir::new()?;
        let capture = root.path().join("capture");
        let project = root.path().join("project");
        fs::create_dir_all(&capture)?;
        fs::create_dir_all(&project)?;
        let mut fixture = json!({
            "schema":"js-redox/execution-coverage/v2", "mode":"none",
            "offsetUnits":"utf16",
            "sessions":[{"cdpSession":"main","status":"disabled","scripts":[]}]
        });
        let path = capture.join("execution-coverage.json");
        fs::write(&path, serde_json::to_vec(&fixture)?)?;
        let index = CoverageIndex::load(&capture, &project, &WorkBudget::unlimited("none"))?
            .context("missing disabled coverage")?;
        assert_eq!(index.mode(), "none");
        assert_eq!(index.for_script("main", "8")["status"], "disabled");
        assert_eq!(index.for_script("main", "8")["coverage_mode"], "none");
        assert_eq!(index.for_script("unknown", "8")["status"], "disabled");
        let output: Value =
            serde_json::from_slice(&fs::read(project.join("analysis/execution-coverage.json"))?)?;
        assert!(output["scripts"].as_array().is_some_and(Vec::is_empty));
        fixture["sessions"][0]["status"] = json!("captured");
        fs::write(&path, serde_json::to_vec(&fixture)?)?;
        assert!(
            CoverageIndex::load(&capture, &project, &WorkBudget::unlimited("none invalid"))
                .is_err()
        );
        fixture["sessions"][0]["status"] = json!("disabled");
        fixture["mode"] = json!("fictitious");
        fs::write(&path, serde_json::to_vec(&fixture)?)?;
        assert!(
            CoverageIndex::load(&capture, &project, &WorkBudget::unlimited("mode invalid"))
                .is_err()
        );
        Ok(())
    }

    #[test]
    fn positive_coverage_is_session_scoped_and_zero_is_not_nonexecution() -> Result<()> {
        let root = TempDir::new()?;
        let capture = root.path().join("capture");
        let project = root.path().join("project");
        fs::create_dir_all(&capture)?;
        fs::create_dir_all(&project)?;
        let fixture = json!({
            "schema": "js-redox/execution-coverage/v2",
            "mode": "precise",
            "offsetUnits": "utf16",
            "sessions": [
                {"cdpSession":"main","status":"captured","scripts":[
                    {"scriptId":"7","functions":[
                        {"ranges":[{"startOffset":0,"endOffset":12,"count":2},
                                   {"startOffset":1,"endOffset":3,"count":0}]}
                    ]},
                    {"scriptId":"8","functions":[{"ranges":[{"startOffset":0,"endOffset":3,"count":0}]}]}
                ]},
                {"cdpSession":"oopif-1","status":"unavailable","scripts":[]}
            ]
        });
        fs::write(
            capture.join("execution-coverage.json"),
            serde_json::to_vec(&fixture)?,
        )?;
        let budget = WorkBudget::unlimited("coverage fixture");
        let index = CoverageIndex::load(&capture, &project, &budget)?.context("expected index")?;
        assert_eq!(index.mode(), "precise");
        assert_eq!(index.for_script("main", "7")["status"], "positive");
        assert_eq!(index.for_script("main", "7")["coverage_mode"], "precise");
        assert_eq!(index.for_script("main", "7")["positive_ranges"], 1);
        assert_eq!(index.for_script("main", "8")["status"], "zero_only");
        assert_eq!(index.for_script("main", "9")["status"], "not_reported");
        assert_eq!(index.for_script("oopif-1", "7")["status"], "unavailable");
        let output: Value =
            serde_json::from_slice(&fs::read(project.join("analysis/execution-coverage.json"))?)?;
        assert_eq!(output["summary"]["positive_script_profiles"], 1);
        assert_eq!(output["mode"], "precise");
        Ok(())
    }
}
