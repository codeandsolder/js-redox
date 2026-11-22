//! Shared identity checks for bounded debugger observations.

use crate::runtime_identity::script_id_text;
use anyhow::Result;
use serde_json::Value;
use std::borrow::Cow;
use work_budget::WorkBudget;

#[derive(PartialEq, Eq)]
struct FunctionFrameIdentity<'a> {
    script: Cow<'a, str>,
    sha: &'a str,
    line: u64,
    column: u64,
}

impl<'a> FunctionFrameIdentity<'a> {
    fn from_frame(frame: &'a Value) -> Option<Self> {
        if frame.get("source_identity")?.as_str()? != "exact" {
            return None;
        }
        let function = frame.get("functionLocation")?;
        let script = script_id_text(function.get("scriptId")?)?;
        // The verified source hash describes the executing location. It must
        // also belong to the recorded function definition's script.
        if script_id_text(frame.pointer("/location/scriptId")?)? != script {
            return None;
        }
        let sha = frame.get("sourceSha256")?.as_str()?;
        if sha.len() != 64 || !sha.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return None;
        }
        Some(Self {
            script,
            sha,
            line: function.get("lineNumber")?.as_u64()?,
            column: function.get("columnNumber")?.as_u64()?,
        })
    }
}

/// Compare the entire recorded stack's normalized function coordinates and
/// verify every frame against the session-local captured source inventory.
/// Matching shapes do not establish that the same dynamic activation survived.
pub(crate) fn same_verified_stack_shape(
    first: &Value,
    second: &Value,
    budget: &WorkBudget,
    mut exact_source: impl FnMut(&str, &str) -> bool,
) -> Result<bool> {
    let (Some(a), Some(b)) = (
        first.get("frames").and_then(Value::as_array),
        second.get("frames").and_then(Value::as_array),
    ) else {
        return Ok(false);
    };
    if a.is_empty() || a.len() != b.len() {
        return Ok(false);
    }
    budget.consume(u64::try_from(a.len())?)?;
    Ok(a.iter().zip(b).all(|(first, second)| {
        let (Some(first), Some(second)) = (
            FunctionFrameIdentity::from_frame(first),
            FunctionFrameIdentity::from_frame(second),
        ) else {
            return false;
        };
        first == second && exact_source(&first.script, first.sha)
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn full_stack_identity_requires_verified_locations_and_agreed_source() -> Result<()> {
        let digest = "a".repeat(64);
        let outer = "b".repeat(64);
        let frame = |script: Value, sha: &str| json!({"source_identity":"exact","sourceSha256":sha,"location":{"scriptId":script},"functionLocation":{"scriptId":script,"lineNumber":0,"columnNumber":1}});
        let first = json!({"frames":[frame(json!(1),&digest),frame(json!(2),&outer)]});
        let second = json!({"frames":[frame(json!("1"),&digest),frame(json!("2"),&outer)]});
        let budget = WorkBudget::unlimited("stack-shape");
        let lookup = |script: &str, sha: &str| {
            (script == "1" && sha == digest) || (script == "2" && sha == outer)
        };
        assert!(same_verified_stack_shape(&first, &second, &budget, lookup)?);
        assert!(!same_verified_stack_shape(
            &first,
            &second,
            &budget,
            |script, _| script == "1"
        )?);
        for (field, value) in [
            ("sourceSha256", Value::Null),
            ("source_identity", json!("unresolved")),
            ("functionLocation", json!({"scriptId":2,"lineNumber":0})),
            ("location", json!({"scriptId":3})),
        ] {
            let mut invalid = first.clone();
            invalid["frames"][1][field] = value;
            assert!(
                !same_verified_stack_shape(&invalid, &invalid, &budget, |_, _| true)?,
                "invalid field {field}"
            );
        }
        let limited = WorkBudget::new("stack-shape-budget", work_budget::BudgetLimits::work(1));
        assert!(same_verified_stack_shape(&first, &second, &limited, lookup).is_err());
        Ok(())
    }
}
