//! Shared normalization of CDP session-local script identities.

pub(crate) fn script_id_text(value: &serde_json::Value) -> Option<std::borrow::Cow<'_, str>> {
    use std::borrow::Cow;
    match value {
        serde_json::Value::String(id) if !id.is_empty() => Some(Cow::Borrowed(id)),
        serde_json::Value::Number(id) if id.is_u64() => Some(Cow::Owned(id.to_string())),
        _ => None,
    }
}

/// A session is an explicit nonempty recorder label, never a default or an ID
/// obtained by stringifying arbitrary JSON. Missing labels cannot join scripts.
pub(crate) fn session_name(value: Option<&Value>) -> Option<&str> {
    nonempty_text(value).filter(|session| !session.trim().is_empty())
}

use anyhow::{Context, Result};
use serde_json::{Map, Value};
use std::collections::{btree_map::Entry, BTreeMap};
use work_budget::WorkBudget;

/// A conflicting identity remains unresolved even if a later row repeats one
/// of its claims. This applies to byte identity and richer coordinate evidence.
pub(crate) enum IdentityState<T> {
    Unique(T),
    Conflict,
}

pub(crate) struct ScriptIdentityIndex<T> {
    sessions: BTreeMap<String, BTreeMap<String, IdentityState<T>>>,
}

impl<T> Default for ScriptIdentityIndex<T> {
    fn default() -> Self {
        Self {
            sessions: BTreeMap::new(),
        }
    }
}

impl<T: Eq> ScriptIdentityIndex<T> {
    pub(crate) fn register(&mut self, session: &str, script: &str, identity: T) {
        match self
            .sessions
            .entry(session.to_owned())
            .or_default()
            .entry(script.to_owned())
        {
            Entry::Vacant(entry) => {
                entry.insert(IdentityState::Unique(identity));
            }
            Entry::Occupied(mut entry) => {
                if matches!(entry.get(), IdentityState::Unique(previous) if previous != &identity) {
                    entry.insert(IdentityState::Conflict);
                }
            }
        }
    }

    pub(crate) fn invalidate(&mut self, session: &str, script: &str) {
        self.sessions
            .entry(session.to_owned())
            .or_default()
            .insert(script.to_owned(), IdentityState::Conflict);
    }

    pub(crate) fn lookup(&self, session: &str, script: &str) -> Option<&IdentityState<T>> {
        self.sessions.get(session)?.get(script)
    }

    pub(crate) fn get(&self, session: &str, script: &str) -> Option<&T> {
        match self.lookup(session, script)? {
            IdentityState::Unique(identity) => Some(identity),
            IdentityState::Conflict => None,
        }
    }

    pub(crate) fn unique_entries(&self) -> impl Iterator<Item = (&str, &str, &T)> {
        self.sessions.iter().flat_map(|(session, scripts)| {
            scripts
                .iter()
                .filter_map(move |(script, state)| match state {
                    IdentityState::Unique(value) => {
                        Some((session.as_str(), script.as_str(), value))
                    }
                    IdentityState::Conflict => None,
                })
        })
    }

    /// Join the stored body inventory to the raw-event conflict inventory.
    /// Contradictory source claims remain significant even when some claimed
    /// bodies were not saved. Enriching the record with coordinates can only
    /// remove certainty, never override the raw source conflict.
    pub(crate) fn from_runtime_report(
        report: &Value,
        budget: &WorkBudget,
        mut identity: impl FnMut(&str, &Value, &Value) -> Option<T>,
    ) -> Result<Self> {
        let mut index = Self::default();
        for source in rows(report, "sources") {
            budget.consume(1)?;
            let Some(sha) = nonempty_text(source.get("sha256")) else {
                continue;
            };
            for instance in rows(source, "script_instances") {
                budget.consume(1)?;
                let Some(session) = session_name(instance.get("cdp_session")) else {
                    continue;
                };
                let Some(script) = instance.get("script_id").and_then(script_id_text) else {
                    continue;
                };
                if let Some(value) = identity(sha, source, instance) {
                    index.register(session, &script, value);
                }
            }
        }
        for conflict in rows(report, "script_identity_conflicts") {
            budget.consume(1)?;
            let session = session_name(conflict.get("cdp_session"))
                .context("runtime identity conflict missing CDP session")?;
            let script = conflict
                .get("script_id")
                .and_then(script_id_text)
                .context("runtime identity conflict missing script ID")?;
            index.invalidate(session, &script);
        }
        Ok(index)
    }
}

pub(crate) fn captured_javascript_digest(event: &Map<String, Value>) -> Option<&str> {
    let captured = event.get("captured")?.as_object()?;
    (nonempty_text(captured.get("kind")) == Some("javascript"))
        .then(|| nonempty_text(captured.get("sha256")))
        .flatten()
}

fn rows<'a>(value: &'a Value, field: &str) -> &'a [Value] {
    value
        .get(field)
        .and_then(Value::as_array)
        .map_or_default(Vec::as_slice)
}

fn nonempty_text(value: Option<&Value>) -> Option<&str> {
    value
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn raw_event_conflicts_invalidate_stored_body_and_coordinate_indices() -> Result<()> {
        let report = json!({"sources":[{"sha256":"body-present","script_instances":[{"cdp_session":"main","script_id":"1","start_line":4},{"cdp_session":"worker","script_id":"1","start_line":6},{"cdp_session":"main","script_id":2,"start_line":8}]}],"script_identity_conflicts":[{"cdp_session":"main","script_id":"1","sha256_claims":["body-present","body-missing"]}]});
        let budget = WorkBudget::unlimited("identity-index");
        let mut bodies =
            ScriptIdentityIndex::from_runtime_report(&report, &budget, |sha, _, _| {
                Some(sha.to_owned())
            })?;
        assert!(matches!(
            bodies.lookup("main", "1"),
            Some(IdentityState::Conflict)
        ));
        bodies.register("main", "1", "body-present".into());
        assert!(bodies.get("main", "1").is_none());
        assert_eq!(
            bodies.get("worker", "1").map(String::as_str),
            Some("body-present")
        );
        assert_eq!(
            bodies.get("main", "2").map(String::as_str),
            Some("body-present")
        );
        let coords =
            ScriptIdentityIndex::from_runtime_report(&report, &budget, |sha, _, instance| {
                Some((sha.to_owned(), instance["start_line"].as_u64()))
            })?;
        assert!(coords.get("main", "1").is_none());
        assert_eq!(
            coords.get("worker", "1"),
            Some(&("body-present".into(), Some(6)))
        );
        Ok(())
    }
}
