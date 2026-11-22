//! Shared normalization of CDP session-local script identities.

pub fn script_id_text(value: &serde_json::Value) -> Option<std::borrow::Cow<'_, str>> {
    use std::borrow::Cow;
    match value {
        serde_json::Value::String(id) if !id.is_empty() => Some(Cow::Borrowed(id)),
        serde_json::Value::Number(id) if id.is_u64() => Some(Cow::Owned(id.to_string())),
        _ => None,
    }
}

/// A session is an explicit nonempty recorder label, never a default or an ID
/// obtained by stringifying arbitrary JSON. Missing labels cannot join scripts.
pub fn session_name(value: Option<&Value>) -> Option<&str> {
    nonempty_text(value).filter(|session| !session.trim().is_empty())
}

use anyhow::{Context, Result};
use serde_json::{Map, Value};
use std::collections::{btree_map::Entry, BTreeMap};
use work_budget::WorkBudget;

/// A conflicting identity remains unresolved even if a later row repeats one
/// of its claims. This applies to byte identity and richer coordinate evidence.
pub enum IdentityState<T> {
    Unique(T),
    Conflict,
}

pub struct ScriptIdentityIndex<T> {
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
        self.register_with(session, script, identity, |previous, next| {
            *previous == next
        });
    }

    fn register_with(
        &mut self,
        session: &str,
        script: &str,
        identity: T,
        merge: impl FnOnce(&mut T, T) -> bool,
    ) {
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
                if let IdentityState::Unique(previous) = entry.get_mut() {
                    if !merge(previous, identity) {
                        entry.insert(IdentityState::Conflict);
                    }
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
        identity: impl FnMut(&str, &Value, &Value) -> T,
    ) -> Result<Self> {
        Self::from_runtime_report_with(report, budget, identity, |previous, next| *previous == next)
    }

    /// Merge independent contextual claims while rejecting incompatible identities.
    pub(crate) fn from_runtime_report_with(
        report: &Value,
        budget: &WorkBudget,
        mut identity: impl FnMut(&str, &Value, &Value) -> T,
        merge: impl Fn(&mut T, T) -> bool,
    ) -> Result<Self> {
        let mut index = Self::default();
        for source in rows(report, "sources") {
            budget.consume(1)?;
            let sha = nonempty_text(source.get("sha256"));
            for instance in rows(source, "script_instances") {
                budget.consume(1)?;
                let Some(session) = session_name(instance.get("cdp_session")) else {
                    continue;
                };
                let Some(script) = instance.get("script_id").and_then(script_id_text) else {
                    continue;
                };
                if let Some(sha) = sha {
                    index.register_with(session, &script, identity(sha, source, instance), &merge);
                } else {
                    // A scoped occurrence with no body claim cannot become
                    // invisible evidence merely because its digest is absent.
                    index.invalidate(session, &script);
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

/// Retain only fields on which all inventory occurrences agree. Unknown or
/// contradictory values remain unknown when more occurrences are merged.
pub fn retain_agreed<T: Eq>(current: &mut Option<T>, next: Option<T>) {
    if *current != next {
        *current = None;
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScriptOriginContext {
    pub(crate) url: Option<String>,
    pub(crate) execution_context_id: Option<u64>,
}

impl ScriptOriginContext {
    pub(crate) fn from_instance(instance: &Value) -> Self {
        Self {
            url: nonempty_text(instance.get("script_url")).map(ToOwned::to_owned),
            execution_context_id: instance.get("execution_context_id").and_then(Value::as_u64),
        }
    }
    pub(crate) fn retain_agreed(&mut self, other: Self) {
        retain_agreed(&mut self.url, other.url);
        retain_agreed(&mut self.execution_context_id, other.execution_context_id);
    }
}

pub fn captured_javascript_digest(event: &Map<String, Value>) -> Option<&str> {
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
    fn missing_body_claims_invalidate_only_their_scoped_instances() -> Result<()> {
        let digest = "body";
        let rows = json!([{"sha256":digest,"script_instances":[{"cdp_session":"main","script_id":"1"},{"cdp_session":"worker","script_id":"1"},{"cdp_session":"main","script_id":"2"}]},{"script_instances":[{"cdp_session":"main","script_id":"1"},{"script_id":"2"}]},{"sha256":digest,"script_instances":[{"cdp_session":"main","script_id":"1"}]}]);
        let budget = WorkBudget::unlimited("missing-inventory-claim");
        let index = ScriptIdentityIndex::from_runtime_report(
            &json!({"sources":rows}),
            &budget,
            |sha, _, _| sha.to_owned(),
        )?;
        assert!(matches!(
            index.lookup("main", "1"),
            Some(IdentityState::Conflict)
        ));
        assert_eq!(index.get("worker", "1").map(String::as_str), Some(digest));
        assert_eq!(index.get("main", "2").map(String::as_str), Some(digest));
        Ok(())
    }

    #[test]
    fn raw_event_conflicts_invalidate_stored_body_and_coordinate_indices() -> Result<()> {
        let report = json!({"sources":[{"sha256":"body-present","script_instances":[{"cdp_session":"main","script_id":"1","start_line":4},{"cdp_session":"worker","script_id":"1","start_line":6},{"cdp_session":"main","script_id":2,"start_line":8}]}],"script_identity_conflicts":[{"cdp_session":"main","script_id":"1","sha256_claims":["body-present","body-missing"]}]});
        let budget = WorkBudget::unlimited("identity-index");
        let mut bodies =
            ScriptIdentityIndex::from_runtime_report(&report, &budget, |sha, _, _| sha.to_owned())?;
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
                (sha.to_owned(), instance["start_line"].as_u64())
            })?;
        assert!(coords.get("main", "1").is_none());
        assert_eq!(
            coords.get("worker", "1"),
            Some(&("body-present".into(), Some(6)))
        );
        Ok(())
    }
}
