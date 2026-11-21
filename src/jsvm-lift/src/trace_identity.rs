//! Shared identity checks for bounded debugger observations.

use serde_json::Value;

/// Match the recorded function locations and source identities of the entire
/// stack, rather than just the script hosting the innermost frame.
pub(crate) fn same_observed_call_stack(first: &Value, second: &Value) -> bool {
    let (Some(a), Some(b)) = (
        first.get("frames").and_then(Value::as_array),
        second.get("frames").and_then(Value::as_array),
    ) else {
        return false;
    };
    !a.is_empty()
        && a.len() == b.len()
        && a.iter().zip(b).all(|(a, b)| {
            a.get("functionLocation").is_some_and(|location| {
                !location.is_null() && b.get("functionLocation") == Some(location)
            }) && a.get("sourceSha256") == b.get("sourceSha256")
        })
}
