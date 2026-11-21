//! Shared normalization of CDP session-local script identities.

pub(crate) fn script_id_text(value: &serde_json::Value) -> Option<std::borrow::Cow<'_, str>> {
    use std::borrow::Cow;
    match value {
        serde_json::Value::String(id) if !id.is_empty() => Some(Cow::Borrowed(id)),
        serde_json::Value::Number(id) if id.is_u64() => Some(Cow::Owned(id.to_string())),
        _ => None,
    }
}
