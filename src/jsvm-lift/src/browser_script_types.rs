#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InlineScriptKind {
    JavaScript,
    Json,
    Text,
}

fn is_standard_executable_script_type(ty: &str) -> bool {
    matches!(
        ty,
        "module"
            | "text/javascript"
            | "application/javascript"
            | "application/ecmascript"
            | "text/ecmascript"
            | "application/x-ecmascript"
            | "application/x-javascript"
            | "text/javascript1.0"
            | "text/javascript1.1"
            | "text/javascript1.2"
            | "text/javascript1.3"
            | "text/javascript1.4"
            | "text/javascript1.5"
            | "text/jscript"
            | "text/livescript"
            | "text/x-ecmascript"
            | "text/x-javascript"
    )
}

#[must_use]
pub fn normalize_script_type(value: Option<&str>) -> String {
    let mut ty = value
        .unwrap_or("text/javascript")
        .trim()
        .to_ascii_lowercase();
    if let Some((essence, _)) = ty.split_once(';') {
        ty = essence.trim().to_owned();
    }
    if ty.is_empty() {
        ty = "text/javascript".into();
    }
    if let Some((prefix, suffix)) = ty.split_once('-') {
        if prefix.len() >= 16
            && prefix.bytes().all(|byte| byte.is_ascii_hexdigit())
            && is_standard_executable_script_type(suffix)
        {
            return suffix.to_owned();
        }
    }
    ty
}

#[must_use]
pub fn inline_script_kind(value: Option<&str>) -> InlineScriptKind {
    let ty = normalize_script_type(value);
    if is_standard_executable_script_type(&ty) {
        InlineScriptKind::JavaScript
    } else if matches!(ty.as_str(), "importmap" | "speculationrules") || ty.contains("json") {
        InlineScriptKind::Json
    } else {
        InlineScriptKind::Text
    }
}

#[must_use]
pub fn inline_script_extension(value: Option<&str>) -> &'static str {
    match inline_script_kind(value) {
        InlineScriptKind::JavaScript => "js",
        InlineScriptKind::Json => "json",
        InlineScriptKind::Text => "txt",
    }
}

#[must_use]
pub fn is_executable_script(value: Option<&str>) -> bool {
    inline_script_kind(value) == InlineScriptKind::JavaScript
}

#[must_use]
pub fn is_json_script(value: Option<&str>) -> bool {
    inline_script_kind(value) == InlineScriptKind::Json
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalizes_executable_and_rocket_loader_types() {
        assert_eq!(normalize_script_type(None), "text/javascript");
        assert_eq!(
            normalize_script_type(Some(" Text/JavaScript ; charset=utf-8 ")),
            "text/javascript"
        );
        assert_eq!(
            normalize_script_type(Some("80bb470769a376240e5e4e06-text/javascript")),
            "text/javascript"
        );
        assert!(is_executable_script(Some("module")));
        assert!(!is_executable_script(Some(
            "80bb470769a376240e5e4e06-application/json"
        )));
    }

    #[test]
    fn classifies_structured_and_inert_script_types() {
        assert_eq!(
            inline_script_kind(Some("importmap")),
            InlineScriptKind::Json
        );
        assert_eq!(
            inline_script_kind(Some("application/ld+json")),
            InlineScriptKind::Json
        );
        assert_eq!(
            inline_script_kind(Some("text/x-template")),
            InlineScriptKind::Text
        );
    }
}
