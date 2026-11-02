use crate::{safe_deob::SourceMode, sha256_hex};
use serde_json::{json, Value};

#[derive(Debug, Clone)]
pub struct StaticStringRecoveryOutcome {
    pub source: String,
    pub report: Value,
}

#[must_use]
pub fn recover_static_strings(
    original: &str,
    input_label: impl Into<String>,
    source_mode: SourceMode,
    max_iterations: usize,
) -> StaticStringRecoveryOutcome {
    let input_label = input_label.into();
    let safe_mode = source_mode.safe_mode();
    let classic = jsvm_safe_core::recover_static_decoders_with_source_mode(
        original,
        max_iterations,
        safe_mode,
    );
    let (
        classic_source,
        classic_iterations,
        decoder_candidates,
        classic_transforms,
        classic_status,
    ) = match classic {
        Some(result) => (
            result.source,
            result.iterations,
            result.decoder_candidates,
            result.transforms,
            "proven",
        ),
        None => (
            original.to_string(),
            0,
            0,
            Default::default(),
            "parse_or_semantic_rejected",
        ),
    };
    let classic_replacements = classic_transforms.values().copied().sum::<usize>();
    let classic_report = json!({
        "schema": "js-static-decoder-recovery/v1",
        "source_mode": source_mode.as_str(),
        "input": input_label,
        "input_sha256": sha256_hex(original.as_bytes()),
        "output_sha256": sha256_hex(classic_source.as_bytes()),
        "changed": classic_source != original,
        "iterations": classic_iterations,
        "decoder_candidates": decoder_candidates,
        "replacements": classic_replacements,
        "transforms": classic_transforms,
        "safe_static_only": true,
        "status": classic_status,
    });

    let base91 =
        jsvm_safe_core::recover_base91_strings_with_source_mode(&classic_source, 4, safe_mode);
    let (source, decoders, base91_iterations, base91_replacements, base91_transforms) = match base91
    {
        Some(result) => {
            let decoder_rows = result
                .decoders
                .iter()
                .map(|decoder| {
                    json!({
                        "decoder": decoder.decoder,
                        "provider": decoder.provider,
                        "mode": "rotated_base91",
                        "offset": 0,
                        "rotation": decoder.rotation,
                        "table_entries": decoder.table_entries,
                        "aliases": [decoder.decoder.clone()],
                        "transform": decoder.transform,
                        "declaration_start": decoder.declaration_start,
                        "scope_start": decoder.scope_start,
                        "scope_end": decoder.scope_end,
                        "replacements": decoder.replacements,
                        "iteration": decoder.iteration,
                        "status": "proven",
                    })
                })
                .collect::<Vec<_>>();
            let iteration_rows = result
                    .iterations
                    .iter()
                    .map(|iteration| {
                        json!({
                            "iteration": iteration.iteration,
                            "preflight_skipped": iteration.preflight_skipped,
                            "decoder_calls": iteration.decoder_calls,
                            "immutable_string_table_replacements": iteration.immutable_string_table_replacements,
                            "literal_concat_folds": iteration.literal_concat_folds,
                        })
                    })
                    .collect::<Vec<_>>();
            (
                result.source,
                decoder_rows,
                iteration_rows,
                result.replacements,
                result.transforms,
            )
        }
        None => (
            classic_source.clone(),
            Vec::new(),
            vec![json!({
                "iteration": 1,
                "preflight_skipped": true,
                "decoder_calls": 0,
                "immutable_string_table_replacements": 0,
                "literal_concat_folds": 0,
            })],
            0,
            Default::default(),
        ),
    };
    let decoder_call_replacements = classic_transforms
        .get("string_array_decode")
        .copied()
        .unwrap_or(0)
        + base91_iterations
            .iter()
            .filter_map(|row| row.get("decoder_calls").and_then(Value::as_u64))
            .filter_map(|value| usize::try_from(value).ok())
            .sum::<usize>();
    let classic_decoder_calls = classic_transforms
        .get("string_array_decode")
        .copied()
        .unwrap_or(0);
    let replacements = classic_decoder_calls.saturating_add(base91_replacements);
    let report = json!({
        "schema": "js-static-string-recovery/v5",
        "safe_static_only": true,
        "changed": source != original,
        "input_sha256": sha256_hex(original.as_bytes()),
        "output_sha256": sha256_hex(source.as_bytes()),
        "classic_decoder_recovery": classic_report,
        "decoders": decoders,
        "decoder_call_replacements": decoder_call_replacements,
        "immutable_string_table_replacements": base91_iterations
            .iter()
            .filter_map(|row| row.get("immutable_string_table_replacements").and_then(Value::as_u64))
            .sum::<u64>(),
        "literal_concat_folds": base91_iterations
            .iter()
            .filter_map(|row| row.get("literal_concat_folds").and_then(Value::as_u64))
            .sum::<u64>(),
        "base91_iterations": base91_iterations,
        "base91_transforms": base91_transforms,
        "replacements": replacements,
    });
    StaticStringRecoveryOutcome { source, report }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordinary_crlf_source_is_byte_identical_when_nothing_is_proven() {
        let source = "const answer = 42;\r\nconsole.log(answer);\r\n";
        let outcome = recover_static_strings(source, "ordinary.js", SourceMode::Auto, 8);
        assert_eq!(outcome.source.as_bytes(), source.as_bytes());
        assert_eq!(outcome.report["changed"], false);
        assert_eq!(outcome.report["replacements"], 0);
        assert_eq!(
            outcome.report["base91_iterations"][0]["preflight_skipped"],
            true
        );
    }

    #[test]
    fn dynamic_with_without_base91_stays_exact_identity() {
        let source = "var value = 1; with ({}) { value; }\r\n";
        let outcome = recover_static_strings(source, "with.js", SourceMode::Auto, 8);
        assert_eq!(outcome.source.as_bytes(), source.as_bytes());
        assert_eq!(outcome.report["changed"], false);
        assert_eq!(outcome.report["replacements"], 0);
        assert_eq!(
            outcome.report["classic_decoder_recovery"]["status"],
            "parse_or_semantic_rejected"
        );
        assert_eq!(
            outcome.report["base91_iterations"][0]["preflight_skipped"],
            true
        );
    }
}
