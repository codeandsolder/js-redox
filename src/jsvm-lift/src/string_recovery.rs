use crate::{safe_deob::SourceMode, sha256_hex};
use serde_json::{json, Value};
use work_budget::{BudgetExceeded, WorkBudget};

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
    budget: &WorkBudget,
) -> Result<StaticStringRecoveryOutcome, BudgetExceeded> {
    let input_label = input_label.into();
    let safe_mode = source_mode.safe_mode();
    let classic = jsvm_safe_core::recover_static_decoders_with_source_mode(
        original,
        max_iterations,
        safe_mode,
        budget,
    )?;
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

    let base91 = jsvm_safe_core::recover_base91_strings_with_source_mode(
        &classic_source,
        4,
        safe_mode,
        budget,
    )?;
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
    Ok(StaticStringRecoveryOutcome { source, report })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scan_report::{scan_source, EmbeddedScanReport};
    use anyhow::{Context, Result};
    use std::{collections::BTreeSet, fs};
    use tempfile::TempDir;

    #[test]
    fn ordinary_crlf_source_is_byte_identical_when_nothing_is_proven() -> Result<()> {
        let source = "const answer = 42;\r\nconsole.log(answer);\r\n";
        let budget = WorkBudget::unlimited("ordinary-test");
        let outcome = recover_static_strings(source, "ordinary.js", SourceMode::Auto, 8, &budget)?;
        assert_eq!(outcome.source.as_bytes(), source.as_bytes());
        assert_eq!(outcome.report["changed"], false);
        assert_eq!(outcome.report["replacements"], 0);
        assert_eq!(
            outcome.report["base91_iterations"][0]["preflight_skipped"],
            true
        );
        Ok(())
    }

    #[test]
    fn dynamic_with_without_base91_stays_exact_identity() -> Result<()> {
        let source = "var value = 1; with ({}) { value; }\r\n";
        let budget = WorkBudget::unlimited("with-test");
        let outcome = recover_static_strings(source, "with.js", SourceMode::Auto, 8, &budget)?;
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
        Ok(())
    }
    fn dumped_generated_sources<'a>(rows: &'a [EmbeddedScanReport], output: &mut Vec<&'a str>) {
        for row in rows {
            if let Some(path) = row.dump_path.as_deref() {
                output.push(path);
            }
            dumped_generated_sources(&row.embedded, output);
        }
    }

    fn assert_generated_base91_fixture(
        source: &str,
        label: &str,
        expected_rotation: u64,
        expected_table_entries: u64,
        expected_decoder: Option<&str>,
    ) -> Result<()> {
        let scratch = TempDir::new()?;
        let budget = work_budget::WorkBudget::unlimited(format!("base91-fixture:{label}"));
        let scan = scan_source(
            source,
            label,
            Some(scratch.path()),
            SourceMode::Auto,
            &budget,
        )?;
        let mut dumps = Vec::new();
        dumped_generated_sources(&scan.embedded, &mut dumps);
        assert!(!dumps.is_empty(), "{label}: no generated source");

        let mut matching_report = None;
        for path in dumps {
            let generated = fs::read_to_string(path)
                .with_context(|| format!("reading generated fixture {path}"))?;
            let recovery_budget = WorkBudget::unlimited(format!("base91-recovery:{path}"));
            let outcome =
                recover_static_strings(&generated, path, SourceMode::Auto, 8, &recovery_budget)?;
            let shapes = outcome.report["decoders"]
                .as_array()
                .context("decoder rows must be an array")?
                .iter()
                .filter(|decoder| decoder["mode"] == "rotated_base91")
                .filter_map(|decoder| {
                    Some((
                        decoder["rotation"].as_u64()?,
                        decoder["table_entries"].as_u64()?,
                    ))
                })
                .collect::<BTreeSet<_>>();
            if shapes.contains(&(expected_rotation, expected_table_entries)) {
                matching_report = Some(outcome.report);
                break;
            }
        }

        let report = matching_report.with_context(|| {
            format!(
                "{label}: no generated child with Base91 family ({expected_rotation}, {expected_table_entries})"
            )
        })?;
        assert_eq!(report["changed"], true, "{label}");
        assert!(
            report["replacements"].as_u64().unwrap_or_default() >= 100,
            "{label}"
        );
        assert!(
            report["decoder_call_replacements"]
                .as_u64()
                .unwrap_or_default()
                >= 90,
            "{label}"
        );
        let base91 = report["decoders"]
            .as_array()
            .context("decoder rows must be an array")?
            .iter()
            .filter(|decoder| decoder["mode"] == "rotated_base91")
            .collect::<Vec<_>>();
        assert!(!base91.is_empty(), "{label}");
        let shapes = base91
            .iter()
            .filter_map(|decoder| {
                Some((
                    decoder["rotation"].as_u64()?,
                    decoder["table_entries"].as_u64()?,
                ))
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            shapes,
            BTreeSet::from([(expected_rotation, expected_table_entries)]),
            "{label}"
        );
        assert!(
            base91
                .iter()
                .any(|decoder| decoder["replacements"].as_u64().unwrap_or_default() > 0),
            "{label}"
        );
        if let Some(expected_decoder) = expected_decoder {
            assert!(
                base91.iter().any(|decoder| {
                    decoder["decoder"].as_str() == Some(expected_decoder)
                        && decoder["scope_start"].as_u64() == Some(0)
                        && decoder["replacements"].as_u64().unwrap_or_default() >= 400
                }),
                "{label}"
            );
        } else {
            assert!(
                base91.iter().any(|decoder| {
                    decoder["scope_start"].as_u64().unwrap_or_default() > 0
                        && decoder["replacements"].as_u64().unwrap_or_default() >= 10
                }),
                "{label}"
            );
        }
        Ok(())
    }

    #[test]
    fn depythonify_vm_base91_fixtures_preserve_decoder_scope_contracts() -> Result<()> {
        assert_generated_base91_fixture(
            include_str!("../../../corpus/generated/js-virtualizer/vm-obfuscated.js"),
            "vm-obfuscated.js",
            12,
            668,
            None,
        )?;
        // The affine fixture's tempting file-scope decoder performs its proven
        // table/transform lookup inside dynamic `with`. The deleted Python
        // regex harness ignored that interception boundary and over-recovered
        // >500 calls. Rust deliberately requires a statically resolved symbol
        // and therefore keeps only the independently proven nested decoders.
        assert_generated_base91_fixture(
            include_str!("../../../corpus/generated/js-virtualizer/vm-obfuscated-affine-cff.js"),
            "vm-obfuscated-affine-cff.js",
            2,
            613,
            None,
        )?;
        assert_generated_base91_fixture(
            include_str!(
                "../../../corpus/generated/js-virtualizer/vm-obfuscated-constructor-local.js"
            ),
            "vm-obfuscated-constructor-local.js",
            22,
            604,
            None,
        )?;
        assert_generated_base91_fixture(
            include_str!(
                "../../../corpus/generated/js-virtualizer/vm-obfuscated-flattened-base91.js"
            ),
            "vm-obfuscated-flattened-base91.js",
            7,
            650,
            Some("olQJbc"),
        )?;
        Ok(())
    }
}
