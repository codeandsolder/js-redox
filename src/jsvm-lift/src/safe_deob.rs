use crate::{forwarding_alias, js_format::format_source, sha256_hex};
use anyhow::{anyhow, Result};
use jsvm_safe_core::{SafeSourceMode, SafeSourceRecovery, SafeSourceRejection};
use serde::Serialize;
use std::{collections::BTreeMap, path::Path};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SourceMode {
    Auto,
    Module,
    CommonJs,
}

impl SourceMode {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Module => "module",
            Self::CommonJs => "commonjs",
        }
    }

    #[must_use]
    pub const fn suffix(self) -> &'static str {
        match self {
            Self::Auto => ".js",
            Self::Module => ".mjs",
            Self::CommonJs => ".cjs",
        }
    }

    #[must_use]
    pub const fn safe_mode(self) -> SafeSourceMode {
        match self {
            Self::Auto => SafeSourceMode::Auto,
            Self::Module => SafeSourceMode::Module,
            Self::CommonJs => SafeSourceMode::CommonJs,
        }
    }

    #[must_use]
    pub fn for_path(path: &Path) -> Self {
        match path.extension().and_then(|extension| extension.to_str()) {
            Some(extension) if extension.eq_ignore_ascii_case("mjs") => Self::Module,
            Some(extension) if extension.eq_ignore_ascii_case("cjs") => Self::CommonJs,
            _ => Self::Auto,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct ArithmeticStateProofReport {
    pub iteration: usize,
    pub input_start: usize,
    pub input_end: usize,
    pub state_var: String,
    pub state_path: Vec<String>,
    pub termination: String,
    pub register_reads_rewritten: usize,
    pub branch_test: Option<String>,
    pub branch_paths: Vec<Vec<String>>,
    pub branch_terminations: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct StaticAliasInstallerCallReport {
    pub start: u32,
    pub end: u32,
    pub installer: String,
    pub resolver: String,
    pub resolver_member: Option<String>,
    pub source_property: String,
    pub target_selector: u8,
    pub target_hint: Option<String>,
    pub alias_property: String,
    pub forwarding_installer_proven: bool,
    pub semantics_proven: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct SafeDeobReport {
    pub schema: &'static str,
    pub source_mode: &'static str,
    pub input: String,
    pub input_sha256: String,
    pub output_sha256: String,
    pub changed: bool,
    pub iterations: usize,
    pub transforms: BTreeMap<String, usize>,
    pub arithmetic_state_proofs: Vec<ArithmeticStateProofReport>,
    pub analysis_source_sha256: String,
    pub static_alias_installer_calls: Vec<StaticAliasInstallerCallReport>,
    pub safe_static_only: bool,
    pub presentation_formatted: bool,
    pub runtime_semantics_preserved_by_design: bool,
    pub analysis_complete: bool,
    pub source_recovery: Option<&'static str>,
}

#[derive(Debug, Clone)]
pub struct SafeDeobOutcome {
    pub source: String,
    pub report: SafeDeobReport,
}

pub fn deobfuscate_source(
    original: &str,
    input_label: impl Into<String>,
    source_mode: SourceMode,
    max_iterations: usize,
    format_output: bool,
) -> Result<SafeDeobOutcome> {
    let safe_mode = source_mode.safe_mode();
    let result = jsvm_safe_core::deobfuscate_with_source_mode(original, max_iterations, safe_mode)
        .ok_or_else(|| {
            let reason = jsvm_safe_core::safe_source_rejection(original, safe_mode)
                .map_or("rewrite-validation-failure", SafeSourceRejection::as_str);
            anyhow!("source rejected by safe deobfuscation: {reason}")
        })?;

    let arithmetic_state_proofs = result
        .arithmetic_state_proofs
        .iter()
        .map(|proof| ArithmeticStateProofReport {
            iteration: proof.iteration,
            input_start: proof.input_start,
            input_end: proof.input_end,
            state_var: proof.state_var.clone(),
            state_path: proof.state_path.clone(),
            termination: proof.termination.clone(),
            register_reads_rewritten: proof.register_reads_rewritten,
            branch_test: proof.branch_test.clone(),
            branch_paths: proof.branch_paths.clone(),
            branch_terminations: proof.branch_terminations.clone(),
        })
        .collect::<Vec<_>>();
    let iterations = result.iterations;
    let analysis_complete = result.analysis_complete;
    let source_recovery = result.source_recovery.map(SafeSourceRecovery::as_str);
    let analysis_source_sha256 = sha256_hex(result.source.as_bytes());
    let static_alias_installer_calls =
        forwarding_alias::static_alias_installer_calls(&result.source)
            .into_iter()
            .map(|call| {
                let target_hint = match (&call.resolver_member, call.target_selector) {
                    (Some(member), 0) => Some(member.clone()),
                    (Some(member), 1) => Some(format!("{member}.prototype")),
                    _ => None,
                };
                StaticAliasInstallerCallReport {
                    start: call.start,
                    end: call.end,
                    installer: call.installer,
                    resolver: call.resolver,
                    resolver_member: call.resolver_member,
                    source_property: call.source_property,
                    target_selector: call.target_selector,
                    target_hint,
                    alias_property: call.alias_property,
                    forwarding_installer_proven: call.forwarding_installer_proven,
                    semantics_proven: call.semantics_proven,
                }
            })
            .collect::<Vec<_>>();

    let mut transforms = result.transforms;
    let source = if format_output {
        let formatted = format_source(&result.source)?;
        if formatted != result.source {
            *transforms.entry("presentation_codegen".into()).or_default() += 1;
        }
        formatted
    } else {
        result.source
    };

    let report = SafeDeobReport {
        schema: "js-safe-deobfuscate/v1",
        source_mode: source_mode.as_str(),
        input: input_label.into(),
        input_sha256: sha256_hex(original.as_bytes()),
        output_sha256: sha256_hex(source.as_bytes()),
        changed: source != original,
        iterations,
        transforms,
        arithmetic_state_proofs,
        analysis_source_sha256,
        static_alias_installer_calls,
        safe_static_only: true,
        presentation_formatted: format_output,
        runtime_semantics_preserved_by_design: !format_output,
        analysis_complete,
        source_recovery,
    };

    Ok(SafeDeobOutcome { source, report })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_mode_follows_logical_suffix() {
        assert_eq!(
            SourceMode::for_path(Path::new("app.mjs")),
            SourceMode::Module
        );
        assert_eq!(
            SourceMode::for_path(Path::new("app.CJS")),
            SourceMode::CommonJs
        );
        assert_eq!(SourceMode::for_path(Path::new("app.js")), SourceMode::Auto);
    }

    #[test]
    fn report_hashes_exact_analysis_source_before_presentation_formatting() -> Result<()> {
        let source = "const x = 1 + 2; sink(x);\n";
        let outcome = deobfuscate_source(source, "fixture.js", SourceMode::Auto, 8, false)?;
        assert!(outcome.report.safe_static_only);
        assert!(outcome.report.runtime_semantics_preserved_by_design);
        assert_eq!(
            outcome.report.analysis_source_sha256,
            sha256_hex(outcome.source.as_bytes())
        );
        Ok(())
    }
}
