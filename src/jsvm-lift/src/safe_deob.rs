use crate::{forwarding_alias, js_format::format_source_as, sha256_hex};
use anyhow::{anyhow, Result};
use jsvm_safe_core::{SafeSourceMode, SafeSourceRecovery, SafeSourceRejection};
use oxc_span::SourceType;
use serde::Serialize;
use std::{collections::BTreeMap, path::Path};
use work_budget::WorkBudget;

mod source_structure;
pub use source_structure::{SourceStructure, SourceStructureComparison};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SourceMode {
    Auto,
    Module,
    CommonJs,
}

impl SourceMode {
    #[must_use = "Use the returned stable spelling when serializing or displaying this value"]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Module => "module",
            Self::CommonJs => "commonjs",
        }
    }

    #[must_use = "Use the returned suffix for the selected source mode"]
    pub const fn suffix(self) -> &'static str {
        match self {
            Self::Auto => ".js",
            Self::Module => ".mjs",
            Self::CommonJs => ".cjs",
        }
    }

    #[must_use = "Use the converted mode when invoking the safe analysis"]
    pub const fn safe_mode(self) -> SafeSourceMode {
        match self {
            Self::Auto => SafeSourceMode::Auto,
            Self::Module => SafeSourceMode::Module,
            Self::CommonJs => SafeSourceMode::CommonJs,
        }
    }

    #[must_use = "Use the returned parser source type to preserve language semantics"]
    pub const fn source_type(self) -> SourceType {
        match self {
            Self::Auto => SourceType::unambiguous(),
            Self::Module => SourceType::mjs(),
            Self::CommonJs => SourceType::cjs(),
        }
    }

    #[must_use = "Use the inferred source mode when parsing this path"]
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

/// Guarantees of the emitted source, independent of iteration convergence.
#[derive(Debug, Clone, Serialize)]
pub struct OutputGuarantees {
    pub safe_static_only: bool,
    pub presentation_formatted: bool,
    pub runtime_semantics_preserved_by_design: bool,
}

impl OutputGuarantees {
    const fn new(format_output: bool) -> Self {
        Self {
            safe_static_only: true,
            presentation_formatted: format_output,
            runtime_semantics_preserved_by_design: !format_output,
        }
    }
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
    /// Syntax inventory under the exact same validated parser mode, before
    /// optional presentation code generation. Null for browser-legacy recovery.
    pub structure: Option<SourceStructureComparison>,
    pub arithmetic_state_proofs: Vec<ArithmeticStateProofReport>,
    pub analysis_source_sha256: String,
    pub static_alias_installer_calls: Vec<StaticAliasInstallerCallReport>,
    #[serde(flatten)]
    pub guarantees: OutputGuarantees,
    /// A validated no-op pass was observed before the iteration limit.
    pub analysis_complete: bool,
    /// Nontrivial multi-pass cycle (the ordinary no-op fixed point is separate).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub iteration_cycle: Option<IterationCycleReport>,
    pub source_recovery: Option<&'static str>,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct IterationCycleReport {
    pub first_seen_iteration: usize,
    pub repeated_at_iteration: usize,
    pub period: usize,
    pub source_sha256: String,
}

impl From<&jsvm_safe_core::IterationCycle> for IterationCycleReport {
    fn from(cycle: &jsvm_safe_core::IterationCycle) -> Self {
        Self {
            first_seen_iteration: cycle.first_seen_iteration,
            repeated_at_iteration: cycle.repeated_at_iteration,
            period: cycle.period,
            source_sha256: cycle.source_sha256.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SafeDeobOutcome {
    pub source: String,
    pub report: SafeDeobReport,
}

/// Run conservative, source-mode-aware deobfuscation and produce its proof report.
///
/// # Errors
///
/// Fails if the source is rejected by safe deobfuscation or rewrite validation, or if
/// work-budget checks or downstream proof analyses fail.
pub fn deobfuscate_source(
    original: &str,
    input_label: impl Into<String>,
    source_mode: SourceMode,
    max_iterations: usize,
    format_output: bool,
    budget: &WorkBudget,
) -> Result<SafeDeobOutcome> {
    let safe_mode = source_mode.safe_mode();
    let result =
        jsvm_safe_core::deobfuscate_with_source_mode(original, max_iterations, safe_mode, budget)?
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
    let iteration_cycle = result
        .iteration_cycle
        .as_ref()
        .map(IterationCycleReport::from);
    let source_recovery = result.source_recovery.map(SafeSourceRecovery::as_str);
    let analysis_source_sha256 = sha256_hex(result.source.as_bytes());
    let structure = result
        .resolved_source_type
        .map(|source_type| source_structure::compare(original, &result.source, source_type, budget))
        .transpose()?;
    let static_alias_installer_calls =
        forwarding_alias::static_alias_installer_calls(&result.source, budget)?
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
        let source_type = result
            .resolved_source_type
            .ok_or_else(|| anyhow!("cannot format source without a validated parser mode"))?;
        let formatted = format_source_as(&result.source, source_type, budget)?;
        if formatted != result.source {
            *transforms.entry("presentation_codegen".into()).or_default() += 1;
        }
        formatted
    } else {
        result.source
    };

    let report = SafeDeobReport {
        schema: "js-safe-deobfuscate/v3",
        source_mode: source_mode.as_str(),
        input: input_label.into(),
        input_sha256: sha256_hex(original.as_bytes()),
        output_sha256: sha256_hex(source.as_bytes()),
        changed: source != original,
        iterations,
        transforms,
        structure,
        arithmetic_state_proofs,
        analysis_source_sha256,
        static_alias_installer_calls,
        guarantees: OutputGuarantees::new(format_output),
        analysis_complete,
        iteration_cycle,
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
    fn report_distinguishes_iteration_limit_from_fixed_point() -> Result<()> {
        let source = "sink(1 + 2);";
        let budget = WorkBudget::unlimited("safe-deob-test");
        let capped = deobfuscate_source(source, "fixture.js", SourceMode::Auto, 1, false, &budget)?;
        let complete =
            deobfuscate_source(source, "fixture.js", SourceMode::Auto, 8, false, &budget)?;
        assert!(capped.report.changed);
        assert!(!capped.report.analysis_complete);
        assert!(complete.report.analysis_complete);
        assert_eq!(capped.source, complete.source);
        assert!(capped.report.structure.is_some());
        assert_eq!(capped.report.structure, complete.report.structure);
        Ok(())
    }

    #[test]
    fn report_structure_uses_analysis_source_not_optional_formatting() -> Result<()> {
        let source = "function f(x){ { {x+=1;} } return x;}";
        let budget = WorkBudget::unlimited("structure-report");
        let plain =
            deobfuscate_source(source, "fixture.mjs", SourceMode::Module, 8, false, &budget)?;
        let formatted =
            deobfuscate_source(source, "fixture.mjs", SourceMode::Module, 8, true, &budget)?;
        assert_eq!(plain.report.structure, formatted.report.structure);
        let structure = plain
            .report
            .structure
            .ok_or_else(|| anyhow!("missing structure"))?;
        assert_eq!(structure.resolved_source_mode, "module");
        assert_eq!(structure.original.block_statements, 2);
        assert_eq!(structure.analysis.block_statements, 0);
        assert_eq!(structure.original.functions, structure.analysis.functions);
        Ok(())
    }

    #[test]
    fn report_does_not_invent_structure_for_unparseable_legacy_source() -> Result<()> {
        let source = "function target() {} target() = 1;";
        let budget = WorkBudget::unlimited("structure-legacy");
        let outcome = deobfuscate_source(
            source,
            "fixture.cjs",
            SourceMode::CommonJs,
            8,
            false,
            &budget,
        )?;
        assert_eq!(outcome.source, source);
        assert!(outcome.report.structure.is_none());
        assert!(!outcome.report.analysis_complete);
        Ok(())
    }

    #[test]
    fn formatting_uses_the_core_validated_script_mode() -> Result<()> {
        let budget = WorkBudget::unlimited("format-script-mode");
        let source = "var await=1; sink(await);";
        let plain = deobfuscate_source(
            source,
            "fixture.cjs",
            SourceMode::CommonJs,
            8,
            false,
            &budget,
        )?;
        let formatted = deobfuscate_source(
            source,
            "fixture.cjs",
            SourceMode::CommonJs,
            8,
            true,
            &budget,
        )?;
        assert_eq!(formatted.report.structure, plain.report.structure);
        assert_eq!(
            formatted.source,
            format_source_as(&plain.source, SourceType::cjs(), &budget)?
        );
        Ok(())
    }

    #[test]
    fn report_hashes_exact_analysis_source_before_presentation_formatting() -> Result<()> {
        let source = "const x = 1 + 2; sink(x);\n";
        let budget = WorkBudget::unlimited("safe-deob-test");
        let outcome =
            deobfuscate_source(source, "fixture.js", SourceMode::Auto, 8, false, &budget)?;
        assert!(outcome.report.guarantees.safe_static_only);
        assert!(
            outcome
                .report
                .guarantees
                .runtime_semantics_preserved_by_design
        );
        assert_eq!(
            outcome.report.analysis_source_sha256,
            sha256_hex(outcome.source.as_bytes())
        );
        Ok(())
    }
}

#[cfg(test)]
#[path = "safe_deob_runtime_tests.rs"]
mod runtime_equivalence;
