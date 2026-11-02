//! Central analysis work-budget policy.
//!
//! The generic mechanism lives in `work-budget`; this module owns js-redox's
//! operation classes and their default wall-clock envelopes. Callers derive a
//! named child budget for each independently useful unit of work and pass that
//! budget through the analysis stack.

use anyhow::{Error as AnyError, Result};
use std::time::Duration;
use work_budget::{find_budget_exceeded, BudgetLimits, WorkBudget};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnalysisOperation {
    CaptureImport,
    SyntaxCheck,
    Format,
    StaticStringRecovery,
    SafeDeobfuscation,
    StructuralScan,
    IrMaterialization,
    VmMaterialization,
    ApiSurface,
    SourceMaterialization,
    ReferenceScan,
    SourcemapRecovery,
    BundleMaterialization,
    WasmAnalysis,
    RuntimeAnalysis,
    SourceGraph,
    ProjectReadme,
    CorpusEvaluation,
}

impl AnalysisOperation {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CaptureImport => "capture-import",
            Self::SyntaxCheck => "syntax-check",
            Self::Format => "format",
            Self::StaticStringRecovery => "static-string-recovery",
            Self::SafeDeobfuscation => "safe-deobfuscation",
            Self::StructuralScan => "structural-scan",
            Self::IrMaterialization => "ir-materialization",
            Self::VmMaterialization => "vm-materialization",
            Self::ApiSurface => "api-surface",
            Self::SourceMaterialization => "source-materialization",
            Self::ReferenceScan => "reference-scan",
            Self::SourcemapRecovery => "sourcemap-recovery",
            Self::BundleMaterialization => "bundle-materialization",
            Self::WasmAnalysis => "wasm-analysis",
            Self::RuntimeAnalysis => "runtime-analysis",
            Self::SourceGraph => "source-graph",
            Self::ProjectReadme => "project-readme",
            Self::CorpusEvaluation => "corpus-evaluation",
        }
    }

    #[must_use]
    pub const fn limits(self) -> BudgetLimits {
        // These envelopes preserve the useful containment behavior of the old
        // process wrappers while moving enforcement into the algorithms. The
        // deterministic `work` dimension remains available for individual
        // algorithms once they expose meaningful units.
        let seconds = match self {
            Self::CaptureImport => 240,
            Self::SyntaxCheck => 90,
            Self::Format => 120,
            Self::StaticStringRecovery | Self::SafeDeobfuscation => 180,
            Self::StructuralScan => 120,
            Self::IrMaterialization => 180,
            Self::VmMaterialization => 180,
            Self::ApiSurface => 120,
            Self::SourceMaterialization => 120,
            Self::ReferenceScan => 120,
            Self::SourcemapRecovery => 120,
            Self::BundleMaterialization => 180,
            Self::WasmAnalysis => 180,
            Self::RuntimeAnalysis => 120,
            Self::SourceGraph => 120,
            Self::ProjectReadme => 120,
            Self::CorpusEvaluation => 360,
        };
        BudgetLimits::wall_time(Duration::from_secs(seconds))
    }
}

#[derive(Debug, Clone)]
pub struct AnalysisBudgets {
    root: WorkBudget,
}

impl AnalysisBudgets {
    #[must_use]
    pub fn new(scope: impl Into<std::sync::Arc<str>>, limits: BudgetLimits) -> Self {
        Self {
            root: WorkBudget::new(scope, limits),
        }
    }

    #[must_use]
    pub fn standard(scope: impl Into<std::sync::Arc<str>>) -> Self {
        Self::new(scope, BudgetLimits::unlimited())
    }

    #[must_use]
    pub fn scope(&self, label: impl AsRef<str>) -> WorkBudget {
        self.root.child(
            format!("scope:{}", label.as_ref()),
            BudgetLimits::unlimited(),
        )
    }

    #[must_use]
    pub fn operation(&self, operation: AnalysisOperation, label: impl AsRef<str>) -> WorkBudget {
        self.operation_under(&self.root, operation, label)
    }

    #[must_use]
    pub fn operation_under(
        &self,
        parent: &WorkBudget,
        operation: AnalysisOperation,
        label: impl AsRef<str>,
    ) -> WorkBudget {
        let scope = format!("{}:{}", operation.as_str(), label.as_ref());
        parent.child(scope, operation.limits())
    }

    #[must_use]
    pub fn root(&self) -> &WorkBudget {
        &self.root
    }
}

/// Preserve the existing per-unit failure semantics without swallowing a
/// project/stage cancellation. Local operation exhaustion is returned to the
/// caller for recording as that unit's failure; inherited exhaustion aborts
/// the enclosing workflow. Non-budget errors are unchanged.
pub fn recoverable_unit_error(error: AnyError) -> Result<AnyError> {
    if find_budget_exceeded(error.as_ref()).is_some_and(|budget| budget.is_inherited()) {
        return Err(error);
    }
    Ok(error)
}

#[cfg(test)]
mod tests {
    use super::*;
    use work_budget::BudgetExceededKind;

    #[test]
    fn operation_budget_inherits_root_limit() {
        let budgets = AnalysisBudgets::new("project", BudgetLimits::work(2));
        let scan = budgets.operation(AnalysisOperation::StructuralScan, "fixture.js");
        assert!(scan.consume(2).is_ok());
        assert!(matches!(
            scan.consume(1),
            Err(error) if error.kind() == BudgetExceededKind::Work && error.scope() == "project"
        ));
    }

    #[test]
    fn nested_operation_reports_stage_exhaustion_as_inherited() {
        let budgets = AnalysisBudgets::standard("project");
        let stage = WorkBudget::new("stage", BudgetLimits::work(1));
        let unit = budgets.operation_under(&stage, AnalysisOperation::StructuralScan, "fixture.js");
        assert!(unit.consume(1).is_ok());
        assert!(matches!(
            unit.consume(1),
            Err(ref error) if error.scope() == "stage" && error.is_inherited()
        ));
    }

    #[test]
    fn inherited_budget_errors_are_not_recoverable_unit_failures() {
        let root = WorkBudget::new("project", BudgetLimits::work(0));
        let unit = root.child("unit", BudgetLimits::work(1));
        let error = unit
            .consume(1)
            .expect_err("root budget should be exhausted");
        assert!(recoverable_unit_error(AnyError::new(error)).is_err());
    }
}
