//! Comparable syntax inventories, deliberately independent of rewrite counts.
//! These describe parser structure, not proof coverage or functional equivalence.

use anyhow::{bail, Result};
use oxc_allocator::Allocator;
use oxc_ast::{
    ast::{Expression, Statement},
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::collections::BTreeMap;
use work_budget::{BudgetPoller, WorkBudget};

/// Oxc AST visitor events and syntactic categories, measured before formatting.
/// Statement counts exclude the parser's separately represented directives.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct SourceStructure {
    pub ast_nodes: u64,
    pub statements: u64,
    pub directives: u64,
    pub functions: u64,
    pub block_statements: u64,
    pub empty_statements: u64,
    pub sequence_expressions: u64,
    pub conditional_expressions: u64,
    pub logical_expressions: u64,
    pub switch_statements: u64,
    pub switch_cases: u64,
    pub literal_numeric_rhs_assignments: u64,
    pub computed_members: u64,
    /// Computed member keys without direct primitive literal syntax. This
    /// includes expressions that may nevertheless be statically resolvable.
    pub nonliteral_computed_members: u64,
    /// Syntactic branch/loop/try/ternary depth, reset at functions and
    /// class static blocks. Else-if chains contribute their actual AST depth.
    pub maximum_control_depth: usize,
    pub control_depth_histogram: BTreeMap<usize, u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SourceStructureComparison {
    pub resolved_source_mode: &'static str,
    pub original: SourceStructure,
    pub analysis: SourceStructure,
}

struct StructureVisitor {
    poller: BudgetPoller,
    exhausted: bool,
    profile: SourceStructure,
    depth: usize,
    outer_depths: Vec<usize>,
}

fn control_node(kind: AstKind<'_>) -> bool {
    matches!(
        kind,
        AstKind::IfStatement(_)
            | AstKind::ConditionalExpression(_)
            | AstKind::SwitchStatement(_)
            | AstKind::ForStatement(_)
            | AstKind::ForInStatement(_)
            | AstKind::ForOfStatement(_)
            | AstKind::WhileStatement(_)
            | AstKind::DoWhileStatement(_)
            | AstKind::TryStatement(_)
    )
}

fn execution_region(kind: AstKind<'_>) -> bool {
    matches!(
        kind,
        AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) | AstKind::StaticBlock(_)
    )
}

fn primitive_literal_key(expression: &Expression<'_>) -> bool {
    match expression.without_parentheses() {
        Expression::StringLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::BigIntLiteral(_) => true,
        Expression::TemplateLiteral(template) => template.expressions.is_empty(),
        _ => false,
    }
}

impl<'a> Visit<'a> for StructureVisitor {
    fn visit_statement(&mut self, statement: &Statement<'a>) {
        if self.exhausted {
            return;
        }
        self.profile.statements += 1;
        walk::walk_statement(self, statement);
    }

    fn visit_expression(&mut self, expression: &Expression<'a>) {
        if !self.exhausted {
            walk::walk_expression(self, expression);
        }
    }

    fn enter_node(&mut self, kind: AstKind<'a>) {
        if !self.poller.poll(1) {
            self.exhausted = true;
            return;
        }
        self.profile.ast_nodes += 1;
        if execution_region(kind) {
            self.outer_depths.push(self.depth);
            self.depth = 0;
        }
        if control_node(kind) {
            self.depth += 1;
            self.profile.maximum_control_depth = self.profile.maximum_control_depth.max(self.depth);
            *self
                .profile
                .control_depth_histogram
                .entry(self.depth)
                .or_default() += 1;
        }
        match kind {
            AstKind::Directive(_) => self.profile.directives += 1,
            AstKind::Function(_) | AstKind::ArrowFunctionExpression(_) => {
                self.profile.functions += 1
            }
            AstKind::BlockStatement(_) => self.profile.block_statements += 1,
            AstKind::EmptyStatement(_) => self.profile.empty_statements += 1,
            AstKind::SequenceExpression(_) => self.profile.sequence_expressions += 1,
            AstKind::ConditionalExpression(_) => self.profile.conditional_expressions += 1,
            AstKind::LogicalExpression(_) => self.profile.logical_expressions += 1,
            AstKind::SwitchStatement(_) => self.profile.switch_statements += 1,
            AstKind::SwitchCase(_) => self.profile.switch_cases += 1,
            AstKind::AssignmentExpression(assignment)
                if matches!(
                    assignment.right.without_parentheses(),
                    Expression::NumericLiteral(_)
                ) =>
            {
                self.profile.literal_numeric_rhs_assignments += 1;
            }
            AstKind::ComputedMemberExpression(member) => {
                self.profile.computed_members += 1;
                self.profile.nonliteral_computed_members +=
                    u64::from(!primitive_literal_key(&member.expression));
            }
            _ => {}
        }
    }

    fn leave_node(&mut self, kind: AstKind<'a>) {
        if self.exhausted {
            return;
        }
        if control_node(kind) {
            self.depth -= 1;
        }
        if execution_region(kind) {
            self.depth = self.outer_depths.pop().unwrap_or_default();
        }
    }
}

fn measure(source: &str, source_type: SourceType, budget: &WorkBudget) -> Result<SourceStructure> {
    budget.checkpoint()?;
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, source_type);
    budget.checkpoint()?;
    if !parsed.is_clean() {
        bail!("structural inventory could not parse the validated analysis mode");
    }
    let mut visitor = StructureVisitor {
        poller: BudgetPoller::new(budget, 256),
        exhausted: false,
        profile: SourceStructure::default(),
        depth: 0,
        outer_depths: Vec::new(),
    };
    visitor.visit_program(&parsed.program);
    visitor.poller.finish()?;
    Ok(visitor.profile)
}

fn source_mode_name(source_type: SourceType) -> &'static str {
    if source_type.is_module() {
        "module"
    } else if source_type.is_commonjs() {
        "commonjs"
    } else if source_type.is_script() {
        "script"
    } else {
        "unambiguous"
    }
}

pub(super) fn compare(
    original: &str,
    analysis: &str,
    source_type: SourceType,
    budget: &WorkBudget,
) -> Result<SourceStructureComparison> {
    let original_profile = measure(original, source_type, budget)?;
    let analysis_profile = if original == analysis {
        original_profile.clone()
    } else {
        measure(analysis, source_type, budget)?
    };
    Ok(SourceStructureComparison {
        resolved_source_mode: source_mode_name(source_type),
        original: original_profile,
        analysis: analysis_profile,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resets_control_depth_at_nested_execution_regions() -> Result<()> {
        let source = "if(a){if(b){const nested=()=>{if(c){while(d){x=e?1:2;}}};}}";
        let profile = measure(
            source,
            SourceType::cjs(),
            &WorkBudget::unlimited("structure"),
        )?;
        assert_eq!(profile.functions, 1);
        assert_eq!(profile.maximum_control_depth, 3);
        assert_eq!(
            profile.control_depth_histogram,
            BTreeMap::from([(1, 2), (2, 2), (3, 1)])
        );
        assert_eq!(profile.conditional_expressions, 1);
        Ok(())
    }

    #[test]
    fn identical_source_is_measured_once_and_budget_failure_is_not_partial() -> Result<()> {
        let source = "if(x){sink(y);}";
        let unlimited = WorkBudget::unlimited("structure");
        let count = measure(source, SourceType::cjs(), &unlimited)?.ast_nodes;
        let exact = WorkBudget::new("structure", work_budget::BudgetLimits::work(count));
        let comparison = compare(source, source, SourceType::cjs(), &exact)?;
        assert_eq!(comparison.original, comparison.analysis);
        assert_eq!(exact.remaining_work(), Some(0));
        let insufficient = WorkBudget::new("structure", work_budget::BudgetLimits::work(count - 1));
        let Err(error) = measure(source, SourceType::cjs(), &insufficient) else {
            bail!("structural measurement exceeded its allowance without reporting an error");
        };
        assert!(work_budget::find_budget_exceeded(error.as_ref()).is_some());
        Ok(())
    }

    #[test]
    fn distinguishes_literal_key_syntax_from_other_computed_members() -> Result<()> {
        let source = r#"obj["x"];obj[(1)];obj[true];obj[null];obj[1n];obj[`x`];obj[key];obj[-1];obj[`x${key}`];x=1;y+=2;z=f();(a,b);;"#;
        let profile = measure(
            source,
            SourceType::cjs(),
            &WorkBudget::unlimited("structure"),
        )?;
        assert_eq!(profile.computed_members, 9);
        assert_eq!(profile.nonliteral_computed_members, 3);
        assert_eq!(profile.literal_numeric_rhs_assignments, 2);
        assert_eq!(profile.sequence_expressions, 1);
        assert_eq!(profile.empty_statements, 1);
        Ok(())
    }
}
