use crate::binding_facts::BindingFacts;
use crate::rewrite::{apply, Counts, Replacement};
use crate::value_eval::{canonical_array_index, eval, eval_binary, Value};
use crate::{
    array_element, parse_as, reference_is_statically_resolved_read, semantically_valid_source_type,
    SafeSourceMode,
};
use oxc_allocator::Allocator;
use oxc_ast::ast::{BindingPattern, ComputedMemberExpression, Expression, VariableDeclarationKind};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping, SemanticBuilder};
use oxc_span::Span;
use oxc_syntax::symbol::SymbolId;
use std::collections::{BTreeMap, HashMap};

use work_budget::{BudgetExceeded, WorkBudget};

#[derive(Default)]
struct StaticArrayCandidateCollector {
    arrays: HashMap<SymbolId, Vec<Value>>,
}

impl<'a> Visit<'a> for StaticArrayCandidateCollector {
    fn visit_variable_declaration(&mut self, declaration: &oxc_ast::ast::VariableDeclaration<'a>) {
        if declaration.kind == VariableDeclarationKind::Const {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    continue;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    continue;
                };
                let Some(Expression::ArrayExpression(array)) = &declarator.init else {
                    continue;
                };
                let Some(values) = array
                    .elements
                    .iter()
                    .map(array_element)
                    .collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                if !values.is_empty() {
                    self.arrays.insert(symbol, values);
                }
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

fn static_array_index(expr: &Expression<'_>) -> Option<usize> {
    usize::try_from(canonical_array_index(&eval(expr)?)?).ok()
}

#[derive(Default)]
struct StaticArrayReadCollector {
    references: HashMap<ReferenceId, usize>,
}

impl<'a> Visit<'a> for StaticArrayReadCollector {
    fn visit_computed_member_expression(&mut self, member: &ComputedMemberExpression<'a>) {
        if !member.optional {
            if let (Expression::Identifier(identifier), Some(index)) =
                (&member.object, static_array_index(&member.expression))
            {
                if let Some(reference_id) = identifier.reference_id.get() {
                    self.references.insert(reference_id, index);
                }
            }
        }
        walk::walk_computed_member_expression(self, member);
    }
}

pub fn static_readonly_arrays(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> HashMap<SymbolId, Vec<Value>> {
    let mut candidate_collector = StaticArrayCandidateCollector::default();
    candidate_collector.visit_program(program);
    let mut read_collector = StaticArrayReadCollector::default();
    read_collector.visit_program(program);
    let mut out = candidate_collector.arrays;
    out.retain(|symbol, values| {
        facts.is_private(scoping, *symbol)
            && scoping
                .get_resolved_reference_ids(*symbol)
                .iter()
                .all(|reference_id| {
                    read_collector
                        .references
                        .get(reference_id)
                        .is_some_and(|index| *index < values.len())
                        && reference_is_statically_resolved_read(scoping, *reference_id, *symbol)
                })
    });
    out
}

pub fn static_array_lookup_text(
    member: &ComputedMemberExpression<'_>,
    scoping: &Scoping,
    arrays: &HashMap<SymbolId, Vec<Value>>,
    facts: &BindingFacts,
) -> Option<String> {
    if member.optional {
        return None;
    }
    let symbol = facts.initialized_read(scoping, &member.object)?;
    let values = arrays.get(&symbol)?;
    let index = static_array_index(&member.expression)?;
    values.get(index)?.render()
}

fn literal_string_concat_text(binary: &oxc_ast::ast::BinaryExpression<'_>) -> Option<String> {
    if binary.operator.as_str() != "+" {
        return None;
    }
    let value = eval_binary("+", &eval(&binary.left)?, &eval(&binary.right)?)?;
    match value {
        Value::String(_) => value.render(),
        _ => None,
    }
}

struct StaticStringExposureCollector<'c> {
    scoping: &'c Scoping,
    arrays: &'c HashMap<SymbolId, Vec<Value>>,
    facts: &'c BindingFacts,
    replacements: Vec<Replacement>,
}

impl StaticStringExposureCollector<'_> {
    fn push(&mut self, span: Span, text: String, kind: &'static str) {
        self.replacements.push(Replacement {
            start: span.start as usize,
            end: span.end as usize,
            text,
            kind,
            arithmetic_state_proof: None,
        });
    }
}

impl<'a> Visit<'a> for StaticStringExposureCollector<'_> {
    fn visit_binary_expression(&mut self, binary: &oxc_ast::ast::BinaryExpression<'a>) {
        if let Some(text) = literal_string_concat_text(binary) {
            self.push(binary.span, text, "literal_string_concat");
            return;
        }
        walk::walk_binary_expression(self, binary);
    }

    fn visit_computed_member_expression(&mut self, member: &ComputedMemberExpression<'a>) {
        if let Some(text) = static_array_lookup_text(member, self.scoping, self.arrays, self.facts)
        {
            self.push(member.span, text, "static_string_table_lookup");
            return;
        }
        walk::walk_computed_member_expression(self, member);
    }
}

pub fn static_string_exposure_pass(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> Vec<Replacement> {
    let facts = BindingFacts::analyze(program);
    let arrays = static_readonly_arrays(program, scoping, &facts);
    let mut collector = StaticStringExposureCollector {
        scoping,
        arrays: &arrays,
        facts: &facts,
        replacements: Vec::new(),
    };
    collector.visit_program(program);
    collector.replacements
}

#[derive(Debug, Clone)]
pub struct StaticStringExposureResult {
    pub source: String,
    pub iterations: usize,
    pub transforms: BTreeMap<String, usize>,
}

fn expose_static_strings_with_mode(
    source: &str,
    max_iterations: usize,
    source_mode: SafeSourceMode,
    budget: &WorkBudget,
) -> Result<Option<StaticStringExposureResult>, BudgetExceeded> {
    budget.checkpoint()?;
    let Some(source_type) = semantically_valid_source_type(source, source_mode) else {
        return Ok(None);
    };
    budget.checkpoint()?;
    let mut current = source.to_string();
    let mut counts = Counts::default();
    let mut iterations = 0usize;

    for iteration in 1..=max_iterations {
        budget.consume(1)?;
        let allocator = Allocator::default();
        let Some(program) = parse_as(&allocator, &current, source_type) else {
            return Ok(None);
        };
        budget.checkpoint()?;
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if !semantic_ret.diagnostics.is_empty() {
            return Ok(None);
        }
        budget.checkpoint()?;
        let scoping = semantic_ret.semantic.scoping();
        let replacements = static_string_exposure_pass(&program, scoping);
        budget.checkpoint()?;
        if replacements.is_empty() {
            break;
        }
        let Some(next) = apply(
            &program,
            replacements,
            &mut counts,
            &mut Vec::new(),
            iteration,
        ) else {
            return Ok(None);
        };
        if next == current {
            break;
        }
        iterations += 1;
        current = next;
    }

    Ok(Some(StaticStringExposureResult {
        source: current,
        iterations,
        transforms: counts.into_inner(),
    }))
}

/// # Errors
/// Returns `BudgetExceeded` if the configured work budget is exhausted.
pub fn expose_static_strings(
    source: &str,
    max_iterations: usize,
    budget: &WorkBudget,
) -> Result<Option<StaticStringExposureResult>, BudgetExceeded> {
    expose_static_strings_with_mode(source, max_iterations, SafeSourceMode::Auto, budget)
}

/// # Errors
/// Returns `BudgetExceeded` if the configured work budget is exhausted.
pub fn expose_static_strings_with_source_mode(
    source: &str,
    max_iterations: usize,
    source_mode: SafeSourceMode,
    budget: &WorkBudget,
) -> Result<Option<StaticStringExposureResult>, BudgetExceeded> {
    expose_static_strings_with_mode(source, max_iterations, source_mode, budget)
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_span::SourceType;

    #[test]
    fn dynamic_with_scope_blocks_only_affected_array_reads() {
        let source = r#"
            {
            const blocked = ["outer"];
            const safe = ["safe"];
            with ({ blocked: ["inner"] }) {
                sink(blocked[0]);
            }
            sink(safe[0]);
            }
        "#;
        let allocator = Allocator::default();
        let program = parse_as(&allocator, source, SourceType::cjs());
        assert!(program.is_some());
        let Some(program) = program else {
            return;
        };
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        assert!(semantic_ret.diagnostics.is_empty());
        let scoping = semantic_ret.semantic.scoping();
        let replacements = static_string_exposure_pass(&program, scoping);
        assert_eq!(replacements.len(), 1);

        let rewritten = apply(
            &program,
            replacements,
            &mut Counts::default(),
            &mut Vec::new(),
            1,
        );
        assert!(rewritten.is_some());
        let rewritten = rewritten.unwrap_or_default();
        assert!(rewritten.contains("sink(blocked[0])"));
        assert!(rewritten.contains("sink(\"safe\")"));
    }
}
