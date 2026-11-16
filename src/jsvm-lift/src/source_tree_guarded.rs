//! Install source-proven, selector-specific fast paths *inside* the original
//! function body.
//!
//! The original callable, its .call lookup and its unmodified fallback body remain
//! in place. Guards inspect only simple formal bindings.
//!
//! Caller supplies variants proven by source_tree_specialize and transformed
//! through the ordinary safe deobfuscator; this module rechecks the binding
//! proof and lexical identity before installing any branch.
use crate::source_tree_specialize::specialize_function;
use anyhow::{anyhow, ensure, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, Expression, Function, Statement, VariableDeclaration, VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::SourceType;
use oxc_syntax::scope::ScopeFlags;
use rolldown_redox::ecmascript::parse_program;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

#[derive(Debug, Clone)]
pub struct GuardedVariant {
    pub function_span: [u32; 2],
    pub constants: Vec<(usize, String)>,
    pub original_wrapper: String,
    pub specialized_wrapper: String,
    pub optimized_wrapper: String,
}

#[derive(Debug)]
pub struct GuardedProgram {
    pub source: String,
    pub fast_paths: usize,
    pub targeted_functions: usize,
}

#[derive(Clone)]
struct FunctionSlot {
    span: [u32; 2],
    insertion: usize,
    parameters: Vec<String>,
}

struct Functions<'s> {
    scoping: &'s Scoping,
    slots: BTreeMap<[u32; 2], FunctionSlot>,
}

impl<'a> Visit<'a> for Functions<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let (Some(body), Some(scope)) = (&function.body, function.scope_id.get()) {
            let own_strict = body
                .directives
                .iter()
                .any(|directive| directive.directive == "use strict");
            let inherited_strict = self.scoping.scope_flags(scope).is_strict_mode() && !own_strict;
            // The detached specializer parses a wrapper in its own source
            // context. Strictness inherited only from the original enclosing
            // scope would otherwise change the meaning of the optimized body.
            if !inherited_strict && !function.r#async && !function.generator {
                let parameters = function
                    .params
                    .items
                    .iter()
                    .map(|param| {
                        if param.initializer.is_some() {
                            return None;
                        }
                        let BindingPattern::BindingIdentifier(id) = &param.pattern else {
                            return None;
                        };
                        Some(id.name.to_string())
                    })
                    .collect::<Option<Vec<_>>>();
                // Duplicate sloppy-mode formals can refer to the same
                // runtime binding at different argument positions. Guarding
                // by textual formal name would conflate those positions.
                if let Some(parameters) = parameters.filter(|names| {
                    let mut seen = BTreeSet::new();
                    names.iter().all(|name| seen.insert(name.as_str()))
                }) {
                    let insertion = body
                        .directives
                        .last()
                        .map_or(body.span.start as usize + 1, |directive| {
                            directive.span.end as usize
                        });
                    self.slots.insert(
                        [function.span.start, function.span.end],
                        FunctionSlot {
                            span: [function.span.start, function.span.end],
                            insertion,
                            parameters,
                        },
                    );
                }
            }
        }
        walk::walk_function(self, function, flags);
    }
}

fn wrapped_function<'a>(
    source: &'a str,
    parsed: &'a oxc_ast::ast::Program<'a>,
) -> Option<(&'a Function<'a>, &'a str)> {
    let Statement::VariableDeclaration(decl) = parsed.body.first()? else {
        return None;
    };
    let declarations = &decl.declarations;
    let mut expr = declarations.first()?.init.as_ref()?;
    while let Expression::ParenthesizedExpression(paren) = expr {
        expr = &paren.expression;
    }
    let Expression::FunctionExpression(function) = expr else {
        return None;
    };
    let slice = source.get(function.span.start as usize..function.span.end as usize)?;
    Some((function, slice))
}

fn literal_is_safe(text: &str) -> bool {
    let wrapper = format!("const __redox_guard_literal = ({text});");
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &wrapper, SourceType::unambiguous());
    if !parsed.is_clean() {
        return false;
    }
    let Some(Statement::VariableDeclaration(decl)) = parsed.program.body.first() else {
        return false;
    };
    let Some(mut expr) = decl
        .declarations
        .first()
        .and_then(|item| item.init.as_ref())
    else {
        return false;
    };
    while let Expression::ParenthesizedExpression(paren) = expr {
        expr = &paren.expression;
    }
    matches!(
        expr,
        Expression::NullLiteral(_)
            | Expression::BooleanLiteral(_)
            | Expression::NumericLiteral(_)
            | Expression::BigIntLiteral(_)
            | Expression::StringLiteral(_)
    ) || matches!(expr, Expression::UnaryExpression(unary)
            if matches!(unary.operator.as_str(), "+" | "-")
            && matches!(&unary.argument, Expression::NumericLiteral(_)))
}

fn condition(slot: &FunctionSlot, constants: &[(usize, String)]) -> Option<String> {
    if constants.is_empty() {
        return None;
    }
    let mut seen = BTreeSet::new();
    let mut expressions = Vec::new();
    for (index, literal) in constants {
        if !seen.insert(*index) || !literal_is_safe(literal) {
            return None;
        }
        let param = slot.parameters.get(*index)?;
        // Strict equality conflates +0 and -0; checking reciprocals only
        // when the value compares equal to numeric zero restores SameValue.
        // For all other primitives the right side short-circuits.
        expressions.push(format!(
            "({param} === ({literal}) && ({param} !== 0 || 1 / {param} === 1 / ({literal})))"
        ));
    }
    Some(expressions.join(" && "))
}

#[derive(Default)]
struct DeclarationHazards {
    function_declaration: bool,
    var_hoisting: bool,
}
impl<'a> Visit<'a> for DeclarationHazards {
    fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
        if declaration.kind == VariableDeclarationKind::Var {
            // A cloned var declaration could create a new function-scoped
            // binding even when the fast path is not taken.
            self.var_hoisting = true;
        }
        walk::walk_variable_declaration(self, declaration);
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if function.r#type == oxc_ast::ast::FunctionType::FunctionDeclaration {
            self.function_declaration = true;
        }
        walk::walk_function(self, function, flags);
    }
}

fn optimized_body(source: &str) -> Option<String> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    if !parsed.is_clean() {
        return None;
    }
    let (function, _) = wrapped_function(source, &parsed.program)?;
    if function.r#async || function.generator {
        return None;
    }
    let body = function.body.as_ref()?;
    let mut hazards = DeclarationHazards::default();
    hazards.visit_function_body(body);
    if hazards.function_declaration || hazards.var_hoisting {
        return None;
    }
    let start = body
        .directives
        .last()
        .map_or(body.span.start as usize + 1, |directive| {
            directive.span.end as usize
        });
    let end = body.span.end as usize - 1;
    Some(source.get(start..end)?.to_string())
}

/// All edges are independently proven pure selector comparisons; ordering
/// them by formal index shares tests without changing which input tuples
/// select a verified optimized body.
#[derive(Default)]
struct SelectorDispatch {
    body: Option<String>,
    children: BTreeMap<(usize, String), SelectorDispatch>,
}

impl SelectorDispatch {
    fn add(&mut self, constants: &[(usize, String)], body: &str) {
        let mut current = self;
        for literal in constants {
            current = current.children.entry(literal.clone()).or_default();
        }
        current.body.get_or_insert_with(|| body.to_owned());
    }

    /// Return generated source and number of executable terminal fast paths,
    /// not the number of internal selector tests used to reach them.
    fn emit(&self, slot: &FunctionSlot) -> Result<(String, usize)> {
        if let Some(body) = &self.body {
            return Ok((format!("{body}\nreturn;\n"), 1));
        }
        let mut by_body = BTreeMap::<String, (usize, Vec<String>)>::new();
        for (literal, child) in &self.children {
            let test = condition(slot, std::slice::from_ref(literal))
                .ok_or_else(|| anyhow!("validated selector became unrenderable"))?;
            let (source, fast_paths) = child.emit(slot)?;
            let group = by_body.entry(source).or_insert((fast_paths, Vec::new()));
            group.1.push(format!("({test})"));
        }
        let mut output = String::new();
        let mut paths = 0;
        for (source, (count, tests)) in by_body {
            let _ = write!(output, "if ({}) {{\n{source}}}\n", tests.join(" || "));
            paths += count;
        }
        Ok((output, paths))
    }
}

pub fn install_guarded_specializations(
    original: &str,
    variants: &[GuardedVariant],
) -> Result<Option<GuardedProgram>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, original, SourceType::unambiguous());
    ensure!(parsed.is_clean(), "invalid original program");
    let semantic = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(&parsed.program);
    ensure!(
        semantic.diagnostics.is_empty(),
        "invalid original lexical program"
    );
    let mut collector = Functions {
        scoping: semantic.semantic.scoping(),
        slots: BTreeMap::new(),
    };
    collector.visit_program(&parsed.program);
    struct ProvenFastPath {
        constants: Vec<(usize, String)>,
        body: String,
    }
    let mut grouped = BTreeMap::<[u32; 2], Vec<ProvenFastPath>>::new();
    for variant in variants {
        let Some(slot) = collector.slots.get(&variant.function_span) else {
            continue;
        };
        let wrapper_allocator = Allocator::default();
        let wrapper = parse_program(
            &wrapper_allocator,
            &variant.original_wrapper,
            SourceType::unambiguous(),
        );
        let Some((_, original_function)) =
            wrapped_function(&variant.original_wrapper, &wrapper.program)
        else {
            continue;
        };
        if original.get(slot.span[0] as usize..slot.span[1] as usize) != Some(original_function) {
            continue;
        }
        if specialize_function(&variant.original_wrapper, &variant.constants)?.as_deref()
            != Some(variant.specialized_wrapper.as_str())
        {
            continue;
        }
        if condition(slot, &variant.constants).is_none() {
            continue;
        }
        let Some(body) = optimized_body(&variant.optimized_wrapper) else {
            continue;
        };
        grouped.entry(slot.span).or_default().push(ProvenFastPath {
            constants: variant.constants.clone(),
            body,
        });
    }
    if grouped.is_empty() {
        return Ok(None);
    }
    let mut placements = Vec::new();
    let mut fast_paths = 0usize;
    for (key, mut paths) in grouped {
        // Each verified specialization is sound for *all* inputs matching
        // its guard, not only for the observed callsite. A less-specific
        // guard therefore subsumes a more-specific one, regardless of the
        // optimized bodies. Only consider validated candidates, so a
        // rejected generic variant never suppresses a valid specific one.
        paths.sort_by(|a, b| {
            a.constants
                .len()
                .cmp(&b.constants.len())
                .then_with(|| a.constants.cmp(&b.constants))
                .then_with(|| a.body.cmp(&b.body))
        });
        let mut retained = Vec::<ProvenFastPath>::new();
        for path in paths {
            if retained.iter().any(|generic| {
                generic
                    .constants
                    .iter()
                    .all(|literal| path.constants.contains(literal))
            }) {
                continue;
            }
            retained.push(path);
        }
        let Some(slot) = collector.slots.get(&key) else {
            continue;
        };
        let mut dispatch = SelectorDispatch::default();
        for path in retained {
            let mut constants = path.constants;
            constants.sort();
            dispatch.add(&constants, &path.body);
        }
        // The selector trie shares pure prefix checks, and equal executable
        // child subtrees automatically share OR-combined selector edges.
        // Every terminal still executes inside the original call frame.
        let (branches, emitted) = dispatch.emit(slot)?;
        fast_paths += emitted;
        placements.push((slot.insertion, format!("\n{branches}")));
    }
    let targeted_functions = placements.len();
    placements.sort_by_key(|item| std::cmp::Reverse(item.0));
    let mut output = original.to_owned();
    for (position, source) in placements {
        output.insert_str(position, &source);
    }
    let check_allocator = Allocator::default();
    let verified = parse_program(&check_allocator, &output, SourceType::unambiguous());
    ensure!(
        verified.is_clean(),
        "guarded source fails syntax validation"
    );
    let semantic = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(&verified.program);
    ensure!(
        semantic.diagnostics.is_empty(),
        "guarded source fails semantic validation"
    );
    Ok(Some(GuardedProgram {
        source: output,
        fast_paths,
        targeted_functions,
    }))
}

#[cfg(test)]
mod tests {
    use super::{install_guarded_specializations, GuardedVariant};
    use crate::source_tree_specialize::specialize_function;
    use anyhow::{ensure, Result};

    fn variant(
        original: &str,
        raw: &str,
        optimized: &str,
        constants: &[(usize, &str)],
    ) -> Result<GuardedVariant> {
        let start = original
            .find(raw)
            .ok_or_else(|| anyhow::anyhow!("missing function"))?;
        let end = start + raw.len();
        let original_wrapper = format!("const __redox_lexical_helper = ({raw});");
        let constants = constants
            .iter()
            .map(|(index, literal)| (*index, (*literal).to_string()))
            .collect::<Vec<_>>();
        let specialized_wrapper = specialize_function(&original_wrapper, &constants)?
            .ok_or_else(|| anyhow::anyhow!("failed to prove specialization"))?;
        Ok(GuardedVariant {
            function_span: [u32::try_from(start)?, u32::try_from(end)?],
            constants,
            original_wrapper,
            specialized_wrapper,
            optimized_wrapper: format!("const __redox_lexical_helper = ({optimized});"),
        })
    }

    #[test]
    fn retains_original_function_and_inserts_a_guarded_optimized_branch() -> Result<()> {
        let raw = "function(J,Q,Y,L,v){if(J===56 && Y===29){IE.call(this,L,Q||xX.Za(),v);return void 0;}return 9;}";
        let source = format!(
            "const mQ={raw};const Xk=function(J,Q,Y){{return mQ.call(this,56,Q,29,J,Y);}};"
        );
        let optimized = "function(J,Q,Y,L,v){IE.call(this,L,Q||xX.Za(),v);return void 0;}";
        let candidate = variant(&source, raw, optimized, &[(0, "56"), (2, "29")])?;
        let output = install_guarded_specializations(&source, &[candidate])?
            .ok_or_else(|| anyhow::anyhow!("missing fast path"))?;
        ensure!(output.fast_paths == 1 && output.targeted_functions == 1);
        ensure!(output.source.contains("J === (56)") && output.source.contains("Y === (29)"));
        ensure!(
            output.source.contains("return 9;")
                && output.source.contains("mQ.call(this,56,Q,29,J,Y)")
        );
        ensure!(output.source.contains("IE.call(this,L,Q||xX.Za(),v)"));
        Ok(())
    }

    #[test]
    fn general_proven_guard_subsumes_more_specific_guards_with_different_bodies() -> Result<()> {
        let raw = "function(mode,argument){if(mode===3){return argument+1;}return argument-1;}";
        let source = format!("const f={raw};");
        let general = variant(
            &source,
            raw,
            "function(mode,argument){return argument+1;}",
            &[(0, "3")],
        )?;
        let specific = variant(
            &source,
            raw,
            "function(mode,argument){return 5;}",
            &[(0, "3"), (1, "4")],
        )?;
        // The generic proof remains sound even where the specific optimized
        // expression would be shorter. Do not emit redundant nested guards.
        let result = install_guarded_specializations(&source, &[specific, general])?
            .ok_or_else(|| anyhow::anyhow!("missing general fast path"))?;
        ensure!(result.fast_paths == 1 && result.targeted_functions == 1);
        ensure!(!result.source.contains("return 5;"), "{result:?}");
        ensure!(result.source.contains("return argument+1;"), "{result:?}");
        Ok(())
    }

    #[test]
    fn identical_proven_bodies_share_an_or_guard() -> Result<()> {
        let raw = "function(selector){if(selector===3||selector===4){return 1;}return 0;}";
        let source = format!("const f={raw};");
        let a = variant(&source, raw, "function(selector){return 1;}", &[(0, "3")])?;
        let b = variant(&source, raw, "function(selector){return 1;}", &[(0, "4")])?;
        let result = install_guarded_specializations(&source, &[a, b])?
            .ok_or_else(|| anyhow::anyhow!("missing grouped fast path"))?;
        ensure!(result.fast_paths == 1 && result.targeted_functions == 1);
        ensure!(result.source.contains("selector === (3)"), "{result:?}");
        ensure!(result.source.contains("selector === (4)"), "{result:?}");
        ensure!(result.source.contains(" || "), "{result:?}");
        ensure!(result.source.contains("return 0;"), "{result:?}");
        Ok(())
    }

    #[test]
    fn factors_common_selector_prefix_into_one_shared_check() -> Result<()> {
        let raw = "function(mode,kind){if(mode===7){return kind===1?10:20;}return 30;}";
        let source = format!("const f={raw};");
        let first = variant(
            &source,
            raw,
            "function(mode,kind){return 10;}",
            &[(0, "7"), (1, "1")],
        )?;
        let second = variant(
            &source,
            raw,
            "function(mode,kind){return 20;}",
            &[(0, "7"), (1, "2")],
        )?;
        let result = install_guarded_specializations(&source, &[first, second])?
            .ok_or_else(|| anyhow::anyhow!("missing common selector dispatch"))?;
        ensure!(result.fast_paths == 2 && result.targeted_functions == 1);
        ensure!(
            result.source.matches("mode === (7)").count() == 1,
            "{result:?}"
        );
        ensure!(result.source.contains("kind === (1)"), "{result:?}");
        ensure!(result.source.contains("kind === (2)"), "{result:?}");
        ensure!(result.source.contains("return 30;"), "{result:?}");
        Ok(())
    }

    #[test]
    fn distinguishes_positive_and_negative_zero_and_checks_immutable_symbols() -> Result<()> {
        let raw = "function(n){return Object.is(n,-0)?1:2;}";
        let source = format!("const fn0={raw};");
        let candidate = variant(&source, raw, "function(n){return 1;}", &[(0, "-0")])?;
        let output = install_guarded_specializations(&source, std::slice::from_ref(&candidate))?
            .ok_or_else(|| anyhow::anyhow!("missing signed zero guard"))?;
        ensure!(output.source.contains("1 / n === 1 / (-0)"));
        let mut tampered = candidate;
        tampered.specialized_wrapper.push_str(" //not-proven");
        ensure!(install_guarded_specializations(&source, &[tampered])?.is_none());
        Ok(())
    }

    #[test]
    fn rejects_fast_path_var_hoisting_or_function_declarations() -> Result<()> {
        let raw = "function(x){return x+1;}";
        let source = format!("const f={raw};");
        for optimized in [
            "function(x){var injected=4;return x+1;}",
            "function(x){function injected(){}return x+1;}",
        ] {
            let candidate = variant(&source, raw, optimized, &[(0, "2")])?;
            ensure!(install_guarded_specializations(&source, &[candidate])?.is_none());
        }
        Ok(())
    }

    #[test]
    fn duplicate_formal_names_never_install_a_guard() -> Result<()> {
        let raw = "function(x,x){return x===4?1:2;}";
        let source = format!("const f={raw};");
        let original_wrapper = format!("const __redox_lexical_helper = ({raw});");
        let constants = vec![(1, "4".to_owned())];
        if let Some(specialized_wrapper) = specialize_function(&original_wrapper, &constants)? {
            let start = source
                .find(raw)
                .ok_or_else(|| anyhow::anyhow!("missing function"))?;
            let candidate = GuardedVariant {
                function_span: [u32::try_from(start)?, u32::try_from(start + raw.len())?],
                constants,
                original_wrapper,
                specialized_wrapper,
                optimized_wrapper: "const __redox_lexical_helper = (function(x,x){return 1;});"
                    .to_owned(),
            };
            ensure!(install_guarded_specializations(&source, &[candidate])?.is_none());
        }
        Ok(())
    }

    #[test]
    fn rejects_optimization_if_original_function_inherits_strictness() -> Result<()> {
        let raw = "function(v){return v+1;}";
        let source = format!(r#""use strict";const f={raw};"#);
        let candidate = variant(&source, raw, "function(v){return v+1;}", &[(0, "2")])?;
        ensure!(install_guarded_specializations(&source, &[candidate])?.is_none());
        Ok(())
    }
}
