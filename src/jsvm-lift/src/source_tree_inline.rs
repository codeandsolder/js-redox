//! Expose short, source-backed helper returns directly inside analyst-only
//! handlers, with exact semantic binding checks. Never modify the executable
//! reconstruction or mistake source identity for observed runtime execution.
use crate::source_tree_context::{ContextHelper, ContextSourceTree, HandlerContext};
use anyhow::{ensure, Result};
use jsvm_safe_core::eval_static_primitive;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, CallExpression, Expression, IdentifierReference, Statement, WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType};
use oxc_syntax::symbol::SymbolId;
use rolldown_redox::ecmascript::parse_program;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug)]
pub struct ExpandedHandler {
    pub source: String,
    pub expanded_calls: usize,
    pub helpers: Vec<String>,
}

struct ReturnTemplate {
    expression: String,
    /// Byte ranges within the return expression, bound to original formal
    /// parameters by Oxc symbol identity rather than identifier spelling.
    substitutions: Vec<ReturnSubstitution>,
    formal_count: usize,
    free_names: BTreeSet<String>,
}

struct ReturnSubstitution {
    start: usize,
    end: usize,
    formal_index: usize,
    /// In {J}, the object key stays J even if the bound formal is replaced by P.
    shorthand_key: Option<String>,
}

struct ReturnReferences<'s> {
    scoping: &'s Scoping,
    parameters: BTreeMap<SymbolId, usize>,
    start: u32,
    substitutions: Vec<ReturnSubstitution>,
    free_names: BTreeSet<String>,
    invalid: bool,
}
impl ReturnReferences<'_> {
    fn record_reference(&mut self, id: &IdentifierReference<'_>, shorthand: bool) {
        if id.name == "arguments" || id.name == "eval" {
            self.invalid = true;
            return;
        }
        let reference = id.reference_id.get();
        let symbol =
            reference.and_then(|reference| self.scoping.get_reference(reference).symbol_id());
        if let Some(index) = symbol.and_then(|symbol| self.parameters.get(&symbol)) {
            if reference.is_some_and(|reference| self.scoping.get_reference(reference).is_write()) {
                self.invalid = true;
            } else {
                self.substitutions.push(ReturnSubstitution {
                    start: (id.span.start - self.start) as usize,
                    end: (id.span.end - self.start) as usize,
                    formal_index: *index,
                    shorthand_key: shorthand.then(|| id.name.to_string()),
                });
            }
        } else if symbol.is_some() {
            // Local helper-only bindings cannot be transplanted into the caller's scope.
            self.invalid = true;
        } else {
            self.free_names.insert(id.name.to_string());
        }
    }
}
impl<'a> Visit<'a> for ReturnReferences<'_> {
    fn visit_object_property(&mut self, property: &oxc_ast::ast::ObjectProperty<'a>) {
        if property.shorthand {
            // Process the value reference exactly once, reconstructing an explicit
            // property when the original value refers to a formal parameter.
            if let Expression::Identifier(id) = &property.value {
                self.record_reference(id, true);
            } else {
                self.invalid = true;
            }
            return;
        }
        walk::walk_object_property(self, property);
    }

    fn visit_expression(&mut self, expression: &Expression<'a>) {
        // Removing the original call frame changes all of these semantics.
        // Nested functions could capture a formal parameter after the call.
        if matches!(
            expression,
            Expression::ThisExpression(_)
                | Expression::NewTarget(_)
                | Expression::FunctionExpression(_)
                | Expression::ArrowFunctionExpression(_)
                | Expression::ClassExpression(_)
                | Expression::AwaitExpression(_)
                | Expression::YieldExpression(_)
        ) {
            self.invalid = true;
            return;
        }
        walk::walk_expression(self, expression);
    }
    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        self.record_reference(id, false);
    }
}

fn template(helper: &ContextHelper) -> Option<ReturnTemplate> {
    if helper.mutable_binding {
        return None;
    }
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &helper.source, SourceType::unambiguous());
    if !parsed.is_clean() {
        return None;
    }
    let function = match parsed.program.body.first()? {
        Statement::VariableDeclaration(vars) => {
            let Expression::FunctionExpression(function) =
                vars.declarations.first()?.init.as_ref()?
            else {
                return None;
            };
            function
        }
        Statement::FunctionDeclaration(function) => function,
        _ => return None,
    };
    if function.r#async || function.generator || function.params.rest.is_some() {
        return None;
    }
    let [Statement::ReturnStatement(ret)] = function.body.as_ref()?.statements.as_slice() else {
        return None;
    };
    let expr = ret.argument.as_ref()?;
    let expression = helper
        .source
        .get(expr.span().start as usize..expr.span().end as usize)?;
    if expression.len() > 160 {
        return None;
    }
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let mut params = BTreeMap::new();
    for (index, formal) in function.params.items.iter().enumerate() {
        if formal.initializer.is_some() {
            return None;
        }
        let BindingPattern::BindingIdentifier(id) = &formal.pattern else {
            return None;
        };
        params.insert(id.symbol_id.get()?, index);
    }

    if params.keys().any(|symbol| {
        semantic
            .semantic
            .scoping()
            .get_resolved_references(*symbol)
            .any(|reference| reference.is_write())
    }) {
        return None;
    }
    let mut visitor = ReturnReferences {
        scoping: semantic.semantic.scoping(),
        parameters: params,
        start: expr.span().start,
        substitutions: Vec::new(),
        free_names: BTreeSet::new(),
        invalid: false,
    };
    visitor.visit_expression(expr);
    if visitor.invalid {
        return None;
    }
    Some(ReturnTemplate {
        expression: expression.to_owned(),
        substitutions: visitor.substitutions,
        formal_count: function.params.items.len(),
        free_names: visitor.free_names,
    })
}

#[derive(Default)]
struct CallerBindings {
    parameters: BTreeSet<SymbolId>,
    dynamic_scope: bool,
}
impl<'a> Visit<'a> for CallerBindings {
    fn visit_formal_parameter(&mut self, formal: &oxc_ast::ast::FormalParameter<'a>) {
        if let BindingPattern::BindingIdentifier(id) = &formal.pattern {
            if let Some(id) = id.symbol_id.get() {
                self.parameters.insert(id);
            }
        }
        walk::walk_formal_parameter(self, formal);
    }
    fn visit_identifier_reference(&mut self, reference: &IdentifierReference<'a>) {
        if reference.name == "arguments" || reference.name == "eval" {
            self.dynamic_scope = true;
        }
    }
    fn visit_with_statement(&mut self, _: &WithStatement<'a>) {
        self.dynamic_scope = true;
    }
}

struct CallExpander<'s> {
    source: &'s str,
    scoping: &'s Scoping,
    parameters: &'s BTreeSet<SymbolId>,
    templates: &'s BTreeMap<String, ReturnTemplate>,
    /// From outside to inside: nested expansions are not applied twice.
    replacements: Vec<(usize, usize, String, String)>,
}
impl<'a> Visit<'a> for CallExpander<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            let mut callee = &call.callee;
            while let Expression::ParenthesizedExpression(paren) = callee {
                callee = &paren.expression;
            }
            if let Expression::Identifier(id) = callee {
                if let Some(reference) = id.reference_id.get() {
                    let binding = self.scoping.get_reference(reference);
                    if binding.symbol_id().is_none() {
                        if let Some(template) = self.templates.get(id.name.as_str()) {
                            // The same free name may be shadowed in one nested
                            // function but not at another callsite. Do not reject
                            // an entire handler for an unrelated local declaration.
                            let scope = binding.scope_id();
                            let free_names_visible = template.free_names.iter().all(|name| {
                                self.scoping
                                    .find_binding(scope, name.as_str().into())
                                    .is_none()
                            });
                            if free_names_visible {
                                if let Some(expanded) = self.expand(call, template) {
                                    self.replacements.push((
                                        call.span.start as usize,
                                        call.span.end as usize,
                                        expanded,
                                        id.name.to_string(),
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}
impl CallExpander<'_> {
    fn expand(&self, call: &CallExpression<'_>, template: &ReturnTemplate) -> Option<String> {
        if call.arguments.len() != template.formal_count {
            return None;
        }
        let mut arguments = Vec::new();
        for arg in &call.arguments {
            let mut expression = arg.as_expression()?;
            while let Expression::ParenthesizedExpression(paren) = expression {
                expression = &paren.expression;
            }
            let value = self
                .source
                .get(expression.span().start as usize..expression.span().end as usize)?;
            let valid_identifier = match expression {
                Expression::Identifier(id) => id
                    .reference_id
                    .get()
                    .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
                    .is_some_and(|symbol| {
                        self.parameters.contains(&symbol)
                            && !self
                                .scoping
                                .get_resolved_references(symbol)
                                .any(|reference| reference.is_write())
                    }),
                _ => false,
            };
            if valid_identifier {
                arguments.push(value.to_owned());
            } else if eval_static_primitive(expression).is_some() {
                arguments.push(format!("({value})"));
            } else {
                return None;
            }
        }
        let mut expanded = template.expression.clone();
        for substitution in template.substitutions.iter().rev() {
            let argument = arguments.get(substitution.formal_index)?;
            let replacement = substitution.shorthand_key.as_ref().map_or_else(
                || argument.clone(),
                |key| {
                    if key == "__proto__" {
                        // A bare '__proto__:' would trigger the special
                        // object-literal prototype setter, unlike shorthand.
                        format!("[\"__proto__\"]: {argument}")
                    } else {
                        format!("{key}: {argument}")
                    }
                },
            );
            expanded.replace_range(substitution.start..substitution.end, &replacement);
        }
        Some(format!("({expanded})"))
    }
}

/// Expand exact original single-return function expressions with binding-safe
/// primitive or immutable formal arguments. This file is an analyst projection
/// only: function-stack traces and source reflection can still differ.
pub fn expand_helper_returns(
    source: &str,
    context: &ContextSourceTree,
    handler: &HandlerContext,
) -> Result<Option<ExpandedHandler>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    ensure!(parsed.is_clean(), "invalid readable handler");
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let scoping = semantic.semantic.scoping();
    let mut caller = CallerBindings::default();
    caller.visit_program(&parsed.program);
    if caller.dynamic_scope {
        return Ok(None);
    }

    let mut counts = BTreeMap::<&str, usize>::new();
    for helper in &context.helpers {
        *counts.entry(&helper.name).or_default() += 1;
    }
    let linked = handler
        .linked_helpers
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let templates = context
        .helpers
        .iter()
        .filter_map(|helper| {
            (linked.contains(helper.name.as_str()) && counts.get(helper.name.as_str()) == Some(&1))
                .then(|| template(helper).map(|candidate| (helper.name.clone(), candidate)))
                .flatten()
        })
        .collect::<BTreeMap<_, _>>();
    if templates.is_empty() {
        return Ok(None);
    }
    let mut expander = CallExpander {
        source,
        scoping,
        parameters: &caller.parameters,
        templates: &templates,
        replacements: Vec::new(),
    };
    expander.visit_program(&parsed.program);
    // Prefer the containing call if eligible, and prevent overlapping edits.
    expander
        .replacements
        .sort_by(|a, b| a.0.cmp(&b.0).then_with(|| b.1.cmp(&a.1)));
    let mut selected = Vec::new();
    let mut last_end = 0usize;
    for edit in expander.replacements {
        if edit.0 >= last_end {
            last_end = edit.1;
            selected.push(edit);
        }
    }
    if selected.is_empty() {
        return Ok(None);
    }
    let helpers = selected
        .iter()
        .map(|edit| edit.3.clone())
        .collect::<BTreeSet<_>>();
    let expanded_calls = selected.len();
    let mut result = source.to_owned();
    for (start, end, replacement, _) in selected.into_iter().rev() {
        result.replace_range(start..end, &replacement);
    }
    let check = Allocator::default();
    ensure!(
        parse_program(&check, &result, SourceType::unambiguous()).is_clean(),
        "expanded handler failed JavaScript parse"
    );
    Ok(Some(ExpandedHandler {
        source: result,
        expanded_calls,
        helpers: helpers.into_iter().collect(),
    }))
}

#[cfg(test)]
mod tests {
    use super::expand_helper_returns;
    use crate::source_tree_context::reconstruct_context;
    use anyhow::{Context as _, Result};

    #[test]
    fn expands_original_return_expression_using_exact_formal_bindings() -> Result<()> {
        let original =
            "function root() {const AM=function(J){return J.Y ? w8(J,J.D) : $X(8,J,true);};}";
        let source = "const capturedHandler=function(P){return AM(P)+AM(P);};";
        let context =
            reconstruct_context(original, &[("nested/handler.js".into(), source.into())])?;
        let out = expand_helper_returns(source, &context, &context.handlers[0])?
            .context("expected a source-backed expanded helper return")?;
        assert_eq!(out.expanded_calls, 2);
        assert_eq!(out.helpers, ["AM"]);
        assert_eq!(
            out.source
                .matches("(P.Y ? w8(P,P.D) : $X(8,P,true))")
                .count(),
            2
        );
        assert!(!out.source.contains("AM(P)"));
        Ok(())
    }

    #[test]
    fn preserves_unknown_or_mutable_inputs_and_shadowed_callees() -> Result<()> {
        let original =
            "function root(){const AM=function(J){return J.Y ? w8(J,J.D) : $X(8,J,true);};}";
        let cases = [
            "const capturedHandler=function(P){return AM(load());};",
            "const capturedHandler=function(P){P=load();return AM(P);};",
            "const capturedHandler=function(P){return AM(...P);};",
            "const capturedHandler=function(P){return (()=>{const AM=v=>v;return AM(P)})()};",
            "const capturedHandler=function(P){eval('P=1');return AM(P);};",
            "const capturedHandler=function(P){arguments[0]=0;return AM(P);};",
            "const capturedHandler=function(P){const w8=()=>0;return AM(P);};",
        ];
        for source in cases {
            let context = reconstruct_context(original, &[("handler.js".into(), source.into())])?;
            assert!(
                expand_helper_returns(source, &context, &context.handlers[0])?.is_none(),
                "unexpected expansion: {source}"
            );
        }
        Ok(())
    }

    #[test]
    fn rejects_helper_capture_and_parameter_mutation() -> Result<()> {
        let sources = [
            "function root(){const AM=function(J){return ()=>J.Y;};}",
            "function root(){const AM=function(J){return this.Y + J.Y;};}",
            "function root(){const AM=function(J){return arguments[0].Y;};}",
            "function root(){const AM=function(J){return ++J;};}",
            "function root(){const AM=function(J){return eval('J');};}",
            "function root(){let AM=function(J){return J.Y;};AM=function(J){return J.D;};}",
        ];
        let source = "const capturedHandler=function(P){return AM(P);};";
        for original in sources {
            let context = reconstruct_context(original, &[("handler.js".into(), source.into())])?;
            assert!(
                expand_helper_returns(source, &context, &context.handlers[0])?.is_none(),
                "unsound helper expansion: {original}"
            );
        }
        Ok(())
    }

    #[test]
    fn preserves_object_shorthand_keys_and_nested_expressions() -> Result<()> {
        let original =
            "function root(){const pack=function(J){return {J, nested:{J}, computed:{[J]:J}, explicit:J};};}";
        let source = "const capturedHandler=function(P){return pack(P);};";
        let context = reconstruct_context(original, &[("handler.js".into(), source.into())])?;
        let out = expand_helper_returns(source, &context, &context.handlers[0])?
            .context("expected shorthand-preserving expansion")?;
        assert_eq!(out.expanded_calls, 1);
        assert!(
            out.source
                .contains("{J: P, nested:{J: P}, computed:{[P]:P}, explicit:P}"),
            "{}",
            out.source
        );
        assert!(!out.source.contains("pack(P)"));
        Ok(())
    }

    #[test]
    fn rejects_shorthand_capture_collisions() -> Result<()> {
        let original = "function root(){const pack=function(J){return {G,J};};}";
        let source = "const capturedHandler=function(P){const G=1;return pack(P);};";
        let context = reconstruct_context(original, &[("handler.js".into(), source.into())])?;
        assert!(expand_helper_returns(source, &context, &context.handlers[0])?.is_none());
        Ok(())
    }

    #[test]
    fn checks_free_name_collisions_in_each_calls_lexical_scope() -> Result<()> {
        let original = "function root(){const AM=function(J){return w8(J);};}";
        let source =
            "const capturedHandler=function(P){function nested(w8){return AM(P)}return AM(P);};";
        let context = reconstruct_context(original, &[("handler.js".into(), source.into())])?;
        let out = expand_helper_returns(source, &context, &context.handlers[0])?
            .context("expected a source-backed outer call expansion")?;
        assert_eq!(out.expanded_calls, 1);
        assert!(
            out.source.contains("function nested(w8){return AM(P)}"),
            "{}",
            out.source
        );
        assert!(out.source.contains("return (w8(P));"), "{}", out.source);
        Ok(())
    }

    #[test]
    fn proto_shorthand_stays_an_own_property_not_a_prototype_setter() -> Result<()> {
        let original = "function root(){const pack=function(__proto__){return {__proto__};};}";
        let source = "const capturedHandler=function(P){return pack(P);};";
        let context = reconstruct_context(original, &[("handler.js".into(), source.into())])?;
        let out = expand_helper_returns(source, &context, &context.handlers[0])?
            .context("expected __proto__ shorthand expansion")?;
        assert_eq!(out.expanded_calls, 1);
        assert!(
            out.source.contains("{[\"__proto__\"]: P}"),
            "{}",
            out.source
        );
        Ok(())
    }

    #[test]
    fn static_literals_are_substituted_without_evaluation() -> Result<()> {
        let original = "function root(){const twice=function(J){return J+J;};}";
        let source = "const capturedHandler=function(){return twice(7)+twice(1+2);};";
        let context = reconstruct_context(original, &[("handler.js".into(), source.into())])?;
        let out = expand_helper_returns(source, &context, &context.handlers[0])?
            .context("expected a source-backed expanded helper return")?;
        assert_eq!(out.expanded_calls, 2);
        assert!(out.source.contains("((7)+(7))"), "{}", out.source);
        assert!(out.source.contains("((1+2)+(1+2))"), "{}", out.source);
        Ok(())
    }
}
