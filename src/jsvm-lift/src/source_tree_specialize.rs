//! Static *callsite* specializations of original lexical helper functions.
//!
//! The actual helper source remains intact. Each derivative substitutes
//! constant arguments only at references to the same parameter SymbolId,
//! and is then passed through the existing JS deobfuscator. This is useful
//! program recovery, not an independently runnable replacement module.
use anyhow::{ensure, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, BindingPattern, CallExpression, Expression, Function, IdentifierReference, Statement,
    WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{operator::UnaryOperator, scope::ScopeFlags, symbol::SymbolId};
use rolldown_redox::ecmascript::parse_program;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct LiteralCall {
    pub helper: String,
    pub constants: Vec<(usize, String)>,
    pub span: Span,
}

fn unparen<'a>(mut expr: &'a Expression<'a>) -> &'a Expression<'a> {
    while let Expression::ParenthesizedExpression(inner) = expr {
        expr = &inner.expression;
    }
    expr
}

fn literal_argument<'a>(arg: &'a Argument<'a>, source: &'a str) -> Option<String> {
    let expr = unparen(arg.as_expression()?);
    let literal = match expr {
        Expression::NumericLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::StringLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::BigIntLiteral(_) => true,
        Expression::UnaryExpression(unary) => {
            matches!(
                unary.operator,
                UnaryOperator::UnaryPlus | UnaryOperator::UnaryNegation
            ) && matches!(unparen(&unary.argument), Expression::NumericLiteral(_))
        }
        _ => false,
    };
    if !literal {
        return None;
    }
    source
        .get(expr.span().start as usize..expr.span().end as usize)
        .map(str::to_owned)
}

struct Calls<'s> {
    source: &'s str,
    scoping: &'s Scoping,
    calls: Vec<LiteralCall>,
}

impl<'a> Visit<'a> for Calls<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            if let Expression::Identifier(callee) = unparen(&call.callee) {
                let unresolved = callee.reference_id.get().is_some_and(|reference| {
                    self.scoping.get_reference(reference).symbol_id().is_none()
                });
                if unresolved {
                    let constants = call
                        .arguments
                        .iter()
                        .enumerate()
                        .filter_map(|(index, argument)| {
                            literal_argument(argument, self.source).map(|literal| (index, literal))
                        })
                        .collect::<Vec<_>>();
                    if !constants.is_empty() {
                        self.calls.push(LiteralCall {
                            helper: callee.name.to_string(),
                            constants,
                            span: call.span,
                        });
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

pub fn literal_calls(source: &str) -> Result<Vec<LiteralCall>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    ensure!(parsed.is_clean(), "invalid JavaScript in handler");
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let mut visitor = Calls {
        source,
        scoping: semantic.semantic.scoping(),
        calls: Vec::new(),
    };
    visitor.visit_program(&parsed.program);
    Ok(visitor.calls)
}

struct FunctionCandidate {
    params: BTreeMap<usize, SymbolId>,
}

/// Never select an arbitrary nested function from an object-valued helper.
/// The helper's root source must itself declare/initialize a function.
fn root_function_params<'a>(program: &'a oxc_ast::ast::Program<'a>) -> Option<FunctionCandidate> {
    let statement = program.body.first()?;
    let formal = match statement {
        Statement::FunctionDeclaration(function) => &function.params,
        Statement::VariableDeclaration(declaration) if declaration.declarations.len() == 1 => {
            let init = declaration.declarations[0].init.as_ref()?;
            match unparen(init) {
                Expression::FunctionExpression(function) => &function.params,
                Expression::ArrowFunctionExpression(function) => &function.params,
                _ => return None,
            }
        }
        _ => return None,
    };
    let mut params = BTreeMap::new();
    for (index, item) in formal.items.iter().enumerate() {
        if item.initializer.is_some() {
            continue;
        }
        if let BindingPattern::BindingIdentifier(id) = &item.pattern {
            if let Some(symbol) = id.symbol_id.get() {
                params.insert(index, symbol);
            }
        }
    }
    Some(FunctionCandidate { params })
}

struct ParameterReferences<'s> {
    scoping: &'s Scoping,
    target: BTreeMap<SymbolId, String>,
    edits: Vec<(Span, String)>,
    unsafe_dynamic_scope: bool,
    // Nested ordinary functions own a distinct arguments object. Arrows
    // inherit the nearest enclosing non-arrow function's binding.
    // The initial helper function is at depth one.
    ordinary_function_depth: usize,
}

impl<'a> Visit<'a> for ParameterReferences<'_> {
    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        if id.name == "eval" || (id.name == "arguments" && self.ordinary_function_depth <= 1) {
            self.unsafe_dynamic_scope = true;
        }
        if let Some(symbol) = id
            .reference_id
            .get()
            .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
        {
            if let Some(literal) = self.target.get(&symbol) {
                self.edits.push((id.span, format!("({literal})")));
            }
        }
    }

    fn visit_with_statement(&mut self, _statement: &WithStatement<'a>) {
        self.unsafe_dynamic_scope = true;
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        self.ordinary_function_depth += 1;
        walk::walk_function(self, function, flags);
        self.ordinary_function_depth -= 1;
    }
}

/// Replace references to stable simple parameters with exact primitive literal
/// arguments. Leaves the parameter list, function name, and external closures
/// unchanged. Rejects dynamic scope and any write or arguments alias to
/// the substituted parameters.
pub fn specialize_function(source: &str, constants: &[(usize, String)]) -> Result<Option<String>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    ensure!(parsed.is_clean(), "invalid helper source");
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let scoping = semantic.semantic.scoping();
    let Some(root) = root_function_params(&parsed.program) else {
        return Ok(None);
    };
    let mut replacements = BTreeMap::new();
    for &(index, ref literal) in constants {
        let Some(&symbol) = root.params.get(&index) else {
            return Ok(None);
        };
        if scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .any(|reference| scoping.get_reference(*reference).is_write())
        {
            return Ok(None);
        }
        replacements.insert(symbol, literal.clone());
    }
    let mut visitor = ParameterReferences {
        scoping,
        target: replacements,
        edits: Vec::new(),
        unsafe_dynamic_scope: false,
        ordinary_function_depth: 0,
    };
    visitor.visit_program(&parsed.program);
    if visitor.unsafe_dynamic_scope || visitor.edits.is_empty() {
        return Ok(None);
    }
    let mut output = source.to_owned();
    visitor
        .edits
        .sort_by_key(|(span, _)| std::cmp::Reverse(span.start));
    for (span, literal) in visitor.edits {
        output.replace_range(span.start as usize..span.end as usize, &literal);
    }
    let verification = Allocator::default();
    if !parse_program(&verification, &output, SourceType::unambiguous()).is_clean() {
        return Ok(None);
    }
    Ok(Some(output))
}

#[derive(Debug, Clone)]
pub struct Specialization {
    pub helper: String,
    pub arguments: Vec<(usize, String)>,
    pub call_sites: BTreeSet<String>,
    pub original: String,
    pub source: String,
}

/// Group same-constant callsites into one specialized helper body each.
/// Their exact arguments are included in the ID; no arbitrary case cap.
pub fn specialize_calls(
    handlers: &[(String, String)],
    helpers: &BTreeMap<String, String>,
) -> Result<Vec<Specialization>> {
    let mut requested = BTreeMap::<(String, Vec<(usize, String)>), BTreeSet<String>>::new();
    for (path, source) in handlers {
        for call in literal_calls(source)? {
            if helpers.contains_key(&call.helper) {
                requested
                    .entry((call.helper, call.constants))
                    .or_default()
                    .insert(format!("{path}:{}", call.span.start));
            }
        }
    }
    let mut output = Vec::new();
    for ((helper, args), call_sites) in requested {
        let original = &helpers[&helper];
        if let Some(source) = specialize_function(original, &args)? {
            output.push(Specialization {
                helper,
                arguments: args,
                call_sites,
                original: original.clone(),
                source,
            });
        }
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::{literal_calls, specialize_function};
    use anyhow::{anyhow, Result};

    #[test]
    fn finds_only_unresolved_lexical_calls_with_primitive_literals() -> Result<()> {
        let src = "const h=function(){const local=(x,y)=>x; O(u,16); M(68,127,P); local(1,2); O(P, true); O(P, 'abc'); O(P,-12); };";
        let calls = literal_calls(src)?;
        assert_eq!(calls.len(), 5);
        assert_eq!(calls[0].constants, vec![(1, "16".to_owned())]);
        assert_eq!(
            calls[1].constants,
            vec![(0, "68".into()), (1, "127".into())]
        );
        assert_eq!(calls[2].constants, vec![(1, "true".into())]);
        assert_eq!(calls[3].constants, vec![(1, "'abc'".into())]);
        assert_eq!(calls[4].constants, vec![(1, "-12".into())]);
        Ok(())
    }

    #[test]
    fn substitutes_original_lexical_parameter_only() -> Result<()> {
        let src =
            "const O=function(J,Q){if(Q===16){const f=(Q)=>Q+1;return J + f(2);}return Q*2;};";
        let output = specialize_function(src, &[(1, "16".to_owned())])?
            .ok_or_else(|| anyhow!("expected specialized helper"))?;
        assert!(output.contains("if((16)===16)"));
        assert!(output.contains("const f=(Q)=>Q+1"));
        assert!(!output.contains("return Q*2"));
        assert!(output.contains("return (16)*2"));
        Ok(())
    }

    #[test]
    fn ignores_arguments_of_nested_ordinary_function_but_not_arrow() -> Result<()> {
        let own_arguments =
            "const M=function(selector,value){const nested=function(){return arguments[0];};return selector+nested(value);};";
        let fixed = specialize_function(own_arguments, &[(0, "68".into())])?
            .ok_or_else(|| anyhow!("nested arguments should not alias outer parameters"))?;
        assert!(fixed.contains("return (68)+nested(value)"), "{fixed}");
        assert!(fixed.contains("return arguments[0]"), "{fixed}");

        let inherited_arguments =
            "const M=function(selector){const nested=()=>arguments[0];return selector+nested();};";
        assert!(specialize_function(inherited_arguments, &[(0, "68".into())])?.is_none());

        // A nested direct eval can still resolve or modify an enclosing
        // function parameter. Preserve the previous dynamic-scope veto.
        let nested_eval =
            "const M=function(selector){const nested=function(){eval('selector=9')};return selector+nested();};";
        assert!(specialize_function(nested_eval, &[(0, "68".into())])?.is_none());
        Ok(())
    }

    #[test]
    fn rejects_aliasing_write_dynamic_scope_and_unsupported_parameters() -> Result<()> {
        for src in [
            "const f=function(x){x=2;return x;};",
            "const f=function(x){return arguments[0];};",
            "const f=function(x){return eval('x');};",
            "const f=function(x){with({x:7})return x;};",
            "const f=function(x=1){return x;};",
            "const f={invoke(x){return x+1;}};",
        ] {
            assert!(
                specialize_function(src, &[(0, "2".to_owned())])?.is_none(),
                "{src}"
            );
        }
        Ok(())
    }
}
