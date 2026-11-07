//! Static *callsite* specializations of original lexical helper functions.
//!
//! The actual helper source remains intact. Each derivative substitutes
//! constant arguments only at references to the same parameter SymbolId,
//! and is then passed through the existing JS deobfuscator. This is useful
//! program recovery, not an independently runnable replacement module.
use crate::source_tree_callflow::ResolvedCallEdge;
use anyhow::{ensure, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, BindingPattern, CallExpression, Expression, Function, IdentifierReference,
    NewExpression, Statement, WithStatement,
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

/// Primitive literal arguments at their *original* AST callsites. A spread
/// consumes an unknown number of positions, so subsequent argument indices
/// cannot be assigned to fixed formal parameters.
struct OriginalCallLiterals<'s> {
    source: &'s str,
    sites: BTreeMap<[u32; 2], Vec<(usize, String)>>,
}

impl OriginalCallLiterals<'_> {
    fn remember(&mut self, span: Span, arguments: &[Argument<'_>]) {
        let mut constants = Vec::new();
        for (index, argument) in arguments.iter().enumerate() {
            if matches!(argument, Argument::SpreadElement(_)) {
                break;
            }
            if let Some(literal) = literal_argument(argument, self.source) {
                constants.push((index, literal));
            }
        }
        if !constants.is_empty() {
            self.sites.insert([span.start, span.end], constants);
        }
    }
}

impl<'a> Visit<'a> for OriginalCallLiterals<'_> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional {
            self.remember(call.span, &call.arguments);
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expr: &NewExpression<'a>) {
        self.remember(expr.span, &expr.arguments);
        walk::walk_new_expression(self, expr);
    }
}

/// An analysis-only variant of a real function, specialized at exact
/// statically resolved lexical callsites in the original JavaScript.
#[derive(Debug, Clone)]
pub struct ResolvedSpecialization {
    pub helper: String,
    pub function_span: [u32; 2],
    pub constants: Vec<(usize, String)>,
    pub call_sites: BTreeSet<[u32; 2]>,
    pub original: String,
    pub specialized: String,
}

/// Materialize selected primitive parameter values for all reachable direct
/// callees. Calls are joined by resolved original callee function spans,
/// **never by function name**, so shadowed identifiers remain distinct.
/// A parameter written inside a helper cannot be replaced; other independent
/// constant parameters still contribute to the best valid specialization.
pub fn specialize_resolved_call_graph(
    original: &str,
    edges: &[ResolvedCallEdge],
) -> Result<Vec<ResolvedSpecialization>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, original, SourceType::unambiguous());
    ensure!(parsed.is_clean(), "invalid original lexical JavaScript");
    let mut collector = OriginalCallLiterals {
        source: original,
        sites: BTreeMap::new(),
    };
    collector.visit_program(&parsed.program);
    let mut requested =
        BTreeMap::<([u32; 2], Vec<(usize, String)>), (String, BTreeSet<[u32; 2]>)>::new();
    for edge in edges {
        let Some(constants) = collector.sites.get(&edge.call.span) else {
            continue;
        };
        let entry = requested
            .entry((edge.to_span, constants.clone()))
            .or_insert_with(|| (edge.call.callee.clone(), BTreeSet::new()));
        entry.1.insert(edge.call.span);
    }

    let mut specializations = Vec::new();
    for ((function_span, constants), (helper, call_sites)) in requested {
        let Some(raw) = original.get(function_span[0] as usize..function_span[1] as usize) else {
            continue;
        };
        // Source function expressions, named declarations, and arrows all
        // become root function-valued initializer expressions. This preserves
        // their own parameter symbols, nested scopes, and function bodies.
        let wrapped = format!("const __redox_lexical_helper = ({raw});\n");
        // A valid expression in its original lexical context can reference
        // contextual syntax such as super. Skip only this unwrappable body,
        // not the entire set of recoverable callsites.
        let wrapper_allocator = Allocator::default();
        if !parse_program(&wrapper_allocator, &wrapped, SourceType::unambiguous()).is_clean() {
            continue;
        }
        // Select precisely the literals that can actually replace a read
        // of their formal parameter. This simultaneously drops reassigned,
        // rest/default, and unused parameters. It avoids duplicate variants
        // differing only by literals irrelevant to the recovered body.
        let mut selected = Vec::new();
        for constant in &constants {
            if specialize_function(&wrapped, std::slice::from_ref(constant))?.is_some() {
                selected.push(constant.clone());
            }
        }
        if selected.is_empty() {
            continue;
        }
        let Some(specialized) = specialize_function(&wrapped, &selected)? else {
            continue;
        };
        specializations.push(ResolvedSpecialization {
            helper,
            function_span,
            constants: selected,
            call_sites,
            original: wrapped,
            specialized,
        });
    }
    // Different callsite literal tuples may reduce to the same viable subset.
    // Merge these instead of emitting identical helper bodies repeatedly.
    let mut deduplicated =
        BTreeMap::<([u32; 2], Vec<(usize, String)>), ResolvedSpecialization>::new();
    for candidate in specializations {
        let key = (candidate.function_span, candidate.constants.clone());
        if let Some(existing) = deduplicated.get_mut(&key) {
            existing.call_sites.extend(candidate.call_sites);
        } else {
            deduplicated.insert(key, candidate);
        }
    }
    Ok(deduplicated.into_values().collect())
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
    // Oxc's parser accepts some context-dependent syntax such as super in a
    // detached arrow. Semantic early-error validation is required for source
    // extraction: such a function may be legal only in its original class.
    let semantic = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(&parsed.program);
    if !semantic.diagnostics.is_empty() {
        return Ok(None);
    }
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
    use super::{literal_calls, specialize_function, specialize_resolved_call_graph};
    use crate::source_tree_callflow::reconstruct_caller_views;
    use anyhow::{anyhow, Result};

    #[test]
    fn recovers_distinct_literal_variants_from_original_lexical_graph() -> Result<()> {
        let src = r#"const helper=function(selector,value){
            if(selector===3)return value+1;
            return value*2;
        };
        const api={};
        api.run=function(x) {return helper(3,x)+helper(4,x);};"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views[0].reachable_edges)?;
        assert_eq!(variants.len(), 2, "{variants:?}");
        assert!(variants.iter().all(|v| v.helper == "helper"));
        assert!(variants.iter().all(|v| v.call_sites.len() == 1));
        assert!(variants.iter().any(|v| {
            v.constants == [(0, "3".into())] && v.specialized.contains("if((3)===3)")
        }));
        assert!(variants.iter().any(|v| {
            v.constants == [(0, "4".into())] && v.specialized.contains("if((4)===3)")
        }));
        Ok(())
    }

    #[test]
    fn uses_unchanged_subset_when_other_literal_parameter_is_written() -> Result<()> {
        let src = r#"const helper=function(a,b){a=9;return b+a;};
          const api={};api.run=()=>helper(3,4);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views[0].reachable_edges)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].constants, [(1, "4".into())]);
        assert!(variants[0].specialized.contains("return (4)+a"));
        assert!(variants[0].specialized.contains("a=9"));
        Ok(())
    }

    #[test]
    fn spread_argument_positions_are_never_misidentified() -> Result<()> {
        let src = r#"const helper=(a,b)=>a+b;
          const api={};api.run=(xs)=>helper(...xs,42)+helper(3,...xs);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views[0].reachable_edges)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].constants, [(0, "3".into())]);
        Ok(())
    }

    #[test]
    fn same_spelling_in_another_scope_is_not_the_target_function() -> Result<()> {
        let src = r#"const helper=(a)=>a*3;
          const api={};api.run=()=>{
              const helper=(a)=>a*4;
              return helper(7);
          };"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views[0].reachable_edges)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert!(variants[0].original.contains("a*4"));
        assert!(!variants[0].original.contains("a*3"));
        Ok(())
    }

    #[test]
    fn contextual_super_expression_does_not_abort_other_valid_helpers() -> Result<()> {
        let src = r#"class Base { method(x){return x;} }
          class Child extends Base {
            method(){
              const contextual=(x)=>super.method(x);
              const regular=(x)=>x*2;
              const api={};api.run=()=>contextual(3)+regular(4);
              return api;
            }
          }"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views[0].reachable_edges)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].helper, "regular");
        assert_eq!(variants[0].constants, [(0, "4".into())]);
        Ok(())
    }

    #[test]
    fn unused_literal_arguments_do_not_produce_redundant_variants() -> Result<()> {
        let src = r#"const helper=(selector,unused)=>selector*2;
            const api={};api.run=()=>helper(3,7)+helper(3,8);"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views[0].reachable_edges)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].constants, [(0, "3".into())]);
        assert_eq!(variants[0].call_sites.len(), 2);
        Ok(())
    }

    #[test]
    fn constructor_call_and_same_literal_tuple_deduplicate() -> Result<()> {
        let src = r#"function Helper(flag){this.result=flag?1:0;}
          const api={};api.run=()=>[new Helper(true),new Helper(true)];"#;
        let views = reconstruct_caller_views(src, Some("run"))?;
        let variants = specialize_resolved_call_graph(src, &views[0].reachable_edges)?;
        assert_eq!(variants.len(), 1, "{variants:?}");
        assert_eq!(variants[0].call_sites.len(), 2);
        assert_eq!(variants[0].constants, [(0, "true".into())]);
        assert!(variants[0].specialized.contains("(true)?1:0"));
        Ok(())
    }

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
