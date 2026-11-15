//! Remove direct empty function invocations in executable recovery.
//! A synchronous function/arrow literal with an empty body and simple
//! formals has no observable call-frame effects, but each argument must
//! still execute once, left-to-right. No spreads are rewritten: materializing
//! them as an array changes argument-list completion semantics.
use oxc_ast::ast::{
    BindingPattern, CallExpression, Expression, FormalParameters, FunctionBody, Statement,
};
use oxc_span::GetSpan;

fn empty_body(body: &FunctionBody<'_>) -> bool {
    body.statements
        .iter()
        .all(|stmt| matches!(stmt, Statement::EmptyStatement(_)))
}

fn simple_parameters(params: &FormalParameters<'_>) -> bool {
    params.items.iter().all(|item| {
        item.initializer.is_none() && matches!(item.pattern, BindingPattern::BindingIdentifier(_))
    }) && params
        .rest
        .as_ref()
        .is_none_or(|rest| matches!(rest.rest.argument, BindingPattern::BindingIdentifier(_)))
}

fn immediate_empty_function(callee: &Expression<'_>) -> bool {
    match callee {
        Expression::ParenthesizedExpression(paren) => immediate_empty_function(&paren.expression),
        Expression::FunctionExpression(function) => {
            !function.r#async
                && !function.generator
                && simple_parameters(&function.params)
                && function.body.as_ref().is_some_and(|body| empty_body(body))
        }
        Expression::ArrowFunctionExpression(arrow) => {
            !arrow.r#async
                && simple_parameters(&arrow.params)
                && matches!(&arrow.body, oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) if empty_body(body))
        }
        _ => false,
    }
}

pub(super) fn simplify_empty_iife(call: &CallExpression<'_>, source: &str) -> Option<String> {
    if call.arguments.iter().any(oxc_ast::ast::Argument::is_spread)
        || !immediate_empty_function(&call.callee)
    {
        return None;
    }
    // A direct function literal always resolves to a callable, even for
    // optional-call syntax. Its body has no effects; arguments still do.
    if call.arguments.is_empty() {
        return Some("(void 0)".to_string());
    }
    let start = call.arguments.first()?.span().start as usize;
    let end = call.arguments.last()?.span().end as usize;
    let argument_list = source.get(start..end)?;
    // Keep argument delimiters and comments in their original order.
    Some(format!("({argument_list}, void 0)"))
}

#[cfg(test)]
mod tests {
    use super::simplify_empty_iife;
    use oxc_allocator::Allocator;
    use oxc_ast::ast::CallExpression;
    use oxc_ast_visit::{walk, Visit};
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    struct Calls<'s> {
        source: &'s str,
        found: Vec<String>,
    }
    impl<'a> Visit<'a> for Calls<'_> {
        fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
            if let Some(rewrite) = simplify_empty_iife(call, self.source) {
                self.found.push(rewrite);
            }
            walk::walk_call_expression(self, call);
        }
    }
    fn simplify(input: &str) -> Vec<String> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, input, SourceType::unambiguous());
        assert!(parsed.is_clean(), "{input}");
        let mut collector = Calls {
            source: input,
            found: Vec::new(),
        };
        collector.visit_program(&parsed.program);
        collector.found
    }
    #[test]
    fn preserves_side_effects_and_argument_order_and_comments() {
        assert_eq!(
            simplify("(function(a,b){})(side(), /*arg*/ next())"),
            vec!["(side(), /*arg*/ next(), void 0)"]
        );
        assert_eq!(simplify("(()=>{})()"), vec!["(void 0)"]);
        assert_eq!(
            simplify("(function named() { 'use strict'; ; })()"),
            vec!["(void 0)"]
        );
        assert_eq!(
            simplify("(function(...rest) {})((foo()), bar)"),
            vec!["((foo()), bar, void 0)"]
        );
    }
    #[test]
    fn keeps_effectful_formal_bindings_async_generator_and_spreads() {
        for input in [
            "(function(x=side()){} )()",
            "(function({x}){})(source)",
            "(function*(){})()",
            "(async function(){})()",
            "(async ()=>{})()",
            "(function(){write()})()",
            "(function(){return 1})()",
            "(function(){}) (...iter)",
            "(function(){}) (arg,...iter)",
            "(function(){}) (side(),...iter,last())",
        ] {
            assert!(simplify(input).is_empty(), "{input}");
        }
    }
    #[test]
    #[ignore = "Node differential oracle"]
    fn node_confirms_observable_effects_of_nonspread_empty_iife(
    ) -> Result<(), Box<dyn std::error::Error>> {
        use std::process::Command;
        let original = "(function(a,b){})(side(1), side(2))";
        let rewrite = simplify(original);
        let [rewritten] = rewrite.as_slice() else {
            return Err("missing rewrite".into());
        };
        for expression in [original, rewritten.as_str()] {
            let code = format!(
                "const events=[]; const side=(v)=>{{events.push(v);return v}};\n                 const ret={expression}; console.log(JSON.stringify([events,ret===undefined]));"
            );
            let result = Command::new("node").arg("-e").arg(code).output()?;
            assert!(result.status.success(), "{result:?}");
            assert_eq!(String::from_utf8(result.stdout)?.trim(), "[[1,2],true]");
        }
        Ok(())
    }
}
