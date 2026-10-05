use oxc_ast::ast::{Argument, ArrayExpressionElement, CallExpression, Expression};

#[derive(Debug, Clone)]
pub struct EmbeddedCodeCandidate {
    pub outer_start: u32,
    pub outer_end: u32,
    pub kind: String,
    pub params: Vec<String>,
    pub body: String,
}

pub fn detect_literal_string_join(call: &CallExpression<'_>) -> Option<EmbeddedCodeCandidate> {
    if call.optional || call.arguments.len() != 1 {
        return None;
    }
    let Expression::StaticMemberExpression(member) = &call.callee else {
        return None;
    };
    if member.optional || member.property.name.as_str() != "join" {
        return None;
    }
    let Expression::ArrayExpression(array) = &member.object else {
        return None;
    };
    let Argument::StringLiteral(separator) = &call.arguments[0] else {
        return None;
    };

    let mut parts = Vec::with_capacity(array.elements.len());
    for element in &array.elements {
        let ArrayExpressionElement::StringLiteral(value) = element else {
            return None;
        };
        parts.push(value.value.as_str());
    }
    if parts.len() < 2 {
        return None;
    }

    let body = parts.join(separator.value.as_str());
    if body.len() < 1024 || body.len() > 5_000_000 {
        return None;
    }
    let looks_like_code = body.contains("function")
        && (body.contains("for(")
            || body.contains("for (")
            || body.contains("switch(")
            || body.contains("switch (")
            || body.contains("=>"));
    if !looks_like_code {
        return None;
    }

    Some(EmbeddedCodeCandidate {
        outer_start: call.span.start,
        outer_end: call.span.end,
        kind: "literal Array.join".to_string(),
        params: Vec::new(),
        body,
    })
}

pub fn detect_function_constructor(
    kind: &str,
    start: u32,
    end: u32,
    args: &[Argument<'_>],
) -> Option<EmbeddedCodeCandidate> {
    if args.is_empty() {
        return None;
    }

    let mut strings = Vec::with_capacity(args.len());
    for arg in args {
        let Argument::StringLiteral(value) = arg else {
            return None;
        };
        strings.push(value.value.to_string());
    }

    let body = strings.pop()?;
    if body.len() < 128 || body.len() > 5_000_000 {
        return None;
    }

    Some(EmbeddedCodeCandidate {
        outer_start: start,
        outer_end: end,
        kind: kind.to_string(),
        params: strings,
        body,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_allocator::Allocator;
    use oxc_ast_visit::{walk, Visit};
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    #[derive(Default)]
    struct Harness {
        candidates: Vec<EmbeddedCodeCandidate>,
    }

    impl<'a> Visit<'a> for Harness {
        fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
            if let Some(candidate) = detect_literal_string_join(call) {
                self.candidates.push(candidate);
            }
            if matches!(&call.callee, Expression::Identifier(id) if id.name.as_str() == "Function")
            {
                if let Some(candidate) = detect_function_constructor(
                    "Function",
                    call.span.start,
                    call.span.end,
                    &call.arguments,
                ) {
                    self.candidates.push(candidate);
                }
            }
            walk::walk_call_expression(self, call);
        }
    }

    fn detect(source: &str) -> Vec<EmbeddedCodeCandidate> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let mut harness = Harness::default();
        harness.visit_program(&parsed.program);
        harness.candidates
    }

    #[test]
    fn recovers_function_constructor() {
        let body = "return value + 1;".repeat(10);
        let source = format!("Function(\"value\", {body:?});");
        let candidates = detect(&source);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].kind, "Function");
        assert_eq!(candidates[0].params, vec!["value"]);
        assert_eq!(candidates[0].body, body);
    }

    #[test]
    fn recovers_large_literal_join() {
        let body = "function vm(){for(;;){break;}}".repeat(40);
        let split = body.len() / 2;
        let (left, right) = body.split_at(split);
        let source = format!("[{left:?}, {right:?}].join(\"\");");
        let candidates = detect(&source);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].kind, "literal Array.join");
        assert_eq!(candidates[0].body, body);
    }
}
