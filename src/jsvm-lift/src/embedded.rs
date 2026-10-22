use jsvm_safe_core::string_literal_value;
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, BindingPattern, CallExpression, Expression, Function,
};
use oxc_ast_visit::{walk, Visit};

#[derive(Debug, Clone)]
pub struct EmbeddedCodeCandidate {
    pub outer_start: u32,
    pub outer_end: u32,
    pub kind: String,
    pub params: Vec<String>,
    pub body: String,
}

fn function_expression<'a>(expr: &'a Expression<'a>) -> Option<&'a Function<'a>> {
    match expr {
        Expression::FunctionExpression(function) => Some(function),
        Expression::ParenthesizedExpression(parenthesized) => {
            function_expression(&parenthesized.expression)
        }
        _ => None,
    }
}

fn has_classic_packer_params(function: &Function<'_>) -> bool {
    const EXPECTED_PREFIX: [&str; 5] = ["p", "a", "c", "k", "e"];
    if function.params.items.len() != 6 {
        return false;
    }
    let prefix_matches = function
        .params
        .items
        .iter()
        .take(EXPECTED_PREFIX.len())
        .zip(EXPECTED_PREFIX)
        .all(|(param, expected)| {
            matches!(
                &param.pattern,
                BindingPattern::BindingIdentifier(identifier)
                    if identifier.name.as_str() == expected
            )
        });
    prefix_matches
        && matches!(
            &function.params.items[5].pattern,
            BindingPattern::BindingIdentifier(_)
        )
}

#[derive(Default)]
struct ClassicPackerProbe {
    parse_int_calls: usize,
    from_char_code_calls: usize,
    regexp_news: usize,
    replace_calls: usize,
    returns_payload: usize,
}

impl<'a> Visit<'a> for ClassicPackerProbe {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        match &call.callee {
            Expression::Identifier(identifier) if identifier.name.as_str() == "parseInt" => {
                self.parse_int_calls += 1;
            }
            Expression::StaticMemberExpression(member)
                if member.property.name.as_str() == "fromCharCode"
                    && matches!(
                        &member.object,
                        Expression::Identifier(identifier)
                            if identifier.name.as_str() == "String"
                    ) =>
            {
                self.from_char_code_calls += 1;
            }
            Expression::StaticMemberExpression(member)
                if member.property.name.as_str() == "replace" =>
            {
                self.replace_calls += 1;
            }
            _ => {}
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
        if matches!(
            &expression.callee,
            Expression::Identifier(identifier) if identifier.name.as_str() == "RegExp"
        ) {
            self.regexp_news += 1;
        }
        walk::walk_new_expression(self, expression);
    }

    fn visit_return_statement(&mut self, statement: &oxc_ast::ast::ReturnStatement<'a>) {
        if matches!(
            &statement.argument,
            Some(Expression::Identifier(identifier)) if identifier.name.as_str() == "p"
        ) {
            self.returns_payload += 1;
        }
        walk::walk_return_statement(self, statement);
    }
}

fn has_classic_packer_decoder(function: &Function<'_>) -> bool {
    let Some(body) = function.body.as_ref() else {
        return false;
    };
    let mut probe = ClassicPackerProbe::default();
    probe.visit_function_body(body);
    probe.parse_int_calls >= 1
        && probe.from_char_code_calls >= 1
        && probe.regexp_news >= 1
        && probe.replace_calls >= 1
        && probe.returns_payload >= 1
}

fn split_literal_keywords(arg: &Argument<'_>) -> Option<Vec<String>> {
    let Argument::CallExpression(call) = arg else {
        return None;
    };
    if call.optional || call.arguments.len() != 1 {
        return None;
    }
    let Expression::StaticMemberExpression(member) = &call.callee else {
        return None;
    };
    if member.optional || member.property.name.as_str() != "split" {
        return None;
    }
    let Expression::StringLiteral(words) = &member.object else {
        return None;
    };
    let Argument::StringLiteral(separator) = &call.arguments[0] else {
        return None;
    };
    if separator.value.as_str() != Some("|") {
        return None;
    }
    Some(
        words
            .value
            .as_str()?
            .split('|')
            .map(ToOwned::to_owned)
            .collect(),
    )
}

fn exact_bounded_u64(value: f64, max: u32) -> Option<u64> {
    if !value.is_finite() || value < 0.0 || value > f64::from(max) || value.fract() != 0.0 {
        return None;
    }
    value.to_string().parse().ok()
}

fn packer_digit(value: u64) -> Option<char> {
    match value {
        0..=9 => char::from_u32(u32::try_from(value).ok()? + u32::from(b'0')),
        10..=35 => char::from_u32(u32::try_from(value - 10).ok()? + u32::from(b'a')),
        36..=61 => char::from_u32(u32::try_from(value - 36).ok()? + u32::from(b'A')),
        _ => None,
    }
}

fn packer_token(mut value: u64, radix: u64) -> Option<String> {
    if !(2..=62).contains(&radix) {
        return None;
    }
    if value == 0 {
        return Some("0".to_string());
    }
    let mut digits = Vec::new();
    while value != 0 {
        digits.push(packer_digit(value % radix)?);
        value /= radix;
    }
    digits.reverse();
    Some(digits.into_iter().collect())
}

const fn is_js_word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn replace_packer_word(source: &str, token: &str, replacement: &str) -> String {
    if token.is_empty() || token == replacement {
        return source.to_string();
    }
    let bytes = source.as_bytes();
    let mut out = String::with_capacity(source.len() + replacement.len());
    let mut cursor = 0usize;
    for (start, _) in source.match_indices(token) {
        if start < cursor {
            continue;
        }
        let end = start + token.len();
        let left_ok = start == 0 || !is_js_word_byte(bytes[start - 1]);
        let right_ok = end == bytes.len() || !is_js_word_byte(bytes[end]);
        if left_ok && right_ok {
            out.push_str(&source[cursor..start]);
            out.push_str(replacement);
            cursor = end;
        }
    }
    out.push_str(&source[cursor..]);
    out
}

/// Recover the payload of the canonical Dean Edwards P.A.C.K.E.R. wrapper
/// without executing the wrapper or any captured JavaScript.
///
/// This intentionally recognizes only the classic literal decoder shape with the canonical four- or six-argument invocation.
/// If a packer variant changes the decoder, argument values, or replacement
/// semantics, fail closed and leave it for another recovery stage.
pub fn detect_packer_eval(call: &CallExpression<'_>) -> Option<EmbeddedCodeCandidate> {
    if call.optional || call.arguments.len() != 1 {
        return None;
    }
    if !matches!(&call.callee, Expression::Identifier(id) if id.name.as_str() == "eval") {
        return None;
    }
    let Argument::CallExpression(inner) = &call.arguments[0] else {
        return None;
    };
    if inner.optional || !matches!(inner.arguments.len(), 4 | 6) {
        return None;
    }
    let function = function_expression(&inner.callee)?;
    if !has_classic_packer_params(function) || !has_classic_packer_decoder(function) {
        return None;
    }
    let Argument::StringLiteral(payload) = &inner.arguments[0] else {
        return None;
    };
    let Argument::NumericLiteral(radix) = &inner.arguments[1] else {
        return None;
    };
    let Argument::NumericLiteral(count) = &inner.arguments[2] else {
        return None;
    };
    let radix = exact_bounded_u64(radix.value, 62)?;
    let count = usize::try_from(exact_bounded_u64(count.value, 100_000)?).ok()?;
    if radix < 2 || payload.value.len() > 5_000_000 {
        return None;
    }
    let keywords = split_literal_keywords(&inner.arguments[3])?;
    if inner.arguments.len() == 6
        && (!matches!(&inner.arguments[4], Argument::NumericLiteral(value) if value.value == 0.0)
            || !matches!(&inner.arguments[5], Argument::ObjectExpression(_)))
    {
        return None;
    }
    if keywords.iter().any(|word| word.contains('$')) {
        return None;
    }

    let mut body = string_literal_value(payload)?;
    for index in (0..count).rev() {
        let token = packer_token(u64::try_from(index).ok()?, radix)?;
        let replacement = keywords
            .get(index)
            .filter(|word| !word.is_empty())
            .map_or(token.as_str(), String::as_str);
        body = replace_packer_word(&body, &token, replacement);
    }
    if body.len() > 5_000_000 {
        return None;
    }

    Some(EmbeddedCodeCandidate {
        outer_start: call.span.start,
        outer_end: call.span.end,
        kind: "Dean Edwards P.A.C.K.E.R.".to_string(),
        params: Vec::new(),
        body,
    })
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
        parts.push(value.value.as_str()?);
    }
    if parts.len() < 2 {
        return None;
    }

    let body = parts.join(separator.value.as_str()?);
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
        strings.push(string_literal_value(value)?);
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
            if let Some(candidate) = detect_packer_eval(call) {
                self.candidates.push(candidate);
            }
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

    #[test]
    fn recovers_classic_packer_eval_without_executing_it() {
        let source = r#"
            eval(function(p,a,c,k,e,d){
                e=function(c){return(c<a?'':e(parseInt(c/a)))+
                    ((c=c%a)>35?String.fromCharCode(c+29):c.toString(36))};
                if(!''.replace(/^/,String)){while(c--){d[e(c)]=k[c]||e(c)}
                    k=[function(e){return d[e]}];e=function(){return'\w+'};c=1};
                while(c--){if(k[c]){p=p.replace(new RegExp('\b'+e(c)+'\b','g'),k[c])}}
                return p
            }('0 1=2;',3,3,'var|answer|fortytwo'.split('|'),0,{}));
        "#;
        let candidates = detect(source);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].kind, "Dean Edwards P.A.C.K.E.R.");
        assert_eq!(candidates[0].body, "var answer=fortytwo;");
    }

    #[test]
    fn recovers_classic_four_argument_packer_eval() {
        let source = r#"
            eval(function(p,a,c,k,e,d){
                e=function(c){return(c<a?'':e(parseInt(c/a)))+
                    ((c=c%a)>35?String.fromCharCode(c+29):c.toString(36))};
                while(c--){if(k[c]){p=p.replace(new RegExp('\\b'+e(c)+'\\b','g'),k[c])}}
                return p
            }('0 1=2;',3,3,'var|answer|fortytwo'.split('|')));
        "#;
        let candidates = detect(source);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].kind, "Dean Edwards P.A.C.K.E.R.");
        assert_eq!(candidates[0].body, "var answer=fortytwo;");
    }

    #[test]
    fn rejects_packer_like_call_with_different_decoder_parameters() {
        let source = r#"
            eval(function(payload,a,c,k,e,d){return payload}(
                '0 1=2;',3,3,'var|answer|fortytwo'.split('|'),0,{}));
        "#;
        assert!(detect(source).is_empty());
    }
}
