use crate::numeric::exact_u64;
use oxc_allocator::Allocator;
use oxc_ast::{
    ast::{Argument, AssignmentTarget, Expression},
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use std::collections::BTreeSet;

#[derive(Default)]
struct ParseIntAliasVisitor {
    aliases: BTreeSet<String>,
}

fn target_ident(target: &AssignmentTarget<'_>) -> Option<String> {
    match target {
        AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.to_string()),
        _ => None,
    }
}

impl<'a> Visit<'a> for ParseIntAliasVisitor {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::VariableDeclarator(v) => {
                let oxc_ast::ast::BindingPattern::BindingIdentifier(id) = &v.id else {
                    return;
                };
                let Some(Expression::Identifier(rhs)) = v.init.as_ref() else {
                    return;
                };
                if rhs.name.as_str() == "parseInt" {
                    self.aliases.insert(id.name.to_string());
                }
            }
            AstKind::AssignmentExpression(a) if a.operator.is_assign() => {
                let Some(name) = target_ident(&a.left) else {
                    return;
                };
                let Expression::Identifier(rhs) = &a.right else {
                    return;
                };
                if rhs.name.as_str() == "parseInt" {
                    self.aliases.insert(name);
                }
            }
            _ => {}
        }
    }

    fn visit_program(&mut self, it: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, it);
    }
}

/// Return identifiers whose source assignment is a direct alias of `parseInt`.
/// This syntax-only helper is for diagnostics, not semantic rewrite proofs.
#[must_use]
pub fn parse_int_aliases(source: &str) -> BTreeSet<String> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::cjs());
    if parsed.fatal_error {
        return BTreeSet::new();
    }
    let mut visitor = ParseIntAliasVisitor::default();
    visitor.visit_program(&parsed.program);
    visitor.aliases
}

fn expression_from_program<'a>(
    program: &'a oxc_ast::ast::Program<'a>,
) -> Option<&'a Expression<'a>> {
    let stmt = program.body.first()?;
    let oxc_ast::ast::Statement::ExpressionStatement(es) = stmt else {
        return None;
    };
    Some(&es.expression)
}

/// Resolve a standalone `parseInt("literal", radix)` expression, including a
/// source-discovered direct alias. Unsupported edge cases remain symbolic.
#[must_use]
pub fn resolve_literal_parse_int(preview: &str, aliases: &BTreeSet<String>) -> Option<u64> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, preview, SourceType::cjs());
    if !parsed.is_clean() {
        return None;
    }

    let mut expr = expression_from_program(&parsed.program)?;
    while let Expression::ParenthesizedExpression(paren) = expr {
        expr = &paren.expression;
    }
    let Expression::CallExpression(call) = expr else {
        return None;
    };
    let Expression::Identifier(callee) = &call.callee else {
        return None;
    };
    if callee.name.as_str() != "parseInt" && !aliases.contains(callee.name.as_str()) {
        return None;
    }
    if call.arguments.len() != 2 {
        return None;
    }
    let Argument::StringLiteral(text) = &call.arguments[0] else {
        return None;
    };
    let Argument::NumericLiteral(radix) = &call.arguments[1] else {
        return None;
    };
    let radix = u32::try_from(exact_u64(radix.value)?).ok()?;
    if !(2..=36).contains(&radix) {
        return None;
    }
    let raw = text.value.as_str()?.trim();
    let raw = raw.strip_prefix('+').unwrap_or(raw);
    u64::from_str_radix(raw, radix).ok()
}

#[cfg(test)]
mod tests {
    use super::{parse_int_aliases, resolve_literal_parse_int};

    #[test]
    fn discovers_direct_aliases_and_resolves_literal_calls() {
        let aliases = parse_int_aliases("const p = parseInt; let q; q = parseInt;");
        assert!(aliases.contains("p"));
        assert!(aliases.contains("q"));
        assert_eq!(
            resolve_literal_parse_int("p('ff', 16)", &aliases),
            Some(255)
        );
        assert_eq!(
            resolve_literal_parse_int("parseInt(\"101\", 2)", &aliases),
            Some(5)
        );
    }

    #[test]
    fn leaves_dynamic_or_invalid_calls_symbolic() {
        let aliases = parse_int_aliases("const p = parseInt;");
        assert_eq!(resolve_literal_parse_int("p(value, 16)", &aliases), None);
        assert_eq!(resolve_literal_parse_int("other('ff', 16)", &aliases), None);
        assert_eq!(resolve_literal_parse_int("p('ff', 1)", &aliases), None);
    }
}
