//! Regression for oxc-project/oxc#28542; retain after removing the backport.
use oxc_allocator::Allocator;
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;

#[test]
fn function_var_redeclaration_respects_statement_lists() {
    for (source, source_type, valid) in [
        (
            "function outer() { function n() {} if (true) { var n = n(); } }",
            SourceType::cjs(),
            true,
        ),
        (
            "function outer() { if (true) { function n() {} { var n; } } }",
            SourceType::cjs(),
            false,
        ),
        (
            "function n() {} if (true) { var n; }",
            SourceType::mjs(),
            false,
        ),
    ] {
        let allocator = Allocator::default();
        let parsed = Parser::new(&allocator, source, source_type).parse();
        assert!(parsed.diagnostics.is_empty(), "{source}");
        let result = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert_eq!(result.diagnostics.is_empty(), valid, "{source}");
    }
}
