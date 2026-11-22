use anyhow::{anyhow, bail, Result};
use oxc_allocator::Allocator;
use oxc_codegen::Codegen;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use work_budget::WorkBudget;

fn generate(source: &str, source_type: SourceType, budget: &WorkBudget) -> Result<Option<String>> {
    budget.checkpoint()?;
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, source_type);
    budget.checkpoint()?;
    if !parsed.is_clean() {
        return Ok(None);
    }
    let output = Codegen::new().build(&parsed.program).code;
    budget.checkpoint()?;
    Ok(Some(output))
}

/// Format JavaScript source using Oxc with a module-first, `CommonJS` fallback.
///
/// # Errors
///
/// Fails on work-budget exhaustion, when both parse modes reject the input, or if code generation unexpectedly emits only whitespace for nonempty input.
pub fn format_source(source: &str, budget: &WorkBudget) -> Result<String> {
    let output = if let Some(output) = generate(source, SourceType::mjs(), budget)? {
        output
    } else {
        generate(source, SourceType::cjs(), budget)?
            .ok_or_else(|| anyhow!("Oxc could not parse source as module or script"))?
    };
    validate_output(source, output)
}

/// Format already validated source in its exact parser mode, without fallback.
///
/// # Errors
/// Returns an error on parse rejection, work-budget exhaustion, or unexpectedly
/// empty code generation. The caller supplies the validated source type.
pub fn format_source_as(
    source: &str,
    source_type: SourceType,
    budget: &WorkBudget,
) -> Result<String> {
    let output = generate(source, source_type, budget)?
        .ok_or_else(|| anyhow!("Oxc could not parse source in the selected mode"))?;
    validate_output(source, output)
}

fn validate_output(source: &str, output: String) -> Result<String> {
    if output.trim().is_empty() && !source.trim().is_empty() {
        bail!("codegen unexpectedly emitted empty source");
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_mode_preserves_script_only_syntax_without_fallback() -> Result<()> {
        let budget = WorkBudget::unlimited("format-mode");
        let source = "var await=1; await;";
        let formatted = format_source_as(source, SourceType::cjs(), &budget)?;
        assert!(formatted.contains("var await = 1;"));
        assert!(format_source_as(source, SourceType::mjs(), &budget).is_err());
        Ok(())
    }

    #[test]
    fn exact_mode_preserves_module_only_syntax_without_fallback() -> Result<()> {
        let budget = WorkBudget::unlimited("format-mode");
        let source = "export const x=1;";
        let formatted = format_source_as(source, SourceType::mjs(), &budget)?;
        assert!(formatted.contains("export const x = 1;"));
        assert!(format_source_as(source, SourceType::cjs(), &budget).is_err());
        Ok(())
    }
}
