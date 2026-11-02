use anyhow::{bail, Result};
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

pub fn format_source(source: &str, budget: &WorkBudget) -> Result<String> {
    let output = if let Some(output) = generate(source, SourceType::mjs(), budget)? {
        output
    } else {
        generate(source, SourceType::cjs(), budget)?
            .ok_or_else(|| anyhow::anyhow!("Oxc could not parse source as module or script"))?
    };
    if output.trim().is_empty() && !source.trim().is_empty() {
        bail!("codegen unexpectedly emitted empty source");
    }
    Ok(output)
}
