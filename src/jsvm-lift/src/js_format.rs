use anyhow::{bail, Result};
use oxc_allocator::Allocator;
use oxc_codegen::Codegen;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;

fn generate(source: &str, source_type: SourceType) -> Option<String> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, source_type);
    if !parsed.is_clean() {
        return None;
    }
    Some(Codegen::new().build(&parsed.program).code)
}

pub fn format_source(source: &str) -> Result<String> {
    let output = generate(source, SourceType::mjs())
        .or_else(|| generate(source, SourceType::cjs()))
        .ok_or_else(|| anyhow::anyhow!("Oxc could not parse source as module or script"))?;
    if output.trim().is_empty() && !source.trim().is_empty() {
        bail!("codegen unexpectedly emitted empty source");
    }
    Ok(output)
}
