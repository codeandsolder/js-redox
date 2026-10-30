use anyhow::{Context, Result};
use jsvm_lift::state_flatten::prove_function_if_ladder_states_before_event;
use oxc_allocator::Allocator;
use oxc_span::{SourceType, Span};
use rolldown_redox::ecmascript::parse_program;
use serde_json::json;
use std::{env, fs, path::PathBuf};

fn arg_u32(args: &[std::ffi::OsString], prefix: &str) -> Result<u32> {
    args.iter()
        .find_map(|arg| arg.to_str()?.strip_prefix(prefix)?.parse::<u32>().ok())
        .with_context(|| format!("missing {prefix}<u32>"))
}

fn main() -> Result<()> {
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    let path = args
        .iter()
        .find(|arg| !arg.to_string_lossy().starts_with("--"))
        .map(PathBuf::from)
        .context("missing JavaScript file")?;
    let function_start = arg_u32(&args, "--function-start=")?;
    let function_end = arg_u32(&args, "--function-end=")?;
    let event_start = arg_u32(&args, "--event-start=")?;
    let event_end = arg_u32(&args, "--event-end=")?;
    let required_states = args
        .iter()
        .filter_map(|arg| {
            arg.to_str()?
                .strip_prefix("--required-state=")?
                .parse::<u64>()
                .ok()
        })
        .collect::<Vec<_>>();
    anyhow::ensure!(
        !required_states.is_empty(),
        "missing --required-state=<u64>"
    );

    let source =
        fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &source, SourceType::cjs());
    anyhow::ensure!(
        parsed.diagnostics == 0 && !parsed.fatal_error,
        "parse diagnostics"
    );
    let event = Span::new(event_start, event_end);
    let proven = prove_function_if_ladder_states_before_event(
        &source,
        &parsed.program,
        function_start,
        function_end,
        &required_states,
        event,
    );
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "function": [function_start, function_end],
            "event": [event_start, event_end],
            "required_states": required_states,
            "proven": proven,
        }))?
    );
    Ok(())
}
