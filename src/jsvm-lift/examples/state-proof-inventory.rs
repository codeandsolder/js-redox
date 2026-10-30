use anyhow::{Context, Result};
use jsvm_lift::state_flatten::{
    prove_function_if_ladder_states_before_event,
    prove_function_protected_if_ladder_event_unreachable_after_state,
    structurally_proven_if_ladder_identifier_equalities_at_event,
};
use oxc_allocator::Allocator;
use oxc_semantic::SemanticBuilder;
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
    let identifier_equalities = args.iter().any(|arg| arg == "--identifier-equalities");
    let after_state = args.iter().find_map(|arg| {
        arg.to_str()?
            .strip_prefix("--unreachable-after-state=")?
            .parse::<u64>()
            .ok()
    });
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
        !required_states.is_empty() || identifier_equalities || after_state.is_some(),
        "missing proof query (--required-state, --identifier-equalities, or --unreachable-after-state)"
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
    let proven = (!required_states.is_empty()).then(|| {
        prove_function_if_ladder_states_before_event(
            &source,
            &parsed.program,
            function_start,
            function_end,
            &required_states,
            event,
        )
    });
    let unreachable_after_state = after_state.map(|state| {
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .build(&parsed.program);
        prove_function_protected_if_ladder_event_unreachable_after_state(
            &source,
            &parsed.program,
            &semantic.semantic,
            function_start,
            function_end,
            state,
            event,
        )
    });
    let equalities = if identifier_equalities {
        let semantic = SemanticBuilder::new()
            .with_build_nodes(true)
            .build(&parsed.program);
        let scoping = semantic.semantic.scoping();
        structurally_proven_if_ladder_identifier_equalities_at_event(
            &source,
            &parsed.program,
            &semantic.semantic,
            function_start,
            function_end,
            event,
        )
        .into_iter()
        .map(|proof| {
            json!({
                "state": proof.state,
                "assignment": [proof.assignment_start, proof.assignment_end],
                "left": scoping.symbol_name(proof.left_symbol),
                "right": scoping.symbol_name(proof.right_symbol),
            })
        })
        .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "function": [function_start, function_end],
            "event": [event_start, event_end],
            "required_states": required_states,
            "proven": proven,
            "identifier_equalities": equalities,
            "unreachable_after_state": unreachable_after_state,
        }))?
    );
    Ok(())
}
