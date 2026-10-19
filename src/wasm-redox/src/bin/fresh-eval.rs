use anyhow::{Context, Result};
use clap::Parser;
use std::{fs, path::PathBuf};
use wasm_redox::fresh_eval::{FreshI32Arg, FreshI32CallRequest, FreshTableGrowRequest};

#[derive(Debug, Parser)]
#[command(
    about = "Fail-closed exact evaluation of an internal i32 WebAssembly call on fresh module state"
)]
struct Args {
    input: PathBuf,

    #[arg(long)]
    function_index: usize,

    #[arg(long = "i32-arg")]
    i32_args: Vec<u32>,

    #[arg(long = "initial-table-grow", value_parser = parse_table_grow)]
    initial_table_grows: Vec<FreshTableGrowRequest>,

    #[arg(long = "then-call", value_parser = parse_call)]
    then_calls: Vec<FreshI32CallRequest>,

    #[arg(long, default_value_t = 1_000_000)]
    fuel: u64,
}

fn parse_sequence_arg(value: &str) -> std::result::Result<FreshI32Arg, String> {
    if let Some(step) = value.strip_prefix('@') {
        return step
            .parse::<usize>()
            .map(|step| FreshI32Arg::StepResult { step })
            .map_err(|error| format!("invalid prior-step reference {value:?}: {error}"));
    }
    value
        .parse::<u32>()
        .map(|value| FreshI32Arg::Literal { value })
        .map_err(|error| format!("invalid i32 argument {value:?}: {error}"))
}

fn parse_call(value: &str) -> std::result::Result<FreshI32CallRequest, String> {
    let (function_index, args) = value
        .split_once(':')
        .ok_or_else(|| "expected FUNCTION_INDEX:ARG[,ARG...]".to_owned())?;
    let function_index = function_index
        .parse::<usize>()
        .map_err(|error| format!("invalid function index: {error}"))?;
    let i32_args = if args.is_empty() {
        Vec::new()
    } else {
        args.split(',')
            .map(parse_sequence_arg)
            .collect::<std::result::Result<Vec<_>, _>>()?
    };
    Ok(FreshI32CallRequest {
        function_index,
        i32_args,
    })
}

fn parse_table_grow(value: &str) -> std::result::Result<FreshTableGrowRequest, String> {
    let (table_index, delta) = value
        .split_once(':')
        .ok_or_else(|| "expected TABLE_INDEX:DELTA".to_owned())?;
    Ok(FreshTableGrowRequest {
        table_index: table_index
            .parse::<usize>()
            .map_err(|error| format!("invalid table index: {error}"))?,
        delta: delta
            .parse::<u32>()
            .map_err(|error| format!("invalid table grow delta: {error}"))?,
    })
}

fn main() -> Result<()> {
    let args = Args::parse();
    let bytes = fs::read(&args.input).with_context(|| format!("read {}", args.input.display()))?;
    if args.then_calls.is_empty() && args.initial_table_grows.is_empty() {
        let report = wasm_redox::fresh_eval::evaluate_fresh_i32_call(
            &bytes,
            args.function_index,
            &args.i32_args,
            Some(args.fuel),
        );
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        let mut calls = Vec::with_capacity(args.then_calls.len() + 1);
        calls.push(FreshI32CallRequest {
            function_index: args.function_index,
            i32_args: args
                .i32_args
                .into_iter()
                .map(|value| FreshI32Arg::Literal { value })
                .collect(),
        });
        calls.extend(args.then_calls);
        let report = wasm_redox::fresh_eval::evaluate_fresh_i32_sequence(
            &bytes,
            &args.initial_table_grows,
            &calls,
            Some(args.fuel),
        );
        println!("{}", serde_json::to_string_pretty(&report)?);
    }
    Ok(())
}
