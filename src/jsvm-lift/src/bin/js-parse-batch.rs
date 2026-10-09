use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::{
    fs,
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
};

#[derive(ClapParser, Debug)]
#[command(about = "Batch-check JavaScript files with Oxc without per-file process startup")]
struct Args {
    list: PathBuf,
    failures: PathBuf,
}

#[derive(Serialize)]
struct ParseFailure<'a> {
    path: &'a str,
    bytes: usize,
    module_diagnostics: usize,
    module_fatal_error: bool,
    script_diagnostics: usize,
    script_fatal_error: bool,
}

fn check_source<'a>(path: &'a Path, source: &str) -> Option<ParseFailure<'a>> {
    let allocator = Allocator::default();
    let module = parse_program(&allocator, source, SourceType::mjs());
    if module.is_clean() {
        return None;
    }

    let allocator = Allocator::default();
    let script = parse_program(&allocator, source, SourceType::cjs());
    if script.is_clean() {
        return None;
    }

    Some(ParseFailure {
        path: path.to_str().unwrap_or("<non-utf8-path>"),
        bytes: source.len(),
        module_diagnostics: module.diagnostics,
        module_fatal_error: module.fatal_error,
        script_diagnostics: script.diagnostics,
        script_fatal_error: script.fatal_error,
    })
}

fn main() -> Result<()> {
    let args = Args::parse();
    let list =
        fs::File::open(&args.list).with_context(|| format!("opening {}", args.list.display()))?;

    let mut checked = 0usize;
    let mut failed = 0usize;
    let mut failures = String::new();

    for line in BufReader::new(list).lines() {
        let line = line?;
        if line.is_empty() {
            continue;
        }
        let path = Path::new(&line);
        let source = match fs::read_to_string(path) {
            Ok(source) => source,
            Err(error) => {
                failed += 1;
                failures.push_str(
                    &serde_json::json!({
                        "path": line,
                        "read_error": error.to_string(),
                    })
                    .to_string(),
                );
                failures.push('\n');
                checked += 1;
                continue;
            }
        };
        if let Some(failure) = check_source(path, &source) {
            failed += 1;
            failures.push_str(&serde_json::to_string(&failure)?);
            failures.push('\n');
        }
        checked += 1;
    }

    if let Some(parent) = args.failures.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&args.failures, failures)
        .with_context(|| format!("writing {}", args.failures.display()))?;
    println!("checked={checked} failed={failed}");
    Ok(())
}
