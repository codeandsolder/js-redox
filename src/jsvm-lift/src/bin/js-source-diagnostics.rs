use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_diagnostics::OxcDiagnostic;
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;
use serde::Serialize;
use std::{
    fs,
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
};

#[derive(ClapParser, Debug)]
#[command(
    about = "Batch-report Oxc parser and semantic diagnostics in module and classic-script modes"
)]
struct Args {
    list: PathBuf,
}

#[derive(Serialize)]
struct LabelReport {
    offset: u32,
    len: u32,
    label: Option<String>,
}

#[derive(Serialize)]
struct DiagnosticReport {
    message: String,
    labels: Vec<LabelReport>,
}

fn diagnostic(d: &OxcDiagnostic) -> DiagnosticReport {
    DiagnosticReport {
        message: d.to_string(),
        labels: d
            .labels
            .iter()
            .map(|label| LabelReport {
                offset: label.offset(),
                len: label.len(),
                label: label.label().map(str::to_owned),
            })
            .collect(),
    }
}

#[derive(Serialize)]
struct ModeReport {
    parser_fatal: bool,
    parser_diagnostics: Vec<DiagnosticReport>,
    semantic_diagnostics: Vec<DiagnosticReport>,
}

#[derive(Serialize)]
struct FileReport {
    path: String,
    bytes: usize,
    module: ModeReport,
    classic: ModeReport,
}

fn analyze(source: &str, source_type: SourceType) -> ModeReport {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, source_type).parse();
    let parser_fatal = parsed.fatal_error;
    let parser_diagnostics = parsed.diagnostics.iter().map(diagnostic).collect();
    let semantic_diagnostics = if parser_fatal {
        Vec::new()
    } else {
        SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program)
            .diagnostics
            .iter()
            .map(diagnostic)
            .collect()
    };
    ModeReport {
        parser_fatal,
        parser_diagnostics,
        semantic_diagnostics,
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    let list =
        fs::File::open(&args.list).with_context(|| format!("opening {}", args.list.display()))?;
    for line in BufReader::new(list).lines() {
        let line = line?;
        if line.is_empty() {
            continue;
        }
        let path = Path::new(&line);
        let source = fs::read_to_string(path).with_context(|| format!("reading {line}"))?;
        let report = FileReport {
            path: line,
            bytes: source.len(),
            module: analyze(&source, SourceType::mjs()),
            classic: analyze(&source, SourceType::cjs()),
        };
        println!("{}", serde_json::to_string(&report)?);
    }
    Ok(())
}
