use anyhow::{Context, Result};
use clap::{Parser as ClapParser, ValueEnum};
use jsvm_lift::{
    browser_decode::{decode_html, decode_script, ScriptDecodeContext, ScriptKind},
    sha256_hex,
};
use serde::Serialize;
use std::{fs, path::PathBuf};

#[derive(Clone, Copy, Debug, ValueEnum)]
enum DecodeKindArg {
    Module,
    Classic,
    ClassicWorker,
    Html,
}

impl DecodeKindArg {
    fn script_kind(self) -> Option<ScriptKind> {
        match self {
            Self::Module => Some(ScriptKind::Module),
            Self::Classic => Some(ScriptKind::Classic),
            Self::ClassicWorker => Some(ScriptKind::ClassicWorker),
            Self::Html => None,
        }
    }
}

#[derive(ClapParser, Debug)]
#[command(about = "Decode captured Web source bytes using browser/WHATWG encoding rules")]
struct Args {
    input: PathBuf,
    #[arg(long, value_enum, default_value = "classic")]
    kind: DecodeKindArg,
    #[arg(long)]
    script_charset: Option<String>,
    #[arg(long)]
    document_encoding: Option<String>,
    #[arg(long)]
    response_encoding: Option<String>,
    #[arg(long)]
    transport_content_type: Option<String>,
    #[arg(long)]
    default_encoding: Option<String>,
    /// Write decoded UTF-8 source to this path.
    #[arg(long)]
    output: Option<PathBuf>,
    /// Emit machine-readable metadata instead of a text summary.
    #[arg(long)]
    json: bool,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    input: String,
    raw_bytes: usize,
    decoded_bytes: usize,
    decoded_sha256: String,
    encoding: String,
    decode_source: &'static str,
    had_errors: bool,
    uncertain: bool,
    bom_encoding: Option<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let bytes =
        fs::read(&args.input).with_context(|| format!("reading {}", args.input.display()))?;
    let (source, encoding, decode_source, had_errors, uncertain, bom_encoding) =
        if let Some(kind) = args.kind.script_kind() {
            let decoded = decode_script(
                &bytes,
                ScriptDecodeContext {
                    kind,
                    script_charset: args.script_charset.as_deref(),
                    document_encoding: args.document_encoding.as_deref(),
                    response_encoding: args.response_encoding.as_deref(),
                },
            );
            (
                decoded.source,
                decoded.encoding,
                decoded.decode_source.as_str(),
                decoded.had_errors,
                decoded.uncertain,
                decoded.bom_encoding,
            )
        } else {
            let decoded = decode_html(
                &bytes,
                args.transport_content_type.as_deref(),
                args.default_encoding.as_deref(),
            );
            (
                decoded.source,
                decoded.encoding,
                decoded.decode_source.as_str(),
                decoded.had_errors,
                decoded.uncertain,
                decoded.bom_encoding,
            )
        };
    if let Some(output) = &args.output {
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(output, source.as_bytes())?;
    }
    let report = Report {
        schema: "js-browser-decode/v2",
        input: args.input.display().to_string(),
        raw_bytes: bytes.len(),
        decoded_bytes: source.len(),
        decoded_sha256: sha256_hex(source.as_bytes()),
        encoding,
        decode_source,
        had_errors,
        uncertain,
        bom_encoding,
    };
    if args.json {
        println!("{}", serde_json::to_string(&report)?);
    } else {
        println!(
            "{} -> {} bytes sha256={} encoding={} source={} errors={} uncertain={}",
            report.raw_bytes,
            report.decoded_bytes,
            report.decoded_sha256,
            report.encoding,
            report.decode_source,
            report.had_errors,
            report.uncertain
        );
    }
    Ok(())
}
