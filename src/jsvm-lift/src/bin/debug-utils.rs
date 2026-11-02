#[path = "debug-utils/bytecode.rs"]
mod bytecode;

use anyhow::{bail, Context, Result};
use clap::{Parser, Subcommand};
use regex::Regex;
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::{Path, PathBuf},
};

#[derive(Debug, Parser)]
#[command(about = "Analyst-only js-redox debugging and corpus inspection utilities")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Vote on likely bytecode instruction widths in scanner JSONL output.
    WidthConsensus {
        jsonl: PathBuf,
        #[arg(long, default_value_t = 0)]
        top_score_slack: i64,
    },
    /// Compare Rust opcode-map recovery against a previously captured JS route dump.
    CompareOpcodeMaps {
        rust_json: PathBuf,
        decoder_id: String,
        js_routes: PathBuf,
    },
    /// Cluster normalized handlers by signature and emit a small semantic dictionary.
    SemanticDictionary {
        batch_json: PathBuf,
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Inspect linked decoder streams in scanner JSON output.
    DumpLinkedBytecode {
        jsonl: PathBuf,
        #[arg(long, default_value_t = 20)]
        instructions: usize,
        #[arg(long)]
        max_decoders: Option<usize>,
        #[arg(long)]
        builder_start: Option<u64>,
        #[arg(long = "all")]
        include_all: bool,
    },
    /// Extract normalized linked bytecode streams from a JavaScript source.
    ExtractLinkedStreams {
        file: PathBuf,
        #[arg(long)]
        scanner: Option<PathBuf>,
        #[arg(long = "out")]
        output: Option<PathBuf>,
        #[arg(long, default_value_t = 12)]
        preview: usize,
    },
}

fn read_json(path: &Path) -> Result<Value> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    serde_json::from_str(&text).with_context(|| format!("parsing {}", path.display()))
}

fn read_jsonl_values(path: &Path) -> Result<Vec<Value>> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    text.lines()
        .enumerate()
        .filter(|(_, line)| !line.trim().is_empty())
        .map(|(index, line)| {
            serde_json::from_str(line)
                .with_context(|| format!("parsing {} line {}", path.display(), index + 1))
        })
        .collect()
}

fn integer(value: Option<&Value>, label: &str) -> Result<i64> {
    value
        .and_then(Value::as_i64)
        .with_context(|| format!("{label} must be an integer"))
}

fn width_consensus(path: &Path, top_score_slack: i64) -> Result<()> {
    for report in read_jsonl_values(path)? {
        let mut votes = BTreeMap::<i64, usize>::new();
        let mut weighted = BTreeMap::<i64, i64>::new();
        let mut streams = 0_usize;
        for builder in report
            .get("push_builders")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let Some(hints) = builder.get("width_hints").and_then(Value::as_array) else {
                continue;
            };
            if hints.is_empty() {
                continue;
            }
            let best = hints
                .iter()
                .filter_map(|hint| hint.get("score").and_then(Value::as_i64))
                .max()
                .context("width hint missing integer score")?;
            let mut accepted = hints
                .iter()
                .filter(|hint| {
                    hint.get("score")
                        .and_then(Value::as_i64)
                        .is_some_and(|score| score >= best - top_score_slack)
                })
                .collect::<Vec<_>>();
            accepted.sort_by_key(|hint| hint.get("width").and_then(Value::as_i64));
            let chosen = accepted.first().context("no accepted width hint")?;
            let width = integer(chosen.get("width"), "width hint width")?;
            *votes.entry(width).or_default() += 1;
            let arguments = builder
                .get("arguments")
                .and_then(Value::as_i64)
                .unwrap_or_default()
                .max(1);
            *weighted.entry(width).or_default() += arguments;
            streams += 1;
        }

        let name = report
            .get("file")
            .and_then(Value::as_str)
            .and_then(|file| Path::new(file).file_name())
            .and_then(|name| name.to_str())
            .unwrap_or("<unknown>");
        if votes.is_empty() {
            println!("{name}: no width consensus");
            continue;
        }
        let max_votes = votes.values().copied().max().unwrap_or_default();
        let best = votes
            .iter()
            .filter(|(_, count)| **count == max_votes)
            .map(|(&width, _)| width)
            .min_by_key(|width| (-weighted.get(width).copied().unwrap_or_default(), *width))
            .context("failed to choose width")?;
        println!("{name}: width={best} streams={streams} votes={votes:?} weighted={weighted:?}");
    }
    Ok(())
}

fn normalize_semantic(text: &str) -> String {
    text.chars().filter(|ch| !ch.is_whitespace()).collect()
}

fn load_js_routes(path: &Path) -> Result<BTreeMap<i64, Value>> {
    let mut routes = BTreeMap::new();
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    for (index, line) in text.lines().enumerate() {
        if !line.starts_with("{\"op\"") {
            continue;
        }
        let row: Value = serde_json::from_str(line)
            .with_context(|| format!("parsing {} line {}", path.display(), index + 1))?;
        let opcode = integer(row.get("op"), "route op")?;
        routes.insert(opcode, row);
    }
    Ok(routes)
}

fn semantic_blob(value: Option<&Value>) -> String {
    value
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(normalize_semantic)
        .collect::<Vec<_>>()
        .join(";")
}

fn compare_opcode_maps(rust_json: &Path, decoder_id: &str, js_routes: &Path) -> Result<()> {
    let text = fs::read_to_string(rust_json)
        .with_context(|| format!("reading {}", rust_json.display()))?;
    let first = text
        .lines()
        .find(|line| !line.trim().is_empty())
        .context("Rust report is empty")?;
    let report: Value = serde_json::from_str(first)
        .with_context(|| format!("parsing first report in {}", rust_json.display()))?;
    let maps = report
        .get("opcode_maps")
        .and_then(Value::as_array)
        .context("Rust report has no opcode_maps array")?
        .iter()
        .filter(|map| map.get("decoder_function_id").and_then(Value::as_str) == Some(decoder_id))
        .collect::<Vec<_>>();
    println!("decoder {decoder_id} rust_maps {}", maps.len());
    if maps.is_empty() {
        bail!("no Rust opcode map for decoder {decoder_id}");
    }

    let js = load_js_routes(js_routes)?;
    let score = |map: &&Value| -> usize {
        map.get("handlers")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter(|handler| {
                let Some(opcode) = handler.get("opcode").and_then(Value::as_i64) else {
                    return false;
                };
                let Some(route) = js.get(&opcode) else {
                    return false;
                };
                handler.get("path") == route.get("trace")
            })
            .count()
    };
    let best = maps
        .iter()
        .max_by_key(|map| score(map))
        .context("failed to choose Rust opcode map")?;
    let handlers = best
        .get("handlers")
        .and_then(Value::as_array)
        .context("opcode map has no handlers array")?;
    let by_opcode = handlers
        .iter()
        .filter_map(|handler| {
            handler
                .get("opcode")
                .and_then(Value::as_i64)
                .map(|opcode| (opcode, handler))
        })
        .collect::<HashMap<_, _>>();

    let mut path_ok = 0_usize;
    let mut terminal_ok = 0_usize;
    let mut semantic_exact = 0_usize;
    let mut mismatches = Vec::new();
    for (opcode, route) in &js {
        let Some(handler) = by_opcode.get(opcode) else {
            mismatches.push(format!("{opcode}: missing-rust-handler"));
            continue;
        };
        let path_matches = handler.get("path") == route.get("trace");
        let terminal_matches = handler.get("terminal") == route.get("terminal");
        let semantics_match =
            semantic_blob(handler.get("semantic")) == semantic_blob(route.get("semantic"));
        path_ok += usize::from(path_matches);
        terminal_ok += usize::from(terminal_matches);
        semantic_exact += usize::from(semantics_match);
        if !(path_matches && terminal_matches) && mismatches.len() < 20 {
            mismatches.push(format!(
                "{opcode}: rust_path={:?} js_path={:?} rust_terminal={:?} js_terminal={:?}",
                handler.get("path"),
                route.get("trace"),
                handler.get("terminal"),
                route.get("terminal")
            ));
        }
    }

    println!(
        "parent={} state={} opcode_max={}",
        best.get("parent_function_id")
            .and_then(Value::as_str)
            .unwrap_or("?"),
        best.get("state_var").and_then(Value::as_str).unwrap_or("?"),
        best.get("opcode_max")
            .map_or_else(|| "?".into(), Value::to_string)
    );
    println!(
        "bindings {}",
        best.get("selector_bindings").unwrap_or(&Value::Null)
    );
    println!(
        "observed={} path_match={path_ok} terminal_match={terminal_ok} semantic_exact={semantic_exact}",
        js.len()
    );
    for mismatch in mismatches {
        println!("MISMATCH {mismatch}");
    }
    if path_ok != js.len() || terminal_ok != js.len() {
        bail!("opcode map differs from captured JS routes");
    }
    Ok(())
}

fn classify_semantic(text: &str) -> Result<&'static str> {
    let rules = [
        ("JUMP_REL", r"^ip\+=op1;$"),
        ("THROW_VM_EXCEPTION", r"^throw:"),
        ("STORE_INDEXED_IMMEDIATE", r"^v\d+\[v\d+=op1\]=op2;$"),
        ("MOVE_INDEXED_SAME_BANK", r"^v\d+\[v\d+=op1\]=v\d+\[op2\];$"),
        (
            "MOVE_INDEXED_CROSS_BANK",
            r"^v\d+\[v\d+=op1\]=v\d+\[op2\];$",
        ),
        ("NEW_ARRAY_INDEXED", r".*\[v\d+=op1\]=\[\];$"),
        ("BINARY_ADD_INDEXED", r".*\[op1\].*\[op2\].*=.*\+.*;?$"),
        ("BINARY_SHIFT_RIGHT", r".*=.*>>.*;?$"),
        ("BINARY_IN", r".*\sin\s.*;?$"),
        ("LOGICAL_NOT_INDEXED", r".*=!.*\[op1\];?$"),
        ("INDEXED_PROPERTY_READ", r".*\[op1\].*\[op2\].*"),
        ("CALL_LIKE", r"^v\d+\(.*\);$"),
    ];
    for (name, pattern) in rules {
        if Regex::new(pattern)?.is_match(text) {
            return Ok(name);
        }
    }
    if text.contains("function") && text.contains("=function") {
        Ok("CREATE_CLOSURE")
    } else if text.contains("try{") && text.contains("finally{") {
        Ok("CALL_OR_PROPERTY_HELPER")
    } else {
        Ok("UNCLASSIFIED")
    }
}

fn semantic_dictionary(batch_json: &Path, output: Option<&Path>) -> Result<()> {
    const EMPTY_SHA: &str = "e3b0c44298fc1c14";
    let rows = read_json(batch_json)?;
    let rows = rows
        .as_array()
        .context("batch JSON root must be an array")?;
    let mut clusters = BTreeMap::<String, Vec<Value>>::new();
    for vm in rows {
        if vm.get("status").and_then(Value::as_str) != Some("ok") {
            continue;
        }
        let decoder = vm.get("decoder").and_then(Value::as_str).unwrap_or("?");
        for handler in vm
            .get("handlers")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let Some(signature) = handler.get("signature").and_then(Value::as_str) else {
                continue;
            };
            if signature == EMPTY_SHA {
                continue;
            }
            clusters
                .entry(signature.to_owned())
                .or_default()
                .push(json!({
                    "decoder": decoder,
                    "opcode": handler.get("opcode").cloned().unwrap_or(Value::Null),
                    "semantic": handler.get("semantic").cloned().unwrap_or(Value::Null),
                }));
        }
    }

    let mut dictionary = Vec::new();
    let mut labels = BTreeMap::<String, usize>::new();
    for (signature, members) in clusters {
        let exemplar = members
            .first()
            .and_then(|member| member.get("semantic"))
            .and_then(Value::as_str)
            .unwrap_or_default();
        let label = classify_semantic(exemplar)?.to_owned();
        *labels.entry(label.clone()).or_default() += 1;
        let vm_count = members
            .iter()
            .filter_map(|member| member.get("decoder").and_then(Value::as_str))
            .collect::<BTreeSet<_>>()
            .len();
        let member_summary = members
            .iter()
            .map(|member| {
                json!({
                    "decoder": member.get("decoder").cloned().unwrap_or(Value::Null),
                    "opcode": member.get("opcode").cloned().unwrap_or(Value::Null),
                })
            })
            .collect::<Vec<_>>();
        dictionary.push(json!({
            "signature": signature,
            "label": label,
            "count": members.len(),
            "vm_count": vm_count,
            "semantic": exemplar,
            "members": member_summary,
        }));
    }
    dictionary.sort_by(|left, right| {
        let left_count = left
            .get("count")
            .and_then(Value::as_u64)
            .unwrap_or_default();
        let right_count = right
            .get("count")
            .and_then(Value::as_u64)
            .unwrap_or_default();
        right_count.cmp(&left_count).then_with(|| {
            left.get("signature")
                .and_then(Value::as_str)
                .cmp(&right.get("signature").and_then(Value::as_str))
        })
    });
    let handlers = dictionary
        .iter()
        .filter_map(|entry| entry.get("count").and_then(Value::as_u64))
        .sum::<u64>();
    let reused = dictionary
        .iter()
        .filter(|entry| {
            entry
                .get("count")
                .and_then(Value::as_u64)
                .is_some_and(|count| count > 1)
        })
        .count();
    let document = json!({
        "summary": {
            "signatures": dictionary.len(),
            "reused": reused,
            "handlers": handlers,
            "labels": labels,
        },
        "dictionary": dictionary,
    });
    let mut text = serde_json::to_string_pretty(&document)?;
    text.push('\n');
    if let Some(path) = output {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
        }
        fs::write(path, text).with_context(|| format!("writing {}", path.display()))?;
    } else {
        print!("{text}");
    }
    Ok(())
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::WidthConsensus {
            jsonl,
            top_score_slack,
        } => width_consensus(&jsonl, top_score_slack),
        Command::CompareOpcodeMaps {
            rust_json,
            decoder_id,
            js_routes,
        } => compare_opcode_maps(&rust_json, &decoder_id, &js_routes),
        Command::SemanticDictionary { batch_json, output } => {
            semantic_dictionary(&batch_json, output.as_deref())
        }
        Command::DumpLinkedBytecode {
            jsonl,
            instructions,
            max_decoders,
            builder_start,
            include_all,
        } => bytecode::dump_linked_bytecode(
            &jsonl,
            instructions,
            max_decoders,
            builder_start,
            include_all,
        ),
        Command::ExtractLinkedStreams {
            file,
            scanner,
            output,
            preview,
        } => {
            bytecode::extract_linked_streams(&file, scanner.as_deref(), output.as_deref(), preview)
        }
    }
}
